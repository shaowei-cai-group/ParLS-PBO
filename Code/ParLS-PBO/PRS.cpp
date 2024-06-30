#include "PRS.hpp"
#include "workers/basesolver.h"
#include <unordered_map>
#include <unordered_set>
using namespace std;
std::atomic<int> terminated;

void *solve_worker(void *arg)
{
    basesolver *sq = (basesolver *)arg;
    sq->parse_from_wecnf();
    sq->shuffle_init();
    int res = sq->solve();
    if (res != 2)
    {
        terminated = 1;
        sq->controller->terminate_workers();
    }
    return NULL;
}

void PRS::init_workers()
{
    terminated = 0;
    for (int i = 0; i < OPT(nThreads); i++)
    {
        basesolver *solver = new basesolver(i, opt_result, this);
        workers.push_back(solver);
    }
}

void PRS::diversity_workers()
{
    for (int i = 0; i < OPT(nThreads); i++)
        workers[i]->diversity();
}

void PRS::terminate_workers()
{
    for (int i = 0; i < OPT(nThreads); i++)
        workers[i]->terminate();
}

void PRS::solve()
{
    printf("c -----------------solve start----------------------\n");
    pthread_t *ptr = new pthread_t[OPT(nThreads)];
    for (int i = 0; i < OPT(nThreads); i++)
    {
        pthread_create(&ptr[i], NULL, solve_worker, workers[i]);
    }

    int sol_thd = 0;
    while (!terminated)
    {
        usleep(100000);
        auto clk_now = chrono::high_resolution_clock::now();
        int solve_time = chrono::duration_cast<chrono::seconds>(clk_now - clk_st_global).count();
        if (solve_time >= OPT(cutoff))
        {
            terminated = 1;
            terminate_workers();
        }
    }
    printf("c ending solve\n");

    for (int i = 0; i < OPT(nThreads); i++)
    {
        pthread_join(ptr[i], NULL);
    }
    printf("c ending join\n");

    int winner_id = -1;
    for (int i = 0; i < OPT(nThreads); i++)
    {
        if (workers[i]->best_weight == -1)
            continue;
        if (winner_id == -1)
            winner_id = i;
        else if (workers[i]->best_weight < workers[winner_id]->best_weight ||
                 (workers[i]->best_weight == workers[winner_id]->best_weight &&
                  workers[i]->best_time < workers[winner_id]->best_time))
            winner_id = i;
    }
    if (OPT(LA) == 1)
    {
        double up_var = 0;
        double up_clause = 0;
        double up_time = 0;
        int cnt = 0;
        for (int i = 0; i < OPT(nThreads); i++)
        {
            if (workers[i]->up_var == -1)
                continue;
            up_var += workers[i]->up_var;
            up_clause += workers[i]->up_clause;
            up_time += workers[i]->up_time;
            cnt++;
        }
        if (cnt > 0)
            printf("P\t\t%f\t%f\t%f\n", up_var / cnt, up_clause / cnt, up_time / cnt);
    }
    if (winner_id != -1)
    {
        printf("c la_idx is %d; la_val is %d\n", workers[winner_id]->la_idx, workers[winner_id]->la_val);
        workers[winner_id]->print_solution();
        printf("c best_time is %lf\n", workers[winner_id]->best_time);
    }

    else
        printf("U\t no feasible solution\n");

    auto clk_now = chrono::high_resolution_clock::now();
    double solve_time = chrono::duration_cast<chrono::milliseconds>(clk_now - clk_st_global).count();
    solve_time = 0.001 * solve_time;
    printf("c winner is %d\n", winner_id);
    delete[] ptr;
}

int UP(int &new_num_vars, int &new_num_clauses, const ll top_clause_weight, ll *&new_org_clause_weight,
       int *&new_clause_lit_count, int *&new_clause_true_lit_thres, lit **&new_clause_lit,
       ll &wecnf_obj_pre, ll &real_obj_pre, int la_idx, int la_val,
       int *&new_old_var, int *&fix_var, const PRS &prs)
{
    // printf("1.....%d,%d\n", la_idx, la_val);
    auto clk_1 = chrono::high_resolution_clock::now();
    vector<ll> sum_left(prs.ori_clause_num);
    vector<int> queue_idx;
    vector<int> queue_val;
    vector<int> scan_idx(prs.ori_clause_num);
    for (int i = 1; i <= prs.ori_var_num; ++i)
    {
        fix_var[i] = -1;
        new_old_var[i] = i;
    }
    if (la_idx != -1)
    {
        queue_idx.reserve(1000);
        queue_val.reserve(1000);
        queue_idx.push_back(la_idx);
        queue_val.push_back(la_val);
        fix_var[la_idx] = la_val;
    }
    for (int c = 0; c < prs.ori_clause_num; ++c)
    {
        scan_idx[c] = prs.clause_lit_count[c] - 1;
        sum_left[c] = 0;
        for (int j = 0; j < prs.clause_lit_count[c]; ++j)
            sum_left[c] += prs.ori_clause_lit[c][j].weight;
    }
    for (int c = 0; c < prs.ori_clause_num; ++c)
    {
        if (prs.org_clause_weight[c] != top_clause_weight)
            continue;
        for (int j = scan_idx[c]; j >= 0; --j)
            if (sum_left[c] - prs.ori_clause_lit[c][j].weight + 1 <= prs.clause_true_lit_thres[c])
            {
                if (fix_var[prs.ori_clause_lit[c][j].var_num] == -1)
                {
                    queue_idx.push_back(prs.ori_clause_lit[c][j].var_num);
                    queue_val.push_back(prs.ori_clause_lit[c][j].sense);
                    fix_var[prs.ori_clause_lit[c][j].var_num] = prs.ori_clause_lit[c][j].sense;
                    scan_idx[c] = j - 1;
                }
                else if (fix_var[prs.ori_clause_lit[c][j].var_num] != prs.ori_clause_lit[c][j].sense)
                    return -1;
            }
            else
                break;
    }
    auto clk_2 = chrono::high_resolution_clock::now();
    if (queue_idx.size() == 0)
        return 0;
    while (queue_idx.size() > 0)
    {
        int idx = queue_idx[queue_idx.size() - 1];
        int val = queue_val[queue_idx.size() - 1];
        queue_idx.pop_back();
        queue_val.pop_back();
        for (int i = 0; i < prs.watch[idx].size(); i++)
        {
            lit now_lit = prs.watch[idx][i];
            int c = now_lit.clause_num;
            if (now_lit.sense == val)
            {
                sum_left[c] -= now_lit.weight;
                new_clause_true_lit_thres[c] -= now_lit.weight;
            }
            else
                sum_left[c] -= now_lit.weight;
            if (prs.org_clause_weight[c] != top_clause_weight)
                continue;
            for (int j = scan_idx[c]; j >= 0; --j)
            {
                if (prs.ori_clause_lit[c][j].var_num == idx)
                    continue;
                if (fix_var[prs.ori_clause_lit[c][j].var_num] != -1)
                    continue;
                if (sum_left[c] - prs.ori_clause_lit[c][j].weight + 1 <= new_clause_true_lit_thres[c])
                {
                    if (fix_var[prs.ori_clause_lit[c][j].var_num] == -1)
                    {
                        queue_idx.push_back(prs.ori_clause_lit[c][j].var_num);
                        queue_val.push_back(prs.ori_clause_lit[c][j].sense);
                        fix_var[prs.ori_clause_lit[c][j].var_num] = prs.ori_clause_lit[c][j].sense;
                        scan_idx[c] = j - 1;
                    }
                    else if (fix_var[prs.ori_clause_lit[c][j].var_num] != prs.ori_clause_lit[c][j].sense)
                        return -1;
                }
                else
                    break;
            }
        }
    }
    // 删数据，重标号
    auto clk_3 = chrono::high_resolution_clock::now();
    new_num_vars = prs.ori_var_num;
    for (int i = 1; i <= prs.ori_var_num; ++i)
        new_num_vars -= (fix_var[i] != -1);
    new_num_clauses = prs.ori_clause_num;
    for (int c = 0; c < prs.ori_clause_num; ++c)
        new_num_clauses -= (new_clause_true_lit_thres[c] <= 0) || (sum_left[c] < new_clause_true_lit_thres[c]);
    int *old_new_var = new int[prs.ori_var_num + 10];
    int *new_old_clause = new int[prs.ori_clause_num + 10];
    int new_idx = 1;
    int old_idx = 1;
    while (old_idx <= prs.ori_var_num)
        if (fix_var[old_idx] == -1)
        {
            old_new_var[old_idx] = new_idx;
            new_old_var[new_idx] = old_idx;
            new_idx++;
            old_idx++;
        }
        else
            old_idx++;
    assert(new_idx == new_num_vars + 1);
    new_idx = 0;
    old_idx = 0;
    while (old_idx < prs.ori_clause_num)
    {
        if (prs.org_clause_weight[old_idx] == top_clause_weight)
        {
            // printf("sum_left[old_idx] < new_clause_true_lit_thres[old_idx]: %d", sum_left[old_idx] < new_clause_true_lit_thres[old_idx]);
            if (sum_left[old_idx] < new_clause_true_lit_thres[old_idx])
            {
                // printf("%d\n", old_idx);
                return -1;
            }

            if (new_clause_true_lit_thres[old_idx] > 0)
            {
                new_old_clause[new_idx] = old_idx;
                new_idx++;
                old_idx++;
            }
            else
                old_idx++;
        }
        else
        {
            if (sum_left[old_idx] < new_clause_true_lit_thres[old_idx])
            {
                // unsat
                wecnf_obj_pre += prs.org_clause_weight[old_idx];
                if (fix_var[prs.ori_clause_lit[old_idx][0].var_num] == 1)
                    real_obj_pre += prs.org_clause_weight[old_idx] * (prs.ori_clause_lit[old_idx][0].sense == 1 ? -1 : 1);
                old_idx++;
            }
            else if (new_clause_true_lit_thres[old_idx] <= 0)
            {
                // sat
                if (fix_var[prs.ori_clause_lit[old_idx][0].var_num] == 1)
                    real_obj_pre += new_org_clause_weight[old_idx] * (prs.ori_clause_lit[old_idx][0].sense == 1 ? -1 : 1);
                old_idx++;
            }
            else
            {
                // unfix
                new_old_clause[new_idx] = old_idx;
                new_idx++;
                old_idx++;
            }
        }
    }
    auto clk_4 = chrono::high_resolution_clock::now();
    assert(new_idx == new_num_clauses);
    int total_lits = 0;
    for (int c = 0; c < new_num_clauses; c++)
    {
        int old_c = new_old_clause[c];
        for (int v = 0; v < prs.clause_lit_count[old_c]; v++)
            if (fix_var[prs.ori_clause_lit[old_c][v].var_num] == -1)
                ++total_lits;
        ++total_lits;
    }
    lit *space = new lit[total_lits];
    int total_id = 0;
    for (int c = 0; c < new_num_clauses; c++)
    {
        int old_c = new_old_clause[c];
        new_org_clause_weight[c] = prs.org_clause_weight[old_c];
        new_clause_lit_count[c] = prs.clause_lit_count[old_c];
        new_clause_true_lit_thres[c] = new_clause_true_lit_thres[old_c];
        new_idx = 0;
        old_idx = 0;
        // new_clause_lit[c] = new lit[prs.clause_lit_count[old_c] + 1];
        new_clause_lit[c] = &space[total_id];
        while (old_idx < new_clause_lit_count[old_c])
        {
            if (fix_var[prs.ori_clause_lit[old_c][old_idx].var_num] == -1)
            {
                new_clause_lit[c][new_idx].clause_num = c;
                new_clause_lit[c][new_idx].var_num = old_new_var[prs.ori_clause_lit[old_c][old_idx].var_num];
                assert(new_clause_lit[c][new_idx].var_num > 0);
                new_clause_lit[c][new_idx].weight = prs.ori_clause_lit[old_c][old_idx].weight;
                new_clause_lit[c][new_idx].sense = prs.ori_clause_lit[old_c][old_idx].sense;
                new_idx++;
                total_id++;
            }
            old_idx++;
        }
        new_clause_lit[c][new_idx].var_num = 0;
        new_clause_lit[c][new_idx].clause_num = -1;
        new_clause_lit[c][new_idx].weight = 0;
        new_clause_lit_count[c] = new_idx;
        total_id++;
        assert(new_idx != 0);
    }
    assert(total_id == total_lits);
    auto clk_5 = chrono::high_resolution_clock::now();
    double solve_1 = 0.001 * chrono::duration_cast<chrono::milliseconds>(clk_2 - clk_1).count();
    double solve_2 = 0.001 * chrono::duration_cast<chrono::milliseconds>(clk_3 - clk_2).count();
    double solve_3 = 0.001 * chrono::duration_cast<chrono::milliseconds>(clk_4 - clk_3).count();
    double solve_4 = 0.001 * chrono::duration_cast<chrono::milliseconds>(clk_5 - clk_4).count();
    printf("time1: %f\ttime2: %f\ttime3: %f\ttime4: %f\n", solve_1, solve_2, solve_3, solve_4);
    // printf("new_num_vars: %d,prs.ori_var_num: %d,new_num_clauses: %d,prs.ori_clause_num: %d\n",
    //        new_num_vars, prs.ori_var_num, new_num_clauses, prs.ori_clause_num);
    return 1;
}

void PRS::get_wecnf(basesolver *worker, int la_idx, int la_val)
{
    Satlike *pms = worker->solver;
    pms->num_vars = num_vars;
    pms->num_clauses = num_clauses;
    pms->top_clause_weight = top_clause_weight;
    pms->wecnf_obj_pre = wecnf_obj_pre;
    pms->real_obj_pre = real_obj_pre;
    for (int c = 0; c < num_clauses; c++)
    {
        pms->clause_lit_count[c] = clause_lit_count[c];
        pms->org_clause_weight[c] = org_clause_weight[c];
        pms->clause_true_lit_thres[c] = clause_true_lit_thres[c];
    }
    if (la_idx == -2)
    {
        int total_lits = 0;
        for (int c = 0; c < num_clauses; c++)
            total_lits += clause_lit_count[c] + 1;
        lit *space = new lit[total_lits];
        int total_id = 0;
        for (int c = 0; c < num_clauses; c++)
        {
            pms->clause_lit[c] = &space[total_id];
            for (int i = 0; i <= clause_lit_count[c]; ++i)
            {
                pms->clause_lit[c][i].clause_num = clause_lit[c][i].clause_num;
                pms->clause_lit[c][i].var_num = clause_lit[c][i].var_num;
                pms->clause_lit[c][i].weight = clause_lit[c][i].weight;
                pms->clause_lit[c][i].sense = clause_lit[c][i].sense;
            }
            total_id += clause_lit_count[c] + 1;
        }
        assert(total_id == total_lits);
        return;
    }
    else
    {
        worker->new_old_var = new int[num_vars + 10];
        worker->fix_var = new int[num_vars + 10];
        auto clk_st = chrono::high_resolution_clock::now();
        int old_num_vars = pms->num_vars;
        int res = UP(pms->num_vars, pms->num_clauses, pms->top_clause_weight, pms->org_clause_weight,
                     pms->clause_lit_count, pms->clause_true_lit_thres, pms->clause_lit,
                     pms->wecnf_obj_pre, pms->real_obj_pre, la_idx, la_val,
                     worker->new_old_var, worker->fix_var, *this);
        if (res == -1)
        {
            if (la_idx == -1)
            {
                printf("infeasible.\n");
                printf("U\t no feasible solution\n");
                exit(0);
            }
            get_wecnf(worker, -1, la_val);
        }
        else if (la_idx != -1)
        {
            auto clk_now = chrono::high_resolution_clock::now();
            double solve_time = chrono::duration_cast<chrono::milliseconds>(clk_now - clk_st).count();
            solve_time = 0.001 * solve_time;
            int hard_num_clauses = 0;
            for (int c = 0; c < pms->num_clauses; c++)
                if (pms->org_clause_weight[c] == pms->top_clause_weight)
                    hard_num_clauses++;
            worker->up_var = (float)pms->num_vars / (float)old_num_vars;
            worker->up_clause = (float)hard_num_clauses / (float)ori_hard_num_clauses;
            worker->up_time = solve_time;
            // printf("%f,%f,%f\n", worker->up_var, worker->up_clause, worker->up_time);
        }
        if (res == 0)
        {
            int total_lits = 0;
            for (int c = 0; c < num_clauses; c++)
                total_lits += clause_lit_count[c] + 1;
            lit *space = new lit[total_lits];
            int total_id = 0;
            for (int c = 0; c < num_clauses; c++)
            {
                pms->clause_lit[c] = &space[total_id];
                for (int i = 0; i <= clause_lit_count[c]; ++i)
                {
                    pms->clause_lit[c][i].clause_num = ori_clause_lit[c][i].clause_num;
                    pms->clause_lit[c][i].var_num = ori_clause_lit[c][i].var_num;
                    pms->clause_lit[c][i].weight = ori_clause_lit[c][i].weight;
                    pms->clause_lit[c][i].sense = ori_clause_lit[c][i].sense;
                }
                total_id += clause_lit_count[c] + 1;
            }
            assert(total_id == total_lits);
        }
    }
    return;
}

void PRS::read_wecnf_UP()
{
    istringstream iss;
    char line[1024];
    string line2;
    char tempstr1[10];
    char tempstr2[10];
    int i, v, c;
    ifstream infile(filename);
    if (!infile)
    {
        printf("c the input filename %s is invalid, please input the correct filename.\n", filename);
        exit(-1);
    }
    getline(infile, line2);
    while (line2[0] != 'p')
        getline(infile, line2);
    for (i = 0; i < 1024; i++)
        line[i] = line2[i];
    sscanf(line, "%s %s %d %d %lld", tempstr1, tempstr2, &num_vars, &num_clauses, &top_clause_weight);
    org_clause_weight = new long long[num_clauses + 10];
    clause_true_lit_thres = new int[num_clauses + 10];
    clause_lit_count = new int[num_clauses + 10];
    ori_clause_lit = new lit *[num_clauses + 10];
    clause_lit = new lit *[num_clauses + 10];
    vector<pair<int, int>> temp_weight_lit;
    temp_weight_lit.reserve(num_vars + 10);
    int cur_weight;
    int cur_lit;
    c = 0;
    while (getline(infile, line2))
    {
        if (line2[0] == 'c')
            continue;
        else
        {
            iss.clear();
            iss.str(line2);
            iss.seekg(0, ios::beg);
        }
        clause_lit_count[c] = 0;
        temp_weight_lit.clear();
        iss >> org_clause_weight[c];
        iss >> clause_true_lit_thres[c];
        iss >> cur_weight;
        iss >> cur_lit;
        while (cur_weight != 0)
        {
            temp_weight_lit.push_back(make_pair(cur_weight, cur_lit));
            clause_lit_count[c]++;
            iss >> cur_weight;
            iss >> cur_lit;
        }
        assert(temp_weight_lit.size() == clause_lit_count[c]);
        std::sort(temp_weight_lit.begin(), temp_weight_lit.end(), std::less<std::pair<int, int>>());
        ori_clause_lit[c] = new lit[clause_lit_count[c] + 1];
        for (i = 0; i < clause_lit_count[c]; ++i)
        {
            ori_clause_lit[c][i].clause_num = c;
            ori_clause_lit[c][i].var_num = abs(temp_weight_lit[i].second);
            ori_clause_lit[c][i].weight = temp_weight_lit[i].first;
            if (temp_weight_lit[i].second > 0)
                ori_clause_lit[c][i].sense = 1;
            else
                ori_clause_lit[c][i].sense = 0;
        }
        ori_clause_lit[c][i].var_num = 0;
        ori_clause_lit[c][i].clause_num = -1;
        ori_clause_lit[c][i].weight = 0;
        c++;
    }
    for (int c = 0; c < num_clauses; c++)
        if (org_clause_weight[c] == top_clause_weight)
            ori_hard_num_clauses++;
    infile.close();
    watch.resize(num_vars + 1);
    for (int c = 0; c < num_clauses; ++c)
        for (int j = 0; j < clause_lit_count[c]; ++j)
            watch[ori_clause_lit[c][j].var_num].push_back(ori_clause_lit[c][j]);

    ori_var_num = num_vars;
    ori_clause_num = num_clauses;
    global_score_0 = new double[ori_var_num + 1];
    global_score_1 = new double[ori_var_num + 1];
    for (int i = 1; i <= ori_var_num; i++)
    {
        global_score_0[i] = 1;
        global_score_1[i] = 1;
    }
    if (OPT(LA) == 0)
    {
        auto clk_st = chrono::high_resolution_clock::now();
        int old_num_vars = num_vars;
        int old_num_clauses = num_clauses;
        new_old_var = new int[num_vars + 10];
        fix_var = new int[num_vars + 10];
        int res;
        if (OPT(UP) == 1)
            res = UP(num_vars, num_clauses, top_clause_weight, org_clause_weight,
                         clause_lit_count, clause_true_lit_thres, clause_lit,
                         wecnf_obj_pre, real_obj_pre, -1, 0,
                         new_old_var, fix_var, *this);
        else
        {
            for (int i = 1; i <= ori_var_num; ++i)
            {
                fix_var[i] = -1;
                new_old_var[i] = i;
            }
            res = 0;
        }
        printf("res: %d\n", res);
        if (res == -1)
        {
            printf("infeasible.\n");
            printf("U\t no feasible solution\n");
            exit(0);
        }
        else if (res == 0)
        {
            int total_lits = 0;
            for (int c = 0; c < num_clauses; c++)
                total_lits += clause_lit_count[c] + 1;
            lit *space = new lit[total_lits];
            int total_id = 0;
            for (int c = 0; c < num_clauses; c++)
            {
                clause_lit[c] = &space[total_id];
                for (int i = 0; i <= clause_lit_count[c]; ++i)
                {
                    clause_lit[c][i].clause_num = ori_clause_lit[c][i].clause_num;
                    clause_lit[c][i].var_num = ori_clause_lit[c][i].var_num;
                    clause_lit[c][i].weight = ori_clause_lit[c][i].weight;
                    clause_lit[c][i].sense = ori_clause_lit[c][i].sense;
                }
                total_id += clause_lit_count[c] + 1;
            }
            assert(total_id == total_lits);
        }
        auto clk_now = chrono::high_resolution_clock::now();
        double solve_time = chrono::duration_cast<chrono::milliseconds>(clk_now - clk_st).count();
        solve_time = 0.001 * solve_time;
        printf("P\t%f \t%f \t%f\n", (float)num_vars / (float)old_num_vars, (float)num_clauses / (float)old_num_clauses, solve_time);
    }
    else
    {
        la_idx_array = new int[16];
        la_idx_array[0] = -1;
        la_idx_array[1] = -1;
        unsigned int seed = 0;
        for (int i = 2; i < 16; i++)
        {
            la_idx_array[i] = rand_r(&seed) % ori_var_num;
            // printf("%d\t", la_idx_array[i]);
        }
    }
}
void PRS::run()
{
    read_wecnf_UP();
    init_workers();
    diversity_workers();
    solve();
}

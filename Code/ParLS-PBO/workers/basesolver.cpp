#include "basesolver.h"
#include "solvers/basis_pms.h"

void call_back_punish(void *issuer)
{
    basesolver *S = (basesolver *)issuer;
    if (S->recent_weight != -1)
        S->recent_weight *= 1.1;
    // printf("c call_back_punish (%lld),(%lld)\n", S->recent_weight, S->best_weight);
    return;
}

int call_back_update_recent(void *issuer, int recent_val, int *sol, int vars)
{
    basesolver *S = (basesolver *)issuer;
    PRS *prs = S->controller;
    if (S->recent_weight == -1 || S->recent_weight > recent_val)
    {
        S->recent_weight = recent_val;
        for (int i = 1; i <= vars; i++)
            S->recent_model[S->new_old_var[i] - 1] = sol[i];
        // printf("c call_back_update_recent (%lld),(%lld)\n", S->recent_weight, S->best_weight);
        return 1;
    }
    return 0;
}

void call_back_update(void *issuer, int best_val, int *sol, int vars, ll best_real)
{
    basesolver *S = (basesolver *)issuer;
    PRS *prs = S->controller;
    if (S->best_weight == -1 || S->best_weight > best_val)
    {
        S->best_weight = best_val;
        S->best_real = best_real;
        // printf("c update best_real (%d)\n", best_real);
        for (int i = 1; i <= vars; i++)
            S->model[S->new_old_var[i] - 1] = sol[i];
        if (S->controller->opt->sharing_period != -1)
        {
            auto clk_1 = chrono::high_resolution_clock::now();
            S->controller->pool_update(S->model, S->best_weight);
            auto clk_now = chrono::high_resolution_clock::now();
            S->pool_time += 0.001 * chrono::duration_cast<chrono::milliseconds>(clk_now - clk_1).count();
            // printf("c   id: %d, pool_time: %.3f\n", S->id, S->pool_time);
        }

        auto now = chrono::high_resolution_clock::now();
        auto duration = chrono::duration_cast<chrono::milliseconds>(now - S->start);
        S->best_time = duration.count() / 1000.0;
    }
}

int call_back_get_other_model(void *issuer, int vars, int now_val, int *cur_sol)
{
    // printf("call_back_get_other_model.......\n");
    basesolver *S = (basesolver *)issuer;
    PRS *prs = S->controller;
    int ran_val = rand_r(&S->solver->seed) % 100;
    if (prs->opt->cross_base == 0 || prs->opt->cross_base == 2 && ran_val < 50)
        return prs->pool_cross(S->id, S->solver->seed, S->best_weight, S->model);
    else if (prs->opt->cross_base == 1 || prs->opt->cross_base == 2 && ran_val >= 50)
    {
        vector<int> cur_model(S->model);
        for (int i = 1; i <= vars; i++)
            cur_model[S->new_old_var[i] - 1] = cur_sol[i];
        return prs->pool_cross(S->id, S->solver->seed, now_val, cur_model);
    }
    else if (prs->opt->cross_base == 3)
        return prs->pool_cross(S->id, S->solver->seed, S->recent_weight, S->recent_model);
}

basesolver::basesolver(int tid, ll opt_result, PRS *PRS) : id(tid), controller(PRS), best_weight(-1), recent_weight(-1)
{
    solver = new Satlike();
    solver->issuer = this;
    solver->cbkUpdateSolution = call_back_update;
    if (controller->opt->punish_period != -1)
    {
        solver->cbkPunish = call_back_punish;
        solver->cbkUpdateRecent = call_back_update_recent;
    }
    else
    {
        solver->cbkPunish = NULL;
        solver->cbkUpdateRecent = NULL;
    }
    if (controller->opt->sharing_period != -1)
        solver->cbkGetOtherModel = call_back_get_other_model;
    else
        solver->cbkGetOtherModel = NULL;
    this->LA = controller->opt->LA;
    solver->opt_result = opt_result;
    solver->seed = id ? id : 1000007;
    solver->id = id;
    solver->sharing_period = controller->opt->sharing_period;
    solver->punish_period = controller->opt->punish_period;
    solver->restart_period = controller->opt->restart_period;
    solver->gs_prob = controller->opt->gs_prob;
    this->cross_proportion = controller->opt->cross_proportion;
}

void basesolver::diversity()
{
    if (id < 16)
        solver->cccheck = 1;
    else
        solver->cccheck = 0;
    solver->weighting = (id + 1) % 2;
}

void basesolver::parse_from_wecnf()
{
    PRS *prs = controller;
    if (LA == 1) // 正常UP+LA
    {
        la_idx = prs->la_idx_array[id / 2];
        la_val = id % 2;
        if (la_idx > prs->num_vars)
            la_idx = -1;
    }
    else // 无LA，仅拷贝主线程的UP
    {
        la_idx = -2;
        new_old_var = prs->new_old_var;
        fix_var = prs->fix_var;
    }
    solver->org_clause_weight = new long long[prs->ori_clause_num + 10];
    solver->clause_true_lit_thres = new int[prs->ori_clause_num + 10];
    solver->clause_lit_count = new int[prs->ori_clause_num + 10];
    solver->clause_lit = new lit *[prs->ori_clause_num + 10];
    for (int c = 0; c < prs->ori_clause_num; c++)
    {
        solver->clause_lit_count[c] = 0;
        solver->clause_true_lit_thres[c] = 1;
        solver->clause_lit[c] = NULL;
    }
    prs->get_wecnf(this, la_idx, la_val);
    this->ori_val_num = prs->ori_var_num;
    this->model.resize(ori_val_num);
    this->recent_model.resize(ori_val_num);
    for (int i = 1; i <= ori_val_num; i++)
    {
        if (fix_var[i] != -1)
        {
            model[i - 1] = fix_var[i];
            recent_model[i - 1] = fix_var[i];
        }
    }
    auto clk_now = chrono::high_resolution_clock::now();
    double pre_time = 0.001 * chrono::duration_cast<chrono::milliseconds>(clk_now - prs->clk_st_global).count();
    // printf("pre_time_1: %f\n", pre_time);
    solver->build_instance();
    clk_now = chrono::high_resolution_clock::now();
    pre_time = 0.001 * chrono::duration_cast<chrono::milliseconds>(clk_now - prs->clk_st_global).count();
    solver->global_score_0 = prs->global_score_0;
    solver->global_score_1 = prs->global_score_1;
    solver->new_old_var = new_old_var;
    // printf("pre_time_2: %f\n", pre_time);
}

void basesolver::shuffle_init()
{
    // assert(!init_solution.size());
    init_solution.clear();
    int vars = solver->num_vars;
    init_solution.push_back(0);
    unsigned int seed = id;
    for (int i = 1; i <= vars; i++)
    {
        if (id == 0)
            init_solution.push_back(0);
        else if (id == 1)
            init_solution.push_back(1);
        else
            init_solution.push_back(rand_r(&seed) % 2);
    }
}

int basesolver::solve()
{
    return solver->local_search_with_decimation(init_solution);
}

void basesolver::terminate()
{
    solver->terminated = 1;
}

void basesolver::print_solution()
{
    int vars = model.size();
    assert(vars);
    solver->opt_time = best_time;
    if (solver->verify_sol())
    {
        printf("B   %lld    %lld\n", best_weight, best_real);
        // for (int i = 1; i <= ori_val_num; i++)
        //     printf("%d ", model[i - 1]);
        // printf("\n");
    }
    else
    {
        printf("wrong.\n");
    }
}

basesolver::~basesolver()
{
    solver->free_memory();
    controller = nullptr;
    model.clear();
}

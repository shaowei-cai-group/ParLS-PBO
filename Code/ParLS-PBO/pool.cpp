#include "PRS.hpp"
#include "workers/basesolver.h"

void PRS::global_score_update(const vector<int> &model)
{
    for (int i = 1; i <= ori_var_num; i++)
    {
        if (global_score_1[i] > 1)
            global_score_1[i] -= 0.1 * OPT(gs_inc);
        else
            global_score_1[i] += 0.1 * OPT(gs_inc);
        if (global_score_0[i] > 1)
            global_score_0[i] -= 0.1 * OPT(gs_inc);
        else
            global_score_0[i] += 0.1 * OPT(gs_inc);
        if (model[i - 1] == 1)
        {
            if (global_score_1[i] < 1 + OPT(gs_bound))
                global_score_1[i] += OPT(gs_inc);
            if (1 - OPT(gs_bound) < global_score_0[i])
                global_score_0[i] -= OPT(gs_inc);
        }
        else
        {
            if (global_score_0[i] < 1 + OPT(gs_bound))
                global_score_0[i] += OPT(gs_inc);
            if (1 - OPT(gs_bound) < global_score_1[i])
                global_score_1[i] -= OPT(gs_inc);
        }
    }
}

void PRS::pool_update(vector<int> model, ll obj)
{
    boost::mutex::scoped_lock lock(pool.mtx_pool);
    // count++;
    solution sol(model, obj);
    for (int i = 0; i < pool.size(); ++i)
    {
        if (sol == pool[i])
        {
            // printf("c exsit same solution in pool (%d)\n", obj);
            return;
        }
    }
    pool.solutions.push_back(sol);
    if (pool.size() <= OPT(pool_size))
    {
        global_score_update(model);
        return;
    }

    for (int i = 0; i < pool.size(); ++i)
    {
        pool[i].same = 0;
        for (int j = 0; j < pool.size(); ++j)
        {
            if (i == j)
                continue;
            for (int k = 0; k < pool[i].model.size(); ++k)
                pool[i].same += (pool[i][k] == pool[j][k]);
        }
    }
    int worst_score, worst_index = -1;
    for (int i = 0; i < pool.size(); ++i)
    {
        int obj_rank = 1, same_rank = 1;
        for (int j = 0; j < pool.size(); ++j)
        {
            if (i == j)
                continue;
            obj_rank += (pool[i].obj < pool[j].obj);
            same_rank += (pool[i].same < pool[j].same);
        }
        pool[i].score = same_rank * OPT(rankpara) + obj_rank * (100 - OPT(rankpara)); // max is better
        if (worst_index == -1 || pool[i].score < worst_score)
        {
            worst_index = i;
            worst_score = pool[i].score;
        }
    }
    int new_index = pool.size() - 1;
    if (worst_index != new_index)
    {
        pool[worst_index].obj = pool[new_index].obj;
        pool[worst_index].same = pool[new_index].same;
        for (int k = 0; k < pool[worst_index].model.size(); ++k)
            pool[worst_index][k] = pool[new_index][k];
    }
    pool.solutions.pop_back();
    // printf("c update pool (%d)\n", obj);
    global_score_update(model);
    return;
}

int PRS::pool_select(ll now_obj, unsigned int seed)
{
    if (now_obj == -1)
        now_obj = 1000000000000000000;
    if (OPT(cross_heuristic) == 0)
    { // 选最好的
        int best_index = 0;
        for (int i = 0; i < pool.size(); ++i)
            if (pool[i].obj < pool[best_index].obj)
                best_index = i;
        if (pool[best_index].obj >= now_obj)
            return -1;
        vector<int> best_arr;
        for (int i = 0; i < pool.size(); ++i)
            if (pool[i].obj == pool[best_index].obj)
                best_arr.push_back(i);
        return best_arr[rand_r(&seed) % best_arr.size()];
    }
    if (OPT(cross_heuristic) == 1)
    { // 在比当前线程(最优解/当前解)优秀的几个中按相同概率选
        vector<int> better_index;
        for (int i = 0; i < pool.size(); ++i)
            if (pool[i].obj < now_obj)
                better_index.push_back(i);
        if (better_index.size() == 0)
            return -1;
        return better_index[rand_r(&seed) % better_index.size()];
    }
    if (OPT(cross_heuristic) == 2) // 在比当前线程(最优解/当前解)优秀的几个中按递增的概率选
    {
        vector<int> better_index;
        vector<double> index_prop;
        int best_index = 0;
        for (int i = 0; i < pool.size(); ++i)
        {
            if (pool[i].obj < now_obj)
            {
                better_index.push_back(i);
                index_prop.push_back(pool[i].obj);
            }
            if (pool[i].obj < pool[best_index].obj)
                best_index = i;
        }
        if (better_index.size() == 0)
            return -1;
        ll best_obj = pool[best_index].obj;
        double prop_sum = 0;
        for (int i = 0; i < better_index.size(); ++i)
        {
            index_prop[i] = best_obj / index_prop[i];
            prop_sum += index_prop[i];
        }
        for (int i = 0; i < better_index.size(); ++i)
            index_prop[i] /= prop_sum;
        double choose_prop = (rand_r(&seed) % 1000) / 1000;
        double temp_prop = 0;
        int choose_index = -1;
        for (int i = 0; i < better_index.size(); ++i)
        {
            temp_prop += index_prop[i];
            if (temp_prop > choose_prop)
            {
                choose_index = better_index[i];
                break;
            }
        }
        return choose_index;
    }
}

int PRS::pool_cross(int id, unsigned int seed, ll cross_obj, vector<int> const &cross_sol)
{
    boost::mutex::scoped_lock lock(pool.mtx_pool);
    if (pool.size() == 0)
        return -1;
    basesolver *S = workers[id];
    int choose_index = pool_select(cross_obj, seed);
    if (choose_index == -1)
        return -1;
    for (int i = 1; i <= ori_var_num; i++)
    {
        if (S->fix_var[i] != -1 && pool[choose_index].model[i - 1] != S->fix_var[i])
            return -2;
    }
    if (cross_obj == -1)
    {
        // assert(cross_sol.size() == 0);
        for (int i = 1; i < S->solver->num_vars; ++i)
            if (rand_r(&seed) % 100 < S->cross_proportion)
                S->init_solution[i] = pool[choose_index].model[S->new_old_var[i] - 1];
            else
                S->init_solution[i] = rand_r(&seed) % 2;
    }
    else
    {
        assert(cross_sol.size() == pool[choose_index].model.size());
        for (int i = 1; i < S->solver->num_vars; ++i)
        {
            int j = S->new_old_var[i];
            if (cross_sol[j - 1] == pool[choose_index].model[j - 1])
                S->init_solution[i] = cross_sol[j - 1];
            else if (rand_r(&seed) % 100 < S->cross_proportion)
                S->init_solution[i] = pool[choose_index].model[j - 1];
            else
                S->init_solution[i] = cross_sol[j - 1];
        }
    }
    return choose_index;
}
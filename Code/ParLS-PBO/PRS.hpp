#ifndef _PRS_h_INCLUDED
#define _PRS_h_INCLUDED

#include <boost/thread.hpp>
#include <boost/thread/thread.hpp>
#include "utils/paras.h"
#include "utils/vec.h"
#include "solvers/basis_pms.h"
using namespace std;
typedef long long ll;

class basesolver;
struct lit;

class solution
{
public:
    vector<int> model;
    ll obj;
    int same = 0;
    int score = 0;
    solution(vector<int> m, ll o) : model(m), obj(o){};
    int &operator[](int index) { return model[index]; }
    bool operator==(const solution &other) const
    {
        if (other.obj != obj || model.size() != other.model.size())
            return false;
        for (int i = 0; i < model.size(); i++)
            if (model[i] != other.model[i])
                return false;
        return true;
    }
};

class solution_pool
{
public:
    vector<solution> solutions;
    mutable boost::mutex mtx_pool;

    solution &operator[](int index) { return solutions[index]; }
    int size() { return solutions.size(); }
};

struct PRS
{
public:
    PRS() : opt_result(-1)
    {
        opt = new paras();
        opt->init_paras();
    }

    ~PRS()
    {
        for (int i = 0; i < workers.size(); i++)
            delete (workers[i]);
    }

    char *filename;
    paras *opt;
    vector<basesolver *> workers;
    solution_pool pool;
    ll opt_result;
    int count;
    double *global_score_0;
    double *global_score_1;

    int vars, clauses;
    vec<vec<ll>> clause;

    void opb2wecnf(char *filename);
    void arg_parse(int argc, char **argv);
    void init_workers();
    void diversity_workers();
    void run();
    void solve();
    void terminate_workers();

    void pool_update(vector<int> model, ll obj);
    int pool_select(ll now_obj, unsigned int seed);
    int pool_cross(int id, unsigned int seed, ll cross_obj, vector<int> const &cross_sol);
    void global_score_update(const vector<int> &model);

    /**************************for UP****************************/
    int num_vars;    // var index from 1 to num_vars
    int num_clauses; // clause index from 0 to num_clauses-1
    ll top_clause_weight;
    int *clause_lit_count; // amount of literals in each clause
    ll *org_clause_weight;
    int *clause_true_lit_thres;
    lit **clause_lit; // clause_lit[i][j] means the j'th literal of clause i.
    chrono::high_resolution_clock::time_point clk_st_global = chrono::high_resolution_clock::now();
    ll wecnf_obj_pre = 0;
    ll real_obj_pre = 0;
    int *new_old_var;
    int *fix_var;
    vector<vector<lit>> watch;
    ll ori_var_num;
    ll ori_clause_num;
    lit **ori_clause_lit;
    int *la_idx_array;
    int ori_hard_num_clauses = 0;

    void read_wecnf_UP();
    void get_wecnf(basesolver *worker, int la_idx, int la_val);

    friend int UP(int &new_num_vars, int &new_num_clauses, const ll top_clause_weight, ll *&new_org_clause_weight,
                  int *&new_clause_lit_count, int *&new_clause_true_lit_thres, lit **&new_clause_lit,
                  ll &wecnf_obj_pre, ll &real_obj_pre, int la_idx, int la_val,
                  int *&new_old_var, int *&fix_var, const PRS &prs);
};

#endif

#ifndef _basesolver_h_INCLUDED
#define _basesolver_h_INCLUDED
#include <chrono>

#include "PRS.hpp"

struct Satlike;

class basesolver
{
public:
    void diversity();
    void parse_from_wecnf();
    int solve();
    void terminate();
    void shuffle_init();
    void print_solution();
    basesolver(int sid, ll opt_result, PRS *light);
    ~basesolver();

    int id;
    double pool_time = 0;
    int cross_proportion;
    ll best_weight;
    ll best_real;
    ll recent_weight;
    double best_time;
    int LA = 0;
    int la_idx = -1;
    int la_val = 0;
    ll ori_val_num;
    int *new_old_var;
    int *fix_var;
    void *issuer;
    PRS *controller;
    vector<int> init_solution, model, recent_model;
    Satlike *solver;
    chrono::high_resolution_clock::time_point start = chrono::high_resolution_clock::now();

    double up_var = -1;
    double up_clause = -1;
    double up_time = -1;

    friend void call_back_update(void *, int, int *, int, ll);
    friend int call_back_get_other_model(void *, int);
    friend void call_back_punish(void *);
    friend int call_back_update_recent(void *, int, int *, int);
};
#endif
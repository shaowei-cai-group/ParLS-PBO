#ifndef _paras_h_INCLUDED
#define _paras_h_INCLUDED

#include <cstring>
#include <unordered_map>

//        name,               type,   default, low, high, comments
#define PARAS \
    PARA( cutoff            , double , 5000                     , 0  , 1e8    , "Cutoff time") \
    PARA( nThreads          , int    , 32                       , 1  , 128    , "Thread number") \
    PARA( pool_size         , int    , 18                       , 0  , 100    , "size of solution pool") \
    PARA( cross_base        , int    , 3                        , 0  , 2      , "0 for best model; 1 for cur sol; 2 for diversity; 3 for recent model") \
    PARA( cross_heuristic   , int    , 0                        , 0  , 2      , "0 for best; 1 for same prob; 2 for prefered prob") \
    PARA( cross_proportion  , int    , 100                      , 0  , 100    , "The probability of choosing the pick sol when crossing") \
    PARA( rankpara          , int    , 58                       , 0  , 100    , "same rank para") \
    PARA( sharing_period    , int    , 86295                    , 0  , 1e11   , "Max no improve steps to share") \
    PARA( punish_period     , int    , 5e5                      , 0  , 1e11   , "Max no improve steps to punish recent obj") \
    PARA( restart_period    , int    , -1                       , 0  , 1e11   , "Max no improve steps to restart") \
    PARA( gs_bound          , double , 0.14439157678643627      , 0  , 1      , "global score bound") \
    PARA( gs_inc            , double , 0.030636422601264736     , 0  , 1      , "global score inc") \
    PARA( gs_prob           , int    , 50                       , 0  , 100    , "global score probability") \
    PARA( UP                , int    , 1                        , 0  , 1      , "unit propagation") \
    PARA( LA                , int    , 1                        , 0  , 1      , "literal assume") 

struct paras 
{
#define PARA(N, T, D, L, H, C) \
    T N = D;
    PARAS 
#undef PARA

    std::unordered_map<std::string, int>    map_int;
    std::unordered_map<std::string, double> map_double;
    
    void init_paras ();
    void sync_paras ();
    void print_change ();
    void set_para   (char *arg, int val);
    void set_para   (char *arg, double val);
    long long identify_opt(char *file);
};

#define OPT(N) (opt->N)

#endif
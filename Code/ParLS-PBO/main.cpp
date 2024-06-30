#include "PRS.hpp"

int main(int argc, char **argv) {
    PRS* S = new PRS();
    S->arg_parse(argc, argv);
    S->run();
    delete(S);
    return 0;
}
/* Differential check of the actual native node_interval against enumeration.
 * This is a bounded test, not a formal proof or a Petersen50 exhaustive run. */
#define main archived_counter_main
#include "petersen.c"
#undef main

static uint32_t probe_rng = 20261103;
static uint32_t draw(void) {
    probe_rng = 1664525U * probe_rng + 1013904223U;
    return probe_rng;
}

int main(int argc, char **argv) {
    if (argc < 2) return 1;
    load_case(argv[1]);
    if (argc > 2) parse_pairs(argv[2]);
    build_structures();
    int checked = 0;
    for (int trial = 0; trial < 256; trial++) {
        int depth = n - (trial % 13);
        if (depth < 0) depth = 0;
        uint16_t used[MAXM] = {0};
        /* Any feasible prefix state has a valid suffix bound; arbitrary
         * feasible used vectors test the stronger domain as well. */
        for (int j = 0; j < m; j++) used[j] = draw() % (caps[j] + 1);
        if (trial % 4 == 0) memset(used, 0, sizeof used);
        uint64_t lo, hi, exact = 0;
        node_interval(depth, used, &lo, &hi);
        for (unsigned mask = 0; mask < (1U << (n-depth)); mask++) {
            int ok = 1;
            for (int j = 0; j < m && ok; j++) {
                unsigned sum = used[j];
                for (int k = depth; k < n; k++)
                    if ((mask >> (k-depth)) & 1U) sum += items[k][j];
                if (sum > (unsigned)caps[j]) ok = 0;
            }
            exact += ok;
        }
        if (lo > exact || exact > hi) {
            fprintf(stderr, "unsound bound trial=%d depth=%d\n", trial, depth);
            return 2;
        }
        checked++;
    }
    printf("{\"case_n\":%d,\"pairs\":%d,\"suffix_states_enumerated\":%d}\n", n, NP, checked);
    return 0;
}

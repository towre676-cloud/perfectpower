/* petersen.c -- compiled exact frontier counter for the Petersen
 * planning cases (PerfectPower).  A faithful C port of the machinery
 * in attempt_50.py / bounded_count.py:
 *
 *   - branching order: decreasing sum_j costs[i][j]/caps[j] (double
 *     keys, stable: ties keep the original index order, as Python's
 *     sorted does);
 *   - suffix total cost vectors;
 *   - suffix single-resource prefix counts pref[j][i][s] = # subsets
 *     of items i..n-1 with resource-j sum <= s;
 *   - an exact suffix resource-pair grid for pair (pj,pk) = (3,4):
 *     grids[i][a][b] = # subsets of items i.. with pair sums <= (a,b),
 *     built by a subset DP clamped at (cap_j+1, cap_k+1);
 *   - node interval: exact subcube collapse when the whole suffix
 *     fits; otherwise hi = min(pair count, all single-resource
 *     counts), lo = pair count - sum over the other resources of
 *     (total - single-resource count), clamped to [0, hi].
 *
 * All counts are < 2^63 for these cases (total subsets <= 2^50), so
 * uint64 storage is exact; the lower-bound computation is done in
 * int64 (intermediate magnitudes < 2^56).  No floating point is used
 * anywhere except the branching-order keys, which replicate the
 * Python double arithmetic operation for operation.
 *
 * Modes:
 *   root   CASE.txt
 *       Print the root interval and the branching order.
 *   dfs    CASE.txt [max_seconds]
 *       Single-process depth-first count with the exact stack
 *       discipline of bounded_count.count (pop node; evaluate the
 *       exclude child, then the include child if feasible; push in
 *       that order, so the include child is popped next; children
 *       with lo == hi collapse into the exact constant).  Prints
 *       progress and a final summary line.
 *   bf     CASE.txt [max_seconds] [heap_cap_nodes]
 *       Best-first (widest-first) count; when the heap reaches
 *       heap_cap_nodes the widest node is solved exactly by a
 *       depth-first dive instead of being expanded.  Used for
 *       calibration against dfs.
 *   split  CASE.txt DEPTH PREFIX.bin
 *       Expand from the root to DEPTH (collapsing exact children),
 *       write the live prefix nodes sorted by decreasing width to
 *       PREFIX.bin and print the accounting.
 *   worker CASE.txt PREFIX.bin WORKER_ID RESULTS_DIR BUDGET_S MODE
 *       Claim prefixes (width order) from a shared counter file in
 *       RESULTS_DIR, solve each exactly with MODE = dfs or bf, and
 *       append one JSON line per solved prefix to
 *       RESULTS_DIR/results_w<ID>.jsonl.  Prefixes already present
 *       in any results_w*.jsonl are skipped, so a stopped campaign
 *       resumes by simply rerunning the workers.
 *
 * Checkpoint / prefix file format (all integers little-endian):
 *   header: char[4] "PFX1"; u32 n; u32 m; u32 depth; u32 count;
 *           u64 split_exact; u64 sum_lo; u64 sum_hi;
 *   record: u8 depth; u8 reserved[3]; u16 used[m]; u64 lo; u64 hi.
 * The global rigorous interval at any moment is
 *   [ split_exact + sum of solved exact + sum of unsolved lo,
 *     split_exact + sum of solved exact + sum of unsolved hi ].
 */
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <sys/resource.h>

#ifndef MAXM
#define MAXM 16
#endif
#define MAXPAIRS 10

static int n, m;
static int caps[MAXM];
static int costs_raw[64][MAXM];
static int items[64][MAXM];          /* in branching order */
static int order_idx[64];
static uint32_t suff_tot[65][MAXM];  /* suffix total costs */
static uint64_t *pref[MAXM];         /* per resource: (n+1) x (cap+1) */
/* Resource-pair suffix grids.  With one pair (3,4) the node bounds
   are exactly attempt_50.py's; additional pairs tighten them:
   hi = min over pairs of the pair count, lo = max over pairs of
   (pair count - other resources' violation counts). */
static int NP = 1;
static int pair_j[MAXPAIRS] = {3};
static int pair_k[MAXPAIRS] = {4};
static int pCJ[MAXPAIRS], pCK[MAXPAIRS], pGS[MAXPAIRS];
static uint64_t *pgrid[MAXPAIRS] = {NULL};

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static long peak_rss_kb(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return ru.ru_maxrss;
}

/* ---------------- case loading and structures ---------------- */

static void load_case(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) { perror(path); exit(1); }
    if (fscanf(f, "%d %d", &n, &m) != 2) { fprintf(stderr, "bad case\n"); exit(1); }
    if (m > MAXM || n > 64) { fprintf(stderr, "case too large for this build (m=%d > MAXM=%d)\n", m, MAXM); exit(1); }
    for (int j = 0; j < m; j++) if (fscanf(f, "%d", &caps[j]) != 1) exit(1);
    for (int i = 0; i < n; i++)
        for (int j = 0; j < m; j++)
            if (fscanf(f, "%d", &costs_raw[i][j]) != 1) exit(1);
    fclose(f);
}

static int cmp_idx(const void *a, const void *b) {
    /* keys precomputed in key[]; sort by key desc, then index asc
       (== Python's stable sort by -key). */
    extern double keybuf[64];
    int ia = *(const int *)a, ib = *(const int *)b;
    if (keybuf[ia] < keybuf[ib]) return 1;
    if (keybuf[ia] > keybuf[ib]) return -1;
    return ia - ib;
}
double keybuf[64];

static void build_structures(void) {
    for (int i = 0; i < n; i++) {
        /* CPython's sum() uses Neumaier compensated summation for
           floats; replicate it operation for operation so that ties
           (and hence the stable order) match the Python code. */
        double s = 0.0, comp = 0.0;
        for (int j = 0; j < m; j++) {
            double x = (double)costs_raw[i][j] / (double)caps[j];
            double t = s + x;
            if (fabs(s) >= fabs(x)) comp += (s - t) + x;
            else                    comp += (x - t) + s;
            s = t;
        }
        keybuf[i] = s + comp;
        order_idx[i] = i;
    }
    qsort(order_idx, n, sizeof(int), cmp_idx);
    for (int i = 0; i < n; i++)
        for (int j = 0; j < m; j++) items[i][j] = costs_raw[order_idx[i]][j];

    for (int j = 0; j < m; j++) suff_tot[n][j] = 0;
    for (int i = n - 1; i >= 0; i--)
        for (int j = 0; j < m; j++) suff_tot[i][j] = suff_tot[i + 1][j] + (uint32_t)items[i][j];

    /* single-resource suffix prefix counts */
    for (int j = 0; j < m; j++) {
        int cap = caps[j];
        pref[j] = malloc(sizeof(uint64_t) * (size_t)(n + 1) * (cap + 1));
        if (!pref[j]) { fprintf(stderr, "oom pref\n"); exit(1); }
        uint64_t *dist = calloc(cap + 1, sizeof(uint64_t));
        uint64_t *nd = malloc(sizeof(uint64_t) * (cap + 1));
        dist[0] = 1;
        for (int i = n; i >= 0; i--) {
            uint64_t run = 0;
            uint64_t *row = pref[j] + (size_t)i * (cap + 1);
            for (int s = 0; s <= cap; s++) { run += dist[s]; row[s] = run; }
            if (i == 0) break;
            int a = items[i - 1][j];
            if (a == 0) {
                for (int s = 0; s <= cap; s++) dist[s] *= 2;
            } else {
                memcpy(nd, dist, sizeof(uint64_t) * (cap + 1));
                for (int s = 0; s + a <= cap; s++) if (dist[s]) nd[s + a] += dist[s];
                memcpy(dist, nd, sizeof(uint64_t) * (cap + 1));
            }
        }
        free(dist); free(nd);
    }

    /* resource-pair suffix grids, clamped DP */
    for (int p = 0; p < NP; p++) {
        int pj = pair_j[p], pk = pair_k[p];
        int CJ = caps[pj], CK = caps[pk], GS = CK + 1;
        pCJ[p] = CJ; pCK[p] = CK; pGS[p] = GS;
        int ENC = CK + 2;
        size_t layer = (size_t)(CJ + 1) * GS;
        uint64_t *grid = malloc(sizeof(uint64_t) * (size_t)(n + 1) * layer);
        if (!grid) { fprintf(stderr, "oom grid\n"); exit(1); }
        pgrid[p] = grid;
        uint64_t *dist = calloc((size_t)(CJ + 2) * ENC, sizeof(uint64_t));
        uint64_t *nd = malloc(sizeof(uint64_t) * (size_t)(CJ + 2) * ENC);
        dist[0] = 1;
        for (int i = n; i >= 0; i--) {
            uint64_t *g = grid + (size_t)i * layer;
            for (int a = 0; a <= CJ; a++) {
                uint64_t run = 0;
                for (int b = 0; b <= CK; b++) {
                    run += dist[(size_t)a * ENC + b];
                    g[(size_t)a * GS + b] = (a ? g[(size_t)(a - 1) * GS + b] : 0) + run;
                }
            }
            if (i == 0) break;
            int aj = items[i - 1][pj], ak = items[i - 1][pk];
            memcpy(nd, dist, sizeof(uint64_t) * (size_t)(CJ + 2) * ENC);
            for (int a = 0; a <= CJ + 1; a++) {
                int na = a + aj; if (na > CJ + 1) na = CJ + 1;
                for (int b = 0; b <= CK + 1; b++) {
                    uint64_t v = dist[(size_t)a * ENC + b];
                    if (!v) continue;
                    int nb = b + ak; if (nb > CK + 1) nb = CK + 1;
                    nd[(size_t)na * ENC + nb] += v;
                }
            }
            memcpy(dist, nd, sizeof(uint64_t) * (size_t)(CJ + 2) * ENC);
        }
        free(dist); free(nd);
    }
}

/* ---------------- node interval ---------------- */

static inline void node_interval(int i, const uint16_t *used,
                                 uint64_t *lo_out, uint64_t *hi_out) {
    uint64_t total = 1ULL << (n - i);
    int exact_fit = 1;
    for (int j = 0; j < m; j++)
        if ((uint32_t)used[j] + suff_tot[i][j] > (uint32_t)caps[j]) { exact_fit = 0; break; }
    if (exact_fit) { *lo_out = total; *hi_out = total; return; }
    uint64_t ple[MAXPAIRS];
    uint64_t hi = UINT64_MAX;
    for (int p = 0; p < NP; p++) {
        int remj = caps[pair_j[p]] - used[pair_j[p]];
        int remk = caps[pair_k[p]] - used[pair_k[p]];
        ple[p] = pgrid[p][(size_t)i * (size_t)(pCJ[p] + 1) * pGS[p] +
                          (size_t)remj * pGS[p] + remk];
        if (ple[p] < hi) hi = ple[p];
    }
    uint64_t single_le[MAXM];
    for (int j = 0; j < m; j++) {
        single_le[j] = pref[j][(size_t)i * (caps[j] + 1) + (caps[j] - used[j])];
        if (single_le[j] < hi) hi = single_le[j];
    }
    if (hi == 0) { *lo_out = 0; *hi_out = 0; return; }
    int64_t lo = 0;
    for (int p = 0; p < NP; p++) {
        int64_t lp = (int64_t)ple[p];
        for (int j = 0; j < m; j++) {
            if (j == pair_j[p] || j == pair_k[p]) continue;
            lp -= (int64_t)(total - single_le[j]);
        }
        if (lp > lo) lo = lp;
    }
    if (lo > (int64_t)hi) lo = (int64_t)hi;
    *lo_out = (uint64_t)lo; *hi_out = hi;
}

/* ---------------- nodes, stacks, heaps ---------------- */

typedef struct {
    uint16_t used[MAXM];
    uint64_t lo, hi;
    uint8_t depth;
    uint8_t pad[7];
} Node;

static Node *stack_buf = NULL;
static size_t stack_len = 0, stack_cap = 0;
static void stack_push(const Node *nd) {
    if (stack_len == stack_cap) {
        stack_cap = stack_cap ? stack_cap * 2 : 1024;
        stack_buf = realloc(stack_buf, stack_cap * sizeof(Node));
        if (!stack_buf) { fprintf(stderr, "oom stack\n"); exit(1); }
    }
    stack_buf[stack_len++] = *nd;
}

/* Evaluate the two children of a node at depth i (exclude, then
   include if feasible).  Exact children are added to *exact and to
   the floor/ceiling accumulators by the caller via the callback
   convention: this helper appends non-exact children to out[] and
   returns their count, and adds exact children's values to *exact. */
static uint64_t expansions = 0;

static int eval_children(int i, const uint16_t *used, Node out[2], uint64_t *exact) {
    int ci = i + 1, cnt = 0;
    /* exclude child */
    {
        uint64_t clo, chi;
        if (ci == n) { clo = chi = 1; }
        else node_interval(ci, used, &clo, &chi);
        if (clo == chi) *exact += clo;
        else { out[cnt] = (Node){0}; memcpy(out[cnt].used, used, sizeof(uint16_t) * MAXM); out[cnt].lo = clo; out[cnt].hi = chi; out[cnt].depth = (uint8_t)ci; cnt++; }
    }
    /* include child, if feasible */
    {
        uint16_t nu[MAXM];
        int ok = 1;
        for (int j = 0; j < m; j++) {
            nu[j] = (uint16_t)(used[j] + items[i][j]);
            if (nu[j] > caps[j]) { ok = 0; break; }
        }
        if (ok) {
            uint64_t clo, chi;
            if (ci == n) { clo = chi = 1; }
            else node_interval(ci, nu, &clo, &chi);
            if (clo == chi) *exact += clo;
            else { out[cnt] = (Node){0}; memcpy(out[cnt].used, nu, sizeof(uint16_t) * MAXM); out[cnt].lo = clo; out[cnt].hi = chi; out[cnt].depth = (uint8_t)ci; cnt++; }
        }
    }
    return cnt;
}

/* ---------------- depth-first count ---------------- */

/* Count the subtree rooted at (depth i0, used0) exactly by DFS.
   Mirrors bounded_count.count's discipline.  If flo/fhi pointers
   are given, they are maintained as the subtree interval. */
static uint64_t dfs_count(int i0, const uint16_t *used0,
                          double deadline, int *timed_out) {
    uint64_t exact = 0;
    stack_len = 0;
    Node root; memset(&root, 0, sizeof root);
    memcpy(root.used, used0, sizeof(uint16_t) * MAXM);
    root.depth = (uint8_t)i0;
    node_interval(i0, used0, &root.lo, &root.hi);
    if (root.lo == root.hi) return root.lo;
    stack_push(&root);
    double tchk = now_s();
    while (stack_len) {
        Node nd = stack_buf[--stack_len];
        expansions++;
        Node out[2];
        uint64_t ex = 0;
        int cnt = eval_children(nd.depth, nd.used, out, &ex);
        exact += ex;
        for (int k = 0; k < cnt; k++) stack_push(&out[k]);
        if (timed_out && (expansions & 0xFFFFF) == 0 && now_s() > tchk) {
            tchk = now_s() + 0.25;
            if (tchk - 0.25 > deadline) { *timed_out = 1; return exact; }
        }
    }
    return exact;
}

/* Recursive exact dive used by best-first when the heap is full. */
static uint64_t dive_rec(int i, uint16_t *used) {
    uint64_t lo, hi;
    node_interval(i, used, &lo, &hi);
    if (lo == hi) return lo;
    expansions++;
    int ci = i + 1;
    uint64_t sum = 0;
    if (ci == n) sum += 1;
    else sum += dive_rec(ci, used);
    int ok = 1;
    for (int j = 0; j < m; j++) { used[j] = (uint16_t)(used[j] + items[i][j]); if (used[j] > caps[j]) ok = 0; }
    if (ok) {
        if (ci == n) sum += 1;
        else sum += dive_rec(ci, used);
    }
    for (int j = 0; j < m; j++) used[j] = (uint16_t)(used[j] - items[i][j]);
    return sum;
}

/* ---------------- best-first count ---------------- */

static Node *heap = NULL;
static size_t heap_len = 0, heap_cap = 0;
static int node_wider(const Node *a, const Node *b) {
    uint64_t wa = a->hi - a->lo, wb = b->hi - b->lo;
    if (wa != wb) return wa > wb;
    return a->depth > b->depth;
}
static void heap_push(const Node *nd) {
    if (heap_len == heap_cap) { fprintf(stderr, "heap overflow\n"); exit(1); }
    size_t i = heap_len++;
    heap[i] = *nd;
    while (i > 0) {
        size_t p = (i - 1) / 2;
        if (!node_wider(&heap[i], &heap[p])) break;
        Node t = heap[i]; heap[i] = heap[p]; heap[p] = t; i = p;
    }
}
static Node heap_pop(void) {
    Node top = heap[0];
    heap[0] = heap[--heap_len];
    size_t i = 0;
    for (;;) {
        size_t l = 2 * i + 1, r = l + 1, best = i;
        if (l < heap_len && node_wider(&heap[l], &heap[best])) best = l;
        if (r < heap_len && node_wider(&heap[r], &heap[best])) best = r;
        if (best == i) break;
        Node t = heap[i]; heap[i] = heap[best]; heap[best] = t; i = best;
    }
    return top;
}

/* Best-first exact count of a subtree; heap_cap_nodes bounds live
   nodes, excess pressure is discharged by diving the widest node. */
static uint64_t bf_count(int i0, const uint16_t *used0, size_t heap_cap_nodes,
                         double deadline, int *timed_out, uint64_t *final_width) {
    uint64_t exact = 0, flo, fhi;
    heap_len = 0;
    if (heap_cap < heap_cap_nodes) {
        heap_cap = heap_cap_nodes;
        heap = realloc(heap, heap_cap * sizeof(Node));
        if (!heap) { fprintf(stderr, "oom heap\n"); exit(1); }
    }
    Node root; memset(&root, 0, sizeof root);
    memcpy(root.used, used0, sizeof(uint16_t) * MAXM);
    root.depth = (uint8_t)i0;
    node_interval(i0, used0, &root.lo, &root.hi);
    if (root.lo == root.hi) { if (final_width) *final_width = 0; return root.lo; }
    flo = root.lo; fhi = root.hi;
    heap_push(&root);
    double tchk = now_s();
    while (heap_len) {
        if (heap_len >= heap_cap_nodes) {
            Node nd = heap_pop();
            flo -= nd.lo; fhi -= nd.hi;
            uint16_t u[MAXM]; memcpy(u, nd.used, sizeof u);
            uint64_t v = dive_rec(nd.depth, u);
            exact += v; flo += v; fhi += v;
        } else {
            Node nd = heap_pop();
            flo -= nd.lo; fhi -= nd.hi;
            expansions++;
            Node out[2];
            uint64_t ex = 0;
            int cnt = eval_children(nd.depth, nd.used, out, &ex);
            exact += ex; flo += ex; fhi += ex;
            for (int k = 0; k < cnt; k++) { heap_push(&out[k]); flo += out[k].lo; fhi += out[k].hi; }
        }
        if (timed_out && (expansions & 0xFFFFF) == 0) {
            double t = now_s();
            if (t > tchk) { tchk = t + 0.25; if (t > deadline) { *timed_out = 1; break; } }
        }
    }
    if (final_width) *final_width = fhi - flo;
    return exact;
}

/* ---------------- modes ---------------- */

static void print_root(void) {
    uint16_t zero[MAXM] = {0};
    uint64_t lo, hi;
    node_interval(0, zero, &lo, &hi);
    printf("root_interval=[%llu, %llu]\n",
           (unsigned long long)lo, (unsigned long long)hi);
    printf("order=");
    for (int i = 0; i < n; i++) printf("%s%d", i ? "," : "", order_idx[i]);
    printf("\n");
}

static int mode_dfs(double max_seconds) {
    uint16_t zero[MAXM] = {0};
    uint64_t lo, hi;
    node_interval(0, zero, &lo, &hi);
    printf("root_interval=[%llu, %llu] target_width=0 max_seconds=%.1f\n",
           (unsigned long long)lo, (unsigned long long)hi, max_seconds);
    fflush(stdout);
    /* Whole-tree DFS maintaining the global interval, mirroring
       bounded_count.count exactly (including expansion counts). */
    double t0 = now_s();
    uint64_t exact = 0, flo = lo, fhi = hi;
    int timed_out = 0;
    stack_len = 0;
    if (lo != hi) {
        Node root; memset(&root, 0, sizeof root);
        root.depth = 0; root.lo = lo; root.hi = hi;
        stack_push(&root);
        double last_print = t0;
        while (stack_len) {
            Node nd = stack_buf[--stack_len];
            flo -= nd.lo; fhi -= nd.hi;
            expansions++;
            Node out[2];
            uint64_t ex = 0;
            int cnt = eval_children(nd.depth, nd.used, out, &ex);
            exact += ex; flo += ex; fhi += ex;
            for (int k = 0; k < cnt; k++) { stack_push(&out[k]); flo += out[k].lo; fhi += out[k].hi; }
            double t = now_s();
            if (t - last_print >= 10.0) {
                last_print = t;
                printf("expansions=%llu stack=%zu interval=[%llu, %llu] width=%llu elapsed=%.1fs maxrss=%ldKB\n",
                       (unsigned long long)expansions, stack_len,
                       (unsigned long long)flo, (unsigned long long)fhi,
                       (unsigned long long)(fhi - flo), t - t0, peak_rss_kb());
                fflush(stdout);
            }
            if (max_seconds > 0 && t - t0 > max_seconds) { timed_out = 1; break; }
        }
    } else { exact = lo; }
    double el = now_s() - t0;
    int completed = !stack_len && !timed_out;
    if (lo == hi) completed = 1;
    printf("RESULT completed=%d interval=[%llu, %llu] width=%llu expansions=%llu count_seconds=%.3f peak_rss_kb=%ld\n",
           completed,
           (unsigned long long)flo, (unsigned long long)fhi,
           (unsigned long long)(fhi - flo),
           (unsigned long long)expansions, el, peak_rss_kb());
    if (completed) printf("EXACT=%llu\n", (unsigned long long)flo);
    return completed ? 0 : 2;
}

static int mode_bf(double max_seconds, size_t heap_cap_nodes) {
    uint16_t zero[MAXM] = {0};
    double t0 = now_s();
    int timed_out = 0;
    uint64_t width = 0;
    uint64_t exact = bf_count(0, zero, heap_cap_nodes,
                               max_seconds > 0 ? t0 + max_seconds : 1e18,
                               &timed_out, &width);
    double el = now_s() - t0;
    printf("RESULT completed=%d width=%llu expansions=%llu count_seconds=%.3f peak_rss_kb=%ld\n",
           !timed_out,
           (unsigned long long)width, (unsigned long long)expansions, el, peak_rss_kb());
    if (!timed_out) printf("EXACT=%llu\n", (unsigned long long)exact);
    return timed_out ? 2 : 0;
}

/* split mode */
static int cmp_node_width(const void *a, const void *b) {
    const Node *x = a, *y = b;
    uint64_t wx = x->hi - x->lo, wy = y->hi - y->lo;
    if (wx < wy) return 1;
    if (wx > wy) return -1;
    return 0;
}

static int mode_split(int depth, const char *outpath) {
    uint16_t zero[MAXM] = {0};
    uint64_t lo, hi;
    node_interval(0, zero, &lo, &hi);
    printf("root_interval=[%llu, %llu]\n",
           (unsigned long long)lo, (unsigned long long)hi);
    Node *frontier = NULL;
    size_t flen = 0, fcap = 0;
    uint64_t split_exact = 0;
    Node root; memset(&root, 0, sizeof root);
    root.depth = 0; root.lo = lo; root.hi = hi;
    frontier = malloc(1024 * sizeof(Node)); fcap = 1024;
    frontier[flen++] = root;
    /* expand level by level until all live nodes are at `depth` */
    while (1) {
        int all_deep = 1;
        for (size_t k = 0; k < flen; k++) if (frontier[k].depth < depth) { all_deep = 0; break; }
        if (all_deep) break;
        Node *next = NULL; size_t nlen = 0, ncap = 0;
        for (size_t k = 0; k < flen; k++) {
            Node nd = frontier[k];
            if (nd.depth >= depth || nd.lo == nd.hi) {
                if (nd.lo == nd.hi) { split_exact += nd.lo; continue; }
                if (nlen == ncap) { ncap = ncap ? ncap * 2 : 1024; next = realloc(next, ncap * sizeof(Node)); }
                next[nlen++] = nd;
                continue;
            }
            Node out[2];
            uint64_t ex = 0;
            int cnt = eval_children(nd.depth, nd.used, out, &ex);
            split_exact += ex;
            for (int t = 0; t < cnt; t++) {
                if (nlen == ncap) { ncap = ncap ? ncap * 2 : 1024; next = realloc(next, ncap * sizeof(Node)); }
                next[nlen++] = out[t];
            }
        }
        free(frontier); frontier = next; flen = nlen; fcap = ncap;
    }
    qsort(frontier, flen, sizeof(Node), cmp_node_width);
    uint64_t sum_lo = 0, sum_hi = 0;
    for (size_t k = 0; k < flen; k++) { sum_lo += frontier[k].lo; sum_hi += frontier[k].hi; }
    FILE *f = fopen(outpath, "wb");
    if (!f) { perror(outpath); return 1; }
    char magic[4] = {'P', 'F', 'X', '1'};
    uint32_t hdr[4] = {(uint32_t)n, (uint32_t)m, (uint32_t)depth, (uint32_t)flen};
    fwrite(magic, 1, 4, f);
    fwrite(hdr, sizeof(uint32_t), 4, f);
    uint64_t sums[3] = {split_exact, sum_lo, sum_hi};
    fwrite(sums, sizeof(uint64_t), 3, f);
    for (size_t k = 0; k < flen; k++) {
        uint8_t rec_hdr[4] = {frontier[k].depth, 0, 0, 0};
        fwrite(rec_hdr, 1, 4, f);
        fwrite(frontier[k].used, sizeof(uint16_t), m, f);
        uint64_t lh[2] = {frontier[k].lo, frontier[k].hi};
        fwrite(lh, sizeof(uint64_t), 2, f);
    }
    fclose(f);
    printf("split depth=%d prefixes=%zu split_exact=%llu interval=[%llu, %llu] width=%llu\n",
           depth, flen, (unsigned long long)split_exact,
           (unsigned long long)(split_exact + sum_lo),
           (unsigned long long)(split_exact + sum_hi),
           (unsigned long long)(sum_hi - sum_lo));
    return 0;
}

/* ---------------- best-first from a split frontier ----------------
 * bfseed CASE.txt PREFIX.bin BUDGET_S HEAP_CAP STATE
 *   Seed the heap with the live prefixes of a split file and expand
 *   widest-first, maintaining the global rigorous interval.  When
 *   the heap reaches HEAP_CAP the widest node is solved by a DFS
 *   dive.  State is checkpointed to STATE every 120 s and at exit:
 *     header: char[4] "BFS1"; u32 n, m, NP; u32 pairs[2*NP];
 *             u64 exact, flo, fhi, expansions, heap_len;
 *     then heap_len records: u8 depth; u16 used[m]; u64 lo, hi.
 *   If STATE exists at startup, the run resumes from it (the prefix
 *   file is then only used for its split accounting cross-check).
 */
static void bfs_save_state(const char *path, uint64_t exact, uint64_t flo,
                           uint64_t fhi) {
    char tmp[1100];
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "wb");
    if (!f) { perror(tmp); return; }
    char magic[4] = {'B', 'F', 'S', '1'};
    fwrite(magic, 1, 4, f);
    uint32_t hdr[3] = {(uint32_t)n, (uint32_t)m, (uint32_t)NP};
    fwrite(hdr, sizeof(uint32_t), 3, f);
    for (int p = 0; p < NP; p++) {
        uint32_t pr[2] = {(uint32_t)pair_j[p], (uint32_t)pair_k[p]};
        fwrite(pr, sizeof(uint32_t), 2, f);
    }
    uint64_t vals[5] = {exact, flo, fhi, expansions, (uint64_t)heap_len};
    fwrite(vals, sizeof(uint64_t), 5, f);
    for (size_t k = 0; k < heap_len; k++) {
        uint8_t dh[4] = {heap[k].depth, 0, 0, 0};
        fwrite(dh, 1, 4, f);
        fwrite(heap[k].used, sizeof(uint16_t), m, f);
        uint64_t lh[2] = {heap[k].lo, heap[k].hi};
        fwrite(lh, sizeof(uint64_t), 2, f);
    }
    fclose(f);
    rename(tmp, path);
}

static int mode_bfseed(const char *pfx_path, double budget_s,
                       size_t heap_cap_nodes, const char *state_path) {
    uint64_t exact = 0, flo = 0, fhi = 0;
    heap_len = 0;
    if (heap_cap < heap_cap_nodes) {
        heap_cap = heap_cap_nodes;
        heap = realloc(heap, heap_cap * sizeof(Node));
        if (!heap) { fprintf(stderr, "oom heap\n"); exit(1); }
    }
    struct stat st;
    if (stat(state_path, &st) == 0) {
        FILE *f = fopen(state_path, "rb");
        if (!f) { perror(state_path); return 1; }
        char magic[4]; uint32_t hdr[3];
        if (fread(magic, 1, 4, f) != 4 || memcmp(magic, "BFS1", 4)) { fprintf(stderr, "bad state\n"); return 1; }
        if (fread(hdr, sizeof(uint32_t), 3, f) != 3) return 1;
        if ((int)hdr[0] != n || (int)hdr[1] != m || (int)hdr[2] != NP) { fprintf(stderr, "state/case mismatch\n"); return 1; }
        for (int p = 0; p < NP; p++) {
            uint32_t pr[2];
            if (fread(pr, sizeof(uint32_t), 2, f) != 2) return 1;
            if ((int)pr[0] != pair_j[p] || (int)pr[1] != pair_k[p]) { fprintf(stderr, "state/pairs mismatch\n"); return 1; }
        }
        uint64_t vals[5];
        if (fread(vals, sizeof(uint64_t), 5, f) != 5) return 1;
        exact = vals[0]; flo = vals[1]; fhi = vals[2]; expansions = vals[3];
        size_t want = (size_t)vals[4];
        for (size_t k = 0; k < want; k++) {
            uint8_t dh[4];
            if (fread(dh, 1, 4, f) != 4) return 1;
            Node nd; memset(&nd, 0, sizeof nd);
            nd.depth = dh[0];
            if (fread(nd.used, sizeof(uint16_t), m, f) != (size_t)m) return 1;
            uint64_t lh[2];
            if (fread(lh, sizeof(uint64_t), 2, f) != 2) return 1;
            nd.lo = lh[0]; nd.hi = lh[1];
            if (heap_len >= heap_cap) { fprintf(stderr, "state exceeds heap cap\n"); return 1; }
            heap[heap_len++] = nd;
        }
        fclose(f);
        /* heap array was saved in heap order: still a valid heap. */
        printf("resumed state: exact=%llu interval=[%llu, %llu] heap=%zu expansions=%llu\n",
               (unsigned long long)exact, (unsigned long long)flo,
               (unsigned long long)fhi, heap_len,
               (unsigned long long)expansions);
    } else {
        FILE *f = fopen(pfx_path, "rb");
        if (!f) { perror(pfx_path); return 1; }
        char magic[4]; uint32_t hdr[4]; uint64_t sums[3];
        if (fread(magic, 1, 4, f) != 4 || memcmp(magic, "PFX1", 4)) { fprintf(stderr, "bad prefix file\n"); return 1; }
        if (fread(hdr, sizeof(uint32_t), 4, f) != 4) return 1;
        if (fread(sums, sizeof(uint64_t), 3, f) != 3) return 1;
        int total = (int)hdr[3];
        exact = sums[0]; flo = sums[0] + sums[1]; fhi = sums[0] + sums[2];
        for (int k = 0; k < total; k++) {
            uint8_t rh[4];
            if (fread(rh, 1, 4, f) != 4) return 1;
            Node nd; memset(&nd, 0, sizeof nd);
            nd.depth = rh[0];
            if (fread(nd.used, sizeof(uint16_t), m, f) != (size_t)m) return 1;
            uint64_t lh[2];
            if (fread(lh, sizeof(uint64_t), 2, f) != 2) return 1;
            nd.lo = lh[0]; nd.hi = lh[1];
            heap_push(&nd);
        }
        fclose(f);
        printf("seeded: prefixes=%d exact=%llu interval=[%llu, %llu] width=%llu\n",
               total, (unsigned long long)exact, (unsigned long long)flo,
               (unsigned long long)fhi, (unsigned long long)(fhi - flo));
    }
    fflush(stdout);
    double t0 = now_s();
    double last_print = t0, last_save = t0;
    int timed_out = 0;
    while (heap_len) {
        if (heap_len >= heap_cap_nodes) {
            Node nd = heap_pop();
            flo -= nd.lo; fhi -= nd.hi;
            uint16_t u[MAXM]; memcpy(u, nd.used, sizeof u);
            uint64_t v = dive_rec(nd.depth, u);
            exact += v; flo += v; fhi += v;
        } else {
            Node nd = heap_pop();
            flo -= nd.lo; fhi -= nd.hi;
            expansions++;
            Node out[2];
            uint64_t ex = 0;
            int cnt = eval_children(nd.depth, nd.used, out, &ex);
            exact += ex; flo += ex; fhi += ex;
            for (int k = 0; k < cnt; k++) { heap_push(&out[k]); flo += out[k].lo; fhi += out[k].hi; }
        }
        double t = now_s();
        if (t - last_print >= 10.0) {
            last_print = t;
            printf("expansions=%llu heap=%zu interval=[%llu, %llu] width=%llu elapsed=%.1fs maxrss=%ldKB\n",
                   (unsigned long long)expansions, heap_len,
                   (unsigned long long)flo, (unsigned long long)fhi,
                   (unsigned long long)(fhi - flo), t - t0, peak_rss_kb());
            fflush(stdout);
        }
        if (t - last_save >= 120.0) { last_save = t; bfs_save_state(state_path, exact, flo, fhi); }
        if (budget_s > 0 && t - t0 > budget_s) { timed_out = 1; break; }
    }
    bfs_save_state(state_path, exact, flo, fhi);
    printf("RESULT completed=%d exact=%llu interval=[%llu, %llu] width=%llu expansions=%llu seconds=%.1f peak_rss_kb=%ld\n",
           !timed_out && !heap_len, (unsigned long long)exact,
           (unsigned long long)flo, (unsigned long long)fhi,
           (unsigned long long)(fhi - flo),
           (unsigned long long)expansions, now_s() - t0, peak_rss_kb());
    return 0;
}

/* worker mode */
static int claim_next(const char *dir, int total) {
    char path[1024];
    snprintf(path, sizeof path, "%s/claim.txt", dir);
    int fd = open(path, O_RDWR | O_CREAT, 0644);
    if (fd < 0) { perror("claim"); return -1; }
    flock(fd, LOCK_EX);
    char buf[64] = {0};
    ssize_t r = read(fd, buf, sizeof buf - 1);
    int cur = (r > 0) ? atoi(buf) : 0;
    int mine = cur;
    if (cur < total) {
        char out[64];
        int len = snprintf(out, sizeof out, "%d\n", cur + 1);
        lseek(fd, 0, SEEK_SET);
        if (write(fd, out, len) < 0) perror("claim write");
        if (ftruncate(fd, len) < 0) perror("claim trunc");
    }
    flock(fd, LOCK_UN);
    close(fd);
    return mine < total ? mine : -1;
}

static int mode_worker(const char *pfx_path, int wid, const char *dir,
                       double budget_s, int use_bf, size_t heap_cap_nodes) {
    FILE *f = fopen(pfx_path, "rb");
    if (!f) { perror(pfx_path); return 1; }
    char magic[4]; uint32_t hdr[4]; uint64_t sums[3];
    if (fread(magic, 1, 4, f) != 4 || memcmp(magic, "PFX1", 4)) { fprintf(stderr, "bad prefix file\n"); return 1; }
    if (fread(hdr, sizeof(uint32_t), 4, f) != 4) return 1;
    if (fread(sums, sizeof(uint64_t), 3, f) != 3) return 1;
    int total = (int)hdr[3];
    Node *pfx = malloc(sizeof(Node) * (size_t)total);
    for (int k = 0; k < total; k++) {
        uint8_t rh[4];
        if (fread(rh, 1, 4, f) != 4) return 1;
        memset(&pfx[k], 0, sizeof(Node));
        pfx[k].depth = rh[0];
        if (fread(pfx[k].used, sizeof(uint16_t), m, f) != (size_t)m) return 1;
        uint64_t lh[2];
        if (fread(lh, sizeof(uint64_t), 2, f) != 2) return 1;
        pfx[k].lo = lh[0]; pfx[k].hi = lh[1];
    }
    fclose(f);

    /* done set: scan all results_w*.jsonl in dir */
    char respath[1024];
    snprintf(respath, sizeof respath, "%s/results_w%d.jsonl", dir, wid);
    char *done = calloc(total, 1);
    for (int w = 0; w < 64; w++) {
        char p2[1024];
        snprintf(p2, sizeof p2, "%s/results_w%d.jsonl", dir, w);
        FILE *rf = fopen(p2, "r");
        if (!rf) continue;
        char line[512];
        while (fgets(line, sizeof line, rf)) {
            int idx; unsigned long long val;
            if (sscanf(line, "{\"prefix\": %d, \"exact\": %llu", &idx, &val) == 2 && idx >= 0 && idx < total) done[idx] = 1;
        }
        fclose(rf);
    }
    FILE *out = fopen(respath, "a");
    if (!out) { perror(respath); return 1; }
    double t0 = now_s();
    int solved = 0;
    for (;;) {
        double elapsed = now_s() - t0;
        if (budget_s > 0 && elapsed > budget_s) break;
        int idx = claim_next(dir, total);
        if (idx < 0) break;
        if (done[idx]) continue;
        uint64_t exp_before = expansions;
        double ts = now_s();
        int timed_out = 0;
        uint64_t exact;
        if (use_bf) {
            uint64_t w = 0;
            exact = bf_count(pfx[idx].depth, pfx[idx].used, heap_cap_nodes,
                             budget_s > 0 ? t0 + budget_s : 1e18, &timed_out, &w);
            if (timed_out) {
                fprintf(out, "{\"prefix\": %d, \"timeout\": true, \"width\": %llu, \"expansions\": %llu, \"seconds\": %.3f, \"worker\": %d}\n",
                        idx, (unsigned long long)w,
                        (unsigned long long)(expansions - exp_before),
                        now_s() - ts, wid);
                fflush(out);
                break;
            }
        } else {
            exact = dfs_count(pfx[idx].depth, pfx[idx].used,
                              budget_s > 0 ? t0 + budget_s : 1e18, &timed_out);
            if (timed_out) {
                fprintf(out, "{\"prefix\": %d, \"timeout\": true, \"expansions\": %llu, \"seconds\": %.3f, \"worker\": %d}\n",
                        idx, (unsigned long long)(expansions - exp_before),
                        now_s() - ts, wid);
                fflush(out);
                break;
            }
        }
        fprintf(out, "{\"prefix\": %d, \"exact\": %llu, \"expansions\": %llu, \"seconds\": %.3f, \"worker\": %d}\n",
                idx, (unsigned long long)exact,
                (unsigned long long)(expansions - exp_before),
                now_s() - ts, wid);
        fflush(out);
        solved++;
        printf("[w%d] prefix %d exact=%llu expansions=%llu elapsed=%.1fs maxrss=%ldKB\n",
               wid, idx, (unsigned long long)exact,
               (unsigned long long)(expansions - exp_before), now_s() - t0,
               peak_rss_kb());
        fflush(stdout);
    }
    fclose(out);
    printf("[w%d] done: solved_this_run=%d total_expansions=%llu wall=%.1fs maxrss=%ldKB\n",
           wid, solved, (unsigned long long)expansions, now_s() - t0, peak_rss_kb());
    return 0;
}

static void parse_pairs(const char *spec) {
    /* spec: "3,4" or "3,4;1,4;0,1" */
    NP = 0;
    const char *s = spec;
    while (*s && NP < MAXPAIRS) {
        pair_j[NP] = strtol(s, (char **)&s, 10);
        if (*s == ',') s++;
        pair_k[NP] = strtol(s, (char **)&s, 10);
        NP++;
        if (*s == ';') s++;
    }
    if (NP == 0) { NP = 1; pair_j[0] = 3; pair_k[0] = 4; }
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s MODE CASE.txt [args] [pairs=J,K[;J,K...]]\n", argv[0]);
        return 1;
    }
    if (!strncmp(argv[argc - 1], "pairs=", 6)) {
        parse_pairs(argv[argc - 1] + 6);
        argc--;
    }
    const char *mode = argv[1];
    load_case(argv[2]);
    double tb = now_s();
    build_structures();
    fprintf(stderr, "structures built in %.2fs (n=%d m=%d grid layers=%d)\n",
            now_s() - tb, n, m, n + 1);
    if (!strcmp(mode, "root")) { print_root(); return 0; }
    if (!strcmp(mode, "dfs")) return mode_dfs(argc > 3 ? atof(argv[3]) : 0);
    if (!strcmp(mode, "bf")) return mode_bf(argc > 3 ? atof(argv[3]) : 0,
                                           argc > 4 ? (size_t)atol(argv[4]) : 4000000);
    if (!strcmp(mode, "split")) {
        if (argc < 5) { fprintf(stderr, "split needs DEPTH and OUT\n"); return 1; }
        return mode_split(atoi(argv[3]), argv[4]);
    }
    if (!strcmp(mode, "bfseed")) {
        if (argc < 7) { fprintf(stderr, "bfseed needs PREFIX BUDGET HEAP_CAP STATE\n"); return 1; }
        return mode_bfseed(argv[3], atof(argv[4]), (size_t)atol(argv[5]), argv[6]);
    }
    if (!strcmp(mode, "worker")) {
        if (argc < 8) { fprintf(stderr, "worker needs PREFIX WORKER_ID DIR BUDGET MODE\n"); return 1; }
        int use_bf = !strcmp(argv[7], "bf");
        size_t cap = argc > 8 ? (size_t)atol(argv[8]) : 4000000;
        return mode_worker(argv[3], atoi(argv[4]), argv[5], atof(argv[6]), use_bf, cap);
    }
    fprintf(stderr, "unknown mode %s\n", mode);
    return 1;
}

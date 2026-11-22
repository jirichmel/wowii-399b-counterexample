/* smallgraph.h -- reusable pieces for exhaustive work on graphs with at most 16 vertices.
 *
 * Header only, C99 with GCC/Clang builtins (__int128, __builtin_popcount).  No external library.
 * Everything here was used and cross-checked in the session of 19 November 2026 (see
 * tools/wowii199/ and runs/wowii199/).  A graph is an array adj[] of bitmasks, adj[v] bit w.
 *
 * Contents
 *   canonical form      sg_canon(n, adj)  -> 128-bit code, equal for isomorphic graphs
 *                       sg_decode(n, code, adj)
 *   set of codes        sg_set_init, sg_set_insert, sg_set_free     (open addressing)
 *   generators          sg_all_graphs(nmax, visit, ctx)             every graph up to isomorphism
 *                       sg_hereditary(start, accept, visit, ...)    every graph of a class closed
 *                                                                   under deleting the added vertices
 *   invariants          sg_connected, sg_components, sg_kappa, sg_alpha, sg_tree_number,
 *                       sg_ham_path, sg_longest_path, sg_tree_through (induced tree containing a
 *                       given vertex with at least a given number of vertices)
 *
 * Costs.  The canonical form tries all labellings that sort the vertices by an invariant
 * (degree, sum of neighbour degrees, triangles), skipping twins; it is fast for the graphs met
 * in practice up to about 14 vertices and can be slow for large highly symmetric graphs without
 * twins.  The invariants enumerate all 2^n vertex subsets: fine up to n = 16, slow beyond.
 *
 * How to use it for a new conjecture "every graph with property A has property B":
 *   1. If A (or a consequence of "A and not B") is hereditary, generate only that class with
 *      sg_hereditary; otherwise use sg_all_graphs (feasible to 10 vertices, 11 with patience).
 *   2. In the visit callback compute the invariants and report violations.
 *   3. Cross-check the counts of the generator against a published sequence (number of graphs:
 *      1, 2, 4, 11, 34, 156, 1044, 12346, 274668, 12005168) and the invariants against plain
 *      brute force on random graphs (see tools/wowii199/crosscheck199.py for the pattern).
 */
#ifndef SMALLGRAPH_H
#define SMALLGRAPH_H
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef unsigned __int128 sg_code;
#define SG_MAXN 16
#define SG_POP(x) __builtin_popcount(x)
#define SG_CTZ(x) __builtin_ctz(x)

/* ------------------------------------------------------------------ canonical form */
static unsigned sg__ca[SG_MAXN]; static int sg__cn, sg__ctotal, sg__cperm[SG_MAXN];
static unsigned sg__cused; static uint32_t sg__cinv[SG_MAXN], sg__ctarget[SG_MAXN]; static sg_code sg__cbest;

static void sg__crec(int pos, sg_code code) {
    if (pos == sg__cn) { if (code < sg__cbest) sg__cbest = code; return; }
    int tried[SG_MAXN], nt = 0;
    for (int v = 0; v < sg__cn; v++) {
        if ((sg__cused >> v) & 1 || sg__cinv[v] != sg__ctarget[pos]) continue;
        int twin = 0;                     /* two unused twins give the same codes: try one of them */
        for (int i = 0; i < nt && !twin; i++) { int w = tried[i]; if ((sg__ca[v] & ~(1u << w)) == (sg__ca[w] & ~(1u << v))) twin = 1; }
        if (twin) continue;
        tried[nt++] = v;
        unsigned row = 0;
        for (int t = 0; t < pos; t++) if ((sg__ca[v] >> sg__cperm[t]) & 1) row |= 1u << t;
        sg_code c2 = (code << pos) | row;
        int bits = pos * (pos + 1) / 2;
        if (c2 > (sg__cbest >> (sg__ctotal - bits))) continue;
        sg__cperm[pos] = v; sg__cused |= 1u << v;
        sg__crec(pos + 1, c2);
        sg__cused &= ~(1u << v);
    }
}
static int sg__cmp_desc(const void *a, const void *b) {
    uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b; return x < y ? 1 : x > y ? -1 : 0;
}
/* smallest adjacency code over the labellings that list the vertices by decreasing invariant */
static sg_code sg_canon(int n, const unsigned *adj) {
    sg__cn = n; sg__ctotal = n * (n - 1) / 2;
    int deg[SG_MAXN];
    for (int v = 0; v < n; v++) { sg__ca[v] = adj[v]; deg[v] = SG_POP(adj[v]); }
    for (int v = 0; v < n; v++) {
        int sd = 0, tri = 0;
        for (int w = 0; w < n; w++) if ((adj[v] >> w) & 1) { sd += deg[w]; tri += SG_POP(adj[v] & adj[w]); }
        sg__cinv[v] = ((uint32_t)deg[v] * 1000 + sd) * 200 + tri / 2;
        sg__ctarget[v] = sg__cinv[v];
    }
    qsort(sg__ctarget, n, sizeof(uint32_t), sg__cmp_desc);
    sg__cbest = sg__ctotal ? (((sg_code)1 << sg__ctotal) - 1) : 0;
    sg__cused = 0;
    sg__crec(0, 0);
    return sg__cbest;
}
static void sg_decode(int n, sg_code code, unsigned *adj) {
    for (int v = 0; v < n; v++) adj[v] = 0;
    for (int j = n - 1; j >= 1; j--) {
        unsigned row = (unsigned)(code & (((sg_code)1 << j) - 1));
        code >>= j;
        for (int t = 0; t < j; t++) if ((row >> t) & 1) { adj[j] |= 1u << t; adj[t] |= 1u << j; }
    }
}

/* ------------------------------------------------------------------ set of codes */
typedef struct { sg_code *slot; size_t cap, count; } sg_set;
static void sg_set_init(sg_set *s, size_t cap) {
    s->cap = cap < 16 ? 16 : cap; s->count = 0; s->slot = (sg_code *)calloc(s->cap, sizeof(sg_code));
    if (!s->slot) { fprintf(stderr, "smallgraph: out of memory\n"); exit(1); }
}
static void sg_set_free(sg_set *s) { free(s->slot); s->slot = NULL; s->cap = s->count = 0; }
static uint64_t sg__mix(sg_code k) {
    uint64_t x = (uint64_t)k ^ ((uint64_t)(k >> 64) * 0x9E3779B97F4A7C15ULL);
    x ^= x >> 31; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 29; return x;
}
/* returns 1 if the code is new.  Codes are stored as code+1 so that 0 marks an empty slot. */
static int sg_set_insert(sg_set *s, sg_code key) {
    sg_code k = key + 1; size_t i = sg__mix(k) % s->cap;
    while (s->slot[i]) { if (s->slot[i] == k) return 0; if (++i == s->cap) i = 0; }
    s->slot[i] = k; s->count++;
    if (s->count * 10 > s->cap * 6) {
        sg_set big; sg_set_init(&big, s->cap * 2);
        for (size_t j = 0; j < s->cap; j++) if (s->slot[j]) { sg_code q = s->slot[j]; size_t h = sg__mix(q) % big.cap; while (big.slot[h]) if (++h == big.cap) h = 0; big.slot[h] = q; big.count++; }
        free(s->slot); *s = big;
    }
    return 1;
}
/* the codes of the set as a plain array (caller frees) */
static sg_code *sg_set_list(const sg_set *s, size_t *count) {
    sg_code *out = (sg_code *)malloc((s->count ? s->count : 1) * sizeof(sg_code)); size_t k = 0;
    for (size_t j = 0; j < s->cap; j++) if (s->slot[j]) out[k++] = s->slot[j] - 1;
    *count = k; return out;
}

/* ------------------------------------------------------------------ invariants */
static int sg_connected(const unsigned *adj, unsigned S) {          /* is G[S] connected (true for S empty) */
    if (!S) return 1;
    unsigned comp = S & -S, g;
    for (;;) { g = comp; for (unsigned t = comp; t; t &= t - 1) g |= adj[SG_CTZ(t)] & S; if (g == comp) break; comp = g; }
    return comp == S;
}
static int sg_components(const unsigned *adj, unsigned S) {         /* number of components of G[S] */
    int c = 0;
    while (S) { unsigned comp = S & -S, g; for (;;) { g = comp; for (unsigned t = comp; t; t &= t - 1) g |= adj[SG_CTZ(t)] & S; if (g == comp) break; comp = g; } S &= ~comp; c++; }
    return c;
}
static int sg_kappa(int n, const unsigned *adj) {                   /* vertex connectivity; n-1 for complete graphs, 0 if disconnected */
    unsigned full = (1u << n) - 1; int best = n - 1;
    for (unsigned X = 0; X <= full; X++) {
        int k = SG_POP(X); if (k >= best) continue;
        unsigned R = full & ~X; if (SG_POP(R) < 2) continue;
        if (!sg_connected(adj, R)) best = k;
    }
    return best;
}
static int sg_alpha(int n, const unsigned *adj) {                   /* independence number */
    unsigned full = (1u << n) - 1; int best = 0;
    for (unsigned S = 1; S <= full; S++) {
        int k = SG_POP(S); if (k <= best) continue;
        int ok = 1; for (unsigned t = S; t && ok; t &= t - 1) if (adj[SG_CTZ(t)] & S) ok = 0;
        if (ok) best = k;
    }
    return best;
}
static int sg_tree_number(int n, const unsigned *adj) {             /* order of a largest induced tree */
    unsigned full = (1u << n) - 1; int best = n ? 1 : 0;
    for (unsigned S = 1; S <= full; S++) {
        int k = SG_POP(S); if (k <= best) continue;
        int e2 = 0; for (unsigned t = S; t; t &= t - 1) e2 += SG_POP(adj[SG_CTZ(t)] & S);
        if (e2 == 2 * (k - 1) && sg_connected(adj, S)) best = k;
    }
    return best;
}
/* Hamiltonian path by dynamic programming over subsets; buf must hold 2^n unsigned */
static int sg_ham_path(int n, const unsigned *adj, unsigned *buf) {
    unsigned full = (1u << n) - 1;
    for (unsigned S = 1; S <= full; S++) {
        if ((S & (S - 1)) == 0) { buf[S] = S; continue; }
        unsigned e = 0;
        for (unsigned t = S; t; t &= t - 1) { int v = SG_CTZ(t); if (buf[S & ~(1u << v)] & adj[v]) e |= 1u << v; }
        buf[S] = e;
    }
    return buf[full] != 0;
}
/* number of vertices of a longest path; buf as above */
static int sg_longest_path(int n, const unsigned *adj, unsigned *buf) {
    unsigned full = (1u << n) - 1; int best = n ? 1 : 0;
    for (unsigned S = 1; S <= full; S++) {
        if ((S & (S - 1)) == 0) { buf[S] = S; continue; }
        unsigned e = 0;
        for (unsigned t = S; t; t &= t - 1) { int v = SG_CTZ(t); if (buf[S & ~(1u << v)] & adj[v]) e |= 1u << v; }
        buf[S] = e;
        if (e && SG_POP(S) > best) best = SG_POP(S);
    }
    return best;
}
/* is there an induced tree with at least `target` vertices that contains all of T and avoids X?
 * Call with T = one vertex, X = 0.  Used to keep a class "no induced tree on t+1 vertices". */
static int sg_tree_through(int n, const unsigned *adj, unsigned T, unsigned X, int target) {
    int sz = SG_POP(T);
    if (sz >= target) return 1;
    unsigned cand = 0, pot = 0, full = (1u << n) - 1;
    for (unsigned rest = full & ~(T | X); rest; rest &= rest - 1) {
        int u = SG_CTZ(rest), c = SG_POP(adj[u] & T);
        if (c == 1) { cand |= 1u << u; pot |= 1u << u; } else if (c == 0) pot |= 1u << u;
    }
    if (sz + SG_POP(pot) < target) return 0;
    while (cand) {
        int c = SG_CTZ(cand); cand &= cand - 1;
        if (sg_tree_through(n, adj, T | (1u << c), X, target)) return 1;
        X |= 1u << c;
    }
    return 0;
}

/* ------------------------------------------------------------------ generators */
typedef void (*sg_visit)(int n, const unsigned *adj, void *ctx);
/* accept(n, adj, ctx): adj has n vertices, vertex n-1 was just added; return 1 to keep the graph */
typedef int (*sg_accept)(int n, const unsigned *adj, void *ctx);

/* Every graph of the class on n0+1 .. nmax vertices, once per isomorphism type, where the class
 * consists of the graphs reachable from the start graph (n0 vertices) by adding one vertex at a
 * time, every intermediate graph being accepted.  visit is called for the start graph too.
 * With accept = NULL and a one-vertex start graph this lists all graphs. */
static void sg_hereditary(int n0, const unsigned *start, int nmax, sg_accept accept, sg_visit visit, void *ctx) {
    size_t ncur = 1; sg_code *cur = (sg_code *)malloc(sizeof(sg_code));
    cur[0] = sg_canon(n0, start);
    unsigned adj[SG_MAXN], g[SG_MAXN];
    for (int n = n0; n <= nmax; n++) {
        for (size_t i = 0; i < ncur; i++) { sg_decode(n, cur[i], adj); visit(n, adj, ctx); }
        if (n == nmax) break;
        sg_set next; sg_set_init(&next, 1 << 12);
        for (size_t i = 0; i < ncur; i++) {
            sg_decode(n, cur[i], adj);
            for (unsigned m = 0; m < (1u << n); m++) {
                for (int v = 0; v < n; v++) g[v] = adj[v] | (((m >> v) & 1) << n);
                g[n] = m;
                if (accept && !accept(n + 1, g, ctx)) continue;
                sg_set_insert(&next, sg_canon(n + 1, g));
            }
        }
        free(cur); cur = sg_set_list(&next, &ncur); sg_set_free(&next);
    }
    free(cur);
}
static void sg_all_graphs(int nmax, sg_visit visit, void *ctx) {
    unsigned one[1] = {0};
    sg_hereditary(1, one, nmax, NULL, visit, ctx);
}
#endif

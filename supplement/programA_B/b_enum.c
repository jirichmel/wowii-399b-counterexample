/* b_enum.c -- search-1, program B.  Shares no code with a_enum.c.
 * Generator: tools/lib/smallgraph.h (sg_hereditary from K1, accepting connected graphs only;
 * every connected graph has a non-cut vertex, so all connected graphs are reached).
 * Invariants: dynamic programming over all 2^n vertex subsets (tables of N[S], of the vertices
 * with >= 1 and >= 2 neighbours in S, and independence).  Different algorithm from program A.
 *
 * Usage: b_enum gen NMAX        (NMAX <= 10)
 *        b_enum g6 < file       (n <= 22)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "smallgraph.h"   /* copied from tools/lib/ of the project */

#define TMAX 22
static unsigned *T_cl, *T_one, *T_two; static unsigned char *T_ind;
static int tab_n = -1;

static void tables(int n, const unsigned *A) {
    if (tab_n < n) {
        size_t sz = (size_t)1 << n;
        T_cl = realloc(T_cl, sz * sizeof(unsigned)); T_one = realloc(T_one, sz * sizeof(unsigned));
        T_two = realloc(T_two, sz * sizeof(unsigned)); T_ind = realloc(T_ind, sz);
        tab_n = n;
    }
    T_cl[0] = T_one[0] = T_two[0] = 0; T_ind[0] = 1;
    for (unsigned S = 1; S < (1u << n); S++) {
        int v = __builtin_ctz(S);
        unsigned P = S & (S - 1);
        T_cl[S] = T_cl[P] | A[v] | (1u << v);
        T_one[S] = T_one[P] | A[v];
        T_two[S] = T_two[P] | (T_one[P] & A[v]);
        T_ind[S] = T_ind[P] && !(A[v] & P);
    }
}

typedef struct {
    int n, a2, wp, k, dD, gam, idm, lmax, NM, g2, aA3, A3empty;
    long lchk, lviol;
} R;

static int wp_count(int n, const unsigned *A) {
    int best = 0;
    for (int j = 1; j <= n; j++) {
        int c = 0;
        for (int v = 0; v < n; v++) if (__builtin_popcount(A[v]) <= n - j) c++;
        if (c >= j) best = j;
    }
    return best;
}

static int hh_steps(int n, const unsigned *A) {
    int cnt[64] = {0};
    for (int v = 0; v < n; v++) cnt[__builtin_popcount(A[v])]++;
    if (cnt[0]) return 0;
    int steps = 0, left = n;
    while (left > 0) {
        int top = 63; while (top > 0 && cnt[top] == 0) top--;
        cnt[top]--; left--; steps++;
        if (top > left) return -1;
        /* subtract one from the 'top' largest remaining entries */
        int need = top, nc[64]; memcpy(nc, cnt, sizeof nc);
        for (int d = 63; d >= 1 && need > 0; d--) {
            int take = cnt[d] < need ? cnt[d] : need;
            nc[d] -= take; nc[d - 1] += take; need -= take;
        }
        memcpy(cnt, nc, sizeof cnt);
        if (cnt[0] > 0) return steps;
    }
    return -2;
}

static void evalB(int n, const unsigned *A, R *r, int lemma) {
    tables(n, A);
    unsigned FULL = (n == 32) ? ~0u : ((1u << n) - 1);
    r->n = n;
    int a2 = 0, gam = 99, idm = 99, g2 = 99, lam[32] = {0};
    unsigned A3 = 0;
    for (int v = 0; v < n; v++) if (__builtin_popcount(A[v]) >= 3) A3 |= 1u << v;
    int aA3 = 0;
    for (unsigned S = 0; S < (1u << n); S++) {
        int c = __builtin_popcount(S);
        if (!(T_two[S] & S) && c > a2) a2 = c;
        if (T_cl[S] == FULL && c < gam) gam = c;
        if (T_ind[S]) {
            if (T_cl[S] == FULL && c < idm) idm = c;
            if (!(S & ~A3) && c > aA3) aA3 = c;
            for (int v = 0; v < n; v++) if (!(S & ~A[v]) && c > lam[v]) lam[v] = c;
        }
        if ((S | T_two[S]) == FULL && c < g2) g2 = c;
    }
    r->a2 = a2; r->gam = gam; r->idm = idm; r->g2 = g2; r->aA3 = aA3; r->A3empty = (A3 == 0);
    r->wp = wp_count(n, A);
    r->k = hh_steps(n, A);
    unsigned D = 0;
    for (int u = 0; u < n; u++) for (int v = 0; v < n; v++)
        if (u != v && (A[u] >> v & 1)) {
            unsigned cu = A[u] | (1u << u), cv = A[v] | (1u << v);
            if ((cu | cv) == cv) D |= 1u << v;
        }
    int dD = 0;
    for (int v = 0; v < n; v++) if (D >> v & 1) { int x = __builtin_popcount(A[v] & D); if (x > dD) dD = x; }
    r->dD = dD;
    int lmax = 0; for (int v = 0; v < n; v++) if (lam[v] > lmax) lmax = lam[v];
    unsigned X = 0; for (int v = 0; v < n; v++) if (lam[v] == lmax) X |= A[v] | (1u << v);
    r->lmax = lmax; r->NM = __builtin_popcount(X);
    r->lchk = r->lviol = 0;
    if (lemma) {
        for (unsigned S = 1; S < (1u << n); S++) {
            if (__builtin_popcount(S) != gam || T_cl[S] != FULL) continue;
            unsigned I = S;
            for (;;) {
                if (I && T_ind[I] && !(S & ~I & ~T_one[I])) {
                    int b = __builtin_popcount(I);
                    for (int v = 0; v < n; v++) if ((S & ~I) >> v & 1) b += lam[v] - 1;
                    r->lchk++;
                    if (idm > b) r->lviol++;
                }
                if (!I) break;
                I = (I - 1) & S;
            }
        }
    }
}

/* ---------------------------------------------------------------- exhaustive mode */
typedef struct { long cnt, v436, op, opeq, v421, eq421, c421, lchk, lviol, a3e, a3ne, a3ge4, v399, g2wp; int m436, m421, m399; } TB;
static TB tb[17];
static int gen_lemma = 1;

static int acc_conn(int n, const unsigned *adj, void *ctx) { (void)ctx; return sg_connected(adj, (1u << n) - 1); }
static void vis(int n, const unsigned *adj, void *ctx) {
    (void)ctx;
    if (n < 4) { tb[n].cnt++; return; }
    R r; evalB(n, adj, &r, gen_lemma);
    TB *t = &tb[n];
    t->cnt++;
    int s = r.k * r.wp + r.dD - r.a2;
    if (s < 0) t->v436++;
    if (t->cnt == 1 || s < t->m436) t->m436 = s;
    if (r.k == 1 && r.dD == 0) { t->op++; if (r.a2 == r.wp) t->opeq++; }
    int s2 = r.gam * (r.NM - 3) - r.idm;
    if (s2 < 0) t->v421++;
    if (s2 == 0) t->eq421++;
    if (t->cnt == 1 || s2 < t->m421) t->m421 = s2;
    if (r.NM == r.lmax + 1) t->c421++;
    t->lchk += r.lchk; t->lviol += r.lviol;
    if (r.g2 > r.wp) t->g2wp++;
    if (r.A3empty) t->a3e++;
    else {
        t->a3ne++;
        if (r.aA3 >= 4) t->a3ge4++;
        int s3 = r.wp + 3 / r.aA3 - r.g2;
        if (s3 < 0) t->v399++;
        if (t->a3ne == 1 || s3 < t->m399) t->m399 = s3;
    }
}

static int g6read(const char *s, unsigned *A) {
    int p = 1, n = s[0] - 63;
    if (n < 1 || n > TMAX) return -1;
    for (int i = 0; i < n; i++) A[i] = 0;
    int k = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++, k++) {
        int byte = s[p + k / 6] - 63;
        if (byte >> (5 - k % 6) & 1) { A[i] |= 1u << j; A[j] |= 1u << i; }
    }
    return n;
}

int main(int argc, char **argv) {
    if (argc >= 3 && !strcmp(argv[1], "gen")) {
        int nmax = atoi(argv[2]);
        if (argc >= 4) gen_lemma = atoi(argv[3]);
        unsigned one[1] = {0};
        sg_hereditary(1, one, nmax, acc_conn, vis, NULL);
        for (int m = 4; m <= nmax; m++) {
            TB *t = &tb[m];
            printf("n=%d connected=%ld | 436c viol=%ld min_slack=%d open(k=1,D indep)=%ld open_eq=%ld"
                   " | 421c viol=%ld eq=%ld min_slack=%d NM=lmax+1:%ld lemma_checks=%ld lemma_viol=%ld"
                   " | 399b A3empty=%ld aA3>=4=%ld viol=%ld min_slack=%d g2>WP=%ld\n",
                   m, t->cnt, t->v436, t->m436, t->op, t->opeq, t->v421, t->eq421, t->m421, t->c421,
                   t->lchk, t->lviol, t->a3e, t->a3ge4, t->v399, t->m399, t->g2wp);
        }
        return 0;
    }
    if (argc >= 2 && !strcmp(argv[1], "g6")) {
        int lemma = argc >= 3 ? atoi(argv[2]) : 0;
        char line[4096]; unsigned A[32];
        while (fgets(line, sizeof line, stdin)) {
            line[strcspn(line, "\r\n")] = 0;
            if (!line[0]) continue;
            int n = g6read(line, A);
            if (n < 0) { printf("skip %s\n", line); continue; }
            if (!sg_connected(A, (1u << n) - 1)) { printf("%s disconnected\n", line); continue; }
            R r; evalB(n, A, &r, lemma);
            printf("%s n=%d a2=%d wp=%d k=%d dD=%d g=%d i=%d lmax=%d NM=%d g2=%d aA3=%d A3empty=%d"
                   " | s436=%d s421=%d s399=%s%d lemma=%ld/%ld\n",
                   line, r.n, r.a2, r.wp, r.k, r.dD, r.gam, r.idm, r.lmax, r.NM, r.g2, r.aA3, r.A3empty,
                   r.k * r.wp + r.dD - r.a2, r.gam * (r.NM - 3) - r.idm,
                   r.A3empty ? "NA:" : "", r.A3empty ? 0 : r.wp + 3 / r.aA3 - r.g2, r.lviol, r.lchk);
        }
        return 0;
    }
    fprintf(stderr, "usage\n");
    return 1;
}

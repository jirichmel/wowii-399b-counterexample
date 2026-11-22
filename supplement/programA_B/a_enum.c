/* a_enum.c -- search-1, program A (written from scratch; shares no code with b_enum.c,
 * with tools/lib, or with the scouts' programs).
 *
 * Conjectures checked (WOWII, G connected):
 *   436c  (n>3)  alpha_2 <= k*WP(compl G) + Delta(G[D])
 *   421c  (n>3)  i <= gamma * (|N[M_lambda]| - 3)
 *   399b  (n>2)  gamma_2 <= WP(compl G) + floor(3/alpha(G[A_3]))   (A_3 empty: reported, skipped)
 *   lemma (421c proof): for every gamma-set D and every maximal independent I of G[D]:
 *                 i <= |I| + sum_{d in D-I} (lambda(d)-1)
 *
 * Generator: own canonical-deletion generator of connected graphs (vertex added last; the
 * deletion vertex is the non-cut vertex of minimum degree with the largest canonical position;
 * canonical form by colour refinement + individualisation with twin pruning; duplicates from
 * the same parent removed with a local hash table).
 * Invariants: recursive branch and bound.
 *
 * Usage:  a_enum gen NMAX        exhaustive connected graphs, n = 4..NMAX (NMAX <= 11)
 *         a_enum g6  < file      evaluate graph6 lines, print one line per graph
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint64_t M;
#define BIT(i) (((M)1) << (i))
#define MAXN 64
static int popc(M x) { return __builtin_popcountll(x); }
static int lowb(M x) { return __builtin_ctzll(x); }

/* ------------------------------------------------------------------ invariants */
static int n;
static M adj[MAXN], cadj[MAXN], full;

static void setup(void) {
    full = (n == 64) ? ~(M)0 : (BIT(n) - 1);
    for (int i = 0; i < n; i++) cadj[i] = adj[i] | BIT(i);
}

/* alpha of G[P] */
static int alpha_set(M P) {
    if (!P) return 0;
    int v = lowb(P);
    int a = 1 + alpha_set(P & ~cadj[v]);
    if (adj[v] & P) { int b = alpha_set(P & ~BIT(v)); if (b > a) a = b; }
    return a;
}

/* alpha_2: largest S with max degree of G[S] <= 1 */
static int a2best;
static void a2rec(int i, M S, int sz, M deg1) {
    if (sz + (n - i) <= a2best) return;
    if (i == n) { a2best = sz; return; }
    M nb = adj[i] & S;
    int c = popc(nb);
    if (c == 0) a2rec(i + 1, S | BIT(i), sz + 1, deg1);
    else if (c == 1 && !(nb & deg1)) a2rec(i + 1, S | BIT(i), sz + 1, deg1 | nb | BIT(i));
    a2rec(i + 1, S, sz, deg1);
}
static int alpha2(void) { a2best = 0; a2rec(0, 0, 0, 0); return a2best; }

/* gamma */
static int gbest;
static void grec(M dom, int sz) {
    if (dom == full) { if (sz < gbest) gbest = sz; return; }
    if (sz + 1 >= gbest) return;
    int u = lowb(~dom & full);
    M c = cadj[u];
    while (c) { int w = lowb(c); c &= c - 1; grec(dom | cadj[w], sz + 1); }
}
static int gamma_(void) { gbest = n + 1; grec(0, 0); return gbest; }

/* independent domination */
static int ibest;
static void irec(M S, M dom, int sz) {
    if (dom == full) { if (sz < ibest) ibest = sz; return; }
    if (sz + 1 >= ibest) return;
    int u = lowb(~dom & full);
    M c = cadj[u];
    while (c) { int w = lowb(c); c &= c - 1; if (!(adj[w] & S)) irec(S | BIT(w), dom | cadj[w], sz + 1); }
}
static int idom(void) { ibest = n + 1; irec(0, 0, 0); return ibest; }

/* 2-domination */
static int g2best;
static void g2rec(M S, int sz) {
    if (sz >= g2best) return;
    int u = -1;
    for (int v = 0; v < n; v++) if (!(S & BIT(v)) && popc(adj[v] & S) < 2) { u = v; break; }
    if (u < 0) { g2best = sz; return; }
    if (sz + 1 >= g2best) return;
    g2rec(S | BIT(u), sz + 1);
    M c = adj[u] & ~S;
    while (c) { int w = lowb(c); c &= c - 1; g2rec(S | BIT(w), sz + 1); }
}
static int gamma2(void) { g2best = n + 1; g2rec(0, 0); return g2best; }

static int deg(int v) { return popc(adj[v]); }

/* WP(compl G): largest j with j + d_j <= n, degrees of G ascending, 1-indexed; 0 if none */
static int wp(void) {
    int d[MAXN];
    for (int i = 0; i < n; i++) d[i] = deg(i);
    for (int i = 1; i < n; i++) { int x = d[i], j = i; while (j > 0 && d[j - 1] > x) { d[j] = d[j - 1]; j--; } d[j] = x; }
    int best = 0;
    for (int j = 1; j <= n; j++) if (j + d[j - 1] <= n) best = j;
    return best;
}

/* Havel-Hakimi: number of steps until a zero first appears (0 if one is there at the start) */
static int hh_k(void) {
    int s[MAXN], m = n;
    for (int i = 0; i < n; i++) s[i] = deg(i);
    for (int i = 0; i < m; i++) if (s[i] == 0) return 0;
    for (int step = 1; step <= 4 * n; step++) {
        /* sort non-increasing */
        for (int i = 1; i < m; i++) { int x = s[i], j = i; while (j > 0 && s[j - 1] < x) { s[j] = s[j - 1]; j--; } s[j] = x; }
        int d = s[0];
        for (int i = 0; i + 1 < m; i++) s[i] = s[i + 1];
        m--;
        if (d > m) return -1; /* not graphic: cannot happen */
        for (int i = 0; i < d; i++) s[i]--;
        for (int i = 0; i < m; i++) if (s[i] == 0) return step;
        if (m == 0) return -2;
    }
    return -3;
}

typedef struct {
    int n, a2, wp, k, dD, Dind, gam, idm, lmax, NM, g2, aA3, A3empty, kalt;
    long lemma_checks, lemma_viol;
} Res;

static void eval(Res *r, int do_lemma) {
    setup();
    r->n = n;
    r->a2 = alpha2();
    r->wp = wp();
    r->k = hh_k();
    /* k==1 iff d_{Delta+1} <= 1 (descending) -- cross-check of the hand characterisation */
    {
        int Dl = 0, cnt2 = 0;
        for (int v = 0; v < n; v++) { if (deg(v) > Dl) Dl = deg(v); if (deg(v) >= 2) cnt2++; }
        r->kalt = (cnt2 <= Dl);
    }
    M D = 0;
    for (int v = 0; v < n; v++) {
        M c = adj[v];
        while (c) { int u = lowb(c); c &= c - 1; if ((cadj[u] & ~cadj[v]) == 0) { D |= BIT(v); break; } }
    }
    int dD = 0;
    for (int v = 0; v < n; v++) if (D & BIT(v)) { int x = popc(adj[v] & D); if (x > dD) dD = x; }
    r->dD = dD; r->Dind = (dD == 0);
    r->gam = gamma_();
    r->idm = idom();
    int lam[MAXN], lmax = 0;
    for (int v = 0; v < n; v++) { lam[v] = alpha_set(adj[v]); if (lam[v] > lmax) lmax = lam[v]; }
    M X = 0;
    for (int v = 0; v < n; v++) if (lam[v] == lmax) X |= cadj[v];
    r->lmax = lmax; r->NM = popc(X);
    r->g2 = gamma2();
    M A3 = 0;
    for (int v = 0; v < n; v++) if (deg(v) >= 3) A3 |= BIT(v);
    r->A3empty = (A3 == 0);
    r->aA3 = alpha_set(A3);
    r->lemma_checks = r->lemma_viol = 0;
    if (do_lemma) {
        /* all gamma-sets: combinations of size gam */
        int g = r->gam;
        int idx[MAXN];
        for (int i = 0; i < g; i++) idx[i] = i;
        for (;;) {
            M S = 0, dom = 0;
            for (int i = 0; i < g; i++) { S |= BIT(idx[i]); dom |= cadj[idx[i]]; }
            if (dom == full) {
                /* maximal independent subsets I of G[S] */
                for (M I = S;; I = (I - 1) & S) {
                    int ok = 1;
                    M t = I;
                    while (t) { int v = lowb(t); t &= t - 1; if (adj[v] & I) { ok = 0; break; } }
                    if (ok) {
                        M rest = S & ~I;
                        t = rest;
                        while (t) { int v = lowb(t); t &= t - 1; if (!(adj[v] & I)) { ok = 0; break; } }
                    }
                    if (ok && I) {
                        int bound = popc(I);
                        M t2 = S & ~I;
                        while (t2) { int v = lowb(t2); t2 &= t2 - 1; bound += lam[v] - 1; }
                        r->lemma_checks++;
                        if (r->idm > bound) r->lemma_viol++;
                    }
                    if (I == 0) break;
                }
            }
            int i = g - 1;
            while (i >= 0 && idx[i] == n - g + i) i--;
            if (i < 0) break;
            idx[i]++;
            for (int j = i + 1; j < g; j++) idx[j] = idx[j - 1] + 1;
        }
    }
}

/* ------------------------------------------------------------------ tallies */
typedef struct {
    long cnt;
    long v436, open436, open436eq, kmismatch; int min436;
    long v421, eq421, case421; int min421;
    long lchk, lviol;
    long a3empty, a3ne, a3ge4, v399, g2gtwp; int min399;
} Tal;
static Tal T[16];

static void tally(Res *r) {
    Tal *t = &T[r->n];
    t->cnt++;
    if ((r->k == 1) != r->kalt) t->kmismatch++;
    int rhs = r->k * r->wp + r->dD, s = rhs - r->a2;
    if (s < 0) t->v436++;
    if (t->cnt == 1 || s < t->min436) t->min436 = s;
    if (r->k == 1 && r->Dind) { t->open436++; if (r->a2 == r->wp) t->open436eq++; }
    int s2 = r->gam * (r->NM - 3) - r->idm;
    if (s2 < 0) t->v421++;
    if (s2 == 0) t->eq421++;
    if (t->cnt == 1 || s2 < t->min421) t->min421 = s2;
    if (r->NM == r->lmax + 1) t->case421++;
    t->lchk += r->lemma_checks; t->lviol += r->lemma_viol;
    if (r->g2 > r->wp) t->g2gtwp++;
    if (r->A3empty) t->a3empty++;
    else {
        if (r->aA3 >= 4) t->a3ge4++;
        int s3 = r->wp + 3 / r->aA3 - r->g2;
        if (s3 < 0) t->v399++;
        t->a3ne++;
        if (t->a3ne == 1 || s3 < t->min399) t->min399 = s3; /* min over graphs with A3 nonempty */
    }
}

/* ------------------------------------------------------------------ canonical form (n <= 11) */
static int cn;
static M cg[16];
static uint64_t cbest; static int cbestlab[16], have;

static uint64_t code_of(const int *lab) {
    int inv[16];
    for (int v = 0; v < cn; v++) inv[lab[v]] = v;
    uint64_t c = 0;
    for (int i = 0; i < cn; i++) for (int j = i + 1; j < cn; j++) c = (c << 1) | ((cg[inv[i]] >> inv[j]) & 1);
    return c;
}

/* equitable refinement of colouring col (colours 0..k-1); returns number of colours */
static int refine(int *col) {
    int k = 0;
    for (int v = 0; v < cn; v++) if (col[v] + 1 > k) k = col[v] + 1;
    for (;;) {
        int sig[16][17];
        for (int v = 0; v < cn; v++) {
            sig[v][0] = col[v];
            for (int c = 0; c < 16; c++) sig[v][c + 1] = 0;
            M x = cg[v];
            while (x) { int u = lowb(x); x &= x - 1; sig[v][col[u] + 1]++; }
        }
        int ord[16];
        for (int v = 0; v < cn; v++) ord[v] = v;
        for (int i = 1; i < cn; i++) {
            int x = ord[i], j = i;
            while (j > 0 && memcmp(sig[ord[j - 1]], sig[x], sizeof(int) * (k + 1)) > 0) { ord[j] = ord[j - 1]; j--; }
            ord[j] = x;
        }
        int nk = 0, nc[16];
        for (int i = 0; i < cn; i++) {
            if (i > 0 && memcmp(sig[ord[i - 1]], sig[ord[i]], sizeof(int) * (k + 1)) != 0) nk++;
            nc[ord[i]] = nk;
        }
        nk++;
        memcpy(col, nc, sizeof(int) * cn);
        if (nk == k) return k;
        k = nk;
    }
}

static long leaves;
static void csearch(int *col0) {
    int col[16];
    memcpy(col, col0, sizeof(int) * cn);
    int k = refine(col);
    if (k == cn) {
        leaves++;
        uint64_t c = code_of(col);
        if (!have || c > cbest) { cbest = c; memcpy(cbestlab, col, sizeof(int) * cn); have = 1; }
        return;
    }
    int size[16] = {0};
    for (int v = 0; v < cn; v++) size[col[v]]++;
    int target = 0;
    while (size[target] == 1) target++;
    M tried = 0;
    for (int v = 0; v < cn; v++) {
        if (col[v] != target) continue;
        int twin = 0;
        M t = tried;
        while (t) { int u = lowb(t); t &= t - 1; if ((cg[u] & ~BIT(v)) == (cg[v] & ~BIT(u))) { twin = 1; break; } }
        if (twin) continue;
        tried |= BIT(v);
        int nc[16];
        for (int u = 0; u < cn; u++) nc[u] = col[u] > target ? col[u] + 1 : (col[u] == target && u != v ? target + 1 : col[u]);
        csearch(nc);
    }
}

/* canonical code of graph g on m vertices; lab gets the canonical position of each vertex */
static uint64_t canon(int m, const M *g, int *lab) {
    cn = m;
    for (int i = 0; i < m; i++) cg[i] = g[i];
    int col[16];
    for (int v = 0; v < m; v++) col[v] = 0;
    have = 0;
    csearch(col);
    if (lab) memcpy(lab, cbestlab, sizeof(int) * m);
    return cbest;
}

static int connected_mask(int m, const M *g, M S) {
    if (!S) return 1;
    M seen = BIT(lowb(S)), fr = seen;
    while (fr) { int v = lowb(fr); fr &= fr - 1; M nw = g[v] & S & ~seen; seen |= nw; fr |= nw; }
    return seen == S;
}

/* ------------------------------------------------------------------ generator */
typedef struct { M g[12]; } GR;
static GR *lev[13]; static long levn[13];
static int NMAX;
static int do_lemma_gen = 1;
static int list_mode = 0;
static void print_g6(int m, const M *g) {
    char out[256]; int p = 0; out[p++] = (char)(m + 63);
    int k = 0, cur = 0;
    for (int j = 1; j < m; j++) for (int i = 0; i < j; i++) {
        cur = (cur << 1) | (int)((g[i] >> j) & 1); k++;
        if (k % 6 == 0) { out[p++] = (char)(cur + 63); cur = 0; }
    }
    if (k % 6) { cur <<= (6 - k % 6); out[p++] = (char)(cur + 63); }
    out[p] = 0; puts(out);
}

static void visit(int m, const M *g) {
    n = m;
    for (int i = 0; i < m; i++) adj[i] = g[i];
    for (int i = m; i < MAXN; i++) adj[i] = 0;
    if (list_mode) { print_g6(m, g); return; }
    if (m >= 4) { Res r; eval(&r, do_lemma_gen); tally(&r); }
}

#define HSZ 1024
static void gen_level(int m) { /* build graphs on m vertices from lev[m-1] */
    long cap = 1024, cnt = 0;
    GR *out = (m < NMAX) ? malloc(sizeof(GR) * cap) : NULL;
    uint64_t hs[HSZ]; int hused[HSZ];
    for (long p = 0; p < levn[m - 1]; p++) {
        M *P = lev[m - 1][p].g;
        uint64_t pcode = canon(m - 1, P, NULL);
        memset(hused, 0, sizeof hused);
        for (M S = 1; S < BIT(m - 1); S++) {
            M g[12];
            for (int i = 0; i < m - 1; i++) g[i] = P[i] | (((S >> i) & 1) ? BIT(m - 1) : 0);
            g[m - 1] = S;
            int v = m - 1, dv = popc(S);
            /* minimum degree among non-cut vertices */
            int mind = 99;
            for (int x = 0; x < m; x++) {
                int dx = popc(g[x]);
                if (dx >= mind) continue;
                if (x == v || connected_mask(m, g, (BIT(m) - 1) & ~BIT(x))) mind = dx;
            }
            if (dv > mind) continue;
            int lab[16];
            uint64_t code = canon(m, g, lab);
            int w = -1, wp_ = -1;
            for (int x = 0; x < m; x++) {
                if (popc(g[x]) != mind) continue;
                if (x != v && !connected_mask(m, g, (BIT(m) - 1) & ~BIT(x))) continue;
                if (lab[x] > wp_) { wp_ = lab[x]; w = x; }
            }
            if (w != v) {
                M h[12]; int q = 0, map[16];
                for (int x = 0; x < m; x++) if (x != w) map[x] = q++;
                for (int x = 0; x < m; x++) if (x != w) {
                    M y = g[x] & ~BIT(w), z = 0;
                    while (y) { int u = lowb(y); y &= y - 1; z |= BIT(map[u]); }
                    h[map[x]] = z;
                }
                if (canon(m - 1, h, NULL) != pcode) continue;
            }
            /* local dedupe */
            unsigned hh = (unsigned)((code * 0x9E3779B97F4A7C15ULL) >> 54) & (HSZ - 1);
            int dup = 0;
            while (hused[hh]) { if (hs[hh] == code) { dup = 1; break; } hh = (hh + 1) & (HSZ - 1); }
            if (dup) continue;
            hused[hh] = 1; hs[hh] = code;
            /* relabel canonically */
            M cgr[12];
            for (int x = 0; x < m; x++) {
                M y = g[x], z = 0;
                while (y) { int u = lowb(y); y &= y - 1; z |= BIT(lab[u]); }
                cgr[lab[x]] = z;
            }
            cnt++;
            visit(m, cgr);
            if (out) {
                if (cnt > cap) { cap *= 2; out = realloc(out, sizeof(GR) * cap); }
                memcpy(out[cnt - 1].g, cgr, sizeof(M) * m);
            }
        }
    }
    lev[m] = out; levn[m] = cnt;
}

/* ------------------------------------------------------------------ graph6 */
static int read_g6(const char *s) {
    int p = 0;
    if (s[0] == '>') return -1;
    int m = s[p++] - 63;
    if (m == 63) { m = ((s[1] - 63) << 12) | ((s[2] - 63) << 6) | (s[3] - 63); p = 4; }
    if (m > MAXN) return -1;
    n = m;
    for (int i = 0; i < MAXN; i++) adj[i] = 0;
    int bitpos = 0, cur = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        if (bitpos % 6 == 0) cur = s[p++] - 63;
        int b = (cur >> (5 - bitpos % 6)) & 1;
        bitpos++;
        if (b) { adj[i] |= BIT(j); adj[j] |= BIT(i); }
    }
    return n;
}

int main(int argc, char **argv) {
    if (argc >= 3 && !strcmp(argv[1], "gen")) {
        NMAX = atoi(argv[2]);
        if (argc >= 4) do_lemma_gen = atoi(argv[3]);
        if (NMAX > 11) { fprintf(stderr, "NMAX <= 11\n"); return 1; }
        lev[1] = malloc(sizeof(GR)); lev[1][0].g[0] = 0; levn[1] = 1;
        for (int m = 2; m <= NMAX; m++) {
            gen_level(m);
            if (m >= 4) {
                Tal *t = &T[m];
                printf("n=%d connected=%ld | 436c viol=%ld min_slack=%d open(k=1,D indep)=%ld open_eq=%ld k1_mismatch=%ld"
                       " | 421c viol=%ld eq=%ld min_slack=%d NM=lmax+1:%ld lemma_checks=%ld lemma_viol=%ld"
                       " | 399b A3empty=%ld aA3>=4=%ld viol=%ld min_slack=%d g2>WP=%ld\n",
                       m, levn[m], t->v436, t->min436, t->open436, t->open436eq, t->kmismatch,
                       t->v421, t->eq421, t->min421, t->case421, t->lchk, t->lviol,
                       t->a3empty, t->a3ge4, t->v399, t->min399, t->g2gtwp);
            } else printf("n=%d connected=%ld\n", m, levn[m]);
            fflush(stdout);
            if (m >= 3 && lev[m - 1] && m - 1 > 1) { free(lev[m - 1]); lev[m - 1] = NULL; }
        }
        return 0;
    }
    if (argc >= 3 && !strcmp(argv[1], "list")) {
        NMAX = atoi(argv[2]); list_mode = 1;
        lev[1] = malloc(sizeof(GR)); lev[1][0].g[0] = 0; levn[1] = 1;
        print_g6(1, lev[1][0].g);
        for (int m = 2; m <= NMAX; m++) gen_level(m);
        return 0;
    }
    if (argc >= 6 && !strcmp(argv[1], "climb")) {
        int target = atoi(argv[2]), m = atoi(argv[3]); long iters = atol(argv[4]); srand(atoi(argv[5]));
        int restart = 20000;
        n = m;
        long evals = 0, neg = 0; int globalmin = 1 << 30, histo[8] = {0};
        for (long it = 0; it < iters; it++) {
            if (it % restart == 0) {
                for (int i = 0; i < MAXN; i++) adj[i] = 0;
                for (int v = 1; v < n; v++) { int u = rand() % v; adj[u] |= BIT(v); adj[v] |= BIT(u); }
                int extra = rand() % (n * 2 + 1);
                for (int e = 0; e < extra; e++) { int a = rand() % n, b = rand() % n; if (a != b) { adj[a] |= BIT(b); adj[b] |= BIT(a); } }
            }
            static int cur = 1 << 30;
            if (it % restart == 0) cur = 1 << 30;
            int a = rand() % n, b = rand() % n;
            if (a == b) continue;
            adj[a] ^= BIT(b); adj[b] ^= BIT(a);
            if (!connected_mask(n, adj, BIT(n) - 1)) { adj[a] ^= BIT(b); adj[b] ^= BIT(a); continue; }
            Res r; eval(&r, 0); evals++;
            int sl = (target == 436) ? r.k * r.wp + r.dD - r.a2
                   : (target == 421) ? r.gam * (r.NM - 3) - r.idm
                   : (r.A3empty ? 99 : r.wp + 3 / r.aA3 - r.g2);
            if (sl < globalmin) globalmin = sl;
            if (sl >= 0 && sl < 8) histo[sl]++;
            if (sl < 0) { neg++; printf("NEG "); print_g6(n, adj); }
            if (sl <= cur || rand() % 100 < 3) cur = sl;
            else { adj[a] ^= BIT(b); adj[b] ^= BIT(a); }
        }
        printf("climb target=%d n=%d evals=%ld min_slack=%d neg=%ld slack0..7:", target, m, evals, globalmin, neg);
        for (int i = 0; i < 8; i++) printf(" %d", histo[i]);
        printf("\n");
        return 0;
    }
    if (argc >= 2 && !strcmp(argv[1], "g6")) {
        char line[4096];
        int lemma = (argc >= 3) ? atoi(argv[2]) : 0;
        while (fgets(line, sizeof line, stdin)) {
            line[strcspn(line, "\r\n")] = 0;
            if (!line[0]) continue;
            if (read_g6(line) < 0) { printf("skip %s\n", line); continue; }
            if (!connected_mask(n, adj, n == 64 ? ~(M)0 : BIT(n) - 1)) { printf("%s disconnected\n", line); continue; }
            Res r; eval(&r, lemma);
            printf("%s n=%d a2=%d wp=%d k=%d dD=%d g=%d i=%d lmax=%d NM=%d g2=%d aA3=%d A3empty=%d"
                   " | s436=%d s421=%d s399=%s%d lemma=%ld/%ld\n",
                   line, r.n, r.a2, r.wp, r.k, r.dD, r.gam, r.idm, r.lmax, r.NM, r.g2, r.aA3, r.A3empty,
                   r.k * r.wp + r.dD - r.a2, r.gam * (r.NM - 3) - r.idm,
                   r.A3empty ? "NA:" : "", r.A3empty ? 0 : r.wp + 3 / r.aA3 - r.g2, r.lemma_viol, r.lemma_checks);
        }
        return 0;
    }
    fprintf(stderr, "usage: a_enum gen NMAX [lemma0/1] | a_enum g6 [lemma] < file\n");
    return 1;
}

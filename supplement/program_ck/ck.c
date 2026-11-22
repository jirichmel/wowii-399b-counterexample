/* ck.c -- checker-1 (Opus 5.5), 21 Nov 2026.
 * Written from the catalogue statements only; shares no code with search-1, the scouts,
 * or tools/lib.  Own generator: vertex addition from connected (n-1)-graphs, de-duplicated
 * by a canonical code (max upper-triangle code over the leaves of an individualisation-
 * refinement tree, pruned only by twins), stored in a hash set.
 *
 * Modes:
 *   ck gen NMAX [alldom]   all connected graphs n = 4..NMAX (NMAX <= 10), statistics per n;
 *                          "alldom" also tests the 421c lemma on every dominating set (slow).
 *   ck g6                  read graph6 lines on stdin, print the invariants of each.
 *   ck F q1 q2             build F_q from the description and print invariants.
 *   ck Fgen t m L q        generalised F: |X| = t, m vertices y, L leaves per x, K_q, w.
 *
 * Definitions (catalogue / glossary):
 *   gamma_2: min |S|, every v not in S has >= 2 neighbours in S.
 *   alpha_2: max |S| with Delta(G[S]) <= 1.
 *   WP(compl G): largest j with j + d_j <= n, degrees nondecreasing (0 if none).
 *   k: Havel-Hakimi steps until a zero first appears.
 *   D: v with N[u] subset of N[v] for some u != v.  lambda(v) = alpha(G[N(v)]).
 *   A_3: vertices of degree >= 3.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define MAXN 26
typedef uint32_t set;
#define BIT(v) ((set)1u << (v))
static int pc(set s) { return __builtin_popcount(s); }

/* ------------------------------------------------------------------ canonical code */
static int cn;              /* order */
static set ca[MAXN];        /* adjacency */
static uint64_t cbest;
static int chave;

static int refine(int *cell, int nc)
{
    for (;;) {
        set mem[MAXN];
        for (int c = 0; c < nc; c++) mem[c] = 0;
        for (int v = 0; v < cn; v++) mem[cell[v]] |= BIT(v);
        uint64_t sig[MAXN];
        for (int v = 0; v < cn; v++) {
            uint64_t s = (uint64_t)cell[v] << 48;
            for (int c = 0; c < nc; c++) s |= (uint64_t)pc(ca[v] & mem[c]) << (4 * c);
            sig[v] = s;
        }
        uint64_t u[MAXN]; int nu = 0;
        for (int v = 0; v < cn; v++) {
            int f = 0;
            for (int t = 0; t < nu; t++) if (u[t] == sig[v]) { f = 1; break; }
            if (!f) u[nu++] = sig[v];
        }
        for (int a = 1; a < nu; a++) { uint64_t x = u[a]; int b = a - 1; while (b >= 0 && u[b] > x) { u[b + 1] = u[b]; b--; } u[b + 1] = x; }
        for (int v = 0; v < cn; v++) for (int t = 0; t < nu; t++) if (u[t] == sig[v]) { cell[v] = t; break; }
        if (nu == nc) return nc;
        nc = nu;
    }
}

static void csearch(int *cell, int nc)
{
    nc = refine(cell, nc);
    if (nc == cn) {
        int perm[MAXN];
        for (int v = 0; v < cn; v++) perm[cell[v]] = v;
        uint64_t c = 0;
        for (int j = 1; j < cn; j++) for (int i = 0; i < j; i++) c = (c << 1) | ((ca[perm[i]] >> perm[j]) & 1);
        if (!chave || c > cbest) { cbest = c; chave = 1; }
        return;
    }
    int size[MAXN] = {0};
    for (int v = 0; v < cn; v++) size[cell[v]]++;
    int t = 0; while (size[t] == 1) t++;
    set tried = 0;
    for (int v = 0; v < cn; v++) {
        if (cell[v] != t) continue;
        int skip = 0;
        for (int u = 0; u < cn; u++) if ((tried >> u) & 1) {
            if ((ca[u] & ~BIT(v)) == (ca[v] & ~BIT(u))) { skip = 1; break; }
        }
        if (skip) continue;
        tried |= BIT(v);
        int nc2[MAXN];
        for (int w = 0; w < cn; w++) {
            if (cell[w] > t) nc2[w] = cell[w] + 1;
            else if (w == v) nc2[w] = t;
            else if (cell[w] == t) nc2[w] = t + 1;
            else nc2[w] = cell[w];
        }
        csearch(nc2, nc + 1);
    }
}

static uint64_t canon(int n, const set *a)
{
    cn = n; for (int v = 0; v < n; v++) ca[v] = a[v];
    chave = 0;
    int cell[MAXN]; for (int v = 0; v < n; v++) cell[v] = 0;
    csearch(cell, 1);
    return cbest;
}

static void decode(int n, uint64_t c, set *a)
{
    int L = n * (n - 1) / 2, p = 0;
    for (int v = 0; v < n; v++) a[v] = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++, p++)
        if ((c >> (L - 1 - p)) & 1) { a[i] |= BIT(j); a[j] |= BIT(i); }
}

/* ------------------------------------------------------------------ invariants */
typedef struct {
    int n, a2, wp, wpbook, k, dD, g, i, lmax, NM, g2, aA3, A3empty, nMl, degx, Nxind;
    long lemma_pairs, lemma_viol;
    int open, supports_indep, k1char;
} inv_t;

static set *D1, *D2; static uint8_t *al, *ind; static int cap_n = -1;
static int alldom = 0;

static void alloc_n(int n)
{
    if (n <= cap_n) return;
    free(D1); free(D2); free(al); free(ind);
    size_t m = (size_t)1 << n;
    D1 = malloc(m * sizeof(set)); D2 = malloc(m * sizeof(set)); al = malloc(m); ind = malloc(m);
    if (!D1 || !D2 || !al || !ind) { fprintf(stderr, "oom\n"); exit(1); }
    cap_n = n;
}

static int hh_k(int n, const int *deg)
{
    int s[MAXN], m = n;
    for (int v = 0; v < n; v++) s[v] = deg[v];
    for (int step = 1; ; step++) {
        /* sort descending */
        for (int a = 1; a < m; a++) { int x = s[a], b = a - 1; while (b >= 0 && s[b] < x) { s[b + 1] = s[b]; b--; } s[b + 1] = x; }
        int d = s[0];
        if (d > m - 1) return -1;           /* not graphic: cannot happen */
        for (int t = 1; t <= d; t++) s[t]--;
        for (int t = 1; t < m; t++) s[t - 1] = s[t];
        m--;
        for (int t = 0; t < m; t++) if (s[t] == 0) return step;
        if (m == 0) return -2;
    }
}

static void evaluate(int n, const set *a, inv_t *r)
{
    alloc_n(n);
    set full = (n == 32) ? ~0u : (BIT(n) - 1);
    D1[0] = D2[0] = 0; al[0] = 0; ind[0] = 1;
    for (set S = 1; S <= full && S != 0; S++) {
        int x = __builtin_ctz(S); set P = S & (S - 1);
        D1[S] = D1[P] | a[x];
        D2[S] = D2[P] | (D1[P] & a[x]);
        ind[S] = ind[P] && !(a[x] & P);
        int v1 = al[P], v2 = 1 + al[P & ~a[x]];
        al[S] = (uint8_t)(v1 > v2 ? v1 : v2);
        if (S == full) break;
    }
    int g = 99, ii = 99, g2 = 99, a2 = 0;
    for (set S = 0; ; S++) {
        int p = pc(S);
        int dom = ((S | D1[S]) == full);
        if (dom && p < g) g = p;
        if (dom && ind[S] && p < ii) ii = p;
        if (((S | D2[S]) == full) && p < g2) g2 = p;
        if (!(S & D2[S]) && p > a2) a2 = p;
        if (S == full) break;
    }
    int deg[MAXN], Delta = 0;
    for (int v = 0; v < n; v++) { deg[v] = pc(a[v]); if (deg[v] > Delta) Delta = deg[v]; }
    /* WP as the glossary states it */
    int ds[MAXN]; for (int v = 0; v < n; v++) ds[v] = deg[v];
    for (int x = 1; x < n; x++) { int y = ds[x], b = x - 1; while (b >= 0 && ds[b] > y) { ds[b + 1] = ds[b]; b--; } ds[b + 1] = y; }
    int wp = 0; for (int j = 1; j <= n; j++) if (j + ds[j - 1] <= n) wp = j;
    /* textbook Welsh-Powell bound of the complement: max_i min(dbar_i + 1, i), dbar nonincreasing */
    int wpb = 0;
    for (int t = 1; t <= n; t++) { int db = n - 1 - ds[t - 1]; int m = db + 1 < t ? db + 1 : t; if (m > wpb) wpb = m; }
    int k = hh_k(n, deg);
    set Dset = 0;
    for (int v = 0; v < n; v++) for (int u = 0; u < n; u++) if (u != v) {
        if (((a[u] | BIT(u)) & ~(a[v] | BIT(v))) == 0) { Dset |= BIT(v); break; }
    }
    int dD = 0; for (int v = 0; v < n; v++) if ((Dset >> v) & 1) { int t = pc(a[v] & Dset); if (t > dD) dD = t; }
    int lam[MAXN], lmax = 0;
    for (int v = 0; v < n; v++) { lam[v] = al[a[v]]; if (lam[v] > lmax) lmax = lam[v]; }
    set Ml = 0, NMs = 0;
    for (int v = 0; v < n; v++) if (lam[v] == lmax) { Ml |= BIT(v); NMs |= a[v] | BIT(v); }
    set A3 = 0; for (int v = 0; v < n; v++) if (deg[v] >= 3) A3 |= BIT(v);
    r->n = n; r->a2 = a2; r->wp = wp; r->wpbook = wpb; r->k = k; r->dD = dD; r->g = g; r->i = ii;
    r->lmax = lmax; r->NM = pc(NMs); r->g2 = g2; r->A3empty = (A3 == 0); r->aA3 = al[A3];
    r->nMl = pc(Ml);
    r->degx = -1; r->Nxind = -1;
    if (pc(Ml) == 1) { int x = __builtin_ctz(Ml); r->degx = deg[x]; r->Nxind = ind[a[x]]; }
    /* refined Bollobas-Cockayne lemma: D a gamma-set (or any dominating set), I maximal independent in D */
    long pairs = 0, viol = 0;
    for (set S = 0; ; S++) {
        int p = pc(S);
        if (((S | D1[S]) == full) && (alldom || p == g)) {
            /* enumerate subsets I of S */
            set I = 0;
            for (;;) {
                if (ind[I]) {
                    int ok = 1; int bound = pc(I);
                    for (set R = S & ~I; R; R &= R - 1) {
                        int d = __builtin_ctz(R);
                        if (!(a[d] & I)) { ok = 0; break; }
                        bound += lam[d] - 1;
                    }
                    if (ok) { pairs++; if (ii > bound) viol++; }
                }
                if (I == S) break;
                I = (I - S) & S;
            }
        }
        if (S == full) break;
    }
    r->lemma_pairs = pairs; r->lemma_viol = viol;
    r->open = (k == 1 && dD == 0);
    /* supports independent? */
    set sup = 0; for (int v = 0; v < n; v++) if (deg[v] == 1) sup |= a[v];
    r->supports_indep = 1;
    for (int v = 0; v < n; v++) if ((sup >> v) & 1) if (a[v] & sup) r->supports_indep = 0;
    int nge2 = 0; for (int v = 0; v < n; v++) if (deg[v] >= 2) nge2++;
    r->k1char = ((k == 1) == (nge2 <= Delta));
}

static void print_inv(const char *tag, const inv_t *r)
{
    int bound399 = r->A3empty ? -999 : r->wp + 3 / r->aA3;
    printf("%s n=%d a2=%d wp=%d wpbook=%d k=%d dD=%d g=%d i=%d lmax=%d NM=%d g2=%d aA3=%d A3empty=%d | s436=%d s421=%d s399=%s%d lemma=%ld/%ld\n",
           tag, r->n, r->a2, r->wp, r->wpbook, r->k, r->dD, r->g, r->i, r->lmax, r->NM, r->g2, r->aA3, r->A3empty,
           r->k * r->wp + r->dD - r->a2, r->g * (r->NM - 3) - r->i,
           r->A3empty ? "NA:" : "", r->A3empty ? 0 : bound399 - r->g2, r->lemma_viol, r->lemma_pairs);
}

/* ------------------------------------------------------------------ graph6 */
static int read_g6(const char *s, int *n, set *a)
{
    int m = s[0] - 63; if (m < 1 || m > MAXN) return 0;
    *n = m; for (int v = 0; v < m; v++) a[v] = 0;
    int bitpos = 0; const char *p = s + 1;
    for (int j = 1; j < m; j++) for (int i = 0; i < j; i++, bitpos++) {
        int byte = p[bitpos / 6] - 63, b = 5 - bitpos % 6;
        if ((byte >> b) & 1) { a[i] |= BIT(j); a[j] |= BIT(i); }
    }
    return 1;
}

static int connected(int n, const set *a)
{
    set seen = 1, fr = 1;
    while (fr) { set nx = 0; for (set f = fr; f; f &= f - 1) nx |= a[__builtin_ctz(f)]; fr = nx & ~seen; seen |= nx; }
    return seen == (BIT(n) - 1);
}

/* ------------------------------------------------------------------ generator */
typedef struct { long cnt, v436, open, open_eq, k1mis, v421, eq421, case_r1, lemma_pairs, lemma_viol,
                 A3empty, aA3ge4, v399, g2gtwp, dp12viol, g2gta2, wpmis, supmis, caseclaim_mis;
                 int min436, min421, min399; } stat_t;

static void stat_add(stat_t *s, const inv_t *r)
{
    s->cnt++;
    int s436 = r->k * r->wp + r->dD - r->a2;
    if (s436 < 0) s->v436++;
    if (s436 < s->min436) s->min436 = s436;
    if (r->open) { s->open++; if (r->a2 == r->wp) s->open_eq++; if (!r->supports_indep) s->supmis++; }
    if (!r->k1char) s->k1mis++;
    int s421 = r->g * (r->NM - 3) - r->i;
    if (s421 < 0) s->v421++;
    if (s421 == 0) s->eq421++;
    if (s421 < s->min421) s->min421 = s421;
    if (r->NM == r->lmax + 1) {
        s->case_r1++;
        if (!(r->nMl == 1 && r->lmax >= 3 && r->degx == r->lmax && r->Nxind == 1)) s->caseclaim_mis++;
    }
    s->lemma_pairs += r->lemma_pairs; s->lemma_viol += r->lemma_viol;
    if (r->A3empty) s->A3empty++;
    else {
        if (r->aA3 >= 4) s->aA3ge4++;
        int s399 = r->wp + 3 / r->aA3 - r->g2;
        if (s399 < 0) s->v399++;
        if (s399 < s->min399) s->min399 = s399;
    }
    if (r->g2 > r->wp) s->g2gtwp++;
    if (r->a2 > r->wp + 1) s->dp12viol++;
    if (r->g2 > r->a2) s->g2gta2++;
    if (r->wp != r->wpbook) s->wpmis++;
}

static uint64_t *H; static uint64_t Hmask;
static int hinsert(uint64_t c)
{
    uint64_t key = c + 1;
    uint64_t h = (key * 0x9E3779B97F4A7C15ULL) >> 20;
    for (uint64_t p = h & Hmask; ; p = (p + 1) & Hmask) {
        if (H[p] == key) return 0;
        if (H[p] == 0) { H[p] = key; return 1; }
    }
}

static void gen(int nmax)
{
    static const int hb[] = {0, 4, 4, 4, 6, 8, 10, 12, 16, 20, 25};
    uint64_t *prev = malloc(sizeof(uint64_t)); long nprev = 1; prev[0] = 0; /* K_1 */
    for (int n = 2; n <= nmax; n++) {
        Hmask = ((uint64_t)1 << hb[n]) - 1;
        H = calloc(Hmask + 1, sizeof(uint64_t));
        long cap = (n < nmax) ? (long)((Hmask + 1) / 2) : 0;
        uint64_t *next = cap ? malloc(cap * sizeof(uint64_t)) : NULL; long nnext = 0, total = 0;
        stat_t st; memset(&st, 0, sizeof st); st.min436 = st.min421 = st.min399 = 1 << 20;
        set a[MAXN];
        for (long t = 0; t < nprev; t++) {
            decode(n - 1, prev[t], a);
            for (set S = 1; S < BIT(n - 1); S++) {
                set b[MAXN];
                for (int v = 0; v < n - 1; v++) b[v] = a[v] | (((S >> v) & 1) ? BIT(n - 1) : 0);
                b[n - 1] = S;
                uint64_t c = canon(n, b);
                if (!hinsert(c)) continue;
                total++;
                if (cap) { if (nnext >= cap) { fprintf(stderr, "list full\n"); exit(1); } next[nnext++] = c; }
                if (n >= 4) {
                    set d[MAXN]; decode(n, c, d);     /* evaluate the canonical copy */
                    if (!connected(n, d)) { fprintf(stderr, "disconnected?!\n"); exit(1); }
                    inv_t r; evaluate(n, d, &r); stat_add(&st, &r);
                    if ((r.wp + (r.A3empty ? 99 : 3 / r.aA3) - r.g2) < 0 ||
                        (r.k * r.wp + r.dD - r.a2) < 0 || (r.g * (r.NM - 3) - r.i) < 0 || r.lemma_viol) {
                        print_inv("VIOL", &r);
                    }
                }
            }
        }
        if (n < 4) printf("n=%d connected=%ld\n", n, total);
        else
            printf("n=%d connected=%ld | 436c viol=%ld min_slack=%d open=%ld open_eq=%ld k1_mismatch=%ld supports_not_indep=%ld"
                   " | 421c viol=%ld eq=%ld min_slack=%d NM=lmax+1:%ld caseclaim_mismatch=%ld lemma_pairs=%ld lemma_viol=%ld"
                   " | 399b A3empty=%ld aA3>=4=%ld viol=%ld min_slack=%d g2>WP=%ld | a2>WP+1=%ld g2>a2=%ld WPdef_mismatch=%ld\n",
                   n, total, st.v436, st.min436, st.open, st.open_eq, st.k1mis, st.supmis,
                   st.v421, st.eq421, st.min421, st.case_r1, st.caseclaim_mis, st.lemma_pairs, st.lemma_viol,
                   st.A3empty, st.aA3ge4, st.v399, st.min399, st.g2gtwp, st.dp12viol, st.g2gta2, st.wpmis);
        fflush(stdout);
        free(H); free(prev); prev = next; nprev = nnext;
    }
}

/* ------------------------------------------------------------------ families */
static int nn; static set fa[MAXN];
static int addv(void) { fa[nn] = 0; return nn++; }
static void edge(int u, int v) { fa[u] |= BIT(v); fa[v] |= BIT(u); }

/* generalised F: t vertices x (independent), each with L leaves; K_q complete to X; w adjacent to all of K_q;
 * m vertices y, each adjacent to all of X.  F_q = Fgen(3, 2, 1, q). */
static void build_Fgen(int t, int m, int L, int q)
{
    nn = 0; int x[MAXN], K[MAXN];
    for (int i = 0; i < t; i++) { x[i] = addv(); for (int l = 0; l < L; l++) edge(x[i], addv()); }
    for (int i = 0; i < q; i++) { K[i] = addv(); for (int j = 0; j < i; j++) edge(K[i], K[j]); for (int j = 0; j < t; j++) edge(K[i], x[j]); }
    int w = addv(); for (int i = 0; i < q; i++) edge(w, K[i]);
    for (int i = 0; i < m; i++) { int y = addv(); for (int j = 0; j < t; j++) edge(y, x[j]); }
}

int main(int argc, char **argv)
{
    if (argc >= 3 && !strcmp(argv[1], "gen")) {
        if (argc >= 4 && !strcmp(argv[3], "alldom")) alldom = 1;
        gen(atoi(argv[2]));
    } else if (argc >= 2 && !strcmp(argv[1], "g6")) {
        if (argc >= 3 && !strcmp(argv[2], "alldom")) alldom = 1;
        char line[512]; int n; set a[MAXN];
        while (fgets(line, sizeof line, stdin)) {
            line[strcspn(line, "\r\n")] = 0;
            if (!line[0]) continue;
            if (!read_g6(line, &n, a)) { printf("BAD %s\n", line); continue; }
            if (n > 24) { printf("TOOBIG %s\n", line); continue; }
            if (!connected(n, a)) { printf("%s disconnected\n", line); continue; }
            inv_t r; evaluate(n, a, &r); print_inv(line, &r);
        }
    } else if (argc >= 4 && !strcmp(argv[1], "F")) {
        for (int q = atoi(argv[2]); q <= atoi(argv[3]); q++) {
            build_Fgen(3, 2, 1, q);
            inv_t r; evaluate(nn, fa, &r);
            char tag[32]; snprintf(tag, sizeof tag, "F_%d", q); print_inv(tag, &r);
        }
    } else if (argc >= 6 && !strcmp(argv[1], "Fgen")) {
        build_Fgen(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]));
        if (nn > 24) { printf("too big\n"); return 0; }
        inv_t r; evaluate(nn, fa, &r);
        char tag[64]; snprintf(tag, sizeof tag, "Fgen(t=%s,m=%s,L=%s,q=%s)", argv[2], argv[3], argv[4], argv[5]); print_inv(tag, &r);
    } else {
        fprintf(stderr, "usage: see header\n"); return 1;
    }
    return 0;
}

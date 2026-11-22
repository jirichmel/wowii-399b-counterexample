/* ext1.c -- verify-order11, implementation 1 (written for this check; shares no code with ext2.c,
 * with the supplement, or with anything else).
 *
 * Reads graph6 lines on stdin; uses the lines with 10 vertices (in input order, index L = 0,1,...).
 * For each such H:
 *   - gamma_2(H) by a table over all 1024 vertex subsets S (incremental "at least one / at least two
 *     neighbours in S" masks), WP(compl H) by the counting form max{k : #{u : d(u) <= n-k} >= k}.
 *   - H is a parent iff gamma_2(H) >= WP(compl H).
 * For each parent and each nonempty N subset V(H) (mask 1..1023), G = H + v (v = vertex 10, N(v) = N):
 *   gamma_2(G) = min( 1 + min{|S| : S subset V(H), every u in V(H)-S has >=1 nbr in S, and those with
 *                                     exactly one are in N},          (D = S + v)
 *                     gamma_2(H)   if some minimum 2-dominating set of H meets N in >= 2 vertices,
 *                     gamma_2(H)+1 otherwise )                         (D subset V(H))
 *   computed for all N at once by a subset-min transform and a superset-OR transform.
 *   WP(compl G) by the counting form with n = 11.  If gamma_2(G) >= WP+1 ("hit"): A_3 and alpha(G[A_3]).
 * Output: parents file (argv[1]) with lines "L gamma2(H) WP(H) hash of its 1023 extensions", hits file (argv[2]) with
 *   "L N g2 wp alphaA3 A3empty viol g6", summary on stdout including a hash of (g2,wp) over all
 *   extensions in the order (L, N).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int pcnt(unsigned x) { return __builtin_popcount(x); }

/* own graph6 decoder for n <= 31: returns n, fills nb[] */
static int dec_g6(const char *s, unsigned *nb) {
    int n = s[0] - 63;
    if (n < 1 || n > 31) return -1;
    for (int i = 0; i < n; i++) nb[i] = 0;
    long nbits = (long)n * (n - 1) / 2;
    long need = (nbits + 5) / 6;
    if ((long)strlen(s) - 1 != need) return -1;
    long t = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++, t++) {
            int byte = s[1 + t / 6] - 63;
            if ((byte >> (5 - t % 6)) & 1) { nb[i] |= 1u << j; nb[j] |= 1u << i; }
        }
    return n;
}

static void enc_g6(int n, const unsigned *nb, char *out) {
    int p = 0; out[p++] = (char)(63 + n);
    int acc = 0, k = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            acc = 2 * acc + ((nb[i] >> j) & 1);
            k++;
            if (k == 6) { out[p++] = (char)(63 + acc); acc = 0; k = 0; }
        }
    if (k > 0) { while (k < 6) { acc *= 2; k++; } out[p++] = (char)(63 + acc); }
    out[p] = 0;
}

static int is_conn(int n, const unsigned *nb) {
    unsigned all = (1u << n) - 1, seen = 1, front = 1;
    while (front) {
        unsigned nf = 0;
        for (int u = 0; u < n; u++) if (front >> u & 1) nf |= nb[u];
        nf &= ~seen; seen |= nf; front = nf;
    }
    return seen == all;
}

/* WP(compl G) = max{k : at least k vertices have degree <= n-k} */
static int wp_count(int n, const int *deg) {
    int hist[40] = {0};
    for (int u = 0; u < n; u++) hist[deg[u]]++;
    int best = 0, cum = 0;
    /* cumulative count of vertices with degree <= t */
    int le[40]; for (int t = 0; t < 40; t++) { cum += (t < 40 ? hist[t] : 0); le[t] = cum; }
    for (int k = 1; k <= n; k++) if (le[n - k] >= k) best = k;
    return best;
}

static unsigned gadj[16];
static int alpha_rec(unsigned P) {
    if (!P) return 0;
    int v = __builtin_ctz(P);
    unsigned rest = P & ~(1u << v);
    int with = 1 + alpha_rec(rest & ~gadj[v]);
    if (!(gadj[v] & rest)) return with;  /* v isolated in P: take it */
    int without = alpha_rec(rest);
    return with > without ? with : without;
}

static unsigned one_[1024], two_[1024];
static unsigned char zok[1024], cmask_ok[1024];
static unsigned short cset[1024];
static unsigned char F[1024], hpair[1024];

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: ext1 parents.out hits.out < graphs.g6\n"); return 1; }
    FILE *fp = fopen(argv[1], "w"), *fh = fopen(argv[2], "w");
    if (!fp || !fh) { perror("open"); return 1; }
    char line[256];
    long L = -1, nparents = 0, next = 0, nhits = 0, nviol = 0, nplus2 = 0, ndisc = 0, nother = 0, nA3empty_hit = 0;
    long hist[12][12]; memset(hist, 0, sizeof hist);
    long ahist[12]; memset(ahist, 0, sizeof ahist);
    long phist[12][12]; memset(phist, 0, sizeof phist);
    uint64_t hash = 0;
    const unsigned ALL = 1023;
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n")] = 0;
        if (!line[0]) continue;
        unsigned nb[32];
        int n = dec_g6(line, nb);
        if (n != 10) { nother++; continue; }
        L++;
        if (!is_conn(10, nb)) { ndisc++; continue; }
        int degH[10];
        for (int u = 0; u < 10; u++) degH[u] = pcnt(nb[u]);
        one_[0] = two_[0] = 0;
        int g2H = 99;
        for (unsigned S = 1; S <= ALL; S++) {
            unsigned Sp = S & (S - 1); int d = __builtin_ctz(S);
            one_[S] = one_[Sp] | nb[d];
            two_[S] = two_[Sp] | (one_[Sp] & nb[d]);
        }
        for (unsigned S = 0; S <= ALL; S++) {
            unsigned out = ALL & ~S;
            unsigned zero = out & ~one_[S];
            unsigned c = out & one_[S] & ~two_[S];
            zok[S] = (zero == 0);
            cset[S] = (unsigned short)c;
            cmask_ok[S] = (zero == 0 && c == 0);
            if (cmask_ok[S] && pcnt(S) < g2H) g2H = pcnt(S);
        }
        int wpH = wp_count(10, degH);
        phist[g2H][wpH]++;
        if (g2H < wpH) continue;
        nparents++;
        /* F[N] = min |S| over S with zok and cset subset N */
        for (unsigned N = 0; N <= ALL; N++) F[N] = 99;
        for (unsigned S = 0; S <= ALL; S++) if (zok[S]) { int p = pcnt(S); if (p < F[cset[S]]) F[cset[S]] = (unsigned char)p; }
        for (int i = 0; i < 10; i++)
            for (unsigned N = 0; N <= ALL; N++) if (N >> i & 1) { unsigned m = N ^ (1u << i); if (F[m] < F[N]) F[N] = F[m]; }
        /* hpair[N] = 1 iff N contains a pair inside some minimum 2-dominating set of H */
        memset(hpair, 0, sizeof hpair);
        for (unsigned S = 0; S <= ALL; S++) if (cmask_ok[S] && pcnt(S) == g2H)
            for (int a = 0; a < 10; a++) if (S >> a & 1) for (int b = a + 1; b < 10; b++) if (S >> b & 1) hpair[(1u << a) | (1u << b)] = 1;
        for (int i = 0; i < 10; i++)
            for (unsigned N = 0; N <= ALL; N++) if (N >> i & 1) { if (hpair[N ^ (1u << i)]) hpair[N] = 1; }
        uint64_t ph = 0;
        for (unsigned N = 1; N <= ALL; N++) {
            next++;
            int a1 = F[N] + 1, a2 = hpair[N] ? g2H : g2H + 1;
            int g2 = a1 < a2 ? a1 : a2;
            int deg[11];
            for (int u = 0; u < 10; u++) deg[u] = degH[u] + (int)((N >> u) & 1);
            deg[10] = pcnt(N);
            int wp = wp_count(11, deg);
            hist[g2][wp]++;
            hash = hash * 1000003ULL + (uint64_t)(g2 * 16 + wp) + 1;
            ph = ph * 1000003ULL + (uint64_t)(g2 * 16 + wp) + 1;
            if (g2 >= wp + 2) nplus2++;
            if (g2 >= wp + 1) {
                nhits++;
                unsigned A3 = 0;
                for (int u = 0; u < 10; u++) gadj[u] = nb[u] | (((N >> u) & 1u) << 10);
                gadj[10] = N;
                for (int u = 0; u < 11; u++) if (deg[u] >= 3) A3 |= 1u << u;
                int al = A3 ? alpha_rec(A3) : 0;
                int viol = 0;
                if (A3) { if (g2 > wp + 3 / al) viol = 1; ahist[al]++; } else nA3empty_hit++;
                nviol += viol;
                char g6[64]; enc_g6(11, gadj, g6);
                fprintf(fh, "%ld %u %d %d %d %d %d %s\n", L, N, g2, wp, al, A3 == 0, viol, g6);
            }
        }
        fprintf(fp, "%ld %d %d %016llx\n", L, g2H, wpH, (unsigned long long)ph);
    }
    fclose(fp); fclose(fh);
    printf("ext1: graphs_on_10=%ld disconnected=%ld other_orders=%ld parents=%ld extensions=%ld hits(g2>=wp+1)=%ld g2>=wp+2=%ld violations=%ld A3empty_hits=%ld\n",
           L + 1, ndisc, nother, nparents, next, nhits, nplus2, nviol, nA3empty_hit);
    printf("ext1: hash=%016llx\n", (unsigned long long)hash);
    printf("ext1: alpha(G[A3]) over labelled hits:");
    for (int a = 1; a < 12; a++) if (ahist[a]) printf(" %d:%ld", a, ahist[a]);
    printf("\next1: (gamma2,WP) table over the 10-vertex graphs:");
    for (int g = 0; g < 12; g++) for (int w = 0; w < 12; w++) if (phist[g][w]) printf(" (%d,%d):%ld", g, w, phist[g][w]);
    printf("\next1: (gamma2,WP) table over all extensions:");
    for (int g = 0; g < 12; g++) for (int w = 0; w < 12; w++) if (hist[g][w]) printf(" (%d,%d):%ld", g, w, hist[g][w]);
    printf("\n");
    return 0;
}

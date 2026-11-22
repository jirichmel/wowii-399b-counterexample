/* ext2.c -- verify-order11, implementation 2.  Written separately from ext1.c; shares no code with it
 * or with any other program.  Different algorithms:
 *   gamma_2: for each graph separately, try candidate sets in order of increasing size (all
 *            combinations of the non-forced vertices, vertices of degree 1 always included), test
 *            each vertex outside the set by counting its neighbours in the set; the first size with a
 *            2-dominating set is gamma_2.
 *   WP(compl G): degrees sorted nondecreasingly, max{k : k + d_k <= n} (1-indexed), as in the paper.
 *   alpha(G[A_3]): all subsets of A_3, independence tested on the adjacency matrix.
 * Every extension G = H + v (v = vertex 10, N(v) = mask N, 1..1023) of every 10-vertex H with
 * gamma_2(H) >= WP(compl H) is built explicitly as an 11-vertex graph and evaluated from scratch.
 * Usage: ext2 LO HI parents.out hits.out < graphs.g6   (only 10-vertex lines with index in [LO,HI))
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct { int n; unsigned char m[12][12]; uint32_t row[12]; int d[12]; } Gr;

/* decode graph6: unpack 6-bit groups to a bit stream, then read the upper triangle column by column */
static int read6(const char *s, Gr *g) {
    size_t len = strlen(s);
    if (len < 1 || len > 60) return 0;
    int n = (unsigned char)s[0] - 63;
    if (n < 1 || n > 11) return 0;
    unsigned char bits[64 * 6];
    size_t nb = 0;
    for (size_t i = 1; i < len; i++) {
        int x = (unsigned char)s[i] - 63;
        if (x < 0 || x > 63) return 0;
        for (int b = 5; b >= 0; b--) bits[nb++] = (unsigned char)((x >> b) & 1);
    }
    size_t want = (size_t)n * (n - 1) / 2;
    if (nb < want || nb - want >= 6) return 0;
    memset(g, 0, sizeof *g);
    g->n = n;
    size_t k = 0;
    for (int c = 1; c < n; c++)
        for (int r = 0; r < c; r++) {
            if (bits[k++]) g->m[r][c] = g->m[c][r] = 1;
        }
    return n;
}

static void finish(Gr *g) {
    for (int i = 0; i < g->n; i++) {
        g->row[i] = 0; g->d[i] = 0;
        for (int j = 0; j < g->n; j++) if (g->m[i][j]) { g->row[i] |= (uint32_t)1 << j; g->d[i]++; }
    }
}

static void write6(const Gr *g, char *out) {
    unsigned char bits[64 * 6]; size_t k = 0;
    for (int c = 1; c < g->n; c++) for (int r = 0; r < c; r++) bits[k++] = g->m[r][c];
    while (k % 6) bits[k++] = 0;
    out[0] = (char)(g->n + 63);
    size_t p = 1;
    for (size_t i = 0; i < k; i += 6) {
        int x = 0;
        for (int b = 0; b < 6; b++) x = x * 2 + bits[i + b];
        out[p++] = (char)(x + 63);
    }
    out[p] = 0;
}

static int connected(const Gr *g) {
    int stack[12], sp = 0, seen[12] = {0}, cnt = 1;
    seen[0] = 1; stack[sp++] = 0;
    while (sp) {
        int u = stack[--sp];
        for (int w = 0; w < g->n; w++) if (g->m[u][w] && !seen[w]) { seen[w] = 1; cnt++; stack[sp++] = w; }
    }
    return cnt == g->n;
}

static int is2dom(const Gr *g, uint32_t D) {
    for (int u = 0; u < g->n; u++) {
        if (D >> u & 1) continue;
        if (__builtin_popcount(g->row[u] & D) < 2) return 0;
    }
    return 1;
}

/* gamma_2 by increasing size; forced = vertices of degree <= 1 */
static int gamma2(const Gr *g) {
    uint32_t forced = 0; int free_[12], nf = 0;
    for (int u = 0; u < g->n; u++) { if (g->d[u] <= 1) forced |= (uint32_t)1 << u; else free_[nf++] = u; }
    int base = __builtin_popcount(forced);
    for (int t = 0; t <= nf; t++) {
        /* all t-combinations of free_ by index array */
        int idx[12];
        for (int i = 0; i < t; i++) idx[i] = i;
        for (;;) {
            uint32_t D = forced;
            for (int i = 0; i < t; i++) D |= (uint32_t)1 << free_[idx[i]];
            if (is2dom(g, D)) return base + t;
            int i = t - 1;
            while (i >= 0 && idx[i] == nf - t + i) i--;
            if (i < 0) break;
            idx[i]++;
            for (int j = i + 1; j < t; j++) idx[j] = idx[j - 1] + 1;
        }
    }
    return -1; /* unreachable: V is 2-dominating */
}

static int wp_sorted(const Gr *g) {
    int a[12], n = g->n;
    for (int i = 0; i < n; i++) a[i] = g->d[i];
    for (int i = 0; i < n; i++) for (int j = 0; j + 1 < n - i; j++) if (a[j] > a[j + 1]) { int t = a[j]; a[j] = a[j + 1]; a[j + 1] = t; }
    int best = 0;
    for (int k = 1; k <= n; k++) if (k + a[k - 1] <= n) best = k;
    return best;
}

static int alphaA3(const Gr *g, uint32_t A3) {
    int best = 0;
    for (uint32_t T = A3;; T = (T - 1) & A3) {
        int sz = __builtin_popcount(T);
        if (sz > best) {
            int ok = 1;
            for (int u = 0; u < g->n && ok; u++) if (T >> u & 1) for (int w = u + 1; w < g->n; w++) if ((T >> w & 1) && g->m[u][w]) { ok = 0; break; }
            if (ok) best = sz;
        }
        if (T == 0) break;
    }
    return best;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: ext2 LO HI parents.out hits.out < g6\n"); return 1; }
    long lo = atol(argv[1]), hi = atol(argv[2]);
    FILE *fp = fopen(argv[3], "w"), *fh = fopen(argv[4], "w");
    if (!fp || !fh) { perror("open"); return 1; }
    char buf[512];
    long idx = -1, npar = 0, next = 0, nhit = 0, nviol = 0, n2 = 0, ndisc = 0, nA3e = 0;
    long tab[13][13] = {{0}}, ptab[13][13] = {{0}}, ah[13] = {0};
    while (fgets(buf, sizeof buf, stdin)) {
        size_t l = strlen(buf);
        while (l && (buf[l - 1] == '\n' || buf[l - 1] == '\r')) buf[--l] = 0;
        if (!l) continue;
        Gr H;
        if (read6(buf, &H) != 10) continue;
        idx++;
        if (idx < lo || idx >= hi) continue;
        finish(&H);
        if (!connected(&H)) { ndisc++; continue; }
        int gh = gamma2(&H), wh = wp_sorted(&H);
        ptab[gh][wh]++;
        if (gh < wh) continue;
        npar++;
        uint64_t ph = 0;
        for (int N = 1; N < 1024; N++) {
            Gr G;
            memset(&G, 0, sizeof G);
            G.n = 11;
            for (int i = 0; i < 10; i++) for (int j = 0; j < 10; j++) G.m[i][j] = H.m[i][j];
            for (int i = 0; i < 10; i++) if (N & (1 << i)) G.m[i][10] = G.m[10][i] = 1;
            finish(&G);
            next++;
            int g2 = gamma2(&G), wp = wp_sorted(&G);
            tab[g2][wp]++;
            ph = ph * 1000003ULL + (uint64_t)(g2 * 16 + wp) + 1;
            if (g2 > wp + 1) n2++;
            if (g2 > wp) {
                nhit++;
                uint32_t A3 = 0;
                for (int u = 0; u < 11; u++) if (G.d[u] >= 3) A3 |= (uint32_t)1 << u;
                int al = A3 ? alphaA3(&G, A3) : 0;
                int viol = 0;
                if (A3) { ah[al]++; viol = (g2 > wp + 3 / al); } else nA3e++;
                nviol += viol;
                char s[64]; write6(&G, s);
                fprintf(fh, "%ld %d %d %d %d %d %d %s\n", idx, N, g2, wp, al, A3 ? 0 : 1, viol, s);
            }
        }
        fprintf(fp, "%ld %d %d %016llx\n", idx, gh, wh, (unsigned long long)ph);
    }
    fclose(fp); fclose(fh);
    printf("ext2 [%ld,%ld): graphs_on_10_seen=%ld disconnected=%ld parents=%ld extensions=%ld hits=%ld g2>wp+1=%ld violations=%ld A3empty_hits=%ld\n",
           lo, hi, idx + 1, ndisc, npar, next, nhit, n2, nviol, nA3e);
    printf("ext2: alpha(G[A3]) over labelled hits:");
    for (int a = 1; a < 13; a++) if (ah[a]) printf(" %d:%ld", a, ah[a]);
    printf("\next2: (gamma2,WP) table over the 10-vertex graphs:");
    for (int a = 0; a < 13; a++) for (int b = 0; b < 13; b++) if (ptab[a][b]) printf(" (%d,%d):%ld", a, b, ptab[a][b]);
    printf("\next2: (gamma2,WP) table over all extensions:");
    for (int a = 0; a < 13; a++) for (int b = 0; b < 13; b++) if (tab[a][b]) printf(" (%d,%d):%ld", a, b, tab[a][b]);
    printf("\n");
    return 0;
}

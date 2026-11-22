/* canon.c -- verify-order11: canonical graph6 form for graphs with n <= 11 vertices.
 * Written for this check; shares no code with the generators or with ext1/ext2.
 * Method: colour refinement (new colour = rank of (old colour, counts of neighbours in each colour)),
 * individualisation of each vertex of the first non-singleton colour class, recursion; at each
 * discrete colouring the upper-triangle adjacency code in colour order; the canonical form is the
 * largest code.  Pruning only by twins: a vertex of the target class is skipped when it has the same
 * neighbourhood (apart from each other) as a vertex already tried, since swapping two such vertices
 * is an automorphism fixing the current colouring.
 * Usage: canon < in.g6 > out.txt     each output line: "canonical_g6 input_g6"
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int N;
static uint32_t A[16];
static uint64_t best; static int have;

static int rd(const char *s) {
    int n = s[0] - 63;
    if (n < 1 || n > 11) return -1;
    if ((int)strlen(s) != 1 + (n * (n - 1) / 2 + 5) / 6) return -1;
    memset(A, 0, sizeof A);
    int pos = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        int c = s[1 + pos / 6] - 63;
        if (c >> (5 - pos % 6) & 1) { A[i] |= 1u << j; A[j] |= 1u << i; }
        pos++;
    }
    return n;
}

/* refine colour vector in place to a stable one; colours are 0..k-1; returns k */
static int refine(int *col) {
    int k = 0;
    for (int v = 0; v < N; v++) if (col[v] >= k) k = col[v] + 1;
    for (;;) {
        int key[16][17];
        for (int v = 0; v < N; v++) {
            memset(key[v], 0, sizeof key[v]);
            key[v][0] = col[v];
            for (int u = 0; u < N; u++) if (A[v] >> u & 1) key[v][1 + col[u]]++;
        }
        int ord[16];
        for (int v = 0; v < N; v++) ord[v] = v;
        /* insertion sort by key */
        for (int i = 1; i < N; i++) {
            int x = ord[i], j = i - 1;
            while (j >= 0 && memcmp(key[ord[j]], key[x], sizeof(int) * (1 + k)) > 0) { ord[j + 1] = ord[j]; j--; }
            ord[j + 1] = x;
        }
        int nc[16], c = 0;
        for (int i = 0; i < N; i++) {
            if (i && memcmp(key[ord[i - 1]], key[ord[i]], sizeof(int) * (1 + k))) c++;
            nc[ord[i]] = c;
        }
        int k2 = c + 1;
        memcpy(col, nc, sizeof nc);
        if (k2 == k) return k;
        k = k2;
    }
}

static uint64_t code(const int *col) {
    int at[16];
    for (int v = 0; v < N; v++) at[col[v]] = v;
    uint64_t c = 0;
    for (int j = 1; j < N; j++) for (int i = 0; i < j; i++) c = (c << 1) | (A[at[i]] >> at[j] & 1);
    return c;
}

static void search(const int *col0) {
    int col[16];
    memcpy(col, col0, sizeof col);
    int k = refine(col);
    if (k == N) { uint64_t c = code(col); if (!have || c > best) { best = c; have = 1; } return; }
    int cnt[16] = {0};
    for (int v = 0; v < N; v++) cnt[col[v]]++;
    int t = 0;
    while (cnt[t] < 2) t++;
    uint32_t done = 0;
    for (int v = 0; v < N; v++) {
        if (col[v] != t) continue;
        int skip = 0;
        for (int u = 0; u < N && !skip; u++)
            if ((done >> u & 1) && ((A[u] & ~(1u << v)) == (A[v] & ~(1u << u)))) skip = 1;
        if (skip) continue;
        done |= 1u << v;
        int c2[16];
        for (int u = 0; u < N; u++) c2[u] = col[u] < t ? col[u] : (u == v ? t : col[u] + 1);
        search(c2);
    }
}

int main(void) {
    char s[128];
    while (fgets(s, sizeof s, stdin)) {
        s[strcspn(s, "\r\n ")] = 0;
        if (!s[0]) continue;
        int n = rd(s);
        if (n < 0) { printf("BAD %s\n", s); continue; }
        N = n;
        int col[16] = {0};
        have = 0; best = 0;
        search(col);
        /* write canonical graph6 from the code (bits in upper-triangle column order) */
        int m = n * (n - 1) / 2;
        char out[32]; int p = 0; out[p++] = (char)(63 + n);
        for (int b = 0; b < m; b += 6) {
            int x = 0;
            for (int q = 0; q < 6; q++) { int bit = (b + q < m) ? (int)(best >> (m - 1 - (b + q)) & 1) : 0; x = 2 * x + bit; }
            out[p++] = (char)(63 + x);
        }
        out[p] = 0;
        printf("%s %s\n", out, s);
    }
    return 0;
}

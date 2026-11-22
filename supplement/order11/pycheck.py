"""pycheck.py -- verify-order11, implementation 3 (Python standard library only; own code, shares
nothing with ext1.c, ext2.c or canon.c).

Brute force from the definitions:
  gamma_2: smallest k such that some k-set D has every outside vertex with >= 2 neighbours in D
           (itertools.combinations, Python sets);
  WP(compl G): degrees sorted nondecreasingly, max{k : k + d_k <= n};
  alpha(G[A_3]): largest independent subset of A_3 by trying sizes downward.

Usage:
  python3 -I pycheck.py hits   A10.g6 HITS                 -> recompute every hit line
  python3 -I pycheck.py sample A10.g6 PARENTS K SEED       -> all 1023 extensions of K random parents,
                                                              compare per-parent hash and hit status
  python3 -I pycheck.py iso    HITS CANON                  -> isomorphism classes of the hit graphs by
                                                              invariant buckets + backtracking isomorphism
                                                              test; compare with canon.c's partition
"""
import sys, random, itertools

def dec6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        x = ord(ch) - 63
        for b in range(5, -1, -1):
            bits.append((x >> b) & 1)
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j); adj[j].add(i)
            k += 1
    return adj

def gamma2(adj):
    n = len(adj)
    V = range(n)
    for k in range(n + 1):
        for D in itertools.combinations(V, k):
            Ds = set(D)
            if all(len(adj[u] & Ds) >= 2 for u in V if u not in Ds):
                return k
    raise RuntimeError

def wp(adj):
    n = len(adj)
    d = sorted(len(a) for a in adj)
    return max(k for k in range(1, n + 1) if k + d[k - 1] <= n)

def alpha_of(adj, S):
    S = sorted(S)
    for k in range(len(S), 0, -1):
        for I in itertools.combinations(S, k):
            if all(I[b] not in adj[I[a]] for a in range(k) for b in range(a + 1, k)):
                return k
    return 0

def extend(H, N):
    G = [set(a) for a in H] + [set()]
    for u in range(10):
        if (N >> u) & 1:
            G[u].add(10); G[10].add(u)
    return G

def load_parents_g6(path, wanted):
    out = {}
    with open(path) as f:
        L = -1
        for line in f:
            s = line.strip()
            if not s or ord(s[0]) - 63 != 10:
                continue
            L += 1
            if L in wanted:
                out[L] = s
    return out

M64 = (1 << 64) - 1

def cmd_hits(a10, hitsfile):
    rows = [l.split() for l in open(hitsfile)]
    wanted = set(int(r[0]) for r in rows)
    P = load_parents_g6(a10, wanted)
    bad = 0; hist = {}
    for r in rows:
        L, N = int(r[0]), int(r[1])
        G = extend(dec6(P[L]), N)
        g2, w = gamma2(G), wp(G)
        A3 = [u for u in range(11) if len(G[u]) >= 3]
        al = alpha_of(G, A3) if A3 else 0
        viol = int(bool(A3) and g2 > w + 3 // al)
        if (g2, w, al, int(not A3), viol) != tuple(int(x) for x in r[2:7]) or not (g2 >= w + 1):
            bad += 1
            print("MISMATCH", r, g2, w, al)
        # the graph6 string in the hit line must encode the same graph
        if [sorted(a) for a in dec6(r[7])] != [sorted(a) for a in G]:
            bad += 1
            print("G6 MISMATCH", r)
        hist[al] = hist.get(al, 0) + 1
    print("pycheck hits: lines=%d mismatches=%d alpha_hist=%s" % (len(rows), bad, sorted(hist.items())))

def cmd_sample(a10, parents, K, seed):
    prow = [l.split() for l in open(parents)]
    random.seed(seed)
    pick = random.sample(range(len(prow)), K)
    wanted = set(int(prow[i][0]) for i in pick)
    P = load_parents_g6(a10, wanted)
    bad = 0; nex = 0; nhit = 0
    for i in pick:
        L, g2H, wpH, hsh = int(prow[i][0]), int(prow[i][1]), int(prow[i][2]), int(prow[i][3], 16)
        H = dec6(P[L])
        if (gamma2(H), wp(H)) != (g2H, wpH):
            bad += 1; print("PARENT MISMATCH", prow[i])
        h = 0
        for N in range(1, 1024):
            G = extend(H, N)
            g2, w = gamma2(G), wp(G)
            nex += 1
            if g2 >= w + 1:
                nhit += 1
            h = (h * 1000003 + g2 * 16 + w + 1) & M64
        if h != hsh:
            bad += 1; print("HASH MISMATCH", prow[i], "%016x" % h)
    print("pycheck sample: parents=%d extensions=%d hits=%d mismatches=%d seed=%d" % (K, nex, nhit, bad, seed))

def invariant(adj):
    n = len(adj)
    deg = [len(a) for a in adj]
    tri = [sum(1 for a in adj[v] for b in adj[v] if a < b and b in adj[a]) for v in range(n)]
    loc = sorted((deg[v], tri[v], tuple(sorted(deg[u] for u in adj[v]))) for v in range(n))
    return tuple(loc)

def isomorphic(A, B):
    n = len(A)
    if n != len(B):
        return False
    sig = lambda adj, v: (len(adj[v]), tuple(sorted(len(adj[u]) for u in adj[v])))
    sa = [sig(A, v) for v in range(n)]
    sb = [sig(B, v) for v in range(n)]
    if sorted(sa) != sorted(sb):
        return False
    order = sorted(range(n), key=lambda v: (-len(A[v]),))
    m = {}; used = set()
    def bt(i):
        if i == n:
            return True
        v = order[i]
        for w in range(n):
            if w in used or sb[w] != sa[v]:
                continue
            ok = True
            for u, x in m.items():
                if (u in A[v]) != (x in B[w]):
                    ok = False; break
            if ok:
                m[v] = w; used.add(w)
                if bt(i + 1):
                    return True
                del m[v]; used.discard(w)
        return False
    return bt(0)

def cmd_iso(hitsfile, canonfile):
    g6s = [l.split()[7] for l in open(hitsfile)]
    can = [l.split()[0] for l in open(canonfile)]
    assert len(can) == len(g6s)
    buckets = {}
    cls = [None] * len(g6s)
    reps = []
    for idx, s in enumerate(g6s):
        G = dec6(s)
        key = invariant(G)
        lst = buckets.setdefault(key, [])
        for c in lst:
            if isomorphic(G, reps[c]):
                cls[idx] = c; break
        else:
            reps.append(G); c = len(reps) - 1; lst.append(c); cls[idx] = c
    # compare partitions
    m1 = {}; m2 = {}; bad = 0
    for idx in range(len(g6s)):
        a, b = cls[idx], can[idx]
        if m1.setdefault(a, b) != b or m2.setdefault(b, a) != a:
            bad += 1
    print("pycheck iso: hit lines=%d python classes=%d canon classes=%d partition mismatches=%d"
          % (len(g6s), len(reps), len(set(can)), bad))

if __name__ == "__main__":
    c = sys.argv[1]
    if c == "hits":
        cmd_hits(sys.argv[2], sys.argv[3])
    elif c == "sample":
        cmd_sample(sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]))
    elif c == "iso":
        cmd_iso(sys.argv[2], sys.argv[3])

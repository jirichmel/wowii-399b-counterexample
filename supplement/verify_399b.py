"""Self-contained check of the counterexamples F_q to Conjecture 399b of Written on the Wall II.

Conjecture 399b: for every connected graph G on n > 2 vertices,
    gamma_2(G) <= WP(complement of G) + floor(3 / alpha(G[A_3])),
where gamma_2 is the 2-domination number, A_3 the set of vertices of degree >= 3, and WP(complement of G) the
largest k with k + d_k <= n, d_1 <= ... <= d_n being the degrees of G (catalogue definition 113).

F_q (q >= 3): X = {x1, x2, x3} independent, leaf l_i at x_i; a clique K on q vertices joined completely to X;
w adjacent to all of K; y1, y2 adjacent to all of X.  n = q + 9.

Everything is computed by brute force, from the definitions only; Python standard library only.
Also: the graph6 string of F_3 printed in the paper is decoded and shown isomorphic to F_3.
Usage: python3 verify_399b.py [QMAX]      (default QMAX = 10)
"""
import itertools
import sys


def build(q):
    names = ['x1', 'x2', 'x3', 'l1', 'l2', 'l3', 'w', 'y1', 'y2'] + ['k%d' % i for i in range(1, q + 1)]
    idx = {v: i for i, v in enumerate(names)}
    E = set()
    def add(a, b):
        E.add(frozenset((idx[a], idx[b])))
    X = ['x1', 'x2', 'x3']
    K = ['k%d' % i for i in range(1, q + 1)]
    for i in range(3):
        add(X[i], 'l%d' % (i + 1))
    for a, b in itertools.combinations(K, 2):
        add(a, b)
    for x in X:
        for k in K:
            add(x, k)
        for y in ('y1', 'y2'):
            add(x, y)
    for k in K:
        add('w', k)
    n = len(names)
    adj = [0] * n
    for e in E:
        a, b = tuple(e)
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    return names, adj


def connected(adj):
    n = len(adj)
    seen, todo = 1, [0]
    while todo:
        v = todo.pop()
        nb = adj[v] & ~seen
        seen |= nb
        todo.extend(i for i in range(n) if nb >> i & 1)
    return seen == (1 << n) - 1


def wp_complement(adj):
    n = len(adj)
    d = sorted(bin(a).count('1') for a in adj)          # d_1 <= ... <= d_n
    ks = [k for k in range(1, n + 1) if k + d[k - 1] <= n]
    wp = max(ks)
    # the Welsh-Powell bound of the complement: max_i min(i, n - d_i); must coincide
    wp2 = max(min(i, n - d[i - 1]) for i in range(1, n + 1))
    assert wp == wp2, (wp, wp2)
    return wp


def wp_complement_other_reading(adj):
    """Same formula with the degrees of the complement (a reading the catalogue does not intend)."""
    n = len(adj)
    d = sorted(n - 1 - bin(a).count('1') for a in adj)
    return max(k for k in range(1, n + 1) if k + d[k - 1] <= n)


def alpha_of(adj, verts):
    best = 0
    verts = list(verts)
    for r in range(len(verts), 0, -1):
        for S in itertools.combinations(verts, r):
            m = 0
            for v in S:
                m |= 1 << v
            if all(not (adj[v] & m) for v in S):
                return r
    return best


def is_2dominating(adj, m):
    n = len(adj)
    for v in range(n):
        if not (m >> v & 1) and bin(adj[v] & m).count('1') < 2:
            return False
    return True


def gamma2(adj):
    n = len(adj)
    for r in range(1, n + 1):
        for S in itertools.combinations(range(n), r):
            m = 0
            for v in S:
                m |= 1 << v
            if is_2dominating(adj, m):
                return r, S
    raise AssertionError


def alpha2(adj):
    """Largest set inducing maximum degree <= 1 (the 2-independence number)."""
    n = len(adj)
    best = 0
    for m in range(1 << n):
        c = bin(m).count('1')
        if c <= best:
            continue
        if all(bin(adj[v] & m).count('1') <= 1 for v in range(n) if m >> v & 1):
            best = c
    return best


def from_graph6(s):
    data = [ord(c) - 63 for c in s]
    n = data[0]
    bits = []
    for x in data[1:]:
        bits.extend((x >> (5 - i)) & 1 for i in range(6))
    adj = [0] * n
    p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            p += 1
    return adj


def isomorphic(a, b):
    n = len(a)
    if n != len(b):
        return False
    deg = lambda adj, v: bin(adj[v]).count('1')
    if sorted(deg(a, v) for v in range(n)) != sorted(deg(b, v) for v in range(n)):
        return False
    order = sorted(range(n), key=lambda v: -deg(a, v))
    mp = {}
    used = 0
    def rec(i):
        nonlocal used
        if i == n:
            return True
        v = order[i]
        for u in range(n):
            if used >> u & 1 or deg(b, u) != deg(a, v):
                continue
            if all(((a[v] >> w) & 1) == ((b[u] >> mp[w]) & 1) for w in mp):
                mp[v] = u
                used |= 1 << u
                if rec(i + 1):
                    return True
                del mp[v]
                used &= ~(1 << u)
        return False
    return rec(0)


def main():
    qmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    print('q  n   connected  WP  WP(other reading)  |A_3|  alpha(G[A_3])  gamma_2  alpha_2  bound  violated')
    for q in range(3, qmax + 1):
        names, adj = build(q)
        n = len(adj)
        A3 = [v for v in range(n) if bin(adj[v]).count('1') >= 3]
        wp = wp_complement(adj)
        wpo = wp_complement_other_reading(adj)
        a3 = alpha_of(adj, A3)
        g2, S = gamma2(adj)
        a2 = alpha2(adj)
        bound = wp + 3 // a3
        print('%-2d %-3d %-10s %-3d %-18d %-6d %-14d %-8d %-8s %-6d %s' % (
            q, n, connected(adj), wp, wpo, len(A3), a3, g2, a2, bound, g2 > bound))
        if q == 3:
            print('   a minimum 2-dominating set of F_3:', sorted(names[v] for v in S))
    g6 = 'KCOfFFb?~?[?'
    _, f3 = build(3)
    print('graph6 %s decodes to a graph isomorphic to F_3: %s' % (g6, isomorphic(from_graph6(g6), f3)))


if __name__ == '__main__':
    main()

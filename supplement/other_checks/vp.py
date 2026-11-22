#!/usr/bin/env python3
"""vp.py -- implementation P of the verify-math checks (plain Python, itertools, sets).
Written from the definitions; shares no code with vc.c.
Generation: graphs on n vertices up to isomorphism by EDGE addition (level m -> m+1),
deduplicated by a canonical form from individualization-refinement (colour refinement,
branch on first non-singleton cell, take the least certificate over all leaves).
Usage:
  python3 vp.py enum N              statistics for connected graphs on N vertices
  python3 vp.py g6 S1 S2 ...        invariants of given graph6 strings
  python3 vp.py canon S1 S2 ...     canonical certificates (equal <=> isomorphic)
  python3 vp.py f3del               F_3 minus a vertex or an edge
  python3 vp.py fq Q                F_Q and the M6 variants
"""
import sys
from itertools import combinations


# ---------------- graph6 ----------------
def from_g6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        val = ord(ch) - 63
        for b in range(5, -1, -1):
            bits.append((val >> b) & 1)
    adj = {v: set() for v in range(n)}
    t = 0
    for j in range(1, n):
        for i in range(j):
            if bits[t]:
                adj[i].add(j)
                adj[j].add(i)
            t += 1
    return n, adj


def to_g6(n, adj):
    bits = [1 if j in adj[i] else 0 for j in range(1, n) for i in range(j)]
    while len(bits) % 6:
        bits.append(0)
    out = chr(n + 63)
    for p in range(0, len(bits), 6):
        out += chr(63 + int("".join(map(str, bits[p:p + 6])), 2))
    return out


# ---------------- invariants ----------------
def is_connected(n, adj):
    seen = {0}
    stack = [0]
    while stack:
        v = stack.pop()
        for u in adj[v]:
            if u not in seen:
                seen.add(u)
                stack.append(u)
    return len(seen) == n


def dominates2(n, adj, D, exact=False):
    for v in range(n):
        if v in D:
            continue
        c = len(adj[v] & D)
        if (c != 2) if exact else (c < 2):
            return False
    return True


def gamma2(n, adj, exact=False):
    for size in range(0, n + 1):
        for D in combinations(range(n), size):
            if dominates2(n, adj, set(D), exact):
                return size, D
    return None


def alpha_of(adj, verts):
    verts = list(verts)
    for size in range(len(verts), 0, -1):
        for S in combinations(verts, size):
            Sset = set(S)
            if all(not (adj[v] & Sset) for v in S):
                return size
    return 0


def alpha2(n, adj):
    for size in range(n, 0, -1):
        for S in combinations(range(n), size):
            Sset = set(S)
            if all(len(adj[v] & Sset) <= 1 for v in S):
                return size
    return 0


def wp_formula(n, degs):
    d = sorted(degs)
    return max(k for k in range(1, n + 1) if k + d[k - 1] <= n)


def wp_coloring_form(n, degs):
    # Welsh-Powell of the complement: max_i min(i, delta_i + 1), delta nonincreasing degrees of complement
    delta = sorted((n - 1 - x for x in degs), reverse=True)
    return max(min(i, delta[i - 1] + 1) for i in range(1, n + 1))


def invariants(n, adj):
    degs = [len(adj[v]) for v in range(n)]
    A3 = [v for v in range(n) if degs[v] >= 3]
    g2 = gamma2(n, adj)[0]
    wp = wp_formula(n, degs)
    assert wp == wp_coloring_form(n, degs)
    wpo = wp_formula(n, [n - 1 - x for x in degs])
    al = alpha_of(adj, A3) if A3 else 0
    return dict(n=n, m=sum(degs) // 2, conn=is_connected(n, adj), gamma2=g2, WP=wp,
                WPother=wpo, A3=len(A3), alphaA3=al)


# ---------------- canonical form ----------------
def refine(n, adj, cells):
    # cells: list of lists (ordered partition). Returns equitable refinement, invariantly ordered.
    while True:
        cell_of = {}
        for idx, c in enumerate(cells):
            for v in c:
                cell_of[v] = idx
        sig = {}
        for v in range(n):
            cnt = [0] * len(cells)
            for u in adj[v]:
                cnt[cell_of[u]] += 1
            sig[v] = (cell_of[v], tuple(cnt))
        keys = sorted(set(sig.values()))
        new = [[] for _ in keys]
        pos = {k: i for i, k in enumerate(keys)}
        for v in range(n):
            new[pos[sig[v]]].append(v)
        if len(new) == len(cells):
            return new
        cells = new


def canon(n, adj):
    best = [None]

    def search(cells):
        cells = refine(n, adj, cells)
        if len(cells) == n:
            order = [c[0] for c in cells]
            place = {v: i for i, v in enumerate(order)}
            cert = tuple(sorted((min(place[a], place[b]), max(place[a], place[b]))
                                for a in range(n) for b in adj[a] if a < b))
            if best[0] is None or cert < best[0]:
                best[0] = cert
            return
        k = next(i for i, c in enumerate(cells) if len(c) > 1)
        for v in cells[k]:
            rest = [u for u in cells[k] if u != v]
            search(cells[:k] + [[v], rest] + cells[k + 1:])

    search([list(range(n))])
    return (n, best[0])


def adj_from_edges(n, edges):
    adj = {v: set() for v in range(n)}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    return adj


def all_graphs(n):
    level = {canon(n, adj_from_edges(n, [])): ()}
    out = list(level.values())
    allpairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for m in range(1, len(allpairs) + 1):
        nxt = {}
        for edges in level.values():
            es = set(edges)
            for p in allpairs:
                if p in es:
                    continue
                ne = tuple(sorted(es | {p}))
                c = canon(n, adj_from_edges(n, ne))
                if c not in nxt:
                    nxt[c] = c[1]  # store canonical edge list
        level = nxt
        out.extend(level.values())
    return out


def enum(n):
    graphs = all_graphs(n)
    conn = 0
    tight = {}
    a3empty = 0
    viol_cat = viol_oth = bad = 0
    tight_list = {}
    oth_list = []
    for edges in graphs:
        adj = adj_from_edges(n, edges)
        if not is_connected(n, adj):
            continue
        conn += 1
        I = invariants(n, adj)
        if I['gamma2'] > I['WP'] + 1:
            bad += 1
        if I['A3'] == 0:
            a3empty += 1
        if I['gamma2'] == I['WP'] + 1:
            tight[I['alphaA3']] = tight.get(I['alphaA3'], 0) + 1
            tight_list.setdefault(I['alphaA3'], []).append(to_g6(n, adj))
        if I['A3']:
            if I['gamma2'] > I['WP'] + 3 // I['alphaA3']:
                viol_cat += 1
            if I['gamma2'] > I['WPother'] + 3 // I['alphaA3']:
                viol_oth += 1
                oth_list.append((to_g6(n, adj), I['gamma2'], I['WPother'], I['alphaA3']))
    mx = max(tight) if tight else None
    print(f"n={n} graphs={len(graphs)} connected={conn} A3empty={a3empty} gamma2>WP+1:{bad} "
          f"viol_cat={viol_cat} viol_other={viol_oth}")
    print(f"n={n} tight by alphaA3: {dict(sorted(tight.items()))} max={mx}")
    for s in tight_list.get(mx, []):
        print(f"  TIGHTMAX n={n} {s}")
    for t in oth_list:
        print(f"  VIOLOTHER n={n} {t[0]} gamma2={t[1]} WPother={t[2]} alphaA3={t[3]}")


# ---------------- F_q ----------------
def build_F(q):
    names = (['x1', 'x2', 'x3', 'l1', 'l2', 'l3'] + [f'k{j}' for j in range(1, q + 1)]
             + ['w', 'y1', 'y2'])
    ix = {s: i for i, s in enumerate(names)}
    E = set()
    for i in (1, 2, 3):
        E.add((f'x{i}', f'l{i}'))
    for a in range(1, q + 1):
        for b in range(a + 1, q + 1):
            E.add((f'k{a}', f'k{b}'))
    for i in (1, 2, 3):
        for j in range(1, q + 1):
            E.add((f'x{i}', f'k{j}'))
    for j in range(1, q + 1):
        E.add(('w', f'k{j}'))
    for a in (1, 2):
        for i in (1, 2, 3):
            E.add((f'y{a}', f'x{i}'))
    n = len(names)
    return n, adj_from_edges(n, [(ix[a], ix[b]) for a, b in E]), names


def violates(I, wpkey):
    return I['A3'] > 0 and I['gamma2'] > I[wpkey] + 3 // I['alphaA3']


def f3del():
    n, adj, names = build_F(3)
    print("F3", to_g6(n, adj), invariants(n, adj))
    tot = conn = vc = vo = 0
    for v in range(n):
        keep = [u for u in range(n) if u != v]
        re = {u: i for i, u in enumerate(keep)}
        h = {re[u]: {re[w] for w in adj[u] if w != v} for u in keep}
        tot += 1
        c = is_connected(n - 1, h)
        I = invariants(n - 1, h) if c else None
        if c:
            conn += 1
            vc += violates(I, 'WP')
            vo += violates(I, 'WPother')
        print(f"F3-{names[v]}", to_g6(n - 1, h), I if c else "disconnected")
    for a in range(n):
        for b in sorted(adj[a]):
            if a < b:
                h = {u: set(adj[u]) for u in range(n)}
                h[a].discard(b)
                h[b].discard(a)
                tot += 1
                c = is_connected(n, h)
                I = invariants(n, h) if c else None
                if c:
                    conn += 1
                    vc += violates(I, 'WP')
                    vo += violates(I, 'WPother')
                print(f"F3-{names[a]}{names[b]}", I if c else "disconnected")
    print(f"SUMMARY total={tot} connected={conn} viol_cat={vc} viol_other={vo}")


def fq(q):
    n, adj, names = build_F(q)
    I = invariants(n, adj)
    print(f"F{q}", I)
    degs = [len(adj[v]) for v in range(n)]
    Ale3 = [v for v in range(n) if degs[v] <= 3]
    a = alpha_of(adj, Ale3)
    rhs_a = I['WP'] + 3 // a
    print(f"F{q} (a) deg<=3 vertices={[names[v] for v in Ale3]} alpha={a} rhs={rhs_a} "
          f"gamma2={I['gamma2']} violates={I['gamma2'] > rhs_a}")
    size, D = gamma2(n, adj, exact=True)
    rhs_b = I['WP'] + 3 // I['alphaA3']
    print(f"F{q} (b) exact-2-dom number={size} example={[names[v] for v in D]} rhs={rhs_b} "
          f"violates={size > rhs_b}")


def main():
    mode = sys.argv[1]
    if mode == 'enum':
        enum(int(sys.argv[2]))
    elif mode == 'g6':
        for s in sys.argv[2:]:
            n, adj = from_g6(s)
            I = invariants(n, adj)
            I['alpha2'] = alpha2(n, adj)
            print(s, I)
    elif mode == 'canon':
        for s in sys.argv[2:]:
            n, adj = from_g6(s)
            print(s, hash(canon(n, adj)), canon(n, adj))
    elif mode == 'canonF':
        q = int(sys.argv[2])
        n, adj, _ = build_F(q)
        c = canon(n, adj)
        for s in sys.argv[3:]:
            n2, adj2 = from_g6(s)
            print(f"F{q} ~ {s}:", canon(n2, adj2) == c)
    elif mode == 'f3del':
        f3del()
    elif mode == 'fq':
        fq(int(sys.argv[2]))


if __name__ == '__main__':
    main()

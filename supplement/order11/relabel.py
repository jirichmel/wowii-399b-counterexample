# relabel.py: random relabelling of graph6 lines (n <= 62), for testing canon. Own code.
import sys, random
def dec(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        x = ord(ch) - 63
        bits += [(x >> (5 - b)) & 1 for b in range(6)]
    E = set(); k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]: E.add((i, j))
            k += 1
    return n, E
def enc(n, E):
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if (i, j) in E or (j, i) in E else 0)
    while len(bits) % 6: bits.append(0)
    out = chr(n + 63)
    for i in range(0, len(bits), 6):
        x = 0
        for b in bits[i:i+6]: x = 2 * x + b
        out += chr(x + 63)
    return out
random.seed(int(sys.argv[1]))
for line in sys.stdin:
    s = line.split()[0] if line.split() else ''
    if not s: continue
    n, E = dec(s)
    p = list(range(n)); random.shuffle(p)
    F = set((min(p[a], p[b]), max(p[a], p[b])) for a, b in E)
    print(enc(n, F))

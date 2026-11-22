# verify-math: small-graph checks of reviewer claims on the 399b paper

Written 2026-11-22, 01:25 to 01:40 CET. Role: small-graph verifier, a Claude instance. It did not consult
the first reviewers' programs, and it reused no supplement code.

## Implementations (they share no code)

- **C** `vc.c` (`cc -O2 -o vc vc.c`): bitmasks; its own graph6 decoder and encoder; generates all
  graphs on n vertices by adding a vertex to every graph on n-1 vertices; canonical form = least
  28-bit adjacency code over relabelings that sort degrees; isomorphism of given graphs by a
  backtracking vertex map; gamma_2 by scanning all subsets with bit-parallel counters.
- **P** `vp.py` (Python standard library, sets and itertools): its own graph6 decoder; generates
  graphs by adding one edge at a time, level by level; canonical form by colour refinement plus
  individualization, taking the least certificate; invariants by `combinations`. It also checks
  that WP(complement) = max_i min(i, delta_i + 1) on every graph it evaluates.
- Sanity check [data]: both give 1, 2, 4, 11, 34, 156, 1044, 12346 graphs and 1, 1, 2, 6, 21, 112,
  853, 11117 connected graphs for n = 1..8 (C) and n = 3..8 (P). These are the OEIS A000088 and
  A001349 values.
- "Other reading" means max{k : k + dbar_k <= n} with dbar the sorted degrees of the complement.
  A violation needs A_3 nonempty.

Logs: `runs_c_enum8.log`, `runs_py_enum3-7.log`, `runs_py_enum8.log`, `runs_c_f3del.log`,
`runs_py_f3del.log`, `runs_c_m5.log`, `runs_py_m5.log`, `runs_py_m5_sets.log`, `runs_c_m6.log`,
`runs_py_m6.log`, `runs_quick_checks.log` (rerun with `quick_checks.sh`).

## M1. Confirmed, with a correction to how the graphs are matched

- Largest alpha(G[A_3]) among connected graphs with gamma_2 = WP + 1 is 1, 1, 2, 2, 3 for
  n = 4..8 [computed, 2]. The counts (tight graphs by alpha) are:
  - n=4: a=1:2, plus one tight graph with A_3 empty (a=0)
  - n=5: a=1:6
  - n=6: a=1:12, a=2:5
  - n=7: a=1:21, a=2:22
  - n=8: a=1:38, a=2:81, a=3:2
- On 8 vertices exactly two classes have alpha = 3 [computed, 2]. C lists them as `G?Ox|o` and
  `G@CZ\W`, P as `G?Ky\c` and `G@CZ\W`. `G?Ox|o` is isomorphic to `G?Ky\c` (both programs).
  `G@CZ\W` and `G?Ky\c` are not isomorphic.
- **`G?bffG` is isomorphic to `G?Ky\c`** (C backtracking and P canonical form) and not to
  `G@CZ\W`. So the three reviewers name the same two graphs.
- The K_{3,3} description (parts {a,b,c}, {d,e,f}, plus edge bc, pendants at e and f) is
  **`G@CZ\W`**, not `G?Ky\c` [computed, 2]. `G?Ky\c` is K_{3,3} plus bc with pendants at **a and
  d**: one pendant on each side, at the vertices of degree 3 [computed, 2]. Both graphs have
  12 edges and degrees 1,1,3,3,4,4,4,4.
- The description's values are confirmed: gamma_2 = 5, WP = 4, alpha(G[A_3]) = 3 [hand;
  computed, 2]. The other reading also gives 4. alpha_2 = 5 [computed, 2].
- Hand proof, fit for a paper (p is the leaf at e, r the leaf at f):

  > The degrees are 1, 1, 3, 3, 4, 4, 4, 4, so WP = 4. The vertices of degree at least three are
  > a, ..., f. An independent set of K_{3,3} lies within one part, and {a,b,c} contains the edge
  > bc, so alpha(G[A_3]) = 3. The set {p, r, d, e, f} is 2-dominating, since each of a, b, c is
  > adjacent to d, e and f. Let D be any 2-dominating set. Then p, r ∈ D. Suppose D' = D ∖ {p, r}
  > has at most two vertices. If d ∉ D, then d needs two neighbours in D, so D' consists of two
  > of a, b, c. The third of these is outside D and has at most one neighbour in D, because its
  > only neighbours among a, b, c come from the edge bc. So d ∈ D. If a ∈ D, then D' = {a, d},
  > and b has only the neighbour d in D. If a ∉ D, then a needs a second neighbour in D among
  > e, f, say e by symmetry. Then D' = {d, e}, and f has only the neighbour r in D. In every case
  > some vertex fails, so gamma_2 = 5 = WP + 1.

- `E^Q?` is isomorphic to the diamond with a pendant at each of its two degree-2 vertices
  [computed, 2]. gamma_2 = 4, WP = 3, alpha(G[A_3]) = 2 [hand; computed, 2]. The other reading
  gives 4.
  - Hand proof. Call the diamond's degree-3 vertices u, v, its degree-2 vertices s, t, and the
    leaves p, r. The degrees are 1,1,3,3,3,3, so WP = 3. A_3 = {u,v,s,t} induces the diamond,
    whose independence number is 2.
  - Upper bound: {p, r, s, t} is 2-dominating.
  - Lower bound: a 2-dominating set of size 3 is {p, r, z}. Neither u nor v has a neighbour among
    p, r, so whichever of u, v is not z has at most one neighbour in D.

## M2. Confirmed

- Under the other reading, no connected graph on 3..6 vertices violates 399b. Exactly 10 do on
  7 vertices and 150 on 8 (up to isomorphism) [computed, 2].
- The C and P lists of violators were matched one-to-one: by C isomorphism tests and by P
  canonical forms.
- The catalogue reading gives 0 violations for n <= 8. gamma_2 <= WP + 1 holds on all of these
  graphs [computed, 2].
- Side note [1 program, C]: on 8 vertices one graph with A_3 empty (a path or cycle) has
  gamma_2 > other-reading + 1. It is excluded because its right side is undefined.
- K_{1,6} (`FsaC?`) is one of the 10 seven-vertex violators [computed, 2], with gamma_2 = 6,
  other-reading value 2, alpha(G[A_3]) = 1 and right side 5.
  - Hand check: the complement degrees are 0, 5,5,5,5,5,5. Then 2 + 5 <= 7 < 3 + 5, so the value
    is 2. The six leaves lie in every 2-dominating set, so gamma_2 = 6. The catalogue reading
    gives WP = 6.

## M3. Confirmed

- K_{1,4} (`Ds_`): the other-reading value is 2, alpha_2 = 4 and gamma_2 = 4 [hand; computed, 2].
  - Hand check: the complement degrees are 0,3,3,3,3, and 2 + 3 <= 5 < 3 + 3, so the value is 2.
    The four leaves induce no edge. Five vertices would include the centre, of degree 4.
- So alpha_2 <= value + 1 fails (4 > 3) under that reading, and DeLaVina-Pepper with k = 2 would
  be false. Under the catalogue reading WP = 4 and 4 <= 5 holds.

## M4. Confirmed

- Of the 36 deletions from F_3 (built from Definition 2 in each program), 30 are connected.
  The 6 disconnected ones are the deletions of x_i or of the edge x_i l_i [computed, 2].
- Under the catalogue reading none of the 30 violates. Under the other reading 21 violate
  [computed, 2, per graph identical].
  - The 21 violators are F_3 - k_j (3 graphs) and the deletion of an edge k_i k_j, x_i k_j or
    x_i y_a (18 graphs).
  - The 9 that do not violate are F_3 - l_i, F_3 - w, F_3 - y_a and F_3 - k_j w.
- F_3 - k_1 has gamma_2 = 7, other-reading value 5 and alpha(G[A_3]) = 3; WP = 6 [computed, 2;
  hand].
  - Hand check: the complement degrees are 5,5,5,5,5,7,7,8,9,9,9 (n = 11), so the value is 5.
    A_3 = X ∪ K ∪ Y because w now has degree 2. X and {k_2, y_1, y_2} are independent sets of
    size 3, and X is complete to K ∪ Y.
  - The paper's proof of Lemma 5 never uses q >= 3, so it gives gamma_2 = 7 at q = 2.
  - So 7 > 5 + 1 under the other reading, and 7 <= 6 + 1 under the catalogue reading.
- `KCOfFFb?~?[?` encodes a graph isomorphic to F_3 (both programs).

## M5. Confirmed

| graph6 | n | m | gamma_2 | WP | alpha(G[A_3]) | min degree | violates |
|---|---|---|---|---|---|---|---|
| `K?CXX\NVz^P~` | 12 | 37 | 5 | 4 | 4 | 1 | yes |
| `K?mKcqXewbYm` | 12 | 30 | 6 | 5 | 4 | 1 (two leaves) | yes |
| `K@Z~Y@gzb{lz` | 12 | 38 | 5 | 4 | 4 | 2 (no leaf) | yes |

All values [computed, 2].

- None of the three is isomorphic to F_3 (24 edges) or to another of the three. The edge counts
  24, 37, 30, 38 differ [hand], and both programs agree.
- The description of `K?CXX\NVz^P~` is exact as a labelled graph. The edge list built from it
  re-encodes to the identical graph6 string (P), and C's decoded edge list equals it.
- Hand argument, checked:
  - **Degrees and A_3.** The degrees are 1, 3,3,3, then 8 eight times, so WP = 4. A_3 is every
    vertex except 0.
  - **Independence.** {1,2,3,11} is independent: N(1) = {8,9,10}, N(2) = {6,7,10},
    N(3) = {4,5,9}, and 11 is adjacent to 0 and 4..10.
  - **alpha = 4.** An independent set has at most two vertices in {4..11}, which induces K_8
    minus 9-10. If it has both 9 and 10, it can contain none of 1, 2, 3, so alpha(G[A_3]) = 4
    [hand].
  - **{0,1,2,3,11} 2-dominates.** Each of 4..10 is adjacent to 11 and to one of 1, 2, 3 [hand;
    computed, 2].
  - **No 4-set containing 0 2-dominates** [computed, 2: 0 of 165]. Hand proof: let
    D = {0} ∪ T with |T| = 3, and t = |T ∩ {1,2,3}|. Each i in {1,2,3} outside D needs two of
    its three neighbours in D, and N_1, N_2, N_3 meet pairwise in at most one vertex.
    - t = 0: the three vertices of T must meet each N_i twice, a total of 6. Only 9 and 10 lie
      in two of the N_i, so the total is at most 5.
    - t = 1: two vertices would have to lie in N_j ∩ N_k for the two outside indices, which has
      at most one vertex.
    - t = 2: the third index has only one vertex of D available.
    - t = 3: vertex 11 has only the neighbour 0 in D.
  - So gamma_2 = 5 > 4 + floor(3/4).

## M6. F_q, q = 3..8: still a violation under both variants

| variant | value | right side | violates |
|---|---|---|---|
| (a) A_3 replaced by the vertices of degree at most 3 | gamma_2 = 7 | 6 | yes, every q |
| (b) "exactly two neighbours in D" | least D has size n = q + 9 | 6 | yes, every q |

**(a)** The vertices of degree at most 3 are l_1, l_2, l_3, y_1, y_2, plus w when q = 3. These
induce no edge, so alpha = 5 (q >= 4) or 6 (q = 3). floor(3/alpha) = 0 and 7 > 6 + 0 [hand;
computed, 2].

**(b)** The least D is V itself, of size n = q + 9. For q = 3..8 that is 12..17, all > 6
[computed, 2].

- Hand proof that only V works. Let a = |D ∩ X|. The leaves are always in D.
  - a = 3: any y_a, k_j outside D would have 3 neighbours in D, so Y and K lie in D. Then w,
    with its q >= 3 neighbours in K, lies in D too.
  - a <= 1: each y_a needs exactly two neighbours in X, so Y ⊆ D. A vertex x_i outside D then
    has l_i and both y's in D, which is too many.
  - a = 2: the x_i outside D has l_i in D, so exactly one vertex of K ∪ Y is in D. Since
    q >= 3, some k_j is outside D and already has two neighbours in X. Hence w ∉ D and K ∩ D is
    empty, and then w has no neighbour in D.
  - In every case D = V [hand].
- Any exact set is a 2-dominating set, so the value is >= 7 > 6 in any case [hand].

## Could not do

- Nothing in M1–M6 was left undone.
- Beyond the brief, I did not search orders above 8.
- The side note in M2 rests on one program: the A_3-empty graph on 8 vertices with
  gamma_2 > other-reading + 1 (C only; P does not report that count).

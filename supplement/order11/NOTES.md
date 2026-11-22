# verify-order11: is there a counterexample to Conjecture 399b on 11 vertices?

> **Paths in this supplement.** The commands below use the verifier's own layout. Here `gen/a_enum.c` is
> `../programA_B/a_enum.c` (byte-identical), and `gen/ck_list.c` is `ck_list.c` in this folder.

Written by Opus 5.5 (role verify-order11). Started Sun Nov 22 01:25 CET 2026 (clock).
Reading: the catalogue reading, WP(compl G) = max{k : k + d_k <= n}, d_1 <= ... <= d_n the
degrees of G. The programs of the paper's first reviewers were not consulted.

Finished Sun Nov 22 01:49 CET 2026 (clock).

## Results

| quantity | value | basis |
|---|---|---|
| connected 10-vertex graphs from generator A (`a_enum list 10`) | 11,716,571, all connected, pairwise non-isomorphic | count and connectivity [computed, 2: ext1, ext2]; non-isomorphism [1 program: canon.c] |
| same from generator C (`ck_list list 10`, copy of ck.c with a list mode) | 11,716,571; the same set of canonical forms as A | [computed: two generators, compared through canon.c] |
| parents: gamma_2(H) >= WP(compl H) | **255,261** | [computed, 2: ext1, ext2 on A's list, identical parent lists]; ext1 on C's list gives the same 255,261 isomorphism classes |
| extensions evaluated (255,261 x 1023) | **261,132,003** | [computed, 2]; gamma_2 and WP of every extension agree: per-parent hashes of the 1023 (gamma_2, WP) pairs identical in ext1 and ext2, and identical (gamma_2, WP) tables |
| labelled extensions with gamma_2 >= WP + 1 | 28,924; none with gamma_2 >= WP + 2 | [computed, 2]; hit files byte-identical |
| connected 11-vertex graphs with gamma_2 = WP + 1, up to isomorphism | **3,022** | [computed, 2: canon.c, and pycheck.py iso (invariant buckets + backtracking isomorphism), same partition]; generator C's extensions give the same 3,022 classes |
| alpha(G[A_3]) among the 3,022 | **1: 227, 2: 2,278, 3: 517**; none >= 4; A_3 empty: 0 | [computed, 2] (alpha by recursion in ext1, by subset brute force in ext2 and pycheck; constant on each class) |
| violations of 399b (catalogue reading) on 11 vertices | **0** | [computed, 2], exhaustive over connected 11-vertex graphs, by the lemma of Section 1 [hand] |

Python brute force from the definitions (pycheck.py, third implementation): all 28,924 labelled hits
recomputed (gamma_2, WP, alpha, violation flag, graph6) with 0 mismatches; 200 random parents
(seed 20261122) with all their 204,600 extensions recomputed, per-parent hashes equal to ext1/ext2,
0 mismatches. Positive control: on F_3 (`KCOfFFb?~?[?`, from the paper) pycheck gives gamma_2 = 7,
WP = 6, alpha(G[A_3]) = 4, violation = True.

The distribution of (gamma_2, WP) over the 3,022 classes: (2,1): 1, (3,2): 15, (4,3): 96,
(5,4): 370, (6,5): 939, (7,6): 1,139, (8,7): 417, (9,8): 43, (10,9): 2.

**Conclusion.** No connected graph on 11 vertices violates Conjecture 399b under the catalogue
reading [computed, 2; reduction by hand]. If the paper's check up to 10 vertices stands (I did not
redo it), the smallest counterexample has 12 vertices, and F_3 is one of the smallest. The other
reading was not examined here.


## 1. The extension lemma [hand]

Write wp(G) for WP(compl G) = max{k : k + d_k <= n}. Since the degrees are sorted, k + d_k <= n
holds exactly when at least k vertices of G have degree at most n - k. So

    wp(G) = max{k >= 1 : at least k vertices of G have degree <= n - k}.        (*)

(The set is nonempty: some vertex has degree <= n - 1.)

**Lemma.** Let G be a graph on n >= 2 vertices, v a vertex of G, H = G - v. Then
(a) gamma_2(G) <= gamma_2(H) + 1;
(b) wp(H) <= wp(G) <= wp(H) + 1.

*Proof.* (a) Let D be a 2-dominating set of H. Every vertex of G outside D + v lies in H - D, so it
has at least two neighbours in D. Hence D + v is 2-dominating in G.

(b) Degrees in H are d_H(u) = d_G(u) - [u adjacent to v] for u != v, so
d_G(u) - 1 <= d_H(u) <= d_G(u). H has n - 1 vertices.
Let k = wp(H): at least k vertices u of H have d_H(u) <= (n-1) - k. For them
d_G(u) <= d_H(u) + 1 <= n - k, so by (*) wp(G) >= k.
Let k = wp(G): at least k vertices of G have d_G <= n - k; at least k - 1 of them differ from v,
and for those d_H(u) <= d_G(u) <= n - k = (n-1) - (k-1). If k >= 2, (*) for H gives
wp(H) >= k - 1. If k = 1, then wp(H) >= 1 > k - 1 trivially (H has a vertex, n - 1 >= 1). []

Neither part needs v to be a non-cut vertex; that is used only to keep H connected.

**Reduction.** Let G be connected on 11 vertices with gamma_2(G) >= wp(G) + 1. (Every
counterexample to 399b is such a graph, because floor(3/alpha) >= 0; DeLaVina and Pepper's bound
gamma_2 <= wp + 1 is not needed for the reduction.) A connected graph on >= 2 vertices has a
non-cut vertex v (a leaf of a spanning tree). H = G - v is connected on 10 vertices and, by the
lemma, gamma_2(H) >= gamma_2(G) - 1 >= wp(G) >= wp(H). So H is a "parent": a connected 10-vertex
graph with gamma_2(H) >= wp(H). H is isomorphic to some graph H' of a complete list of connected
10-vertex graphs, and G is isomorphic to H' plus a new vertex joined to the image of N(v), a
nonempty set because G is connected. Hence: evaluating every extension H' + v (N(v) any of the
1023 nonempty subsets of V(H')) of every parent H' in a complete list finds, up to isomorphism,
**every** connected 11-vertex graph with gamma_2 >= wp + 1, and so every counterexample.
Conversely each extension is a connected 11-vertex graph, so after deduplication the hits are
exactly the isomorphism classes of connected 11-vertex graphs with gamma_2 >= wp + 1.

With gamma_2 <= wp + 1 [DeLaVina-Pepper with Favaron; also checked by the computation below: no
extension has gamma_2 >= wp + 2], a counterexample has gamma_2 = wp + 1 and floor(3/alpha) = 0,
i.e. alpha(G[A_3]) >= 4 (A_3 nonempty).

## 2. Pipeline

All programs are in this folder. The large intermediate files (the two lists of connected graphs on
10 vertices, `o11/a10.g6` and `c10.g6`, and the outputs of `ext2`) are not shipped. The commands
below regenerate them, and their SHA-256 sums are in `logs/sha256.txt`.

1. **Generators** (project code, as the brief allows; copies in `gen/`).
   `gen/a_enum.c` is an unmodified copy of supplement program A; its existing `list` mode prints all
   connected graphs on 1..10 vertices; the 10-vertex lines (`^I`) form `a10.g6`.
   `gen/ck_list.c` is a copy of supplement program C with one addition, a `list` mode that prints the
   graph6 of every connected graph on NMAX vertices (`put_g6`, and the evaluation skipped).
       cc -O2 -o gen/a_enum gen/a_enum.c;  nice -n 15 gen/a_enum list 10 > a_all.g6; grep '^I' a_all.g6 > a10.g6
       cc -O2 -o gen/ck_list gen/ck_list.c; nice -n 15 gen/ck_list list 10 > c10.g6
   Both give 11,716,571 graphs (`logs/a_list10.log`, `logs/c_list10.log`; also OEIS A001349 [data]).
2. **canon.c** (mine): colour refinement + individualisation, largest adjacency code over the leaves,
   pruning only by twins. Tested: invariant under random relabelling (relabel.py) on all 261,080
   connected 9-vertex graphs and, three seeds, on the 28,924 hits; 261,080 distinct forms on 9
   vertices. On a10.g6 and c10.g6: 11,716,571 distinct forms each, and the two sets are equal
   (`logs/canon10.log`).
3. **ext1.c** (implementation 1, mine): own graph6 decoder; gamma_2(H) from a table over all 1024
   subsets (incremental masks "at least one / at least two neighbours in S"); WP by the counting
   form max{k : #{u : d(u) <= n-k} >= k}. For a parent H and N = N(v):
   gamma_2(H+v) = min(1 + min{|S| : every u in V(H)-S has >= 1 neighbour in S, and those with
   exactly one lie in N}, gamma_2(H) if some minimum 2-dominating set of H meets N twice, else
   gamma_2(H) + 1), for all 1023 N at once by a subset-min transform and a superset-OR transform.
   (Correctness: a 2-dominating set of G either contains v, D = S + v, giving the first term, or
   is a 2-dominating set of H meeting N twice; the first term is <= gamma_2(H) + 1, since a
   minimum 2-dominating set S of H qualifies.) alpha(G[A_3]) by recursion.
       nice -n 15 ./ext1 parents.txt hits.txt < a10.g6      (2.5 min wall)
4. **ext2.c** (implementation 2, mine, no shared code): own graph6 reader (bit stream) and writer,
   adjacency matrix; every extension built as an explicit 11-vertex graph; gamma_2 by trying sets
   in order of increasing size (vertices of degree <= 1 forced); WP by sorting, max{k : k+d_k <= n};
   alpha(G[A_3]) by brute force over subsets of A_3. Run in two halves.
       nice -n 15 ./ext2 0 5858286 p0 h0 < a10.g6 ; nice -n 15 ./ext2 5858286 11716571 p1 h1 < a10.g6
   Both programs write, for every parent, "index gamma_2(H) WP(H) hash", the hash being
   h <- h*1000003 + 16*gamma_2 + WP + 1 (mod 2^64) over its 1023 extensions in mask order, and,
   for every extension with gamma_2 >= WP+1, "index mask gamma_2 WP alpha A3empty viol graph6".
   `cmp` of the two parent files and of the two hit files: identical. The hit files decide the hit
   status of every extension exactly (an extension is a hit iff it appears there); the hashes
   compare the exact (gamma_2, WP) values of the non-hits up to the (negligible) chance of a 64-bit
   collision, backed by equal (gamma_2, WP) tables over all extensions.
5. **pycheck.py** (implementation 3, Python standard library, brute force from the definitions):
   `hits` (all hits), `sample` (all extensions of 200 random parents, compared through the hash),
   `iso` (its own isomorphism classes of the hits: invariant buckets, then an exact backtracking
   isomorphism test; compared with canon.c's partition).
       python3 -I pycheck.py hits a10.g6 results/A_ext1_hits.txt
       python3 -I pycheck.py sample a10.g6 results/A_parents_ext1.txt 200 20261122
       python3 -I pycheck.py iso results/A_ext1_hits.txt results/A_hits_canon.txt
6. **Generator cross-check**: ext1 on c10.g6 (`logs/C_ext1.log`) gives the same tables, 255,261
   parents whose canonical forms equal those of A's parents, and hits with the same 3,022 classes.

Files: `results/A_parents_ext1.txt` (parents in a10.g6 order, with hashes), `results/A_ext1_hits.txt`
(28,924 hits), `results/A_hits_canon.txt` (canonical form of each hit line), `results/classes_11.txt`
(the 3,022 classes with gamma_2, WP, alpha(G[A_3])). Logs in `logs/`.

## 3. What could not be done / limits

- Pairwise non-isomorphism of the 11,716,571 generator graphs rests on canon.c alone [1 program];
  completeness is supported by the count (two generators and OEIS) and by the equality of the
  canonical sets of the two generators. Completeness is what the reduction needs.
- Both generators are project code (programs A and C of the supplement), not mine, as the brief
  directed; I did not write a third generator.
- DeLaVina-Pepper's gamma_2 <= WP + 1 is cited, not reproved; the reduction does not need it, and
  on 11 vertices the computation finds no graph with gamma_2 >= WP + 2.
- No positive control of ext1/ext2 on a violating graph was possible at order 11 (there is none);
  the violation test was checked against pycheck on all hits, and pycheck on F_3.

## 4. Comparison with the reviewer (made only after the numbers above were final)

Reviewer: 255,261 parents among 11,716,571 graphs; 261,132,003 extensions; 3,022 connected
11-vertex graphs with gamma_2 = WP + 1, alpha(G[A_3]) histogram 1: 227, 2: 2,278, 3: 517; no
violation. Mine: identical in every number.


# Supplement to "A counterexample to Conjecture 399b of Written on the Wall II"

Everything here is optional reading. The proof in the paper does not depend on any computation.

| File | What it is | How to run |
|---|---|---|
| `verify_399b.py` | Self-contained check of F_q, q = 3..10, by brute force from the definitions (Python standard library only). Computes gamma_2, alpha_2, WP(complement) by both formulas of Section 2 and under the other reading, and alpha(G[A_3]). Shows that the graph6 string of F_3 in the paper encodes F_3. | `python3 verify_399b.py 10` (a few seconds) |
| `verify_399b_output.txt` | Its output (regenerated on 22 November 2026 after the cap that skipped alpha_2 for q = 10 was removed; every other line is unchanged). | |
| `programA_B/a_enum.c` | Program A: its own canonical generator of connected graphs; invariants by branch and bound. | `cc -O2 -o a_enum a_enum.c`; `./a_enum gen 10` (about 3 min); `./a_enum g6 < F.g6` |
| `programA_B/b_enum.c`, `smallgraph.h` | Program B, sharing no code with A: generator from the project's `smallgraph.h`; invariants by dynamic programming over all vertex subsets. The include line was changed to use the copied header. | `cc -O2 -o b_enum b_enum.c`; `./b_enum gen 10` (about 5 min, 1.1 GB); `./b_enum g6 < F.g6` |
| `programA_B/a_gen10.txt`, `b_gen10.txt` | Statistics for all connected graphs with 4 to 10 vertices. They agree in every field they share. A also prints the orders 2 and 3 and an extra 436c field, k1_mismatch (always 0). Each log ends with the command line and its run time, and B's also with memory statistics. | |
| `programA_B/F.g6`, `F_A.txt`, `F_B.txt` | F_q for q = 3..10 in graph6, and the invariants computed by A and B (identical). | |
| `programA_B/F3_minus.g6`, `F3_minus_A.txt`, `F3_minus_B.txt` | The graphs obtained from F_3 by deleting one vertex or one edge, and their evaluation. | |
| `program_ck/ck.c` | Program C, written independently of A and B from the catalogue statements: its own generator and invariants. | `cc -O2 -o ck ck.c`; `./ck gen 10` (about 5 min); `./ck F 3 15` |
| `program_ck/ck_gen10.txt`, `ck_F.txt` | Its statistics for 4 to 10 vertices (equal to A and B), and its values for F_q. | |
| `order11/` | The search showing that no connected graph on 11 vertices violates 399b (Section 4, "Eleven vertices"): `ext1.c` and `ext2.c`, two evaluators that share no code; `canon.c`, a canonical form for deduplication; `pycheck.py`, a Python recheck of all hits and of random extensions; `ck_list.c`, program C with a mode that lists every connected graph on 10 vertices. The other generator is program A, `programA_B/a_enum.c` in its `list` mode. `NOTES.md` has the proof of the extension lemma, the exact commands and the results. `results/` has the 3,022 isomorphism classes on 11 vertices with gamma_2 = WP + 1 (`classes_11.txt`), every hit (`A_ext1_hits.txt`, `A_hits_canon.txt`), and the SHA-256 of the 7.5 MB parents file, which `ext1` regenerates. `logs/` has the run logs. | See `NOTES.md`; about 2.5 min for `ext1` over the 11,716,571 graphs on 10 vertices |
| `other_checks/` | The checks behind the new claims of Section 2 and Remarks 8 and 9: the other reading on small graphs and on F_q; A_3 read as degree at most 3; "exactly two" 2-domination; the deletions from F_3 under both readings; the second 12-vertex counterexample; and the 8-vertex graph of the introduction. `vc.c` (C, bitmasks) and `vp.py` (Python), which share no code. `NOTES.md` has the results, and `logs/` the outputs. | `cc -O2 -o vc vc.c`; `bash quick_checks.sh` |
| `lean/` | The Lean 4 + Mathlib formalisation: F_3 and the family F_q refute the formal statement of 399b, checked by the kernel with the standard axioms only. See `lean/README.md`. | `cd lean && lake exe cache get && lake build` |

In the statistics lines, `aA3>=4` counts the graphs with alpha(G[A_3]) >= 4 (the only ones for which 399b is not
already a theorem), `viol` counts violations of 399b, and `A3empty` counts the graphs with no vertex of degree >= 3
(paths and cycles), for which the right side is undefined.

# A counterexample to Conjecture 399b of Written on the Wall II

Jiří Chmel. Preprint, version 1, 22 November 2026.

> **Status: preprint, not yet fully reviewed by the author.** A version reviewed by the author will replace this one.
> Until then, read it as unreviewed work.

**The paper:** [`WOWII399b_counterexample.pdf`](WOWII399b_counterexample.pdf), 8 pages.

## Abstract

Conjecture 399b of Written on the Wall II, a list of conjectures made by the program Graffiti.pc, states the
following. Every connected graph G on n > 2 vertices satisfies γ₂(G) ≤ WP(Ḡ) + ⌊3/α(G[A₃])⌋. Here γ₂ is the
2-domination number, WP(Ḡ) is the Welsh–Powell invariant of the complement, and A₃ is the set of vertices of degree
at least three.

DeLaViña and Pepper proved γ₂(G) ≤ WP(Ḡ) + 1, which settles every graph with 1 ≤ α(G[A₃]) ≤ 3. We show that the
conjecture is false in the remaining case. For every q ≥ 3 we give a connected graph F_q on q + 9 vertices with
γ₂(F_q) = 7, WP(F̄_q) = 6 and α(F_q[A₃]) = 4. The proof is elementary, and it has also been checked in the Lean proof
assistant. The smallest member of the family has 12 vertices. Exhaustive computer searches show that, with the
catalogue's reading of the Welsh–Powell invariant, no counterexample has 11 or fewer.

## How it was checked

- **The hand proof** (Section 3 of the paper) went through two rounds of adversarial review. In each round, separate
  Claude instances wrote their own programs and attacked the proof, the numbers and the sources. This is not external
  peer review.
- **A formal proof in Lean 4 with Mathlib,** checked by the Lean kernel, refutes the formal statement, both by F_3
  and by F_q for every q ≥ 3.
  - It uses only the standard axioms propext, Classical.choice and Quot.sound, and no `sorry` or `native_decide`.
  - Audits checked the formal statement against the catalogue's definitions, including negative controls. They also
    proved that the formal graphs are the graphs of the paper.
- **Computations:**
  - the family for q = 3..10, by two programs that share no code and by a standard-library verifier;
  - all connected graphs on at most 10 vertices, by three programs;
  - all connected graphs on 11 vertices, by a reduction proved in the paper and two evaluators that share no code;
  - the deletions from F_3, and the other claims of Section 2 and Remarks 8 and 9.

## Use of generative AI

The counterexample was found, and the paper, the programs and the formal proof were written, by Claude Opus 5.5, a
generative AI system made by Anthropic. Claude was used through Claude Code, in sessions directed by the author.
Section 1.1 of the paper describes this. Claude is not an author. The Lean kernel's check of the formal proof does
not depend on any AI system.

## Contents

| Path | Contents |
|---|---|
| `WOWII399b_counterexample.pdf` | The paper (preprint, version 1). |
| `source/paper.tex`, `source/build.sh` | Its LaTeX source and build script (Tectonic or pdflatex). |
| `supplement/README.md` | What the supplement contains, and how to run each program. |
| `supplement/verify_399b.py` | A self-contained check of F_q, q = 3..10 (Python standard library only), and its output. |
| `supplement/programA_B/`, `supplement/program_ck/` | Programs A, B and C: generators of all connected graphs up to 10 vertices, with the evaluation of 399b and their logs. |
| `supplement/order11/` | The exhaustive search on 11 vertices, with notes, logs and results. |
| `supplement/other_checks/` | The checks behind the remaining claims of Section 2 and Remarks 8 and 9. |
| `supplement/lean/` | The Lean 4 formalisation (Lean 4.37.0-rc1, Mathlib rev 31ce06eaadf4), with build instructions and SHA-256 sums. |
| `SHA256SUMS` | The SHA-256 hash of every file. |

## Reproduce

    python3 supplement/verify_399b.py 10           # F_q for q = 3..10, a few seconds
    cd source && bash build.sh                     # the paper
    cd supplement/lean && lake exe cache get && lake build   # the formal proof

Each folder of the supplement says how to run its programs (C programs: `cc -O2 -o NAME NAME.c`, no dependencies).

## Licence

CC BY 4.0; see `LICENSE.md`.

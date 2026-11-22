# Lean 4 formalisation of the counterexample to WOWII Conjecture 399b

Copied on 2026-11-22 01:58 CET from the project's Lean workspace (`lean_wowii/`). Every file except the root file `LeanWowii.lean`, which was written for this copy and imports the 399b modules, is
byte-identical to the file that was built and checked there. Lean `v4.37.0-rc1` (`lean-toolchain`), Mathlib `v4.37.0-rc1` (rev 31ce06eaadf4, `lake-manifest.json`).

## Build

    lake exe cache get      # fetch the Mathlib build cache
    lake build              # builds LeanWowii.lean, which imports every 399b file

A build of this copy from a fresh checkout has not been run, because it needs the Mathlib download. The same files
build without errors in the project workspace (22 November 2026), and each was also re-elaborated there from source
with `lake env lean`.

## What is proved (all checked by the Lean kernel)

| File | Content |
|---|---|
| `LeanWowii/W399b/Defs.lean` | Catalogue definitions: `wpCompl` (definition 113: the largest k with k + d_k <= n, degrees of G in nondecreasing order), `A3` (degree >= 3), `alphaA3`, and `Conjecture399bStatement` (connected, n > 2, A_3 nonempty: gamma_2 <= WP + floor(3/alpha(G[A_3]))) |
| `LeanWowii/W399b/Counterexample.lean` | F_3 on `Fin 12`: connected, WP = 6, alpha(G[A_3]) = 4, gamma_2 = 7; `not_conjecture399b : ¬ Conjecture399bStatement` |
| `LeanWowii/W399b/Family.lean` | F_q for every q >= 3 (Theorem 1 of the paper): `W399b.Family.theorem1` and `W399b.Family.not_conjecture399b_family` |
| `LeanWowii/W399b/FamilyCheck.lean` | an isomorphism between F 3 of Family.lean and F3 of Counterexample.lean |
| `LeanWowii/W399b/Audit.lean` | audit of the statement: the sorted degree sequence of F_3, negative controls for WP, agreement with Definition 2 and with the graph6 string `KCOfFFb?~?[?` |
| `LeanWowii/W399b/FamilyAudit.lean` | audit of the family: F q equals the graph of the edge list of Definition 2, for every q; the edge count |
| `LeanWowii/W213/*.lean` | 2-domination (`IsTwoDominating`, `gamma2`) and the helper `ofEdges`, reused from the project's formalisation of WOWII 213. W213/Audit.lean imports W213/Main.lean, so the whole 213 development comes along. |

Axioms: `W399b.not_conjecture399b`, `W399b.Family.theorem1`, `W399b.Family.not_conjecture399b_family` and the audit theorems depend only on
`propext`, `Classical.choice` and `Quot.sound`. No file uses `sorry`, `native_decide` or an `axiom` declaration.
Check with `#print axioms W399b.not_conjecture399b` after `import LeanWowii.W399b.Counterexample`.

## SHA-256 of the files

```
c5c9f0c5efb72f490aee9a67fb1fc58efdb836f003bfb8dcd5a17edd8cec3913  ./LeanWowii.lean
9e0c796707de7e4a272f0c25905405a27e6a3288fb307ee22dbf3a4066de0384  ./LeanWowii/W213/Audit.lean
8d02d8f909be239a81f63bf5dc7347884193a51de6c1cf45a8f237c66682b04b  ./LeanWowii/W213/CaseJ.lean
844829d10b5cc954ae34e8c3215bbd9c96c11f91484c7a15bb02607dd293beed  ./LeanWowii/W213/Closure.lean
9f882bb73d647e95b217605612854c82fae4c264c4a93bb6847bb379214b26ad  ./LeanWowii/W213/Defs.lean
23727c689068a7271806f3c7705de94429c23ecee2106c0855bab8e42d6957e6  ./LeanWowii/W213/Main.lean
b588949fb7839e229f703c0fc85af491888b63a173fddbf372fabddadab6fe82  ./LeanWowii/W213/Monotone.lean
13aa659c6b8c0fc3f5943e038976ca55e03162aca60944dc0d4a73cf99d4caa4  ./LeanWowii/W213/Selection.lean
996dba7cecc3a8ad26afde1a1d53a02421d853cad66719c283e3535f5e2750b5  ./LeanWowii/W213/Structure.lean
a0fd4d8190e7fc9ba547e5852e5d51711373e10dd8a7d7100ff056ce08e0f30a  ./LeanWowii/W213/Theorem1.lean
baa1ea1c88efc625a281d62b89e79bdde205f31344cd4c03a1a9229ec52b49ea  ./LeanWowii/W399b/Audit.lean
561757a938def000f819ace149824b1445d16bfb23aa82d70282be726cede7c6  ./LeanWowii/W399b/Counterexample.lean
1c7e8f98856c56eaf85249a70d081238181a48d662b4804f51e504fd72fc0c96  ./LeanWowii/W399b/Defs.lean
1d54c07f9e48ad6aadd032158fe1207392c4aa3cf70397b05ed055db23672a26  ./LeanWowii/W399b/Family.lean
c10b2d4f9b768ba17831ce1ae1fea1b14828759816ef6ccc0e343c95b58f179f  ./LeanWowii/W399b/FamilyAudit.lean
ba818d53993080568ce6c1c5ea86a1216e51063890388c68b7a58de6ca2bf50f  ./LeanWowii/W399b/FamilyCheck.lean
16db208a82f1a8987be051e4f14b6cb29511ed43c6759ac06d4fcca37444d966  ./lake-manifest.json
d652329933946869305f06adfff766872f01c709dafa0b728d5bbec098e234db  ./lakefile.toml
f11739c25d1640e2b3fda8a98af6d64e97d7b2b1c99840535587a9079b3afee7  ./lean-toolchain
```

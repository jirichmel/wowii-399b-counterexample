/-
# Definitions for Conjecture 399b (Graffiti.pc, Written on the Wall II)

Conjecture 399b (as catalogued): "If G is a connected graph on n > 2 vertices, then
gamma_2 <= WP(complement of G) + FLOOR[3/alpha(G[A_3])], where A_3 is the set of vertices of
degree at least three."

This file contains only definitions and their basic lemmas (no sorry):
* `sortedDegrees`, `wpCompl` (catalogue definition 113: the largest `k` with `k + d_k <= n`,
  degrees of `G` in nondecreasing order) and its counting characterisation `wpCompl_eq_count`;
* `A3` (vertices of degree at least three) and `alphaA3` (independence number of `G[A_3]`),
  with its attainment and maximality lemmas;
* `Conjecture399bStatement` (refuted in `Counterexample.lean`).
`gamma2` (catalogue definition 90) is taken from `LeanWowii.W213.Defs`.

Working text for an unpublished project; nothing here has been published.
-/
import LeanWowii.W213.Defs

/-! Definitions for Conjecture 399b. -/

namespace W399b

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

section WP

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The degrees of `G` in nondecreasing order, `d_1 ≤ d_2 ≤ ... ≤ d_n` (as a 0-based list). -/
def sortedDegrees : List ℕ :=
  W213.sortedValues (fun v => G.degree v)

theorem sortedDegrees_pairwise : (sortedDegrees G).Pairwise (· ≤ ·) :=
  W213.sortedValues_pairwise _

theorem length_sortedDegrees : (sortedDegrees G).length = Fintype.card V :=
  W213.length_sortedValues _

/-- Catalogue definition 113: "Welsh-Powell of the complement of G, WP(complement G), is the
largest k such that k + d_k <= n, where the degree sequence is ordered in nondecreasing order
(d_1 <= ... <= d_n)", with the degrees of `G`. Here `k` ranges over `1..n` and
`d_k = (sortedDegrees G)[k-1]`; the value is `0` when no such `k` exists (only when `n = 0`). -/
def wpCompl : ℕ :=
  ((Finset.Icc 1 (Fintype.card V)).filter
      (fun k => k + (sortedDegrees G).getD (k - 1) 0 ≤ Fintype.card V)).sup id

/-- For `1 ≤ k ≤ n`: `k + d_k ≤ n` iff at least `k` vertices have degree `≤ n - k`. -/
theorem add_dk_le_iff {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    k + (sortedDegrees G).getD (k - 1) 0 ≤ Fintype.card V ↔
      k ≤ (univ.filter (fun v => G.degree v + k ≤ Fintype.card V)).card := by
  have hlt : k - 1 < (sortedDegrees G).length := by rw [length_sortedDegrees]; omega
  have hget : (sortedDegrees G).getD (k - 1) 0 = (sortedDegrees G)[k - 1] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  rw [hget]
  have h := W213.sorted_getElem_le_iff (sortedDegrees_pairwise G) hlt (Fintype.card V - k)
  have hc : (sortedDegrees G).countP (fun x => decide (x ≤ Fintype.card V - k)) =
      (univ.filter (fun v => G.degree v ≤ Fintype.card V - k)).card :=
    W213.countP_sortedValues (fun v => G.degree v) (fun x => x ≤ Fintype.card V - k)
  rw [hc] at h
  have hf : (univ.filter (fun v => G.degree v ≤ Fintype.card V - k)) =
      (univ.filter (fun v => G.degree v + k ≤ Fintype.card V)) := by
    apply Finset.filter_congr; intro v _; omega
  rw [hf] at h
  constructor
  · intro h1; have := h.mp (by omega); omega
  · intro h1; have := h.mpr (by omega); omega

/-- Counting characterisation of `wpCompl`: the same maximum over `1..n`, with the condition
`k + d_k ≤ n` replaced by "at least `k` vertices have degree `≤ n - k`". -/
theorem wpCompl_eq_count :
    wpCompl G = ((Finset.Icc 1 (Fintype.card V)).filter
      (fun k => k ≤ (univ.filter (fun v => G.degree v + k ≤ Fintype.card V)).card)).sup id := by
  unfold wpCompl
  congr 1
  apply Finset.filter_congr
  intro k hk
  rw [Finset.mem_Icc] at hk
  exact add_dk_le_iff G hk.1 hk.2

end WP

section Alpha

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `A_3`: the set of vertices of degree at least three. -/
def A3 : Finset V := univ.filter (fun v => 3 ≤ G.degree v)

/-- `S` is an independent set of `G` (no two vertices of `S` are adjacent). -/
def IsIndep (S : Finset V) : Prop := ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

instance (S : Finset V) : Decidable (IsIndep G S) := by unfold IsIndep; infer_instance

theorem isIndep_iff_isIndepSet (S : Finset V) : IsIndep G S ↔ G.IsIndepSet (S : Set V) := by
  constructor
  · intro h u hu v hv _; exact h u hu v hv
  · intro h u hu v hv huv
    exact h hu hv (G.ne_of_adj huv) huv

/-- `alpha(G[A_3])`: the largest size of an independent set of `G` contained in `A_3`, i.e. the
independence number of the subgraph induced by `A_3` (`0` if `A_3` is empty). -/
def alphaA3 : ℕ := ((A3 G).powerset.filter (IsIndep G)).sup Finset.card

theorem card_le_alphaA3 {S : Finset V} (hS : S ⊆ A3 G) (hI : IsIndep G S) :
    S.card ≤ alphaA3 G :=
  Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, hI⟩)

theorem exists_alphaA3 : ∃ S, S ⊆ A3 G ∧ IsIndep G S ∧ S.card = alphaA3 G := by
  have hne : ((A3 G).powerset.filter (IsIndep G)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by simp [IsIndep]⟩⟩
  obtain ⟨S, hS, he⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  exact ⟨S, hS.1, hS.2, he.symm⟩

/-- Agreement with Mathlib's independence number of the induced subgraph `G[A_3]` (vertex type
the subtype of `A_3`). -/
theorem alphaA3_eq_indepNum :
    alphaA3 G = (G.induce (A3 G : Set V)).indepNum := by
  classical
  apply le_antisymm
  · obtain ⟨S, hS, hI, hc⟩ := exists_alphaA3 G
    rw [← hc]
    let T : Finset (A3 G : Set V) := S.subtype (· ∈ A3 G)
    have hT : T.card = S.card := by
      rw [Finset.card_subtype]; congr 1
      exact Finset.filter_true_of_mem (fun x hx => hS hx)
    rw [← hT]
    apply SimpleGraph.IsIndepSet.card_le_indepNum
    intro a ha b hb _ hab
    have ha' : (a : V) ∈ S := by simpa [T] using ha
    have hb' : (b : V) ∈ S := by simpa [T] using hb
    exact hI a ha' b hb' hab
  · obtain ⟨T, hT⟩ := (G.induce (A3 G : Set V)).exists_isNIndepSet_indepNum
    rw [← hT.card_eq]
    have hle := card_le_alphaA3 G (S := T.map (Function.Embedding.subtype _))
      (by intro x hx; obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hx; exact y.property)
      (by
        intro u hu v hv huv
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
        have hab : a ≠ b := by rintro rfl; exact G.loopless.irrefl _ huv
        exact hT.isIndepSet ha hb hab huv)
    simpa using hle

end Alpha

/-- Conjecture 399b (Graffiti.pc, Written on the Wall II): "If G is a connected graph on
n > 2 vertices, then gamma_2 <= WP(complement of G) + FLOOR[3/alpha(G[A_3])]". The extra
hypothesis `0 < alphaA3 G` (i.e. `A_3` nonempty) excludes the graphs where the right side is
undefined; it only weakens the statement, so refuting it refutes the catalogue statement.
`3 / alphaA3 G` is natural-number division, i.e. the floor. -/
def Conjecture399bStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → 2 < Fintype.card V → 0 < alphaA3 G →
      W213.gamma2 G ≤ wpCompl G + 3 / alphaA3 G

end W399b

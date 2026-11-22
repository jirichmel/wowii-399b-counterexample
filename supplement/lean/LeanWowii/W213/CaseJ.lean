/-
# Conjecture 213: Lemma J (the case 2m ≥ n of Theorem 1)

Proof file: conjectures/wowii213_conjR_round_inprogress/prover-claimC/proof.md, Section 3.

For every graph X on n ≥ 2 vertices with m = lowerMedian X and 2m ≥ n: gamma2 X ≤ m + 1.
Proof: W = {v : deg v ≥ m} has ≥ ⌊n/2⌋+1 vertices (Fact A (ii)); choose A ⊆ W with
|A| = n - m - 1 and take D = V \ A. Each x ∈ A has ≥ m neighbours, at most |A| - 1 in A,
so ≥ 2m - n + 2 ≥ 2 in D.

Working text for an unpublished project; nothing here has been published.
-/
import LeanWowii.W213.Defs

namespace W213

set_option linter.unusedSectionVars false

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Lemma J (a): if `n ≥ 2` and `n ≤ 2 * lowerMedian X`, then `gamma2 X ≤ lowerMedian X + 1`. -/
theorem lemmaJ (X : SimpleGraph V) [DecidableRel X.Adj] (hn : 2 ≤ Fintype.card V)
    (hm : Fintype.card V ≤ 2 * lowerMedian X) : gamma2 X ≤ lowerMedian X + 1 := by
  set n := Fintype.card V with hn_def
  set m := lowerMedian X with hm_def
  have hpos : 0 < n := by omega
  -- m ≤ n - 1
  obtain ⟨v0, hv0⟩ := exists_degree_eq_lowerMedian X hpos
  have hmlt : m < n := by
    have := X.degree_lt_card_verts v0
    rw [hm_def, ← hv0]; exact this
  -- W
  set W := Finset.univ.filter (fun v => m ≤ X.degree v) with hW
  have hWcard : n / 2 + 1 ≤ W.card := card_degree_ge_of_le_lowerMedian X hpos le_rfl
  have ha : n - m - 1 ≤ W.card := by omega
  obtain ⟨A, hAW, hAcard⟩ := Finset.exists_subset_card_eq ha
  set D := Finset.univ \ A with hD
  have hDcard : D.card = m + 1 := by
    rw [hD, Finset.card_univ_sdiff, hAcard]; omega
  refine (gamma2_le_iff X (m + 1)).mpr ⟨D, ?_, hDcard.le⟩
  intro x hx
  have hxA : x ∈ A := by simpa [hD] using hx
  have hxdeg : m ≤ X.degree x := by
    have := hAW hxA; simpa [hW] using this
  -- split the neighbourhood of x into the parts in D and in A
  have hsplit : (Finset.univ.filter (X.Adj x)).card =
      (D.filter (X.Adj x)).card + (A.filter (X.Adj x)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext w; simp [hD]; tauto
    · exact Finset.disjoint_filter_filter (Finset.sdiff_disjoint)
  have hdeg : (Finset.univ.filter (X.Adj x)).card = X.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have hAx : (A.filter (X.Adj x)).card ≤ A.card - 1 := by
    have hsub : A.filter (X.Adj x) ⊆ A.erase x := by
      intro w hw
      rw [Finset.mem_filter] at hw
      exact Finset.mem_erase.mpr ⟨fun h => X.irrefl (h ▸ hw.2), hw.1⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem hxA] at this
  have hApos : 0 < A.card := Finset.card_pos.mpr ⟨x, hxA⟩
  omega

/-- Lemma J for the complement, in the form used by Theorem 1 / Conjecture 213. -/
theorem lemmaJ_compl (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 2 ≤ Fintype.card V)
    (hm : Fintype.card V ≤ 2 * lowerMedian Gᶜ) : gamma2 Gᶜ ≤ lowerMedian Gᶜ + 1 :=
  lemmaJ Gᶜ hn hm

end W213

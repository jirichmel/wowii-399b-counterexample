/-
# Theorem 1 for Conjecture 213

Source: `conjectures/wowii213_conjR_round_inprogress/prover-claimC/proof.md`, Section 5.

Theorem 1: every closed, connected, non-complete graph `G` satisfies
`gamma2 Gᶜ ≤ lowerMedian Gᶜ + 1`.

* Case 1, `n ≤ 2m`: Lemma J (`lemmaJ_compl`).
* Case 2a, `2m ≤ n - 1` and `r ≤ |Y|`: the selection lemma with `A_y = N(y) ∩ P` gives
  `B ⊆ P`, `R ⊆ Y`; `D = U ∪ B ∪ R` has `m + 1` vertices and is 2-dominating in `Gᶜ`.
* Case 2b, `2m ≤ n - 1` and `|Y| < r`: `D = U ∪ Y ∪ B0` with `B0 ⊆ P` of size
  `m + 1 - u - |Y|`.

Corollary 2: no closed, connected, non-complete graph has `lowerMedian Gᶜ + 2 ≤ gamma2 Gᶜ`.

Working text for an unpublished project; nothing here has been published.
-/
import LeanWowii.W213.Defs
import LeanWowii.W213.Selection
import LeanWowii.W213.Structure
import LeanWowii.W213.CaseJ

namespace W213

set_option linter.unusedSectionVars false

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Case 2a of Theorem 1. -/
theorem theorem1_case2a {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcl : IsClosedGraph G) (hne : G ≠ ⊤)
    (hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1) (hY : rS G ≤ (setY G).card) :
    gamma2 Gᶜ ≤ lowerMedian Gᶜ + 1 := by
  have hr := two_le_rS hcl hm hne
  have hru := rS_add_card_setU hcl hm hne
  obtain ⟨B, hBP, R, hRY, hcard, hR2, hsel⟩ :=
    selection_lemma (rS G) hr (setP G) (setY G) hY (fun y => (setP G).filter (G.Adj y))
      (fun y hy => card_filter_setP_le_rS_sub_two hm hy)
  set D := setU G ∪ B ∪ R with hD_def
  have hdUB : Disjoint (setU G) B := disjoint_setU_setP.mono_right hBP
  have hdUBR : Disjoint (setU G ∪ B) R :=
    Finset.disjoint_union_left.mpr
      ⟨(disjoint_setU_setY hm).mono_right hRY, (disjoint_setP_setY.mono_left hBP).mono_right hRY⟩
  have hDcard : D.card = lowerMedian Gᶜ + 1 := by
    rw [hD_def, Finset.card_union_of_disjoint hdUBR, Finset.card_union_of_disjoint hdUB]
    omega
  have hdom : IsTwoDominating Gᶜ D := by
    intro v hv
    have hvU : v ∉ setU G := fun h => hv (by rw [hD_def]; simp [h])
    have hvB : v ∉ B := fun h => hv (by rw [hD_def]; simp [h])
    have hvR : v ∉ R := fun h => hv (by rw [hD_def]; simp [h])
    rcases mem_setU_or_setP_or_setY (G := G) v with h | h | h
    · exact absurd h hvU
    · -- v ∈ P \ B: at least two vertices of R are non-adjacent to v
      have hs := hsel v (Finset.mem_sdiff.mpr ⟨h, hvB⟩)
      have hfeq : R.filter (fun y => v ∈ (setP G).filter (G.Adj y)) = R.filter (G.Adj v) := by
        apply Finset.filter_congr
        intro y _
        simp only [Finset.mem_filter, h, true_and]
        exact ⟨fun e => e.symm, fun e => e.symm⟩
      rw [hfeq] at hs
      have hsplit := card_filter_compl_add (G := G) R hvR
      have hsub : R.filter (Gᶜ.Adj v) ⊆ D.filter (Gᶜ.Adj v) :=
        Finset.filter_subset_filter _ (by rw [hD_def]; exact Finset.subset_union_right)
      have := Finset.card_le_card hsub
      omega
    · exact two_le_card_filter_of_mem_setY (by omega) h hv
  have := gamma2_le Gᶜ hdom
  omega

/-- Case 2b of Theorem 1. -/
theorem theorem1_case2b {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcl : IsClosedGraph G) (hc : G.Connected) (hne : G ≠ ⊤)
    (hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1) (hY : (setY G).card < rS G) :
    gamma2 Gᶜ ≤ lowerMedian Gᶜ + 1 := by
  have hru := rS_add_card_setU hcl hm hne
  have hsum := card_setU_add_card_setP_add_card_setY hm
  have hc0 : lowerMedian Gᶜ + 1 - (setU G).card - (setY G).card ≤ (setP G).card := by
    have := one_lt_card_of_ne_top hne
    omega
  obtain ⟨B0, hB0P, hB0card⟩ := Finset.exists_subset_card_eq hc0
  set D := setU G ∪ setY G ∪ B0 with hD_def
  have hDcard : D.card ≤ lowerMedian Gᶜ + 1 := by
    have h1 := Finset.card_union_le (setU G ∪ setY G) B0
    have h2 := Finset.card_union_le (setU G) (setY G)
    rw [hD_def]
    omega
  have hYD : setY G ⊆ D := by
    rw [hD_def]
    exact Finset.subset_union_left.trans' Finset.subset_union_right
  have hdom : IsTwoDominating Gᶜ D := by
    intro v hv
    have hvU : v ∉ setU G := fun h => hv (by rw [hD_def]; simp [h])
    have hvY : v ∉ setY G := fun h => hv (hYD h)
    rcases mem_setU_or_setP_or_setY (G := G) v with h | h | h
    · exact absurd h hvU
    · exact two_le_card_filter_of_setY_subset hcl hc hYD h
    · exact absurd h hvY
  exact (gamma2_le Gᶜ hdom).trans hDcard

/-- **Theorem 1.** Every closed, connected, non-complete graph `G` satisfies
`gamma2 Gᶜ ≤ lowerMedian Gᶜ + 1`. -/
theorem theorem1 {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcl : IsClosedGraph G) (hc : G.Connected) (hne : G ≠ ⊤) :
    gamma2 Gᶜ ≤ lowerMedian Gᶜ + 1 := by
  have hn := one_lt_card_of_ne_top hne
  by_cases h1 : Fintype.card V ≤ 2 * lowerMedian Gᶜ
  · exact lemmaJ_compl G (by omega) h1
  · have hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1 := by omega
    by_cases hY : rS G ≤ (setY G).card
    · exact theorem1_case2a hcl hne hm hY
    · exact theorem1_case2b hcl hc hne hm (by omega)

/-- **Corollary 2 (Claim C).** No closed, connected, non-complete graph satisfies
`lowerMedian Gᶜ + 2 ≤ gamma2 Gᶜ`. -/
theorem corollary2 {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcl : IsClosedGraph G) (hc : G.Connected) (hne : G ≠ ⊤) :
    ¬ lowerMedian Gᶜ + 2 ≤ gamma2 Gᶜ := by
  have := theorem1 hcl hc hne
  omega

end W213

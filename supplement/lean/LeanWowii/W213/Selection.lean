import Mathlib

/-!
# Lemma 4 (selection lemma) for Conjecture 213

Abstract form (no graphs). Let `r ≥ 2`, `P : Finset α`, `Y' : Finset β` with `r ≤ |Y'|`,
and `A : β → Finset α` with `|A y| ≤ r - 2` for `y ∈ Y'`. Then there are `B ⊆ P` and
`R ⊆ Y'` with `|B| + |R| = r`, `2 ≤ |R|`, such that every `q ∈ P \ B` lies in at most
`|R| - 2` of the sets `A y`, `y ∈ R`.

Proof by induction on `r`, as in `proof.md`, Section 5. The sets `A y` need not lie in `P`.
-/

namespace W213

theorem selection_lemma {α β : Type*} [DecidableEq α] [DecidableEq β]
    (r : ℕ) (hr : 2 ≤ r) (P : Finset α) (Y' : Finset β) (hY : r ≤ Y'.card)
    (A : β → Finset α) (hA : ∀ y ∈ Y', (A y).card ≤ r - 2) :
    ∃ B ⊆ P, ∃ R ⊆ Y', B.card + R.card = r ∧ 2 ≤ R.card ∧
      ∀ q ∈ P \ B, (R.filter (fun y => q ∈ A y)).card ≤ R.card - 2 := by
  induction r, hr using Nat.le_induction generalizing P Y' A with
  | base =>
    -- every `A y` is empty; take `B = ∅` and any two indices
    obtain ⟨R, hRY, hRc⟩ := Finset.exists_subset_card_eq hY
    refine ⟨∅, Finset.empty_subset _, R, hRY, by simp [hRc], by omega, ?_⟩
    intro q _
    have : R.filter (fun y => q ∈ A y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro y hy hq
      have h0 := hA y (hRY hy)
      have : (A y).card = 0 := by omega
      rw [Finset.card_eq_zero] at this
      simp [this] at hq
    simp [this]
  | succ r hr ih =>
    obtain ⟨R0, hR0Y, hR0c⟩ := Finset.exists_subset_card_eq hY
    by_cases hgood : ∀ q ∈ P, (R0.filter (fun y => q ∈ A y)).card ≤ r + 1 - 2
    · refine ⟨∅, Finset.empty_subset _, R0, hR0Y, by simp [hR0c], by omega, ?_⟩
      intro q hq
      rw [hR0c]
      exact hgood q (Finset.mem_sdiff.1 hq).1
    · push Not at hgood
      obtain ⟨x, hxP, hx⟩ := hgood
      set Y'' := R0.filter (fun y => x ∈ A y) with hY''
      have hY''c : r ≤ Y''.card := by omega
      have hA' : ∀ y ∈ Y'', ((A y).erase x).card ≤ r - 2 := by
        intro y hy
        rw [Finset.mem_filter] at hy
        rw [Finset.card_erase_of_mem hy.2]
        have := hA y (hR0Y hy.1)
        omega
      obtain ⟨B', hB'P, R, hRY'', hcard, hR2, hsel⟩ :=
        ih (P.erase x) Y'' hY''c (fun y => (A y).erase x) hA'
      have hxB' : x ∉ B' := fun h => by simpa using hB'P h
      refine ⟨insert x B', ?_, R, ?_, ?_, hR2, ?_⟩
      · exact Finset.insert_subset hxP (hB'P.trans (Finset.erase_subset _ _))
      · exact hRY''.trans ((Finset.filter_subset _ _).trans hR0Y)
      · rw [Finset.card_insert_of_notMem hxB']
        omega
      · intro q hq
        rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hq
        obtain ⟨hqP, hqx, hqB'⟩ := hq
        have hq' : q ∈ P.erase x \ B' :=
          Finset.mem_sdiff.2 ⟨Finset.mem_erase.2 ⟨hqx, hqP⟩, hqB'⟩
        have heq : R.filter (fun y => q ∈ A y) = R.filter (fun y => q ∈ (A y).erase x) := by
          apply Finset.filter_congr
          intro y _
          simp [hqx]
        rw [heq]
        exact hsel q hq'

end W213

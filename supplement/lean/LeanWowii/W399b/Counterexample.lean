/-
# The counterexample F_3 to Conjecture 399b (Graffiti.pc, Written on the Wall II)

Contents (all kernel-checked; no sorry, no native_decide):
* `F3 : SimpleGraph (Fin 12)`, the graph F_3 of Definition 2 of the paper, labelled
  x1,x2,x3 = 0,1,2; l1,l2,l3 = 3,4,5; k1,k2,k3 = 6,7,8; w = 9; y1,y2 = 10,11.
  With this labelling the graph6 string `KCOfFFb?~?[?` decodes to exactly this edge list
  (identity map; checked outside Lean by a separate script).
* `F3_connected`, `wpCompl_F3 : wpCompl F3 = 6`, `A3_F3`, `alphaA3_F3 : alphaA3 F3 = 4`,
  `gamma2_F3 : W213.gamma2 F3 = 7`, and the main theorem `not_conjecture399b`.
* The lower bound `gamma2 F3 ≥ 7` goes through a Boolean reformulation: `IsTwoDominating F3 D`
  is equivalent (`twoDom_iff`) to a condition on the 12 Booleans `decide (i ∈ D)` read along
  explicit neighbour lists, and the resulting statement over all 2^12 Boolean assignments is
  checked by `decide +kernel` (`key_bool`).

Working text for an unpublished project; nothing here has been published.
-/
import LeanWowii.W399b.Defs
import LeanWowii.W213.Audit

/-! The counterexample F_3 to Conjecture 399b. -/

namespace W399b

set_option linter.unusedSectionVars false

open Finset

/-! ## The graph -/

/-- The 24 edges of F_3: `x_i l_i`; the triangle on `K = {6,7,8}`; `X × K`; `w × K`; `Y × X`. -/
def edgesF3 : List (ℕ × ℕ) :=
  [(0,3),(1,4),(2,5),                               -- x_i l_i
   (6,7),(6,8),(7,8),                               -- K is a triangle
   (0,6),(0,7),(0,8),(1,6),(1,7),(1,8),(2,6),(2,7),(2,8),  -- X joined to K
   (9,6),(9,7),(9,8),                               -- w joined to K
   (10,0),(10,1),(10,2),(11,0),(11,1),(11,2)]       -- Y joined to X

/-- The graph F_3 (Definition 2 of the paper with q = 3), on `Fin 12`. -/
abbrev F3 : SimpleGraph (Fin 12) := W213.Audit.ofEdges 12 edgesF3

example : edgesF3.length = 24 := rfl

/-- Explicit neighbour lists. -/
def nbL : Fin 12 → List (Fin 12)
  | 0 => [3,6,7,8,10,11] | 1 => [4,6,7,8,10,11] | 2 => [5,6,7,8,10,11]
  | 3 => [0] | 4 => [1] | 5 => [2]
  | 6 => [0,1,2,7,8,9] | 7 => [0,1,2,6,8,9] | 8 => [0,1,2,6,7,9]
  | 9 => [6,7,8] | 10 => [0,1,2] | 11 => [0,1,2]

set_option maxRecDepth 10000 in
theorem adj_iff_mem_nbL : ∀ v u : Fin 12, F3.Adj v u ↔ u ∈ nbL v := by decide +kernel

theorem nbL_nodup : ∀ v : Fin 12, (nbL v).Nodup := by decide +kernel

set_option maxRecDepth 10000 in
/-- Degrees: leaves 1, `y_a` 3, `w` 3, `x_i` and `k_j` 6. -/
theorem degree_F3 : ∀ v : Fin 12, F3.degree v = (nbL v).length := by decide +kernel

/-! ## Connectivity -/

theorem reach_from_6 (v : Fin 12) : F3.Reachable 6 v := by
  have a : ∀ a b : Fin 12, F3.Adj a b → F3.Reachable a b := fun _ _ h => h.reachable
  fin_cases v
  · exact a 6 0 (by decide)
  · exact a 6 1 (by decide)
  · exact a 6 2 (by decide)
  · exact (a 6 0 (by decide)).trans (a 0 3 (by decide))
  · exact (a 6 1 (by decide)).trans (a 1 4 (by decide))
  · exact (a 6 2 (by decide)).trans (a 2 5 (by decide))
  · exact SimpleGraph.Reachable.refl _
  · exact a 6 7 (by decide)
  · exact a 6 8 (by decide)
  · exact a 6 9 (by decide)
  · exact (a 6 0 (by decide)).trans (a 0 10 (by decide))
  · exact (a 6 0 (by decide)).trans (a 0 11 (by decide))

theorem F3_connected : F3.Connected :=
  ⟨fun u v => (reach_from_6 u).symm.trans (reach_from_6 v)⟩

/-! ## WP(complement of F_3) = 6 -/

set_option maxRecDepth 100000 in
theorem wpCompl_F3 : wpCompl F3 = 6 := by
  rw [wpCompl_eq_count]; simp only [Fintype.card_fin]; decide +kernel

/-- The sorted degree sequence itself, for the record (the list is computed with
`Multiset.sort`, so it is checked through the counting lemma rather than by evaluation). -/
theorem wpCompl_F3_witness :
    6 + (sortedDegrees F3).getD 5 0 ≤ 12 ∧ ∀ k, 7 ≤ k → k ≤ 12 →
      ¬ k + (sortedDegrees F3).getD (k - 1) 0 ≤ 12 := by
  have h := fun k (h1 : 1 ≤ k) (h2 : k ≤ 12) =>
    add_dk_le_iff F3 (k := k) h1 (by simpa using h2)
  simp only [Fintype.card_fin] at h
  refine ⟨(h 6 (by norm_num) (by norm_num)).mpr (by decide +kernel), ?_⟩
  intro k hk1 hk2
  rw [h k (by omega) hk2]
  interval_cases k <;> decide +kernel

/-! ## A_3 and alpha(F_3[A_3]) = 4 -/

set_option maxRecDepth 10000 in
theorem A3_F3 : A3 F3 = {0, 1, 2, 6, 7, 8, 9, 10, 11} := by decide +kernel

set_option maxRecDepth 100000 in
theorem alphaA3_F3 : alphaA3 F3 = 4 := by
  unfold alphaA3; rw [A3_F3]; decide +kernel

/-- The independent set `X ∪ {w}` of the paper. -/
example : {0, 1, 2, 9} ⊆ A3 F3 ∧ IsIndep F3 {0, 1, 2, 9} := by
  rw [A3_F3]; decide +kernel

/-! ## gamma_2(F_3) = 7 -/

/-- Counting the members of `D` along a duplicate-free list. -/
theorem card_filter_toFinset {α : Type*} [DecidableEq α] (D : Finset α) :
    ∀ L : List α, L.Nodup →
      (L.toFinset.filter (· ∈ D)).card = L.countP (fun u => decide (u ∈ D))
  | [], _ => by simp
  | a :: L, h => by
    rw [List.nodup_cons] at h
    have ih := card_filter_toFinset D L h.2
    rw [List.toFinset_cons, Finset.filter_insert, List.countP_cons]
    by_cases ha : a ∈ D
    · simp only [ha, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp [h.1]), ih]; simp
    · simp only [ha, ↓reduceIte]
      rw [ih]; simp

theorem card_filter_adj (D : Finset (Fin 12)) (v : Fin 12) :
    (D.filter (F3.Adj v)).card = (nbL v).countP (fun u => decide (u ∈ D)) := by
  rw [← card_filter_toFinset D (nbL v) (nbL_nodup v)]
  congr 1
  ext u
  simp only [Finset.mem_filter, List.mem_toFinset, adj_iff_mem_nbL]
  exact and_comm

theorem card_eq_countP (D : Finset (Fin 12)) :
    D.card = (List.finRange 12).countP (fun u => decide (u ∈ D)) := by
  rw [← card_filter_toFinset D _ (List.nodup_finRange 12)]
  congr 1
  ext u
  simp

/-- 2-domination in F_3, read along the neighbour lists. -/
theorem twoDom_iff (D : Finset (Fin 12)) :
    W213.IsTwoDominating F3 D ↔
      ∀ v : Fin 12, v ∉ D → 2 ≤ (nbL v).countP (fun u => decide (u ∈ D)) := by
  unfold W213.IsTwoDominating
  simp only [card_filter_adj]

set_option maxRecDepth 100000 in
/-- The finite check: every Boolean assignment to the 12 vertices that satisfies the
2-domination condition along the neighbour lists has at least 7 `true` entries. -/
theorem key_bool : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
    (∀ v : Fin 12, ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] v = false →
      2 ≤ (nbL v).countP ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]) →
    7 ≤ (List.finRange 12).countP ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] := by
  decide +kernel

theorem seven_le_card (D : Finset (Fin 12)) (hD : W213.IsTwoDominating F3 D) :
    7 ≤ D.card := by
  set f : Fin 12 → Bool := fun u => decide (u ∈ D) with hf
  have hvec : ![f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11] = f := by
    funext i; fin_cases i <;> rfl
  have hk := key_bool (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) (f 11)
  rw [hvec] at hk
  rw [card_eq_countP]
  apply hk
  intro v hv
  have hv' : v ∉ D := by simpa [hf] using hv
  exact (twoDom_iff D).mp hD v hv'

/-- The 2-dominating set `D_0 = {l_1,l_2,l_3,x_1,x_2,x_3,w}` of the paper. -/
theorem twoDom_D0 : W213.IsTwoDominating F3 {0, 1, 2, 3, 4, 5, 9} := by
  rw [twoDom_iff]; decide +kernel

theorem gamma2_F3 : W213.gamma2 F3 = 7 := by
  apply le_antisymm
  · exact (W213.gamma2_le F3 twoDom_D0).trans (by decide)
  · exact (W213.le_gamma2_iff F3 7).mpr seven_le_card

/-! ## The main theorem -/

/-- F_3 violates the inequality: `gamma_2 = 7 > 6 = WP(complement) + ⌊3/4⌋`. -/
theorem F3_violates : wpCompl F3 + 3 / alphaA3 F3 < W213.gamma2 F3 := by
  rw [wpCompl_F3, alphaA3_F3, gamma2_F3]
  norm_num

/-- Conjecture 399b of Written on the Wall II is false. -/
theorem not_conjecture399b : ¬ Conjecture399bStatement := by
  intro h
  have hle := h (Fin 12) F3 F3_connected (by simp) (by rw [alphaA3_F3]; norm_num)
  exact absurd hle (not_le.mpr F3_violates)

/-! ## Sanity checks of the definitions on small graphs (values computed by hand) -/

set_option maxRecDepth 10000 in
/-- P4 (path 0-1-2-3): degrees 1,1,2,2; `k + d_k ≤ 4` holds for k = 1, 2 only. -/
example : wpCompl W213.Audit.P4 = 2 := by
  rw [wpCompl_eq_count]; simp only [Fintype.card_fin]; decide +kernel

set_option maxRecDepth 10000 in
/-- K_{1,3}: degrees 1,1,1,3; `k + d_k ≤ 4` holds for k = 1, 2, 3. -/
example : wpCompl W213.Audit.K13 = 3 := by
  rw [wpCompl_eq_count]; simp only [Fintype.card_fin]; decide +kernel

set_option maxRecDepth 10000 in
example : A3 W213.Audit.K13 = {0} ∧ alphaA3 W213.Audit.K13 = 1 := by
  unfold alphaA3; decide +kernel

set_option maxRecDepth 10000 in
/-- P4 has no vertex of degree at least three, so `alphaA3 P4 = 0`; such graphs are excluded by
the hypothesis `0 < alphaA3 G` of `Conjecture399bStatement`. -/
example : A3 W213.Audit.P4 = ∅ ∧ alphaA3 W213.Audit.P4 = 0 := by
  unfold alphaA3; decide +kernel

set_option maxRecDepth 100000 in
/-- Remark 4 of the paper (the other reading, with the degrees of the complement): the
formula applied to the complement of F_3 gives q + 3 = 6. -/
example : wpCompl F3ᶜ = 6 := by
  rw [wpCompl_eq_count]; simp only [Fintype.card_fin]; decide +kernel

end W399b

#print axioms W399b.not_conjecture399b
#print axioms W399b.gamma2_F3
#print axioms W399b.wpCompl_F3
#print axioms W399b.alphaA3_F3
#print axioms W399b.A3_F3
#print axioms W399b.F3_connected
#print axioms W399b.alphaA3_eq_indepNum

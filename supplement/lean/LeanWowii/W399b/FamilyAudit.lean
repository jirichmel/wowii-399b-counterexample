/-
# Audit of `Family.lean`: the graph `F q` read by roles, in the words of Definition 2

Written by the auditor of `Family.lean` and `FamilyCheck.lean` (label audit-lean-family); it
changes neither file. Contents:
* `paperEdges q`: the edge set of Definition 2 of the paper, written as a set of unordered pairs
  ("x_i l_i for i = 1,2,3; all k_i k_j; all x_i k_j; all w k_j; all y_a x_i"), and
  `F_eq_fromEdgeSet : F q = SimpleGraph.fromEdgeSet (paperEdges q)`, for every `q`;
* `adj_iff_roles`: the same adjacency as a disjunction over the roles, and the role-pair lemmas
  that say which pairs are never adjacent (X and Y independent, w has no neighbour outside K, ...);
* `card_edgeFinset_F`: `F q` has `q(q-1)/2 + 4q + 9` edges (24 for q = 3), from the handshake
  lemma and the degrees of `Family.lean`;
* `alpha_induce_F`: `alpha(F_q[A_3]) = 4` stated with Mathlib's `indepNum` of the induced graph;
* `theorem1_paper`: Theorem 1 restated, and `#print`/`#check` of the refuted statement.

Working text for an unpublished project; nothing here has been published.
-/
import LeanWowii.W399b.Family

/-! Audit of the family `F q`: adjacency by roles, edge count, Theorem 1 restated. -/

namespace W399b.Family.FamilyAudit

open Finset W399b.Family

variable {q : ℕ}

/-- The edges of Definition 2: `x_i l_i`; `k_i k_j` (`i ≠ j`); `x_i k_j`; `w k_j`; `y_a x_i`. -/
def paperEdges (q : ℕ) : Set (Sym2 (Vt q)) :=
  {e | (∃ i : Fin 3, e = s(Vt.x i, Vt.l i)) ∨
       (∃ i j : Fin q, i ≠ j ∧ e = s(Vt.k i, Vt.k j)) ∨
       (∃ (i : Fin 3) (j : Fin q), e = s(Vt.x i, Vt.k j)) ∨
       (∃ j : Fin q, e = s(Vt.w, Vt.k j)) ∨
       (∃ (a : Fin 2) (i : Fin 3), e = s(Vt.y a, Vt.x i))}

/-- `F q` is exactly the graph with the edge set of Definition 2, for every `q`. -/
theorem F_eq_fromEdgeSet : F q = SimpleGraph.fromEdgeSet (paperEdges q) := by
  ext u v
  simp only [F_adj, SimpleGraph.fromEdgeSet_adj, paperEdges, Set.mem_ofPred_eq, Sym2.eq_iff]
  cases u <;> cases v <;> simp [adjB] <;>
    first | exact eq_comm | exact fun h => ⟨_, _, h, Or.inl ⟨rfl, rfl⟩⟩

/-- Adjacency in `F q` by roles. -/
theorem adj_iff_roles (u v : Vt q) : (F q).Adj u v ↔
    (∃ i : Fin 3, (u = .x i ∧ v = .l i) ∨ (u = .l i ∧ v = .x i)) ∨
    (∃ i j : Fin q, i ≠ j ∧ u = .k i ∧ v = .k j) ∨
    (∃ (i : Fin 3) (j : Fin q), (u = .x i ∧ v = .k j) ∨ (u = .k j ∧ v = .x i)) ∨
    (∃ j : Fin q, (u = .w ∧ v = .k j) ∨ (u = .k j ∧ v = .w)) ∨
    (∃ (a : Fin 2) (i : Fin 3), (u = .y a ∧ v = .x i) ∨ (u = .x i ∧ v = .y a)) := by
  cases u <;> cases v <;> simp [adjB] <;> exact eq_comm

/-! Role pairs, one statement per clause of Definition 2 and of "there are no other edges". -/

theorem adj_x_l (i i' : Fin 3) : (F q).Adj (.x i) (.l i') ↔ i = i' := by simp [adjB]
theorem adj_k_k (j j' : Fin q) : (F q).Adj (.k j) (.k j') ↔ j ≠ j' := by simp [adjB]
theorem adj_x_k (i : Fin 3) (j : Fin q) : (F q).Adj (.x i) (.k j) := by simp [adjB]
theorem adj_w_k (j : Fin q) : (F q).Adj .w (.k j) := by simp [adjB]
theorem adj_y_x (a : Fin 2) (i : Fin 3) : (F q).Adj (.y a) (.x i) := by simp [adjB]
theorem X_indep (i i' : Fin 3) : ¬ (F q).Adj (.x i) (.x i') := by simp [adjB]
theorem Y_indep (a a' : Fin 2) : ¬ (F q).Adj (.y a) (.y a') := by simp [adjB]
theorem L_indep (i i' : Fin 3) : ¬ (F q).Adj (.l i) (.l i') := by simp [adjB]
theorem w_nbrs (v : Vt q) : (F q).Adj .w v ↔ ∃ j, v = .k j := by cases v <;> simp [adjB]
theorem l_nbrs (i : Fin 3) (v : Vt q) : (F q).Adj (.l i) v ↔ v = .x i := by
  cases v <;> simp [adjB, eq_comm]
theorem y_nbrs (a : Fin 2) (v : Vt q) : (F q).Adj (.y a) v ↔ ∃ i, v = .x i := by
  cases v <;> simp [adjB]
theorem k_not_l (j : Fin q) (i : Fin 3) : ¬ (F q).Adj (.k j) (.l i) := by simp [adjB]
theorem k_not_y (j : Fin q) (a : Fin 2) : ¬ (F q).Adj (.k j) (.y a) := by simp [adjB]
theorem x_not_w (i : Fin 3) : ¬ (F q).Adj (.x i) .w := by simp [adjB]

/-! Edge count, from the handshake lemma. -/

/-- The degrees of `Family.lean`, by role. -/
def degF (q : ℕ) : Vt q → ℕ
  | .x _ => q + 3 | .l _ => 1 | .k _ => q + 3 | .w => q | .y _ => 3

theorem degree_eq_degF (v : Vt q) : (F q).degree v = degF q v := by
  cases v
  · exact degree_x _
  · exact degree_l _
  · exact degree_k _
  · exact degree_w
  · exact degree_y _

theorem sum_degrees_F : ∑ v : Vt q, (F q).degree v = q * q + 7 * q + 18 := by
  rw [Finset.sum_congr rfl (fun v _ => degree_eq_degF v)]
  rw [Fintype.sum_equiv equivSum _ (fun s => degF q (ofSum s)) (fun v => by cases v <;> rfl)]
  simp [Fintype.sum_sum_type, ofSum, degF]
  ring

theorem card_edgeFinset_F (hq : 1 ≤ q) :
    2 * (F q).edgeFinset.card = q * (q - 1) + 8 * q + 18 := by
  have h := (F q).sum_degrees_eq_twice_card_edges
  rw [sum_degrees_F] at h
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  nlinarith [h]

example : (F 3).edgeFinset.card = 24 := by
  have := card_edgeFinset_F (q := 3) (by norm_num); omega

/-! Theorem 1 in the words of the paper. -/

theorem alpha_induce_F (hq : 3 ≤ q) :
    ((F q).induce (A3 (F q) : Set (Vt q))).indepNum = 4 := by
  rw [← alphaA3_eq_indepNum, alphaA3_F hq]

/-- Theorem 1: for every `q ≥ 3`, `F_q` is connected, has `q + 9` vertices,
`γ₂ = 7`, `WP(complement) = 6`, `α(F_q[A_3]) = 4`, and `7 > 6 + ⌊3/4⌋`. -/
theorem theorem1_paper (hq : 3 ≤ q) :
    (F q).Connected ∧ Fintype.card (Vt q) = q + 9 ∧ W213.gamma2 (F q) = 7 ∧
      wpCompl (F q) = 6 ∧ ((F q).induce (A3 (F q) : Set (Vt q))).indepNum = 4 ∧
      6 + 3 / 4 < 7 :=
  ⟨(theorem1 hq).1, card_Vt, gamma2_F (by omega), wpCompl_F hq, alpha_induce_F hq,
    by norm_num⟩

/-- The family theorem refutes the very constant `W399b.Conjecture399bStatement` of `Defs.lean`. -/
example : (∀ q, 3 ≤ q → ¬ W399b.Conjecture399bStatement) :=
  fun _ hq => not_conjecture399b_family hq

end W399b.Family.FamilyAudit

#print W399b.Conjecture399bStatement
#check @W399b.Family.not_conjecture399b_family
#check @W399b.Family.theorem1
#print W399b.Family.adjB
#print axioms W399b.Family.FamilyAudit.F_eq_fromEdgeSet
#print axioms W399b.Family.FamilyAudit.adj_iff_roles
#print axioms W399b.Family.FamilyAudit.card_edgeFinset_F
#print axioms W399b.Family.FamilyAudit.theorem1_paper

/-
# The family F_q (q >= 3) of counterexamples to Conjecture 399b (Written on the Wall II)

Theorem 1 of the paper, for every `q ≥ 3`, uniformly in `q` (no evaluation over `q`):
* `Vt q`: the `q + 9` vertices x_1..x_3, l_1..l_3, k_1..k_q, w, y_1, y_2 (an inductive type,
  `card_Vt : Fintype.card (Vt q) = q + 9`); `F q : SimpleGraph (Vt q)` is Definition 2 of the
  paper: edges x_i l_i, K a clique, X × K, w × K, Y × X, nothing else.
* `F_connected`; degrees `degree_x .. degree_y`; the sorted degree sequence of Lemma 3,
  `sortedDegrees_F : sortedDegrees (F q) = [1,1,1,3,3,q] ++ replicate (q+3) (q+3)`;
* `wpCompl_F : wpCompl (F q) = 6` (Lemma 3; also `wpCompl_F_via_sorted`, a second proof from the
  sorted sequence), `mem_A3`, `alphaA3_F : alphaA3 (F q) = 4` (Lemma 4),
  `gamma2_F : W213.gamma2 (F q) = 7` (Lemma 5: leaves forced, then observations (i)-(iv));
* `theorem1`, `F_violates`, `F_not_conjecture_inequality`, `not_conjecture399b_family`.
The definitions `wpCompl`, `A3`, `alphaA3`, `Conjecture399bStatement` are those of
`LeanWowii.W399b.Defs`; `gamma2` is `W213.gamma2`. No sorry, no native_decide, no axioms added.

Working text for an unpublished project; nothing here has been published.
-/
import LeanWowii.W399b.Defs

/-! The family `F q` (`q ≥ 3`) of counterexamples to Conjecture 399b. -/

namespace W399b.Family

open Finset

inductive Vt (q : ℕ) where
  | x : Fin 3 → Vt q
  | l : Fin 3 → Vt q
  | k : Fin q → Vt q
  | w : Vt q
  | y : Fin 2 → Vt q
  deriving DecidableEq

variable {q : ℕ}

def toSum : Vt q → Fin 3 ⊕ Fin 3 ⊕ Fin q ⊕ Unit ⊕ Fin 2
  | .x i => .inl i
  | .l i => .inr (.inl i)
  | .k j => .inr (.inr (.inl j))
  | .w => .inr (.inr (.inr (.inl ())))
  | .y a => .inr (.inr (.inr (.inr a)))

def ofSum : Fin 3 ⊕ Fin 3 ⊕ Fin q ⊕ Unit ⊕ Fin 2 → Vt q
  | .inl i => .x i
  | .inr (.inl i) => .l i
  | .inr (.inr (.inl j)) => .k j
  | .inr (.inr (.inr (.inl _))) => .w
  | .inr (.inr (.inr (.inr a))) => .y a

def equivSum : Vt q ≃ Fin 3 ⊕ Fin 3 ⊕ Fin q ⊕ Unit ⊕ Fin 2 where
  toFun := toSum
  invFun := ofSum
  left_inv v := by cases v <;> rfl
  right_inv s := by rcases s with i | i | j | ⟨⟩ | a <;> rfl

instance : Fintype (Vt q) := Fintype.ofEquiv _ equivSum.symm

theorem card_Vt : Fintype.card (Vt q) = q + 9 := by
  rw [Fintype.card_congr equivSum]; simp only [Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit]; omega

theorem card_filter_univ (p : Vt q → Prop) [DecidablePred p] :
    (univ.filter p).card =
      (univ.filter (fun i => p (.x i))).card + (univ.filter (fun i => p (.l i))).card +
      (univ.filter (fun j => p (.k j))).card + (if p .w then 1 else 0) +
      (univ.filter (fun a => p (.y a))).card := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_equiv equivSum _ (fun s => if p (ofSum s) then 1 else 0)
    (fun v => by cases v <;> rfl)]
  simp only [Fintype.sum_sum_type, Fintype.univ_unit, Finset.sum_singleton]
  simp only [ofSum, add_assoc]
  rfl

/-! ## The graph -/

def adjB : Vt q → Vt q → Bool
  | .x i, .l i' => decide (i = i')
  | .l i, .x i' => decide (i = i')
  | .k j, .k j' => decide (j ≠ j')
  | .x _, .k _ => true
  | .k _, .x _ => true
  | .w, .k _ => true
  | .k _, .w => true
  | .y _, .x _ => true
  | .x _, .y _ => true
  | _, _ => false

def F (q : ℕ) : SimpleGraph (Vt q) where
  Adj u v := adjB u v = true
  symm := ⟨fun u v h => by
    cases u <;> cases v <;> simp only [adjB, decide_eq_true_eq, Bool.false_eq_true] at h ⊢ <;>
      exact h.symm⟩
  loopless := ⟨fun u h => by cases u <;> simp_all [adjB]⟩

instance : DecidableRel (F q).Adj := fun u v => inferInstanceAs (Decidable (adjB u v = true))

@[simp] theorem F_adj (u v : Vt q) : (F q).Adj u v ↔ adjB u v = true := Iff.rfl

/-- Counting neighbours inside a set `D`. -/
theorem card_filter_adj (D : Finset (Vt q)) (v : Vt q) :
    (D.filter ((F q).Adj v)).card = (univ.filter (fun u => u ∈ D ∧ adjB v u = true)).card := by
  congr 1; ext u; simp

theorem degree_eq (v : Vt q) :
    (F q).degree v = (univ.filter (fun u => adjB v u = true)).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  rfl

theorem degree_x (i : Fin 3) : (F q).degree (.x i) = q + 3 := by
  rw [degree_eq, card_filter_univ]; simp [adjB, Finset.filter_eq]; omega

theorem degree_l (i : Fin 3) : (F q).degree (.l i) = 1 := by
  rw [degree_eq, card_filter_univ]; simp [adjB, Finset.filter_eq]

theorem degree_k (j : Fin q) : (F q).degree (.k j) = q + 3 := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact j.elim0)
  rw [degree_eq, card_filter_univ]; simp [adjB, Finset.filter_ne, Finset.card_erase_of_mem]
  omega

theorem degree_w : (F q).degree .w = q := by
  rw [degree_eq, card_filter_univ]; simp [adjB]

theorem degree_y (a : Fin 2) : (F q).degree (.y a) = 3 := by
  rw [degree_eq, card_filter_univ]; simp [adjB]

/-! ## The sorted degree sequence (Lemma 3) -/

/-- Lemma 3: in nondecreasing order the degrees are `1,1,1,3,3,q`, then `q+3` repeated `q+3`
times. -/
theorem sortedDegrees_F (hq : 3 ≤ q) :
    sortedDegrees (F q) = [1, 1, 1, 3, 3, q] ++ List.replicate (q + 3) (q + 3) := by
  have hL : ([1, 1, 1, 3, 3, q] ++ List.replicate (q + 3) (q + 3)).Pairwise (· ≤ ·) := by
    simp [List.pairwise_replicate]
    omega
  apply List.Perm.eq_of_sortedLE (sortedDegrees_pairwise _).sortedLE hL.sortedLE
  rw [List.perm_iff_count]
  intro n
  have h := W213.countP_sortedValues (fun v => (F q).degree v) (fun x => x = n)
  rw [List.count_eq_countP]
  rw [show (List.countP (fun x => x == n) (sortedDegrees (F q))) =
    (sortedDegrees (F q)).countP (fun x => decide (x = n)) from
      List.countP_congr (fun x _ => by simp)]
  unfold sortedDegrees
  rw [h, card_filter_univ]
  simp [degree_x, degree_l, degree_k, degree_w, degree_y, List.count_cons, List.count_replicate,
    Finset.filter_const]
  split_ifs <;> simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin] <;> omega

/-- The defining inequalities of catalogue definition 113, read on the sorted sequence:
`k = 6` satisfies `k + d_k ≤ n`, and no `k` with `7 ≤ k ≤ n` does. -/
theorem wpCompl_F_witness (hq : 3 ≤ q) :
    6 + (sortedDegrees (F q)).getD 5 0 ≤ q + 9 ∧
      ∀ k, 7 ≤ k → k ≤ q + 9 → ¬ k + (sortedDegrees (F q)).getD (k - 1) 0 ≤ q + 9 := by
  rw [sortedDegrees_F hq]
  refine ⟨by simp; omega, fun k hk1 hk2 => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 7 := ⟨k - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega]
  simp [List.getD_eq_getElem?_getD, show m < q + 3 by omega]
  omega

/-- A second proof of `wpCompl (F q) = 6`, straight from definition 113 and Lemma 3. -/
theorem wpCompl_F_via_sorted (hq : 3 ≤ q) : wpCompl (F q) = 6 := by
  obtain ⟨h6, h7⟩ := wpCompl_F_witness hq
  unfold wpCompl
  rw [card_Vt]
  apply le_antisymm
  · apply Finset.sup_le
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    rw [id_eq]
    by_contra h
    exact h7 k (by omega) hk.1.2 hk.2
  · exact Finset.le_sup (f := id)
      (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h6⟩)

/-! ## Connectivity -/

theorem F_connected (hq : 1 ≤ q) : (F q).Connected := by
  let k0 : Fin q := ⟨0, hq⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨.k k0, fun v => ?_⟩
  have a : ∀ u v : Vt q, adjB u v = true → (F q).Reachable u v :=
    fun u v h => SimpleGraph.Adj.reachable h
  cases v with
  | x i => exact a _ _ rfl
  | l i => exact (a _ (.x i) rfl).trans (a _ _ (by simp [adjB]))
  | k j =>
    by_cases h : k0 = j
    · subst h; rfl
    · exact a _ _ (by simp [adjB, h])
  | w => exact a _ _ rfl
  | y b => exact (a _ (.x 0) rfl).trans (a _ _ rfl)

/-! ## WP(complement) = 6 -/

theorem card_filter_le_six (p : Vt q → Prop) [DecidablePred p] (hx : ∀ i, ¬ p (.x i))
    (hk : ∀ j, ¬ p (.k j)) : (univ.filter p).card ≤ 6 := by
  rw [card_filter_univ]
  rw [Finset.filter_false_of_mem (fun i _ => hx i), Finset.filter_false_of_mem (fun j _ => hk j)]
  have h1 := Finset.card_filter_le (univ : Finset (Fin 3)) (fun i => p (.l i))
  have h2 := Finset.card_filter_le (univ : Finset (Fin 2)) (fun a => p (.y a))
  have h3 : (if p .w then 1 else 0) ≤ 1 := by split_ifs <;> omega
  simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
  simp only [Finset.card_empty]
  omega

theorem wpCompl_F (hq : 3 ≤ q) : wpCompl (F q) = 6 := by
  rw [wpCompl_eq_count, card_Vt]
  apply le_antisymm
  · apply Finset.sup_le
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨_, _⟩, hc⟩ := hk
    rw [id_eq]
    by_contra h7
    have h6 := card_filter_le_six (fun v => (F q).degree v + k ≤ q + 9)
      (fun i => by simp only [degree_x]; omega) (fun j => by simp only [degree_k]; omega)
    omega
  · have hmem : 6 ∈ (Finset.Icc 1 (q + 9)).filter
        (fun k => k ≤ (univ.filter (fun v => (F q).degree v + k ≤ q + 9)).card) := by
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [Finset.filter_true_of_mem (fun v _ => by
        cases v <;> simp only [degree_x, degree_l, degree_k, degree_w, degree_y] <;> omega)]
      rw [Finset.card_univ, card_Vt]; omega
    exact Finset.le_sup (f := id) hmem

/-! ## A_3 and alpha(F_q[A_3]) = 4 -/

theorem mem_A3 (hq : 3 ≤ q) (v : Vt q) : v ∈ A3 (F q) ↔ ∀ i, v ≠ .l i := by
  unfold A3
  cases v <;> simp [degree_x, degree_l, degree_k, degree_w, degree_y, hq]

theorem card_eq_filter (S : Finset (Vt q)) : S.card = (univ.filter (· ∈ S)).card := by
  congr 1; ext; simp

theorem exists_of_card_pos {α : Type*} [Fintype α] {p : α → Prop} [DecidablePred p]
    (h : 0 < (univ.filter p).card) : ∃ a, p a := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp h
  exact ⟨a, (Finset.mem_filter.mp ha).2⟩

theorem alphaA3_F (hq : 3 ≤ q) : alphaA3 (F q) = 4 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hsub, hI⟩ := hS
    have hadj : ∀ u ∈ S, ∀ v ∈ S, adjB u v = false := by
      intro u hu v hv; simpa using hI u hu v hv
    rw [card_eq_filter, card_filter_univ]
    have hL : (univ.filter (fun i : Fin 3 => Vt.l i ∈ S)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi
      exact (mem_A3 hq _).mp (hsub hi) i rfl
    have hX := Finset.card_filter_le (univ : Finset (Fin 3)) (fun i => Vt.x i ∈ S)
    have hY := Finset.card_filter_le (univ : Finset (Fin 2)) (fun a => Vt.y a ∈ S)
    have hW : (if Vt.w ∈ S then 1 else 0) ≤ 1 := by split_ifs <;> omega
    simp only [Finset.card_univ, Fintype.card_fin] at hX hY
    -- (a) a vertex of K in S excludes X, w and the rest of K
    have ha : (univ.filter (fun j : Fin q => Vt.k j ∈ S)).card = 0 ∨
        ((univ.filter (fun i : Fin 3 => Vt.x i ∈ S)).card = 0 ∧
          (if Vt.w ∈ S then 1 else 0) = 0 ∧
          (univ.filter (fun j : Fin q => Vt.k j ∈ S)).card ≤ 1) := by
      rcases Nat.eq_zero_or_pos (univ.filter (fun j : Fin q => Vt.k j ∈ S)).card with h | h
      · exact Or.inl h
      obtain ⟨j, hj⟩ := exists_of_card_pos h
      refine Or.inr ⟨?_, ?_, ?_⟩
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _ hi; have := hadj _ hi _ hj; simp [adjB] at this
      · split_ifs with hw
        · have := hadj _ hw _ hj; simp [adjB] at this
        · rfl
      · apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        have h1 := hadj _ ha _ hj; have h2 := hadj _ hb _ hj
        simp only [adjB, decide_eq_false_iff_not, ne_eq, not_not] at h1 h2; rw [h1, h2]
    -- (b) X and Y are joined completely
    have hb : (univ.filter (fun i : Fin 3 => Vt.x i ∈ S)).card = 0 ∨
        (univ.filter (fun a : Fin 2 => Vt.y a ∈ S)).card = 0 := by
      rcases Nat.eq_zero_or_pos (univ.filter (fun i : Fin 3 => Vt.x i ∈ S)).card with h | h
      · exact Or.inl h
      rcases Nat.eq_zero_or_pos (univ.filter (fun a : Fin 2 => Vt.y a ∈ S)).card with h' | h'
      · exact Or.inr h'
      obtain ⟨i, hi⟩ := exists_of_card_pos h
      obtain ⟨a, ha⟩ := exists_of_card_pos h'
      have := hadj _ hi _ ha; simp [adjB] at this
    omega
  · have hS : ({.x 0, .x 1, .x 2, .w} : Finset (Vt q)) ⊆ A3 (F q) := by
      intro v hv
      rw [mem_A3 hq]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> simp
    have hI : IsIndep (F q) ({.x 0, .x 1, .x 2, .w} : Finset (Vt q)) := by
      intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
        simp [adjB]
    have := card_le_alphaA3 (F q) hS hI
    rwa [show ({.x 0, .x 1, .x 2, .w} : Finset (Vt q)).card = 4 by simp] at this

/-! ## gamma_2(F_q) = 7 -/

/-- `D_0 = {l_1,l_2,l_3,x_1,x_2,x_3,w}`. -/
def isD0 : Vt q → Bool
  | .x _ => true
  | .l _ => true
  | .w => true
  | _ => false

def D0 (q : ℕ) : Finset (Vt q) := univ.filter (fun v => isD0 v = true)

@[simp] theorem mem_D0_x (i : Fin 3) : Vt.x i ∈ D0 q :=
  Finset.mem_filter.mpr ⟨mem_univ _, rfl⟩
@[simp] theorem mem_D0_l (i : Fin 3) : Vt.l i ∈ D0 q :=
  Finset.mem_filter.mpr ⟨mem_univ _, rfl⟩
@[simp] theorem mem_D0_w : Vt.w ∈ D0 q :=
  Finset.mem_filter.mpr ⟨mem_univ _, rfl⟩
@[simp] theorem not_mem_D0_k (j : Fin q) : Vt.k j ∉ D0 q := by
  unfold D0; rw [Finset.mem_filter]; simp [isD0]
@[simp] theorem not_mem_D0_y (a : Fin 2) : Vt.y a ∉ D0 q := by
  unfold D0; rw [Finset.mem_filter]; simp [isD0]

theorem card_D0 : (D0 q).card = 7 := by
  rw [card_eq_filter, card_filter_univ]; simp

theorem twoDom_D0 : W213.IsTwoDominating (F q) (D0 q) := by
  intro v hv
  rw [card_filter_adj, card_filter_univ]
  cases v <;> simp [adjB] at hv ⊢

section LowerBound

variable (D : Finset (Vt q))

/-- `a = |D ∩ X|`, `b = |D ∩ K|`, `e = |D ∩ {w}|`, `f = |D ∩ Y|`, `c = |D ∩ L|`. -/
def cX : ℕ := (univ.filter (fun i : Fin 3 => Vt.x i ∈ D)).card
def cL : ℕ := (univ.filter (fun i : Fin 3 => Vt.l i ∈ D)).card
def cK : ℕ := (univ.filter (fun j : Fin q => Vt.k j ∈ D)).card
def cW : ℕ := if Vt.w ∈ D then 1 else 0
def cY : ℕ := (univ.filter (fun a : Fin 2 => Vt.y a ∈ D)).card

theorem card_D_eq : D.card = cX D + cL D + cK D + cW D + cY D := by
  rw [card_eq_filter, card_filter_univ]; rfl

theorem cX_le : cX D ≤ 3 := (Finset.card_filter_le _ _).trans (by simp)
theorem cY_le : cY D ≤ 2 := (Finset.card_filter_le _ _).trans (by simp)
theorem cW_le : cW D ≤ 1 := by unfold cW; split_ifs <;> omega

theorem nb_l (i : Fin 3) : (D.filter ((F q).Adj (.l i))).card ≤ 1 := by
  rw [card_filter_adj, card_filter_univ]
  simp only [adjB]
  simp only [decide_eq_true_eq, Bool.false_eq_true, and_false, filter_false, card_empty,
    add_zero, ↓reduceIte]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  rw [← ha.2, ← hb.2]

theorem nb_w : (D.filter ((F q).Adj .w)).card = cK D := by
  rw [card_filter_adj, card_filter_univ]; simp [adjB, cK]

theorem nb_y (a : Fin 2) : (D.filter ((F q).Adj (.y a))).card = cX D := by
  rw [card_filter_adj, card_filter_univ]; simp [adjB, cX]

theorem nb_x (i : Fin 3) : (D.filter ((F q).Adj (.x i))).card ≤ 1 + cK D + cY D := by
  rw [card_filter_adj, card_filter_univ]
  simp only [adjB]
  simp only [Bool.false_eq_true, and_false, filter_false, card_empty, decide_eq_true_eq,
    zero_add, and_true, ↓reduceIte, add_zero]
  have : (univ.filter (fun i' : Fin 3 => Vt.l i' ∈ D ∧ i = i')).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rw [← ha.2, ← hb.2]
  unfold cK cY
  omega

theorem nb_k (j : Fin q) : (D.filter ((F q).Adj (.k j))).card ≤ cX D + cK D + cW D := by
  rw [card_filter_adj, card_filter_univ]
  simp only [adjB]
  simp only [and_true, Bool.false_eq_true, and_false, filter_false, card_empty, add_zero, ne_eq,
    decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  have : (univ.filter (fun j' : Fin q => Vt.k j' ∈ D ∧ ¬ j = j')).card ≤ cK D :=
    Finset.card_le_card (fun j' h => by
      simp only [mem_filter, mem_univ, true_and] at h ⊢; exact h.1)
  unfold cX cW
  omega

theorem filter_eq_univ_of_card {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (h : (univ.filter p).card < n) : ∃ a, ¬ p a := by
  by_contra hc
  push Not at hc
  rw [Finset.filter_true_of_mem (fun a _ => hc a), Finset.card_univ, Fintype.card_fin] at h
  omega

theorem seven_le_card (hD : W213.IsTwoDominating (F q) D) (hq : 1 ≤ q) : 7 ≤ D.card := by
  have hX := cX_le D
  have hY := cY_le D
  have hW := cW_le D
  -- the leaves lie in every 2-dominating set
  have hL : cL D = 3 := by
    unfold cL
    rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    intro i _
    by_contra hi
    have := hD _ hi
    have := nb_l D i
    omega
  -- (i) w ∉ D forces two vertices of K in D
  have h1 : cW D = 1 ∨ 2 ≤ cK D := by
    by_cases hw : Vt.w ∈ D
    · left; simp [cW, hw]
    · right; have := hD _ hw; rwa [nb_w] at this
  -- (ii) some y_a ∉ D forces two vertices of X in D
  have h2 : cY D = 2 ∨ 2 ≤ cX D := by
    by_cases hy : cY D = 2
    · exact Or.inl hy
    · right
      obtain ⟨a, ha⟩ := filter_eq_univ_of_card (fun a : Fin 2 => Vt.y a ∈ D)
        (lt_of_le_of_ne hY hy)
      have := hD _ ha; rwa [nb_y] at this
  -- (iii) some x_i ∉ D needs a neighbour in K ∪ Y besides l_i
  have h3 : cX D = 3 ∨ 1 ≤ cK D + cY D := by
    by_cases hx : cX D = 3
    · exact Or.inl hx
    · right
      obtain ⟨i, hi⟩ := filter_eq_univ_of_card (fun i : Fin 3 => Vt.x i ∈ D)
        (lt_of_le_of_ne hX hx)
      have := hD _ hi; have := nb_x D i; omega
  -- (iv) if D misses K, a vertex k_j ∉ D needs two neighbours in X ∪ {w}
  have h4 : 1 ≤ cK D ∨ 2 ≤ cX D + cW D := by
    by_cases hk : 1 ≤ cK D
    · exact Or.inl hk
    · right
      obtain ⟨j, hj⟩ := filter_eq_univ_of_card (fun j : Fin q => Vt.k j ∈ D)
        (by unfold cK at hk; omega)
      have := hD _ hj; have := nb_k D j; omega
  rw [card_D_eq]
  omega

end LowerBound

theorem gamma2_F (hq : 1 ≤ q) : W213.gamma2 (F q) = 7 := by
  apply le_antisymm
  · exact (W213.gamma2_le (F q) twoDom_D0).trans card_D0.le
  · exact (W213.le_gamma2_iff (F q) 7).mpr (fun D hD => seven_le_card D hD hq)

/-! ## Theorem 1 -/

/-- `F q` violates the inequality: `gamma_2 = 7 > 6 = WP(complement) + ⌊3/4⌋`. -/
theorem F_violates (hq : 3 ≤ q) : wpCompl (F q) + 3 / alphaA3 (F q) < W213.gamma2 (F q) := by
  rw [wpCompl_F hq, alphaA3_F hq, gamma2_F (by omega)]; norm_num

/-- Theorem 1 of the paper, for every `q ≥ 3`. -/
theorem theorem1 (hq : 3 ≤ q) :
    (F q).Connected ∧ Fintype.card (Vt q) = q + 9 ∧ W213.gamma2 (F q) = 7 ∧
      wpCompl (F q) = 6 ∧ alphaA3 (F q) = 4 ∧
      wpCompl (F q) + 3 / alphaA3 (F q) < W213.gamma2 (F q) :=
  ⟨F_connected (by omega), card_Vt, gamma2_F (by omega), wpCompl_F hq, alphaA3_F hq,
    F_violates hq⟩

/-- Every `F q` (`q ≥ 3`) meets all hypotheses of `Conjecture399bStatement` and fails its
conclusion. -/
theorem F_not_conjecture_inequality (hq : 3 ≤ q) :
    (F q).Connected ∧ 2 < Fintype.card (Vt q) ∧ 0 < alphaA3 (F q) ∧
      ¬ W213.gamma2 (F q) ≤ wpCompl (F q) + 3 / alphaA3 (F q) :=
  ⟨F_connected (by omega), by rw [card_Vt]; omega, by rw [alphaA3_F hq]; omega,
    not_le.mpr (F_violates hq)⟩

/-- Conjecture 399b is false; refuted by `F q` for any chosen `q ≥ 3`. -/
theorem not_conjecture399b_family (hq : 3 ≤ q) : ¬ Conjecture399bStatement := by
  intro h
  obtain ⟨hc, hn, ha, hneg⟩ := F_not_conjecture_inequality hq
  exact hneg (h (Vt q) (F q) hc hn ha)

end W399b.Family

#print axioms W399b.Family.theorem1
#print axioms W399b.Family.not_conjecture399b_family
#print axioms W399b.Family.gamma2_F
#print axioms W399b.Family.wpCompl_F
#print axioms W399b.Family.wpCompl_F_via_sorted
#print axioms W399b.Family.sortedDegrees_F
#print axioms W399b.Family.alphaA3_F
#print axioms W399b.Family.F_connected
#print axioms W399b.Family.card_Vt

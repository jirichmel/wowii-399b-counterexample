/-
# Definitions for Conjecture 213 (Graffiti.pc, Written on the Wall II)

Conjecture 213 (as catalogued): "If G is a simple connected graph with n > 1 such that
2 + the lower median of the degree sequence of the complement of G <= gamma_2(complement of G),
then G has a Hamiltonian path."

This file contains only definitions and their basic lemmas (no sorry):
* `IsTwoDominating`, `gamma2` (2-domination number) with attainment and minimality;
* `lowerMedianOf`, `lowerMedian` (lower median of the degree sequence) with the counting
  characterisations of Fact A (both directions);
* `IsClosedGraph`, `Traceable`, and the statement `Conjecture213Statement` (not proved here).

Working text for an unpublished project; nothing here has been published.
-/
import Mathlib

namespace W213

set_option linter.unusedSectionVars false

open Finset

universe u

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 2-domination -/

section TwoDom

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- "gamma_2 = 2-domination number: the smallest D such that every vertex is in D or adjacent
to 2 vertices of D." A set `D` is 2-dominating if every vertex not in `D` has at least two
neighbours in `D`. -/
def IsTwoDominating (D : Finset V) : Prop :=
  ∀ v, v ∉ D → 2 ≤ (D.filter (G.Adj v)).card

instance (D : Finset V) : Decidable (IsTwoDominating G D) := by
  unfold IsTwoDominating; infer_instance

theorem isTwoDominating_univ : IsTwoDominating G (Finset.univ : Finset V) := by
  intro v hv
  exact absurd (Finset.mem_univ v) hv

theorem exists_twoDominating_card : ∃ k, ∃ D : Finset V, IsTwoDominating G D ∧ D.card = k :=
  ⟨_, _, isTwoDominating_univ G, rfl⟩

/-- The 2-domination number: "the smallest D such that every vertex is in D or adjacent to
2 vertices of D", i.e. the least cardinality of a 2-dominating set. -/
noncomputable def gamma2 : ℕ :=
  @Nat.find _ (Classical.decPred _) (exists_twoDominating_card G)

/-- `gamma2` is attained by some 2-dominating set. -/
theorem gamma2_spec : ∃ D : Finset V, IsTwoDominating G D ∧ D.card = gamma2 G :=
  @Nat.find_spec _ (Classical.decPred _) (exists_twoDominating_card G)

/-- `gamma2` is at most the size of every 2-dominating set. -/
theorem gamma2_le {D : Finset V} (hD : IsTwoDominating G D) : gamma2 G ≤ D.card :=
  @Nat.find_min' _ (Classical.decPred _) (exists_twoDominating_card G) _ ⟨D, hD, rfl⟩

/-- Characterisation: `gamma2 G ≤ k` iff some 2-dominating set has at most `k` vertices. -/
theorem gamma2_le_iff (k : ℕ) :
    gamma2 G ≤ k ↔ ∃ D : Finset V, IsTwoDominating G D ∧ D.card ≤ k := by
  constructor
  · intro h
    obtain ⟨D, hD, hc⟩ := gamma2_spec G
    exact ⟨D, hD, hc ▸ h⟩
  · rintro ⟨D, hD, hc⟩
    exact (gamma2_le G hD).trans hc

/-- Characterisation: `k ≤ gamma2 G` iff every 2-dominating set has at least `k` vertices. -/
theorem le_gamma2_iff (k : ℕ) :
    k ≤ gamma2 G ↔ ∀ D : Finset V, IsTwoDominating G D → k ≤ D.card := by
  constructor
  · intro h D hD
    exact h.trans (gamma2_le G hD)
  · intro h
    obtain ⟨D, hD, hc⟩ := gamma2_spec G
    exact hc ▸ h D hD

theorem gamma2_le_card : gamma2 G ≤ Fintype.card V := by
  simpa using gamma2_le G (isTwoDominating_univ G)

end TwoDom

/-! ## Sorted lists of naturals: counting lemmas -/

section SortedList

theorem sorted_le_getElem {L : List ℕ} (hs : L.Pairwise (· ≤ ·)) {i j : ℕ}
    (hi : i < L.length) (hj : j < L.length) (hij : i ≤ j) : L[i] ≤ L[j] := by
  rcases Nat.eq_or_lt_of_le hij with h | h
  · subst h; exact le_rfl
  · exact List.pairwise_iff_getElem.mp hs i j hi hj h

/-- In a nondecreasing list, the entry at index `k` is `≤ t` iff at least `k+1` entries are
`≤ t`. -/
theorem sorted_getElem_le_iff {L : List ℕ} (hs : L.Pairwise (· ≤ ·)) {k : ℕ}
    (hk : k < L.length) (t : ℕ) :
    L[k] ≤ t ↔ k + 1 ≤ L.countP (fun x => decide (x ≤ t)) := by
  constructor
  · intro h
    have hall : ∀ x ∈ L.take (k + 1), decide (x ≤ t) = true := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
      have hj' : j ≤ k := by omega
      simpa using (sorted_le_getElem hs _ hk hj').trans h
    have h1 := (List.countP_eq_length).mpr hall
    have h2 := (List.take_sublist (k + 1) L).countP_le (p := fun x => decide (x ≤ t))
    rw [h1, List.length_take] at h2
    omega
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have hnone : ∀ x ∈ L.drop k, ¬ decide (x ≤ t) = true := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hx
      have := sorted_le_getElem hs hk (show k + j < L.length by omega) (Nat.le_add_right k j)
      simp only [decide_eq_true_eq, not_le]
      omega
    have h0 := (List.countP_eq_zero).mpr hnone
    have hsplit := List.countP_append (p := fun x => decide (x ≤ t)) (l₁ := L.take k) (l₂ := L.drop k)
    rw [List.take_append_drop, h0] at hsplit
    have h3 := List.countP_le_length (p := fun x => decide (x ≤ t)) (l := L.take k)
    rw [List.length_take] at h3
    omega

/-- In a nondecreasing list of length `N`, `t ≤` the entry at index `k` iff at least `N - k`
entries are `≥ t`. -/
theorem le_sorted_getElem_iff {L : List ℕ} (hs : L.Pairwise (· ≤ ·)) {k : ℕ}
    (hk : k < L.length) (t : ℕ) :
    t ≤ L[k] ↔ L.length - k ≤ L.countP (fun x => decide (t ≤ x)) := by
  constructor
  · intro h
    have hall : ∀ x ∈ L.drop k, decide (t ≤ x) = true := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hx
      simpa using h.trans
        (sorted_le_getElem hs hk (show k + j < L.length by omega) (Nat.le_add_right k j))
    have h1 := (List.countP_eq_length).mpr hall
    have h2 := (List.drop_sublist k L).countP_le (p := fun x => decide (t ≤ x))
    rw [h1, List.length_drop] at h2
    omega
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have hnone : ∀ x ∈ L.take (k + 1), ¬ decide (t ≤ x) = true := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
      have := sorted_le_getElem hs (by omega) hk (show j ≤ k by omega)
      simp only [decide_eq_true_eq, not_le]
      omega
    have h0 := (List.countP_eq_zero).mpr hnone
    have hsplit := List.countP_append (p := fun x => decide (t ≤ x)) (l₁ := L.take (k + 1))
      (l₂ := L.drop (k + 1))
    rw [List.take_append_drop, h0] at hsplit
    have h3 := List.countP_le_length (p := fun x => decide (t ≤ x)) (l := L.drop (k + 1))
    rw [List.length_drop] at h3
    omega

end SortedList

/-! ## Lower median -/

section Median

/-- The values `f v` sorted in nondecreasing order: `d_1 ≤ d_2 ≤ ... ≤ d_n`. -/
def sortedValues (f : V → ℕ) : List ℕ :=
  (Finset.univ.val.map f).sort (· ≤ ·)

theorem sortedValues_pairwise (f : V → ℕ) : (sortedValues f).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _

theorem length_sortedValues (f : V → ℕ) : (sortedValues f).length = Fintype.card V := by
  simp [sortedValues, Multiset.length_sort, Finset.card_univ]

theorem countP_sortedValues (f : V → ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (sortedValues f).countP (fun x => decide (p x)) =
      (Finset.univ.filter (fun v => p (f v))).card := by
  have h1 : Multiset.countP p (Finset.univ.val.map f) =
      (sortedValues f).countP (fun x => decide (p x)) := by
    rw [sortedValues]
    conv_lhs => rw [← Multiset.sort_eq (Finset.univ.val.map f) (· ≤ ·)]
    rw [Multiset.coe_countP]
  rw [← h1, Multiset.countP_map]
  rfl

/-- The lower median of a family of values `f : V → ℕ`: with the values in nondecreasing
order `d_1 ≤ ... ≤ d_n`, it is `d_{⌈n/2⌉}` (1-based), i.e. index `⌈n/2⌉ - 1 = (n+1)/2 - 1`
(0-based). For `n = 0` it is `0` (a junk value; never used). -/
def lowerMedianOf (f : V → ℕ) : ℕ :=
  (sortedValues f).getD ((Fintype.card V + 1) / 2 - 1) 0

/-- "The lower median of the degree sequence" of `G`: with the degrees in nondecreasing order
`d_1 ≤ ... ≤ d_n`, the lower median is `d_{⌈n/2⌉}` (`d_{n/2}` for even `n`, the median for
odd `n`). -/
def lowerMedian (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  lowerMedianOf (fun v => G.degree v)

theorem lowerMedianOf_eq_getElem (f : V → ℕ) (hn : 0 < Fintype.card V) :
    ∃ h : (Fintype.card V + 1) / 2 - 1 < (sortedValues f).length,
      lowerMedianOf f = (sortedValues f)[(Fintype.card V + 1) / 2 - 1] := by
  have h : (Fintype.card V + 1) / 2 - 1 < (sortedValues f).length := by
    rw [length_sortedValues]; omega
  exact ⟨h, by simp [lowerMedianOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]⟩

/-- Fact A (i), both directions: `lowerMedianOf f ≤ t` iff at least `⌈n/2⌉` vertices have
value `≤ t`. Holds also for `n = 0`. -/
theorem lowerMedianOf_le_iff (f : V → ℕ) (t : ℕ) :
    lowerMedianOf f ≤ t ↔
      (Fintype.card V + 1) / 2 ≤ (Finset.univ.filter (fun v => f v ≤ t)).card := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
  · have : lowerMedianOf f = 0 := by
      have hl : (sortedValues f) = [] := by
        rw [← List.length_eq_zero_iff, length_sortedValues, hn]
      simp [lowerMedianOf, hl]
    rw [this, hn]; simp
  · obtain ⟨hk, heq⟩ := lowerMedianOf_eq_getElem f hn
    rw [heq, sorted_getElem_le_iff (sortedValues_pairwise f) hk t,
      countP_sortedValues f (fun x => x ≤ t)]
    constructor <;> intro h <;> omega

/-- Fact A (ii), both directions: `t ≤ lowerMedianOf f` iff at least `⌊n/2⌋ + 1` vertices have
value `≥ t` (for `n ≥ 1`). -/
theorem le_lowerMedianOf_iff (f : V → ℕ) (hn : 0 < Fintype.card V) (t : ℕ) :
    t ≤ lowerMedianOf f ↔
      Fintype.card V / 2 + 1 ≤ (Finset.univ.filter (fun v => t ≤ f v)).card := by
  obtain ⟨hk, heq⟩ := lowerMedianOf_eq_getElem f hn
  rw [heq, le_sorted_getElem_iff (sortedValues_pairwise f) hk t,
    countP_sortedValues f (fun x => t ≤ x), length_sortedValues]
  have : Fintype.card V - ((Fintype.card V + 1) / 2 - 1) = Fintype.card V / 2 + 1 := by omega
  rw [this]

/-- Fact A (i), the direction used in the proof. -/
theorem card_le_of_lowerMedianOf_le (f : V → ℕ) {t : ℕ} (h : lowerMedianOf f ≤ t) :
    (Fintype.card V + 1) / 2 ≤ (Finset.univ.filter (fun v => f v ≤ t)).card :=
  (lowerMedianOf_le_iff f t).mp h

/-- Fact A (ii), the direction used in the proof. -/
theorem card_ge_of_le_lowerMedianOf (f : V → ℕ) (hn : 0 < Fintype.card V) {t : ℕ}
    (h : t ≤ lowerMedianOf f) :
    Fintype.card V / 2 + 1 ≤ (Finset.univ.filter (fun v => t ≤ f v)).card :=
  (le_lowerMedianOf_iff f hn t).mp h

/-- The lower median is itself the value of some vertex (for `n ≥ 1`). -/
theorem exists_eq_lowerMedianOf (f : V → ℕ) (hn : 0 < Fintype.card V) :
    ∃ v, f v = lowerMedianOf f := by
  obtain ⟨hk, heq⟩ := lowerMedianOf_eq_getElem f hn
  have hmem : lowerMedianOf f ∈ sortedValues f := by
    rw [heq]; exact List.getElem_mem hk
  have : lowerMedianOf f ∈ (Finset.univ.val.map f) := by
    rw [← Multiset.sort_eq (Finset.univ.val.map f) (· ≤ ·)]
    exact Multiset.mem_coe.mpr hmem
  obtain ⟨v, -, hv⟩ := Multiset.mem_map.mp this
  exact ⟨v, hv⟩

/-- Monotonicity (used in Lemma M): if `f ≤ g` pointwise then the lower median of `f` is at most
that of `g`. -/
theorem lowerMedianOf_mono {f g : V → ℕ} (hfg : ∀ v, f v ≤ g v) :
    lowerMedianOf f ≤ lowerMedianOf g := by
  rw [lowerMedianOf_le_iff]
  have h := (lowerMedianOf_le_iff g (lowerMedianOf g)).mp le_rfl
  refine h.trans (Finset.card_le_card ?_)
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact (hfg v).trans hv

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Fact A (i) for `lowerMedian`, both directions. -/
theorem lowerMedian_le_iff (t : ℕ) :
    lowerMedian G ≤ t ↔
      (Fintype.card V + 1) / 2 ≤ (Finset.univ.filter (fun v => G.degree v ≤ t)).card :=
  lowerMedianOf_le_iff _ t

/-- Fact A (ii) for `lowerMedian`, both directions (`n ≥ 1`). -/
theorem le_lowerMedian_iff (hn : 0 < Fintype.card V) (t : ℕ) :
    t ≤ lowerMedian G ↔
      Fintype.card V / 2 + 1 ≤ (Finset.univ.filter (fun v => t ≤ G.degree v)).card :=
  le_lowerMedianOf_iff _ hn t

/-- Fact A (i): if `lowerMedian G ≤ t`, at least `⌈n/2⌉` vertices have degree `≤ t`. -/
theorem card_degree_le_of_lowerMedian_le {t : ℕ} (h : lowerMedian G ≤ t) :
    (Fintype.card V + 1) / 2 ≤ (Finset.univ.filter (fun v => G.degree v ≤ t)).card :=
  (lowerMedian_le_iff G t).mp h

/-- Fact A (ii): if `t ≤ lowerMedian G`, at least `⌊n/2⌋ + 1` vertices have degree `≥ t`. -/
theorem card_degree_ge_of_le_lowerMedian (hn : 0 < Fintype.card V) {t : ℕ}
    (h : t ≤ lowerMedian G) :
    Fintype.card V / 2 + 1 ≤ (Finset.univ.filter (fun v => t ≤ G.degree v)).card :=
  (le_lowerMedian_iff G hn t).mp h

theorem exists_degree_eq_lowerMedian (hn : 0 < Fintype.card V) :
    ∃ v, G.degree v = lowerMedian G :=
  exists_eq_lowerMedianOf _ hn

/-- Monotonicity of `lowerMedian` under pointwise degree comparison (used in Lemma M). -/
theorem lowerMedian_mono {G' : SimpleGraph V} [DecidableRel G'.Adj]
    (h : ∀ v, G'.degree v ≤ G.degree v) : lowerMedian G' ≤ lowerMedian G :=
  lowerMedianOf_mono h

end Median

/-! ## Closed graphs, traceability, the statement -/

section Rest

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `G` is *closed* (Bondy-Chvátal closure is `G` itself, in the form used by the proof):
"d(u) + d(v) <= n - 2 for all distinct non-adjacent u, v". -/
def IsClosedGraph : Prop :=
  ∀ u v, u ≠ v → ¬ G.Adj u v → G.degree u + G.degree v ≤ Fintype.card V - 2

/-- `G` has a Hamiltonian path: "G has a Hamiltonian path", i.e. some walk visits every vertex
exactly once. -/
def Traceable : Prop :=
  ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

end Rest

/-- Conjecture 213 (Graffiti.pc, Written on the Wall II): "If G is a simple connected graph with
n > 1 such that 2 + the lower median of the degree sequence of the complement of G <=
gamma_2(complement of G), then G has a Hamiltonian path." Stated here, not proved. -/
def Conjecture213Statement : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → 1 < Fintype.card V → lowerMedian Gᶜ + 2 ≤ gamma2 Gᶜ → Traceable G

end W213

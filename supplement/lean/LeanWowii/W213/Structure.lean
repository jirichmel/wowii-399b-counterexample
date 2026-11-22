/-
# Structure in Setting S (Lemma G (a)-(g) and Lemma 3) for Conjecture 213

Source: `conjectures/wowii213_conjR_round_inprogress/prover-claimC/proof.md`, Section 4.

Setting S: `G` closed, connected, not complete, and `2 * m ≤ n - 1` where `m = lowerMedian Gᶜ`.
Sets (all `Finset V`):
* `setT G = {v : Gᶜ.degree v ≤ m}`;
* `setQ G = {v : m ≤ G.degree v}`;
* `setU G = {v : G.degree v = n - 1}` (universal vertices);
* `setY G = {v : G.degree v < m}` (= complement of `setQ G`);
* `setP G = setQ G \ setU G`;
* `rS G = m - |U| + 1`.

Each lemma states only the hypotheses it needs; `SettingS G` bundles all of them.
Working text for an unpublished project; nothing here has been published.
-/
import LeanWowii.W213.Defs

namespace W213

set_option linter.unusedSectionVars false

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Definitions -/

/-- `T = {v : d_H(v) ≤ m}` with `H = Gᶜ`, `m = lowerMedian Gᶜ`. -/
def setT : Finset V := univ.filter (fun v => Gᶜ.degree v ≤ lowerMedian Gᶜ)

/-- `Q = {v : m ≤ d(v)}`. -/
def setQ : Finset V := univ.filter (fun v => lowerMedian Gᶜ ≤ G.degree v)

/-- `U = {v : d(v) = n - 1}`, the universal vertices. -/
def setU : Finset V := univ.filter (fun v => G.degree v = Fintype.card V - 1)

/-- `Y = V \ Q = {v : d(v) ≤ m - 1}`. -/
def setY : Finset V := univ.filter (fun v => G.degree v < lowerMedian Gᶜ)

/-- `P = Q \ U`. -/
def setP : Finset V := setQ G \ setU G

/-- `r = m - u + 1`. -/
def rS : ℕ := lowerMedian Gᶜ - (setU G).card + 1

/-- Setting S of the proof. -/
structure SettingS : Prop where
  closed : IsClosedGraph G
  connected : G.Connected
  ne_top : G ≠ ⊤
  two_m : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1

variable {G}

@[simp] theorem mem_setT {v : V} : v ∈ setT G ↔ Gᶜ.degree v ≤ lowerMedian Gᶜ := by
  simp [setT]

@[simp] theorem mem_setQ {v : V} : v ∈ setQ G ↔ lowerMedian Gᶜ ≤ G.degree v := by
  simp [setQ]

@[simp] theorem mem_setU {v : V} : v ∈ setU G ↔ G.degree v = Fintype.card V - 1 := by
  simp [setU]

@[simp] theorem mem_setY {v : V} : v ∈ setY G ↔ G.degree v < lowerMedian Gᶜ := by
  simp [setY]

@[simp] theorem mem_setP {v : V} :
    v ∈ setP G ↔ lowerMedian Gᶜ ≤ G.degree v ∧ G.degree v ≠ Fintype.card V - 1 := by
  simp [setP]

theorem mem_setY_iff_not_mem_setQ {v : V} : v ∈ setY G ↔ v ∉ setQ G := by
  simp

theorem setY_eq_compl : setY G = (setQ G)ᶜ := by
  ext v; simp

/-! ## Basic graph facts -/

theorem degree_le_card_sub_one (v : V) : G.degree v ≤ Fintype.card V - 1 := by
  have := G.degree_lt_card_verts v; omega

theorem degree_compl_eq (v : V) : Gᶜ.degree v = Fintype.card V - 1 - G.degree v :=
  SimpleGraph.degree_compl G v

theorem adj_of_mem_setU {u w : V} (hu : u ∈ setU G) (huw : u ≠ w) : G.Adj u w := by
  have h : G.IsUniversal u := (G.degree_eq_card_sub_one u).mp (mem_setU.mp hu)
  exact h huw

/-- A vertex that is not universal has a non-neighbour. -/
theorem exists_nonadj_of_not_mem_setU {v : V} (hv : v ∉ setU G) :
    ∃ w, v ≠ w ∧ ¬ G.Adj v w := by
  have h : ¬ G.IsUniversal v := by
    intro h; exact hv (mem_setU.mpr ((G.degree_eq_card_sub_one v).mpr h))
  simp only [SimpleGraph.IsUniversal, not_forall] at h
  obtain ⟨w, hw, hna⟩ := h
  exact ⟨w, hw, hna⟩

/-- In a connected graph with at least two vertices, every vertex has degree at least 1. -/
theorem degree_pos_of_connected (hc : G.Connected) (hn : 1 < Fintype.card V) (v : V) :
    0 < G.degree v := by
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hn v
  obtain ⟨p⟩ := hc.preconnected v w
  rw [SimpleGraph.degree_pos_iff_exists_adj]
  cases p with
  | nil => exact absurd rfl hw
  | cons h _ => exact ⟨_, h⟩

/-- A non-complete graph has two distinct non-adjacent vertices. -/
theorem exists_nonadj_of_ne_top (h : G ≠ ⊤) : ∃ a b : V, a ≠ b ∧ ¬ G.Adj a b := by
  by_contra hc
  push Not at hc
  apply h
  ext a b
  simp only [SimpleGraph.top_adj]
  exact ⟨fun hab => G.ne_of_adj hab, fun hab => hc a b hab⟩

theorem one_lt_card_of_ne_top (h : G ≠ ⊤) : 1 < Fintype.card V := by
  obtain ⟨a, b, hab, -⟩ := exists_nonadj_of_ne_top h
  exact Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩

/-- The number of `Gᶜ`-neighbours of `v` inside `D` plus the number of `G`-neighbours of `v`
inside `D` is `|D|`, when `v ∉ D`. -/
theorem card_filter_compl_add (D : Finset V) {v : V} (hv : v ∉ D) :
    (D.filter (Gᶜ.Adj v)).card + (D.filter (G.Adj v)).card = D.card := by
  have h1 : D.filter (Gᶜ.Adj v) = D.filter (fun w => ¬ G.Adj v w) := by
    apply Finset.filter_congr
    intro w hw
    rw [SimpleGraph.compl_adj]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨fun e => hv (e ▸ hw), h⟩
  rw [h1, add_comm]
  exact Finset.card_filter_add_card_filter_not _

theorem card_filter_adj_le_degree (D : Finset V) (v : V) :
    (D.filter (G.Adj v)).card ≤ G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter] at hw
  simpa using hw.2

/-! ## Lemma G -/

section LemmaG

/-- Lemma G (a): `|T| ≥ ⌈n/2⌉`. -/
theorem card_setT : (Fintype.card V + 1) / 2 ≤ (setT G).card :=
  card_degree_le_of_lowerMedian_le Gᶜ le_rfl

/-- Lemma G (a): `T ⊆ Q` when `2m ≤ n - 1`. -/
theorem setT_subset_setQ (hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1) : setT G ⊆ setQ G := by
  intro v hv
  rw [mem_setT, degree_compl_eq] at hv
  rw [mem_setQ]
  have := degree_le_card_sub_one (G := G) v
  omega

/-- A vertex of `T` has degree at least `n - 1 - m`. -/
theorem degree_ge_of_mem_setT {v : V} (hv : v ∈ setT G) :
    Fintype.card V - 1 - lowerMedian Gᶜ ≤ G.degree v := by
  rw [mem_setT, degree_compl_eq] at hv
  have := degree_le_card_sub_one (G := G) v
  omega

/-- Lemma G (b): `Q` is a clique of `G`. Only closedness is needed: the proof's use of
`2m ≤ n - 1` (to get `T ⊆ Q`) can be avoided, since `t ∈ T` and `x ∈ Q` already give
`d(t) + d(x) ≥ n - 1`. -/
theorem setQ_adj (hcl : IsClosedGraph G)
    {a b : V} (ha : a ∈ setQ G) (hb : b ∈ setQ G) (hab : a ≠ b) : G.Adj a b := by
  have hn : 1 < Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
  -- a vertex of T is adjacent to every other vertex of Q
  have key : ∀ t x, t ∈ setT G → x ∈ setQ G → t ≠ x → G.Adj t x := by
    intro t x ht hx htx
    by_contra hna
    have h1 := hcl t x htx hna
    have h2 := degree_ge_of_mem_setT ht
    rw [mem_setQ] at hx
    omega
  by_contra hna
  by_cases haT : a ∈ setT G
  · exact hna (key a b haT hb hab)
  by_cases hbT : b ∈ setT G
  · exact hna (G.adj_symm (key b a hbT ha hab.symm))
  -- neither is in T: both are adjacent to all of T
  have hdeg : ∀ x, x ∈ setQ G → x ∉ setT G → (setT G).card ≤ G.degree x := by
    intro x hx hxT
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro t ht
    rw [SimpleGraph.mem_neighborFinset]
    exact G.adj_symm (key t x ht hx (fun e => hxT (e ▸ ht)))
  have h1 := hdeg a ha haT
  have h2 := hdeg b hb hbT
  have h3 := hcl a b hab hna
  have h4 := card_setT (G := G)
  omega

/-- Lemma G (d), first part: every non-neighbour of a vertex of `Q` lies in `Y`. -/
theorem mem_setY_of_nonadj (hcl : IsClosedGraph G)
    {q w : V} (hq : q ∈ setQ G) (hqw : q ≠ w) (hna : ¬ G.Adj q w) : w ∈ setY G := by
  rw [mem_setY_iff_not_mem_setQ]
  intro hw
  exact hna (setQ_adj hcl hq hw hqw)

/-- Lemma G (d), in complement form: every `Gᶜ`-neighbour of a vertex of `Q` lies in `Y`. -/
theorem mem_setY_of_compl_adj (hcl : IsClosedGraph G)
    {q w : V} (hq : q ∈ setQ G) (h : Gᶜ.Adj q w) : w ∈ setY G := by
  rw [SimpleGraph.compl_adj] at h
  exact mem_setY_of_nonadj hcl hq h.1 h.2

/-- Lemma G (c): `U ⊆ Q`. -/
theorem setU_subset_setQ (hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1) : setU G ⊆ setQ G := by
  intro v hv
  rw [mem_setU] at hv
  rw [mem_setQ]
  omega

/-- Lemma G (c): `Y` is nonempty when `G` is closed and not complete. -/
theorem setY_nonempty (hcl : IsClosedGraph G) (hne : G ≠ ⊤) : (setY G).Nonempty := by
  obtain ⟨a, b, hab, hna⟩ := exists_nonadj_of_ne_top hne
  by_contra hY
  rw [Finset.not_nonempty_iff_eq_empty] at hY
  have hQ : ∀ v, v ∈ setQ G := by
    intro v
    by_contra hv
    have : v ∈ setY G := mem_setY_iff_not_mem_setQ.mpr hv
    rw [hY] at this
    simp at this
  exact hna (setQ_adj hcl (hQ a) (hQ b) hab)

/-- Lemma G (c): every `y ∈ Y` is adjacent to every vertex of `U`. -/
theorem adj_setU_of_mem_setY (hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1)
    {y u : V} (hy : y ∈ setY G) (hu : u ∈ setU G) : G.Adj y u := by
  have hyu : u ≠ y := by
    rintro rfl
    rw [mem_setY] at hy
    rw [mem_setU] at hu
    omega
  exact G.adj_symm (adj_of_mem_setU hu hyu)

/-- Lemma G (c): `U ⊆ N(y)` for `y ∈ Y`. -/
theorem setU_subset_neighborFinset (hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1)
    {y : V} (hy : y ∈ setY G) : setU G ⊆ G.neighborFinset y := by
  intro u hu
  rw [SimpleGraph.mem_neighborFinset]
  exact adj_setU_of_mem_setY hm hy hu

/-- Lemma G (c): `u ≤ d(y) ≤ m - 1` for `y ∈ Y` (stated as `u ≤ d(y)` and `d(y) + 1 ≤ m`). -/
theorem card_setU_le_degree (hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1)
    {y : V} (hy : y ∈ setY G) : (setU G).card ≤ G.degree y := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_le_card (setU_subset_neighborFinset hm hy)

theorem degree_add_one_le_of_mem_setY {y : V} (hy : y ∈ setY G) :
    G.degree y + 1 ≤ lowerMedian Gᶜ := by
  rw [mem_setY] at hy; omega

/-- Lemma G (c): `u ≤ m - 1`, i.e. `u + 1 ≤ m`. -/
theorem card_setU_add_one_le (hcl : IsClosedGraph G)
    (hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1) (hne : G ≠ ⊤) :
    (setU G).card + 1 ≤ lowerMedian Gᶜ := by
  obtain ⟨y, hy⟩ := setY_nonempty hcl hne
  have h1 := card_setU_le_degree hm hy
  have h2 := degree_add_one_le_of_mem_setY hy
  omega

/-- Lemma G (c): `r ≥ 2`. -/
theorem two_le_rS (hcl : IsClosedGraph G)
    (hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1) (hne : G ≠ ⊤) : 2 ≤ rS G := by
  have := card_setU_add_one_le hcl hm hne
  unfold rS; omega

/-- `r + u = m + 1` (in Setting S). -/
theorem rS_add_card_setU (hcl : IsClosedGraph G)
    (hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1) (hne : G ≠ ⊤) :
    rS G + (setU G).card = lowerMedian Gᶜ + 1 := by
  have := card_setU_add_one_le hcl hm hne
  unfold rS; omega

/-- Lemma G (d), second part: every vertex of `P` has a non-neighbour. -/
theorem exists_nonadj_of_mem_setP {q : V} (hq : q ∈ setP G) : ∃ w, q ≠ w ∧ ¬ G.Adj q w := by
  apply exists_nonadj_of_not_mem_setU
  simp only [setP, Finset.mem_sdiff] at hq
  exact hq.2

/-- Lemma G (e): every vertex of `P` has degree at most `n - 3`. -/
theorem degree_add_three_le_of_mem_setP (hcl : IsClosedGraph G) (hc : G.Connected)
    {q : V} (hq : q ∈ setP G) : G.degree q + 3 ≤ Fintype.card V := by
  obtain ⟨y, hqy, hna⟩ := exists_nonadj_of_mem_setP hq
  have hn : 1 < Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨q, y, hqy⟩
  have h1 := hcl q y hqy hna
  have h2 := degree_pos_of_connected hc hn y
  omega

/-- Lemma G (e): every vertex of `P` has at least two non-neighbours (`Gᶜ`-degree `≥ 2`). -/
theorem two_le_degree_compl_of_mem_setP (hcl : IsClosedGraph G) (hc : G.Connected)
    {q : V} (hq : q ∈ setP G) : 2 ≤ Gᶜ.degree q := by
  have := degree_add_three_le_of_mem_setP hcl hc hq
  rw [degree_compl_eq]
  omega

/-- Lemma G (d)+(e): every vertex `q` of `P` has at least two `Gᶜ`-neighbours inside `Y`. -/
theorem two_le_card_filter_setY_of_mem_setP (hcl : IsClosedGraph G) (hc : G.Connected)
    {q : V} (hq : q ∈ setP G) : 2 ≤ ((setY G).filter (Gᶜ.Adj q)).card := by
  have h := two_le_degree_compl_of_mem_setP hcl hc hq
  have hqQ : q ∈ setQ G := (Finset.mem_sdiff.mp hq).1
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at h
  refine h.trans (Finset.card_le_card ?_)
  intro w hw
  rw [SimpleGraph.mem_neighborFinset] at hw
  exact Finset.mem_filter.mpr ⟨mem_setY_of_compl_adj hcl hqQ hw, hw⟩

/-- Lemma G (d)+(e), for any `D ⊇ Y`: every vertex of `P` has two `Gᶜ`-neighbours in `D`. -/
theorem two_le_card_filter_of_setY_subset (hcl : IsClosedGraph G) (hc : G.Connected)
    {D : Finset V} (hD : setY G ⊆ D)
    {q : V} (hq : q ∈ setP G) : 2 ≤ (D.filter (Gᶜ.Adj q)).card :=
  (two_le_card_filter_setY_of_mem_setP hcl hc hq).trans
    (Finset.card_le_card (Finset.filter_subset_filter _ hD))

/-- Lemma G (f): `|N(y) ∩ P| + u + 1 ≤ m` for `y ∈ Y`. -/
theorem card_filter_setP_add_le (hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1)
    {y : V} (hy : y ∈ setY G) :
    ((setP G).filter (G.Adj y)).card + (setU G).card + 1 ≤ lowerMedian Gᶜ := by
  have hdisj : Disjoint ((setP G).filter (G.Adj y)) (setU G) := by
    rw [Finset.disjoint_left]
    intro v hv hvU
    have := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2
    exact this hvU
  have hsub : (setP G).filter (G.Adj y) ∪ setU G ⊆ G.neighborFinset y := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rw [SimpleGraph.mem_neighborFinset]; exact (Finset.mem_filter.mp hv).2
    · exact setU_subset_neighborFinset hm hy hv
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, SimpleGraph.card_neighborFinset_eq_degree] at h1
  have h2 := degree_add_one_le_of_mem_setY hy
  omega

/-- Lemma G (f): every `y ∈ Y` has at most `r - 2` neighbours in `P`. -/
theorem card_filter_setP_le_rS_sub_two (hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1)
    {y : V} (hy : y ∈ setY G) : ((setP G).filter (G.Adj y)).card ≤ rS G - 2 := by
  have := card_filter_setP_add_le hm hy
  unfold rS; omega

/-- Lemma G (g): `U`, `P`, `Y` are pairwise disjoint. -/
theorem disjoint_setU_setP : Disjoint (setU G) (setP G) := by
  rw [Finset.disjoint_left]
  intro v hU hP
  exact (Finset.mem_sdiff.mp hP).2 hU

theorem disjoint_setP_setY : Disjoint (setP G) (setY G) := by
  rw [Finset.disjoint_left]
  intro v hP hY
  exact (mem_setY_iff_not_mem_setQ.mp hY) (Finset.mem_sdiff.mp hP).1

theorem disjoint_setU_setY (hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1) :
    Disjoint (setU G) (setY G) := by
  rw [Finset.disjoint_left]
  intro v hU hY
  exact (mem_setY_iff_not_mem_setQ.mp hY) (setU_subset_setQ hm hU)

/-- Lemma G (g): every vertex lies in `U`, `P` or `Y`. -/
theorem mem_setU_or_setP_or_setY (v : V) : v ∈ setU G ∨ v ∈ setP G ∨ v ∈ setY G := by
  by_cases hU : v ∈ setU G
  · exact Or.inl hU
  by_cases hQ : v ∈ setQ G
  · exact Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨hQ, hU⟩))
  · exact Or.inr (Or.inr (mem_setY_iff_not_mem_setQ.mpr hQ))

/-- Lemma G (g): `U ∪ P ∪ Y = V`. -/
theorem setU_union_setP_union_setY : setU G ∪ setP G ∪ setY G = Finset.univ := by
  ext v
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  rcases mem_setU_or_setP_or_setY (G := G) v with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- Lemma G (g): `u + |P| + |Y| = n`. -/
theorem card_setU_add_card_setP_add_card_setY (hm : 2 * lowerMedian Gᶜ ≤ Fintype.card V - 1) :
    (setU G).card + (setP G).card + (setY G).card = Fintype.card V := by
  rw [← Finset.card_union_of_disjoint disjoint_setU_setP,
    ← Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨disjoint_setU_setY hm, disjoint_setP_setY⟩),
    setU_union_setP_union_setY, Finset.card_univ]

end LemmaG

/-! ## Lemma 3 -/

/-- Lemma 3: if `y ∈ Y` (i.e. `d(y) ≤ m - 1`), `y ∉ D` and `|D| ≥ m + 1`, then at least two
vertices of `D` are `Gᶜ`-adjacent to `y`. (No other hypothesis is needed.) -/
theorem two_le_card_filter_of_mem_setY {D : Finset V} (hD : lowerMedian Gᶜ + 1 ≤ D.card)
    {y : V} (hy : y ∈ setY G) (hyD : y ∉ D) : 2 ≤ (D.filter (Gᶜ.Adj y)).card := by
  have h1 := card_filter_compl_add (G := G) D hyD
  have h2 := card_filter_adj_le_degree (G := G) D y
  have h3 := degree_add_one_le_of_mem_setY hy
  omega

/-! ## Lemma G bundled under Setting S -/

section Bundled

variable (hS : SettingS G)
include hS

theorem SettingS.one_lt_card : 1 < Fintype.card V := one_lt_card_of_ne_top hS.ne_top

/-- (a) -/
theorem SettingS.lemmaG_a :
    (Fintype.card V + 1) / 2 ≤ (setT G).card ∧ setT G ⊆ setQ G :=
  ⟨card_setT, setT_subset_setQ hS.two_m⟩

/-- (b) -/
theorem SettingS.lemmaG_b {a b : V} (ha : a ∈ setQ G) (hb : b ∈ setQ G) (hab : a ≠ b) :
    G.Adj a b := setQ_adj hS.closed ha hb hab

/-- (c) -/
theorem SettingS.lemmaG_c :
    (setY G).Nonempty ∧ setU G ⊆ setQ G ∧
      (∀ y ∈ setY G, ∀ u ∈ setU G, G.Adj y u) ∧
      (∀ y ∈ setY G, (setU G).card ≤ G.degree y ∧ G.degree y + 1 ≤ lowerMedian Gᶜ) ∧
      (setU G).card + 1 ≤ lowerMedian Gᶜ ∧ 2 ≤ rS G :=
  ⟨setY_nonempty hS.closed hS.ne_top, setU_subset_setQ hS.two_m,
    fun _ hy _ hu => adj_setU_of_mem_setY hS.two_m hy hu,
    fun _ hy => ⟨card_setU_le_degree hS.two_m hy, degree_add_one_le_of_mem_setY hy⟩,
    card_setU_add_one_le hS.closed hS.two_m hS.ne_top,
    two_le_rS hS.closed hS.two_m hS.ne_top⟩

/-- (d) -/
theorem SettingS.lemmaG_d :
    (∀ q ∈ setQ G, ∀ w, Gᶜ.Adj q w → w ∈ setY G) ∧
      (∀ q ∈ setP G, ∃ w, q ≠ w ∧ ¬ G.Adj q w) :=
  ⟨fun _ hq _ h => mem_setY_of_compl_adj hS.closed hq h,
    fun _ hq => exists_nonadj_of_mem_setP hq⟩

/-- (e) -/
theorem SettingS.lemmaG_e {q : V} (hq : q ∈ setP G) :
    2 ≤ Gᶜ.degree q ∧ 2 ≤ ((setY G).filter (Gᶜ.Adj q)).card :=
  ⟨two_le_degree_compl_of_mem_setP hS.closed hS.connected hq,
    two_le_card_filter_setY_of_mem_setP hS.closed hS.connected hq⟩

/-- (f) -/
theorem SettingS.lemmaG_f {y : V} (hy : y ∈ setY G) :
    ((setP G).filter (G.Adj y)).card ≤ rS G - 2 :=
  card_filter_setP_le_rS_sub_two hS.two_m hy

/-- (g) -/
theorem SettingS.lemmaG_g :
    Disjoint (setU G) (setP G) ∧ Disjoint (setP G) (setY G) ∧ Disjoint (setU G) (setY G) ∧
      setU G ∪ setP G ∪ setY G = Finset.univ ∧
      (setU G).card + (setP G).card + (setY G).card = Fintype.card V :=
  ⟨disjoint_setU_setP, disjoint_setP_setY, disjoint_setU_setY hS.two_m,
    setU_union_setP_union_setY, card_setU_add_card_setP_add_card_setY hS.two_m⟩

/-- `r + u = m + 1`. -/
theorem SettingS.rS_add_card_setU : rS G + (setU G).card = lowerMedian Gᶜ + 1 :=
  W213.rS_add_card_setU hS.closed hS.two_m hS.ne_top

/-- Lemma 3 under Setting S. -/
theorem SettingS.lemma3 {D : Finset V} (hD : lowerMedian Gᶜ + 1 ≤ D.card)
    {y : V} (hy : y ∈ setY G) (hyD : y ∉ D) : 2 ≤ (D.filter (Gᶜ.Adj y)).card :=
  two_le_card_filter_of_mem_setY hD hy hyD

/-- (d)+(e) for any `D ⊇ Y`, under Setting S (used in Case 2b of Theorem 1). -/
theorem SettingS.two_le_of_setY_subset {D : Finset V} (hD : setY G ⊆ D)
    {q : V} (hq : q ∈ setP G) : 2 ≤ (D.filter (Gᶜ.Adj q)).card :=
  two_le_card_filter_of_setY_subset hS.closed hS.connected hD hq

end Bundled

end W213

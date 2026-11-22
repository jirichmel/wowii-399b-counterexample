import LeanWowii.W213.Defs

/-!
# Lemma C (closure) for Conjecture 213

Bondy-Chvatal closure step for Hamiltonian paths, proved directly on paths (no auxiliary
universal vertex):

* `traceable_of_traceable_sup_edge` : if `u ≠ v` are non-adjacent, `n - 1 ≤ d(u) + d(v)` and
  `G ⊔ edge u v` has a Hamiltonian path, then `G` has a Hamiltonian path.
* `isClosedGraph_of_maximal_nontraceable` : a graph without a Hamiltonian path, in which every
  added edge creates one, is closed (`d(u) + d(v) ≤ n - 2` for all distinct non-adjacent `u, v`).

Proof (for a Hamiltonian path of `G + uv` that uses `uv`): it splits as `A ++ B` with `A` ending
in `u`, `B` starting in `v`, both paths of `G`. Let `a` be the first vertex of `A`, `b` the last
vertex of `B`. If `a ~ v` take `rev A ++ B`; if `u ~ b` take `A ++ rev B`. Otherwise, in the
list `L = A ++ B` (indices `0..n-1`, `u` at `k-1`, `v` at `k`) the sets
`U = {i < n-1 : u ~ L[i]}` and `W = {i < n-1 : L[i+1] ~ v}` have at least `d(u)` and `d(v)`
elements, both avoid `k-1`, so they share an index `i`. If `i < k-1`, reverse the segment
`L[i+1..k-1]`; if `i ≥ k`, reverse the segment `L[k..i]`.

Working text for an unpublished project; nothing here has been published.
-/

namespace W213

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

section Closure

variable (G : SimpleGraph V)

/-- A Hamiltonian path written as its list of vertices. -/
def IsHamList (L : List V) : Prop :=
  L ≠ [] ∧ L.Nodup ∧ (∀ x, x ∈ L) ∧ L.IsChain G.Adj

/-- `G` has a Hamiltonian path iff some vertex list is a Hamiltonian path. -/
theorem traceable_iff_exists_isHamList : Traceable G ↔ ∃ L, IsHamList G L := by
  constructor
  · rintro ⟨a, b, p, hp⟩
    exact ⟨p.support, p.support_ne_nil, hp.isPath.support_nodup, hp.mem_support,
      p.isChain_adj_support⟩
  · rintro ⟨L, hne, hnd, hmem, hch⟩
    refine ⟨_, _, SimpleGraph.Walk.ofSupport L hne hch, ?_⟩
    rw [SimpleGraph.Walk.isHamiltonian_iff_isPath_and_forall_mem_support,
      SimpleGraph.Walk.support_ofSupport]
    refine ⟨SimpleGraph.Walk.IsPath.mk' ?_, hmem⟩
    rw [SimpleGraph.Walk.support_ofSupport]
    exact hnd

variable {G}

theorem isChain_reverse_adj {l : List V} (h : l.IsChain G.Adj) : l.reverse.IsChain G.Adj :=
  List.isChain_reverse.2 (h.imp fun _ _ hab => hab.symm)

/-- A permutation of a Hamiltonian vertex list that is a chain is again one. -/
theorem isHamList_of_perm {L L' : List V} (hp : L'.Perm L) (hne : L ≠ []) (hnd : L.Nodup)
    (hcov : ∀ x, x ∈ L) (hch : L'.IsChain G.Adj) : IsHamList G L' := by
  refine ⟨?_, hp.nodup_iff.2 hnd, fun x => hp.mem_iff.2 (hcov x), hch⟩
  intro h
  subst h
  exact hne (List.Perm.nil_eq hp).symm

/-- A nodup chain in `G ⊔ edge u v` is a chain in `G`, or splits at the edge `uv`. -/
theorem split_of_isChain_sup_edge {u v : V} :
    ∀ L : List V, L.Nodup → L.IsChain (G ⊔ SimpleGraph.edge u v).Adj →
    L.IsChain G.Adj ∨ ∃ A B : List V, L = A ++ B ∧ A.IsChain G.Adj ∧ B.IsChain G.Adj ∧
      ((A.getLast? = some u ∧ B.head? = some v) ∨ (A.getLast? = some v ∧ B.head? = some u))
  | [], _, _ => Or.inl List.IsChain.nil
  | [a], _, _ => Or.inl (List.IsChain.singleton a)
  | a :: b :: l, hnd, hch => by
    rw [List.isChain_cons_cons] at hch
    obtain ⟨hab, hrest⟩ := hch
    have hnd' : (b :: l).Nodup := (List.nodup_cons.1 hnd).2
    have hanot : a ∉ b :: l := (List.nodup_cons.1 hnd).1
    have hab' : G.Adj a b ∨ (a = u ∧ b = v ∨ a = v ∧ b = u) := by
      simp only [SimpleGraph.sup_adj, SimpleGraph.edge_adj] at hab
      tauto
    rcases split_of_isChain_sup_edge (b :: l) hnd' hrest with h | ⟨A, B, hL, hA, hB, hend⟩
    · by_cases hG : G.Adj a b
      · exact Or.inl (List.IsChain.cons_cons hG h)
      · right
        refine ⟨[a], b :: l, rfl, List.IsChain.singleton a, h, ?_⟩
        rcases hab' with hab' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd hab' hG
        · left; simp
        · right; simp
    · by_cases hG : G.Adj a b
      · right
        refine ⟨a :: A, B, by simp [hL], ?_, hB, ?_⟩
        · cases A with
          | nil => simp at hend
          | cons c A' =>
            simp only [List.cons_append, List.cons.injEq] at hL
            obtain ⟨rfl, -⟩ := hL
            exact List.IsChain.cons_cons hG hA
        · cases A with
          | nil => simp at hend
          | cons c A' =>
            simpa [List.getLast?_cons] using hend
      · exfalso
        have huv : u ∈ b :: l ∧ v ∈ b :: l := by
          rw [hL]
          rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨List.mem_append_left _ (List.mem_of_mem_getLast? h1),
              List.mem_append_right _ (List.mem_of_mem_head? h2)⟩
          · exact ⟨List.mem_append_right _ (List.mem_of_mem_head? h2),
              List.mem_append_left _ (List.mem_of_mem_getLast? h1)⟩
        rcases hab' with hab' | ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact hG hab'
        · exact hanot huv.1
        · exact hanot huv.2

variable [DecidableRel G.Adj]

/-- The core of the closure step: a Hamiltonian path of `G + uv` through `uv`, cut into
`A` (ending at `u`) and `B` (starting at `v`), gives a Hamiltonian path of `G` when
`n - 1 ≤ d(u) + d(v)`. -/
theorem exists_isHamList_of_split {u v : V} (A B : List V) (hnd : (A ++ B).Nodup)
    (hcov : ∀ x, x ∈ A ++ B) (hA : A.IsChain G.Adj) (hB : B.IsChain G.Adj)
    (hu : A.getLast? = some u) (hv : B.head? = some v)
    (hdeg : Fintype.card V - 1 ≤ G.degree u + G.degree v) : ∃ L, IsHamList G L := by
  have hAne : A ≠ [] := by rintro rfl; simp at hu
  have hBne : B ≠ [] := by rintro rfl; simp at hv
  have hLne : A ++ B ≠ [] := by simp [hAne]
  obtain ⟨a, ha⟩ : ∃ a, A.head? = some a := Option.isSome_iff_exists.1 (by
    cases A with
    | nil => exact absurd rfl hAne
    | cons c A' => simp)
  obtain ⟨b, hb⟩ : ∃ b, B.getLast? = some b := Option.isSome_iff_exists.1 (by
    cases B using List.reverseRecOn with
    | nil => exact absurd rfl hBne
    | append_singleton B' c => simp)
  -- the two easy cases
  by_cases hav : G.Adj a v
  · refine ⟨A.reverse ++ B, isHamList_of_perm (List.Perm.append_right B (List.reverse_perm A))
      hLne hnd hcov ?_⟩
    refine (isChain_reverse_adj hA).append hB ?_
    intro x hx y hy
    rw [List.getLast?_reverse, ha] at hx
    rw [hv] at hy
    simp only [Option.mem_def, Option.some.injEq] at hx hy
    subst hx hy
    exact hav
  by_cases hub : G.Adj u b
  · refine ⟨A ++ B.reverse, isHamList_of_perm (List.Perm.append_left A (List.reverse_perm B))
      hLne hnd hcov ?_⟩
    refine hA.append (isChain_reverse_adj hB) ?_
    intro x hx y hy
    rw [hu] at hx
    rw [List.head?_reverse, hb] at hy
    simp only [Option.mem_def, Option.some.injEq] at hx hy
    subst hx hy
    exact hub
  -- the counting case
  set n := Fintype.card V with hn
  have hlen : (A ++ B).length = n := by
    rw [← List.toFinset_card_of_nodup hnd, hn, ← Finset.card_univ]
    congr 1
    ext x
    simpa using hcov x
  set k := A.length with hkdef
  have hk : 0 < k := List.length_pos_iff.2 hAne
  have hBl : 0 < B.length := List.length_pos_iff.2 hBne
  have hkn : k < n := by rw [← hlen, List.length_append]; omega
  have hLk1 : (A ++ B)[k - 1]? = some u := by
    rw [List.getElem?_append_left (by omega), ← hu, List.getLast?_eq_getElem?]
  have hLk : (A ++ B)[k]? = some v := by
    rw [List.getElem?_append_right (le_refl _), Nat.sub_self, ← List.head?_eq_getElem?, hv]
  have hL0 : (A ++ B)[0]? = some a := by
    rw [List.getElem?_append_left hk, ← List.head?_eq_getElem?, ha]
  have hLn : (A ++ B)[n - 1]? = some b := by
    rw [← hlen, ← List.getLast?_eq_getElem?, List.getLast?_append, hb]
    rfl
  set f : ℕ → V := fun i => ((A ++ B)[i]?).getD u with hf
  set g : ℕ → V := fun i => ((A ++ B)[i + 1]?).getD v with hg
  set U := (range (n - 1)).filter (fun i => G.Adj u (f i)) with hU
  set W := (range (n - 1)).filter (fun i => G.Adj (g i) v) with hW
  have hUsub : G.neighborFinset u ⊆ U.image f := by
    intro x hx
    rw [SimpleGraph.mem_neighborFinset] at hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 (hcov x)
    have hi' : (A ++ B)[i]? = some x := by rw [List.getElem?_eq_getElem hi, hix]
    have hin : i ≠ n - 1 := by
      rintro rfl
      rw [hLn, Option.some.injEq] at hi'
      subst hi'
      exact hub hx
    rw [Finset.mem_image]
    refine ⟨i, ?_, ?_⟩
    · rw [hU, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      simp only [hf, hi', Option.getD_some]
      exact hx
    · simp only [hf, hi', Option.getD_some]
  have hWsub : G.neighborFinset v ⊆ W.image g := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.1 (hcov y)
    have hj' : (A ++ B)[j]? = some y := by rw [List.getElem?_eq_getElem hj, hjy]
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [hL0, Option.some.injEq] at hj'
      subst hj'
      exact hav hy.symm
    have hj1 : j - 1 + 1 = j := by omega
    rw [Finset.mem_image]
    refine ⟨j - 1, ?_, ?_⟩
    · rw [hW, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      simp only [hg, hj1, hj', Option.getD_some]
      exact hy.symm
    · simp only [hg, hj1, hj', Option.getD_some]
  have hkU : k - 1 ∉ U := by
    rw [hU, Finset.mem_filter]
    rintro ⟨-, h⟩
    simp only [hf, hLk1, Option.getD_some] at h
    exact G.irrefl h
  have hkW : k - 1 ∉ W := by
    rw [hW, Finset.mem_filter]
    rintro ⟨-, h⟩
    have hk1 : k - 1 + 1 = k := by omega
    simp only [hg, hk1, hLk, Option.getD_some] at h
    exact G.irrefl h
  have hUW : U ∪ W ⊆ (range (n - 1)).erase (k - 1) := by
    intro i hi
    rw [Finset.mem_erase]
    rcases Finset.mem_union.1 hi with hi | hi
    · exact ⟨fun h => hkU (h ▸ hi), (Finset.mem_filter.1 hi).1⟩
    · exact ⟨fun h => hkW (h ▸ hi), (Finset.mem_filter.1 hi).1⟩
  have hcardE : ((range (n - 1)).erase (k - 1)).card = n - 1 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.2 (by omega)), Finset.card_range]
  have hdu : G.degree u ≤ U.card := by
    rw [← G.card_neighborFinset_eq_degree]
    exact (Finset.card_le_card hUsub).trans Finset.card_image_le
  have hdv : G.degree v ≤ W.card := by
    rw [← G.card_neighborFinset_eq_degree]
    exact (Finset.card_le_card hWsub).trans Finset.card_image_le
  have hunion := Finset.card_union_add_card_inter U W
  have hle := Finset.card_le_card hUW
  have hpos : 0 < (U ∩ W).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
  rw [Finset.mem_inter, hU, hW, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨⟨hin, hui⟩, -, hiv⟩ := hi
  have hik : i ≠ k - 1 := by
    rintro rfl
    exact hkU (by rw [hU, Finset.mem_filter, Finset.mem_range]; exact ⟨hin, hui⟩)
  by_cases hcase : i + 1 < k
  · -- reverse the segment `A[i+1..k-1]`
    have hfi : f i = A[i] := by
      simp only [hf, List.getElem?_append_left (show i < A.length by omega),
        List.getElem?_eq_getElem (show i < A.length by omega), Option.getD_some]
    have hgi : g i = A[i + 1] := by
      simp only [hg, List.getElem?_append_left (show i + 1 < A.length by omega),
        List.getElem?_eq_getElem (show i + 1 < A.length by omega), Option.getD_some]
    rw [hfi] at hui
    rw [hgi] at hiv
    refine ⟨A.take (i + 1) ++ (A.drop (i + 1)).reverse ++ B,
      isHamList_of_perm ?_ hLne hnd hcov ?_⟩
    · have := ((List.reverse_perm (A.drop (i + 1))).append_left (A.take (i + 1))).append_right B
      rwa [List.take_append_drop] at this
    · refine ((hA.take _).append (isChain_reverse_adj (hA.drop _)) ?_).append hB ?_
      · intro x hx y hy
        rw [List.getLast?_take, ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i + 1 = 0 by omega)),
          List.getElem?_eq_getElem (show i + 1 - 1 < A.length by omega)] at hx
        rw [List.head?_reverse, List.getLast?_drop,
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ A.length ≤ i + 1 by omega)), hu] at hy
        simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hx hy
        subst hx hy
        exact hui.symm
      · intro x hx y hy
        rw [List.getLast?_append, List.getLast?_reverse, List.head?_drop,
          List.getElem?_eq_getElem (show i + 1 < A.length by omega)] at hx
        rw [hv] at hy
        simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hx hy
        subst hx hy
        exact hiv
  · -- reverse the segment `B[0..i-k]`
    have hki : k ≤ i := by omega
    set j := i - k with hj
    have hjB : j + 1 < B.length := by rw [← hlen, List.length_append] at hin; omega
    have hfi : f i = B[j] := by
      simp only [hf, List.getElem?_append_right (show A.length ≤ i by omega), ← hkdef, ← hj,
        List.getElem?_eq_getElem (show j < B.length by omega), Option.getD_some]
    have hgi : g i = B[j + 1] := by
      have : i + 1 - k = j + 1 := by omega
      simp only [hg, List.getElem?_append_right (show A.length ≤ i + 1 by omega), ← hkdef, this,
        List.getElem?_eq_getElem hjB, Option.getD_some]
    rw [hfi] at hui
    rw [hgi] at hiv
    refine ⟨A ++ (B.take (j + 1)).reverse ++ B.drop (j + 1),
      isHamList_of_perm ?_ hLne hnd hcov ?_⟩
    · have := ((List.reverse_perm (B.take (j + 1))).append_left A).append_right (B.drop (j + 1))
      rwa [List.append_assoc A (B.take (j + 1)), List.take_append_drop] at this
    · refine (hA.append (isChain_reverse_adj (hB.take _)) ?_).append (hB.drop _) ?_
      · intro x hx y hy
        rw [hu] at hx
        rw [List.head?_reverse, List.getLast?_take,
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j + 1 = 0 by omega)),
          List.getElem?_eq_getElem (show j + 1 - 1 < B.length by omega)] at hy
        simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hx hy
        subst hx hy
        exact hui
      · intro x hx y hy
        rw [List.getLast?_append, List.getLast?_reverse, List.head?_take,
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j + 1 = 0 by omega)), hv] at hx
        rw [List.head?_drop, List.getElem?_eq_getElem hjB] at hy
        simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hx hy
        subst hx hy
        exact hiv.symm

/-- **Lemma C, closure step for Hamiltonian paths.** If `n - 1 ≤ d(u) + d(v)` and `G ⊔ edge u v`
has a Hamiltonian path, then `G` has one. (Distinctness and non-adjacency of `u, v` are not
needed: if `u = v` or `u ~ v` then `G ⊔ edge u v = G`.) -/
theorem traceable_of_traceable_sup_edge' {u v : V}
    (hdeg : Fintype.card V - 1 ≤ G.degree u + G.degree v)
    (h : Traceable (G ⊔ SimpleGraph.edge u v)) : Traceable G := by
  rw [traceable_iff_exists_isHamList] at h ⊢
  obtain ⟨L, hne, hnd, hcov, hch⟩ := h
  rcases split_of_isChain_sup_edge L hnd hch with hG | ⟨A, B, rfl, hA, hB, hend⟩
  · exact ⟨L, hne, hnd, hcov, hG⟩
  · rcases hend with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact exists_isHamList_of_split A B hnd hcov hA hB hu hv hdeg
    · refine exists_isHamList_of_split (u := u) (v := v) B.reverse A.reverse ?_ ?_
        (isChain_reverse_adj hB) (isChain_reverse_adj hA) (by rw [List.getLast?_reverse, hv])
        (by rw [List.head?_reverse, hu]) hdeg
      · rw [← List.reverse_append, List.nodup_reverse]
        exact hnd
      · intro x
        rw [← List.reverse_append, List.mem_reverse]
        exact hcov x

/-- **Lemma C, closure step** in the form stated in the proof: for distinct non-adjacent `u, v`
with `d(u) + d(v) ≥ n - 1`, if `G + uv` is traceable then so is `G`. -/
theorem traceable_of_traceable_sup_edge {u v : V} (_hne : u ≠ v) (_hnadj : ¬ G.Adj u v)
    (hdeg : Fintype.card V - 1 ≤ G.degree u + G.degree v)
    (h : Traceable (G ⊔ SimpleGraph.edge u v)) : Traceable G :=
  traceable_of_traceable_sup_edge' hdeg h

/-- **Lemma C.** A graph with no Hamiltonian path such that adding any non-edge creates one
(an edge-maximal non-traceable graph) is closed: `d(u) + d(v) ≤ n - 2` for all distinct
non-adjacent `u, v`. -/
theorem isClosedGraph_of_maximal_nontraceable (hnt : ¬ Traceable G)
    (hmax : ∀ u v, u ≠ v → ¬ G.Adj u v → Traceable (G ⊔ SimpleGraph.edge u v)) :
    IsClosedGraph G := by
  intro u v hne hnadj
  by_contra hlt
  exact hnt (traceable_of_traceable_sup_edge hne hnadj (by omega) (hmax u v hne hnadj))

end Closure

end W213

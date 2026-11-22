/-
# Conjecture 213 (Graffiti.pc, Written on the Wall II): the assembly

Source: `conjectures/wowii213_conjR_round_inprogress/prover-claimC/proof.md`, Corollary 3.

"If G is a simple connected graph with n > 1 such that 2 + the lower median of the degree
sequence of the complement of G <= gamma_2(complement of G), then G has a Hamiltonian path."

Proof. Suppose `G` is connected, `n ≥ 2`, satisfies the hypothesis and is not traceable. Among
the (finitely many) non-traceable spanning supergraphs of `G` take a maximal one, `G'`
(`Set.Finite.exists_le_maximal`). Every added non-edge makes `G'` traceable, so `G'` is closed
(Lemma C). `G'` is connected (it contains `G`), not complete (the complete graph is traceable),
and satisfies the hypothesis (Lemma M, in the form `hyp_of_le`). This contradicts Corollary 2.

Working text for an unpublished project; nothing here has been published.
-/
import LeanWowii.W213.Defs
import LeanWowii.W213.Monotone
import LeanWowii.W213.Closure
import LeanWowii.W213.Theorem1

namespace W213

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

universe u

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete graph on a nonempty vertex set has a Hamiltonian path. -/
theorem traceable_top [Nonempty V] : Traceable (⊤ : SimpleGraph V) := by
  rw [traceable_iff_exists_isHamList]
  refine ⟨Finset.univ.toList, ?_, Finset.nodup_toList _, fun x => by simp, ?_⟩
  · intro h
    have := congrArg List.length h
    rw [Finset.length_toList, List.length_nil, Finset.card_univ] at this
    exact Fintype.card_ne_zero this
  · exact (Finset.nodup_toList _).isChain.imp (fun _ _ h => (SimpleGraph.top_adj _ _).mpr h)

/-- A non-traceable graph `G'` that is maximal among non-traceable graphs: adding any non-edge
makes it traceable. -/
theorem traceable_sup_edge_of_maximal {G' : SimpleGraph V}
    (hmax : Maximal (fun H : SimpleGraph V => ¬ Traceable H) G') :
    ∀ a b, a ≠ b → ¬ G'.Adj a b → Traceable (G' ⊔ SimpleGraph.edge a b) := by
  intro a b hab hna
  by_contra hnt
  have hle : G' ⊔ SimpleGraph.edge a b ≤ G' := hmax.2 hnt le_sup_left
  apply hna
  apply hle
  exact Or.inr ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, hab⟩)

/-- **Conjecture 213**, for one vertex type. -/
theorem conjecture213 (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 1 < Fintype.card V) (hyp : lowerMedian Gᶜ + 2 ≤ gamma2 Gᶜ) : Traceable G := by
  classical
  by_contra hnt
  obtain ⟨G', hGG', hmax⟩ :=
    (Set.toFinite {H : SimpleGraph V | ¬ Traceable H}).exists_le_maximal (a := G) hnt
  have hnt' : ¬ Traceable G' := hmax.1
  have hcl : IsClosedGraph G' :=
    isClosedGraph_of_maximal_nontraceable hnt' (traceable_sup_edge_of_maximal hmax)
  have hc' : G'.Connected := hc.mono hGG'
  have hne : G' ≠ ⊤ := by
    rintro rfl
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    exact hnt' traceable_top
  exact corollary2 hcl hc' hne (hyp_of_le hGG' hyp)

/-- **Conjecture 213** in the form stated in `Defs.lean`. -/
theorem conjecture213Statement : Conjecture213Statement.{u} := by
  intro V _ _ G _ hc hn hyp
  exact conjecture213 G hc hn hyp

end W213

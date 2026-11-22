/-
# Lemma M (monotonicity) for Conjecture 213

Proof file: conjectures/wowii213_conjR_round_inprogress/prover-claimC/proof.md, Lemma M.

Let `G` be a graph and `e = s(u, v)` a non-edge of `G`; write `G' = G ⊔ edge u v`.
The complement of `G'` is `Gᶜ \ edge u v`, a spanning subgraph of `Gᶜ`. Then
* `gamma2 Gᶜ ≤ gamma2 G'ᶜ` (a 2-dominating set of a subgraph is 2-dominating in the bigger graph);
* `lowerMedian G'ᶜ ≤ lowerMedian Gᶜ` (degrees only go down);
* hence the slack `gamma2 - lowerMedian - 2` of the complement does not decrease;
* `G'` is connected if `G` is.

All statements are proved for an arbitrary spanning supergraph `G ≤ G'` first, so they apply
equally to adding one edge or many. The `DecidableRel` instances are arbitrary.

Working text for an unpublished project; nothing here has been published.
-/
import LeanWowii.W213.Defs

namespace W213

set_option linter.unusedSectionVars false

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

section General

/-- Degrees are monotone under taking spanning supergraphs. -/
theorem degree_le_of_le {H H' : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel H'.Adj]
    (h : H' ≤ H) (v : V) : H'.degree v ≤ H.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro w hw
  rw [SimpleGraph.mem_neighborFinset] at hw ⊢
  exact h hw

/-- A 2-dominating set of a spanning subgraph `H'` of `H` is 2-dominating in `H`. -/
theorem IsTwoDominating.mono {H H' : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel H'.Adj]
    (h : H' ≤ H) {D : Finset V} (hD : IsTwoDominating H' D) : IsTwoDominating H D := by
  intro v hv
  refine (hD v hv).trans (Finset.card_le_card ?_)
  intro w hw
  simp only [Finset.mem_filter] at hw ⊢
  exact ⟨hw.1, h hw.2⟩

/-- Removing edges does not decrease the 2-domination number: `H' ≤ H → γ₂(H) ≤ γ₂(H')`. -/
theorem gamma2_anti {H H' : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel H'.Adj]
    (h : H' ≤ H) : gamma2 H ≤ gamma2 H' := by
  obtain ⟨D, hD, hc⟩ := gamma2_spec H'
  rw [← hc]
  exact gamma2_le H (hD.mono h)

/-- Removing edges does not increase the lower median of the degree sequence. -/
theorem lowerMedian_mono_of_le {H H' : SimpleGraph V} [DecidableRel H.Adj]
    [DecidableRel H'.Adj] (h : H' ≤ H) : lowerMedian H' ≤ lowerMedian H :=
  lowerMedian_mono H (degree_le_of_le h)

/-- For a spanning supergraph `G'` of `G`: `γ₂(Gᶜ) ≤ γ₂(G'ᶜ)`. -/
theorem gamma2_compl_le_of_le {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G ≤ G') : gamma2 Gᶜ ≤ gamma2 G'ᶜ :=
  gamma2_anti (compl_le_compl h)

/-- For a spanning supergraph `G'` of `G`: `lm(G'ᶜ) ≤ lm(Gᶜ)`. -/
theorem lowerMedian_compl_le_of_le {G G' : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (h : G ≤ G') : lowerMedian G'ᶜ ≤ lowerMedian Gᶜ :=
  lowerMedian_mono_of_le (compl_le_compl h)

/-- Lemma M for a spanning supergraph, slack form over `ℤ`:
`σ(G) ≤ σ(G')` where `σ(G) = γ₂(Gᶜ) - lm(Gᶜ) - 2`. -/
theorem slack_le_of_le {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G ≤ G') :
    (gamma2 Gᶜ : ℤ) - lowerMedian Gᶜ - 2 ≤ (gamma2 G'ᶜ : ℤ) - lowerMedian G'ᶜ - 2 := by
  have h1 := gamma2_compl_le_of_le h
  have h2 := lowerMedian_compl_le_of_le h
  omega

/-- Lemma M for a spanning supergraph, hypothesis form: the hypothesis of Conjecture 213,
`lm(Gᶜ) + 2 ≤ γ₂(Gᶜ)`, passes from `G` to every spanning supergraph `G'`. -/
theorem hyp_of_le {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G ≤ G') (hyp : lowerMedian Gᶜ + 2 ≤ gamma2 Gᶜ) :
    lowerMedian G'ᶜ + 2 ≤ gamma2 G'ᶜ := by
  have h1 := gamma2_compl_le_of_le h
  have h2 := lowerMedian_compl_le_of_le h
  omega

end General

section AddEdge

variable (G : SimpleGraph V)

/-- The complement of `G + uv` is `Gᶜ - uv`. -/
theorem compl_sup_edge (u v : V) : (G ⊔ SimpleGraph.edge u v)ᶜ = Gᶜ \ SimpleGraph.edge u v := by
  rw [compl_sup, sdiff_eq]

/-- Adding an edge keeps connectivity. -/
theorem connected_sup_edge {G : SimpleGraph V} (hG : G.Connected) (u v : V) :
    (G ⊔ SimpleGraph.edge u v).Connected :=
  hG.mono le_sup_left

variable [DecidableRel G.Adj]

/-- Lemma M, first half: `γ₂((G + uv)ᶜ) ≥ γ₂(Gᶜ)`. Holds for every `u, v`
(the non-edge hypothesis is not needed). -/
theorem gamma2_compl_le_sup_edge (u v : V)
    [DecidableRel (G ⊔ SimpleGraph.edge u v).Adj] :
    gamma2 Gᶜ ≤ gamma2 (G ⊔ SimpleGraph.edge u v)ᶜ :=
  gamma2_compl_le_of_le le_sup_left

/-- Lemma M, second half: `lm((G + uv)ᶜ) ≤ lm(Gᶜ)`. Holds for every `u, v`. -/
theorem lowerMedian_compl_sup_edge_le (u v : V)
    [DecidableRel (G ⊔ SimpleGraph.edge u v).Adj] :
    lowerMedian (G ⊔ SimpleGraph.edge u v)ᶜ ≤ lowerMedian Gᶜ :=
  lowerMedian_compl_le_of_le le_sup_left

/-- Lemma M (as in the proof): for a non-edge `e = uv` of `G`,
`σ(G + e) ≥ σ(G)` with `σ(G) = γ₂(Gᶜ) - lm(Gᶜ) - 2` (over `ℤ`).
The hypotheses `u ≠ v` and `¬ G.Adj u v` are recorded for fidelity; they are not used. -/
theorem lemmaM {u v : V} (_huv : u ≠ v) (_hnadj : ¬ G.Adj u v)
    [DecidableRel (G ⊔ SimpleGraph.edge u v).Adj] :
    (gamma2 Gᶜ : ℤ) - lowerMedian Gᶜ - 2 ≤
      (gamma2 (G ⊔ SimpleGraph.edge u v)ᶜ : ℤ) - lowerMedian (G ⊔ SimpleGraph.edge u v)ᶜ - 2 :=
  slack_le_of_le le_sup_left

/-- Lemma M, hypothesis form for one added edge. -/
theorem hyp_sup_edge (u v : V) [DecidableRel (G ⊔ SimpleGraph.edge u v).Adj]
    (hyp : lowerMedian Gᶜ + 2 ≤ gamma2 Gᶜ) :
    lowerMedian (G ⊔ SimpleGraph.edge u v)ᶜ + 2 ≤ gamma2 (G ⊔ SimpleGraph.edge u v)ᶜ :=
  hyp_of_le le_sup_left hyp

end AddEdge

end W213

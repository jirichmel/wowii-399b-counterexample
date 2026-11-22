/-
# Audit of the statement of Conjecture 213 (auditor's file)

Checks, on concrete graphs, that the definitions in `Defs.lean` mean what the catalogue says.
Working text for an unpublished project; nothing here has been published.
-/
import LeanWowii.W213.Main

namespace W213.Audit

open W213 Finset

set_option linter.unusedSectionVars false

/-! ## Axioms of the main results (fresh check) -/

#print axioms W213.conjecture213Statement
#print axioms W213.conjecture213
#print W213.Conjecture213Statement
#print W213.Traceable
#print W213.IsTwoDominating
#print W213.lowerMedianOf

/-! ## A computable twin of `gamma2`, proved equal to it -/

variable {V : Type*} [Fintype V] [DecidableEq V]

def gamma2c (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((univ : Finset (Finset V)).filter (IsTwoDominating G)).inf'
    ⟨univ, by simp [isTwoDominating_univ]⟩ Finset.card

theorem gamma2_eq_gamma2c (G : SimpleGraph V) [DecidableRel G.Adj] :
    gamma2 G = gamma2c G := by
  apply le_antisymm
  · obtain ⟨D, hD, he⟩ := Finset.exists_mem_eq_inf'
      (s := (univ : Finset (Finset V)).filter (IsTwoDominating G))
      ⟨univ, by simp [isTwoDominating_univ]⟩ Finset.card
    unfold gamma2c; rw [he]
    exact gamma2_le G (Finset.mem_filter.mp hD).2
  · obtain ⟨D, hD, hc⟩ := gamma2_spec G
    rw [← hc]
    exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨mem_univ _, hD⟩)

/-! ## Graphs on `Fin n` from an edge list -/

def ofEdges (n : ℕ) (E : List (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => (i.val, j.val) ∈ E)

instance (n : ℕ) (E : List (ℕ × ℕ)) : DecidableRel (ofEdges n E).Adj :=
  fun i j => decidable_of_iff (i ≠ j ∧ ((i.val, j.val) ∈ E ∨ (j.val, i.val) ∈ E))
    (SimpleGraph.fromRel_adj (fun a b : Fin n => (a.val, b.val) ∈ E) i j).symm

/-- Path P4: 0-1-2-3. -/
abbrev P4 := ofEdges 4 [(0,1),(1,2),(2,3)]
/-- Star K_{1,3}, centre 0. -/
abbrev K13 := ofEdges 4 [(0,1),(0,2),(0,3)]
/-- Path P3: 0-1-2. -/
abbrev P3 := ofEdges 3 [(0,1),(1,2)]
/-- Degree sequence (of the graph) 0,1,1,2,2 example: 1-2, 3-4, 3-0? Let us take
edges (1,2),(2,3),(3,4): degrees 0,1,2,2,1 -> sorted 0,1,1,2,2, lower median (index 2) = 1. -/
abbrev G5 := ofEdges 5 [(1,2),(2,3),(3,4)]
/-- Six vertices: star K_{1,5}: degrees 5,1,1,1,1,1 -> sorted 1,1,1,1,1,5; d_3 = 1. -/
abbrev K15 := ofEdges 6 [(0,1),(0,2),(0,3),(0,4),(0,5)]
/-- Six vertices with degrees sorted 0,0,1,1,2,2 (edge 2-3 and path 4-?): edges (2,3),(4,5)?
That gives 0,0,1,1,1,1. Use edges (1,2),(2,3),(4,5): degrees 0,1,2,1,1,1 -> 0,1,1,1,1,2; d_3=1.
Use instead edges (2,3),(3,4),(4,5),(5,2): a 4-cycle on 2..5: degrees 0,0,2,2,2,2; d_3 = 2. -/
abbrev C4plus2 := ofEdges 6 [(2,3),(3,4),(4,5),(5,2)]
/-- Even n, distinguishes d_{n/2} from d_{n/2+1}: 4 vertices, one edge (0,1):
degrees 1,1,0,0 sorted 0,0,1,1; d_2 = 0 (lower median), upper median d_3 = 1. -/
abbrev E1on4 := ofEdges 4 [(0,1)]

#eval sortedValues (fun v => P4.degree v)     -- [1,1,2,2]
#eval lowerMedian P4                           -- d_2 = 1
#eval lowerMedian P4ᶜ                          -- compl P4 is P4: 1
#eval sortedValues (fun v => G5.degree v)     -- [0,1,1,2,2]
#eval lowerMedian G5                           -- d_3 = 1
#eval lowerMedian K15                          -- d_3 = 1
#eval sortedValues (fun v => C4plus2.degree v) -- [0,0,2,2,2,2]
#eval lowerMedian C4plus2                      -- d_3 = 2
#eval sortedValues (fun v => E1on4.degree v)  -- [0,0,1,1]
#eval lowerMedian E1on4                        -- d_2 = 0
#eval sortedValues (fun v => E1on4ᶜ.degree v) -- compl: degrees 2,2,3,3 -> [2,2,3,3]
#eval lowerMedian E1on4ᶜ                       -- 2

#eval gamma2c K13     -- 2-domination of K_{1,3}: 3 (double domination would be 4)
#eval gamma2c P3      -- 2 (double domination would be 3)
#eval gamma2c P4      -- 2-domination of P4 = 3? {0,2,3}: 1 has nbrs 0,2. yes 3? or {0,3}+...
#eval gamma2c (⊥ : SimpleGraph (Fin 4))  -- empty graph: 4
#eval gamma2c (⊤ : SimpleGraph (Fin 5))  -- complete graph: 2

/-! ## Kernel-checked versions (no `native_decide`) -/

/-- Exact value of the lower median via the two directions of Fact A (proved in Defs). -/
theorem lowerMedian_eq_of {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hn : 0 < Fintype.card W) (k : ℕ)
    (h1 : (Fintype.card W + 1) / 2 ≤ (univ.filter (fun v => H.degree v ≤ k)).card)
    (h2 : Fintype.card W / 2 + 1 ≤ (univ.filter (fun v => k ≤ H.degree v)).card) :
    lowerMedian H = k :=
  le_antisymm ((lowerMedian_le_iff H k).mpr h1) ((le_lowerMedian_iff H hn k).mpr h2)

example : lowerMedian E1on4 = 0 := lowerMedian_eq_of _ (by decide) 0 (by decide) (by decide)
example : lowerMedian E1on4ᶜ = 2 := lowerMedian_eq_of _ (by decide) 2 (by decide) (by decide)
example : lowerMedian C4plus2 = 2 := lowerMedian_eq_of _ (by decide) 2 (by decide) (by decide)
example : lowerMedian G5 = 1 := lowerMedian_eq_of _ (by decide) 1 (by decide) (by decide)
example : lowerMedian K15 = 1 := lowerMedian_eq_of _ (by decide) 1 (by decide) (by decide)
/-- Negative control: for `E1on4` the upper median (1) is NOT the value. -/
example : lowerMedian E1on4 ≠ 1 := by
  intro h
  have := (le_lowerMedian_iff E1on4 (by decide) 1).mp h.ge
  revert this; decide
example : gamma2 K13 = 3 := by rw [gamma2_eq_gamma2c]; decide
example : gamma2 P3 = 2 := by rw [gamma2_eq_gamma2c]; decide
example : gamma2 (⊥ : SimpleGraph (Fin 3)) = 3 := by rw [gamma2_eq_gamma2c]; decide

/-- The hypothesis of the statement is satisfiable: `K_3` (complement empty: lower median 0,
gamma2 = 3). So `Conjecture213Statement` is not vacuous. -/
example : lowerMedian (⊤ : SimpleGraph (Fin 3))ᶜ + 2 ≤ gamma2 (⊤ : SimpleGraph (Fin 3))ᶜ := by
  rw [lowerMedian_eq_of _ (by decide) 0 (by decide) (by decide), gamma2_eq_gamma2c]; decide

/-- The complement is the graph complement. -/
example (G : SimpleGraph V) (a b : V) : Gᶜ.Adj a b ↔ a ≠ b ∧ ¬ G.Adj a b :=
  SimpleGraph.compl_adj G a b

/-! ## Traceability sanity: P4 is traceable via the walk 0-1-2-3 -/

example : Traceable P4 := by
  rw [traceable_iff_exists_isHamList]
  refine ⟨[0, 1, 2, 3], by simp, by decide, by decide, by decide⟩

/-! ## Batch output for comparison with an independent program:
all labelled graphs on `Fin n`, `n ≤ 5`, edge mask over pairs `i < j` in lexicographic order;
prints `n mask lowerMedian(compl) gamma2(compl)`. -/

def pairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap (fun i => ((List.range n).filter (fun j => i < j)).map (fun j => (i, j)))

def graphOfMask (n mask : ℕ) : SimpleGraph (Fin n) :=
  ofEdges n (((pairs n).zipIdx).filterMap (fun ⟨p, k⟩ => if mask.testBit k then some p else none))

instance (n mask : ℕ) : DecidableRel (graphOfMask n mask).Adj :=
  fun i j => by unfold graphOfMask; infer_instance

def batch (n : ℕ) : List String :=
  (List.range (2 ^ (pairs n).length)).map fun m =>
    let G := graphOfMask n m
    s!"{n} {m} {lowerMedian Gᶜ} {gamma2c Gᶜ}"

/-! ## Definitional unfoldings checked by `Iff.rfl` -/

example (G : SimpleGraph V) : Traceable G ↔
    ∃ a b : V, ∃ p : G.Walk a b, SimpleGraph.Walk.IsHamiltonian p := Iff.rfl
example (G : SimpleGraph V) {a b : V} (p : G.Walk a b) :
    p.IsHamiltonian ↔ ∀ x, p.support.count x = 1 := Iff.rfl
example (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) :
    IsTwoDominating G D ↔ ∀ v, v ∉ D → 2 ≤ (D.filter (G.Adj v)).card := Iff.rfl

#print axioms gamma2_eq_gamma2c
#print axioms lowerMedian_eq_of

end W213.Audit

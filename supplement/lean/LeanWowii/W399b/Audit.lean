/-
# Audit of the Lean statement and refutation of Conjecture 399b (auditor's file)

Independent checks that `Defs.lean` states Conjecture 399b as catalogued and that
`Counterexample.lean` refutes it without a loophole:
* axioms of every main theorem;
* the sorted degree sequence of F_3 (and of small graphs) pinned down exactly, and `wpCompl`
  evaluated from its definition through that list (not through the counting lemma);
* negative controls (nonincreasing order, off-by-one index) that give other values;
* the edge set of `F3` against Definition 2 of the paper (vertex roles) and against a graph6
  decoder written here;
* independence from the `DecidableRel` instance; natural division equals the floor;
* small graphs with hand-computed values (K_3, K_4, P_4, K_{1,3}, C_5);
* `#eval` batch output (program only) for comparison with an independent Python program.

No sorry, no native_decide. Working text for an unpublished project; nothing here has been
published.
-/
import LeanWowii.W399b.Counterexample

/-! Audit of Conjecture 399b: statement and counterexample. -/

namespace W399b.AuditCheck

open Finset W399b

set_option linter.unusedSectionVars false

/-! ## 1. Axioms and the statements as elaborated -/

#print axioms W399b.not_conjecture399b
#print axioms W399b.F3_violates
#print axioms W399b.gamma2_F3
#print axioms W399b.seven_le_card
#print axioms W399b.key_bool
#print axioms W399b.twoDom_D0
#print axioms W399b.wpCompl_F3
#print axioms W399b.wpCompl_F3_witness
#print axioms W399b.wpCompl_eq_count
#print axioms W399b.add_dk_le_iff
#print axioms W399b.alphaA3_F3
#print axioms W399b.alphaA3_eq_indepNum
#print axioms W399b.A3_F3
#print axioms W399b.F3_connected
#print axioms W399b.degree_F3
#print axioms W399b.adj_iff_mem_nbL
#print W399b.Conjecture399bStatement
#print W399b.wpCompl
#print W399b.sortedDegrees
#print W213.sortedValues
#print W399b.A3
#print W399b.alphaA3
#print W399b.IsIndep
#print W213.IsTwoDominating
#print W213.gamma2
#print W213.Audit.ofEdges

/-! ## 2. Sorted degree sequences pinned down exactly -/

/-- If `L` is nondecreasing and a permutation of the degrees listed by vertex, then it is the
sorted degree sequence. -/
theorem sortedDegrees_eq_of {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (L : List ℕ) (hperm : List.Perm (List.ofFn (fun v => G.degree v)) L)
    (hsort : L.Pairwise (· ≤ ·)) : sortedDegrees G = L := by
  apply List.Perm.eq_of_pairwise' (sortedDegrees_pairwise G) hsort
  have h1 : ((sortedDegrees G : List ℕ) : Multiset ℕ) =
      Finset.univ.val.map (fun v => G.degree v) := by
    unfold sortedDegrees W213.sortedValues; exact Multiset.sort_eq _ _
  rw [Fin.univ_val_map] at h1
  exact (Quotient.exact h1).trans hperm

/-- The degree sequence of F_3 by vertex: x 6,6,6; l 1,1,1; k 6,6,6; w 3; y 3,3. -/
theorem ofFn_degree_F3 :
    List.ofFn (fun v => F3.degree v) = [6, 6, 6, 1, 1, 1, 6, 6, 6, 3, 3, 3] := by
  simp only [degree_F3]; decide

theorem sortedDegrees_F3 : sortedDegrees F3 = [1, 1, 1, 3, 3, 3, 6, 6, 6, 6, 6, 6] :=
  sortedDegrees_eq_of F3 _ (by rw [ofFn_degree_F3]; decide) (by decide)

/-- `wpCompl F3 = 6` straight from the definition (largest `k ∈ 1..12` with `k + d_k ≤ 12`,
1-based on the sorted list), without the counting lemma. -/
example : wpCompl F3 = 6 := by
  unfold wpCompl; rw [sortedDegrees_F3]; simp only [Fintype.card_fin]; decide

/-- The defining inequalities, written out: `6 + d_6 = 6 + 3 ≤ 12`, `7 + d_7 = 13 > 12`. -/
example : (sortedDegrees F3).getD 5 0 = 3 ∧ (sortedDegrees F3).getD 6 0 = 6 := by
  rw [sortedDegrees_F3]; decide

/-- Negative control: with the degrees in NONINCREASING order the same formula gives 11, so the
value 6 really reflects the nondecreasing order of definition 113. -/
example : ((Finset.Icc 1 12).filter (fun k =>
    k + [6, 6, 6, 6, 6, 6, 3, 3, 3, 1, 1, 1].getD (k - 1) 0 ≤ 12)).sup id = 11 := by decide

/-- Small graphs. -/
abbrev K3 := W213.Audit.ofEdges 3 [(0,1),(0,2),(1,2)]
abbrev K4 := W213.Audit.ofEdges 4 [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
abbrev C5 := W213.Audit.ofEdges 5 [(0,1),(1,2),(2,3),(3,4),(4,0)]
/-- Star with centre at the LAST vertex, so that the by-vertex degree list is not sorted. -/
abbrev K13r := W213.Audit.ofEdges 4 [(3,0),(3,1),(3,2)]
abbrev P4 := W213.Audit.P4
abbrev K13 := W213.Audit.K13

set_option maxRecDepth 10000

theorem sd_K3 : sortedDegrees K3 = [2, 2, 2] :=
  sortedDegrees_eq_of K3 _ (by decide) (by decide)
theorem sd_K4 : sortedDegrees K4 = [3, 3, 3, 3] :=
  sortedDegrees_eq_of K4 _ (by decide) (by decide)
theorem sd_C5 : sortedDegrees C5 = [2, 2, 2, 2, 2] :=
  sortedDegrees_eq_of C5 _ (by decide) (by decide)
theorem sd_P4 : sortedDegrees P4 = [1, 1, 2, 2] :=
  sortedDegrees_eq_of P4 _ (by decide) (by decide)
theorem sd_K13 : sortedDegrees K13 = [1, 1, 1, 3] :=
  sortedDegrees_eq_of K13 _ (by decide) (by decide)
theorem sd_K13r : sortedDegrees K13r = [1, 1, 1, 3] :=
  sortedDegrees_eq_of K13r _ (by decide) (by decide)

/-- Hand values of WP(complement): K_3: 1 (2+2 > 3); K_4: 1; C_5: 3 (3+2 = 5, 4+2 > 5);
P_4: 2 (2+1 ≤ 4, 3+2 > 4); K_{1,3}: 3 (3+1 ≤ 4, 4+3 > 4), in both labellings. -/
example : wpCompl K3 = 1 := by unfold wpCompl; rw [sd_K3]; decide
example : wpCompl K4 = 1 := by unfold wpCompl; rw [sd_K4]; decide
example : wpCompl C5 = 3 := by unfold wpCompl; rw [sd_C5]; decide
example : wpCompl P4 = 2 := by unfold wpCompl; rw [sd_P4]; decide
example : wpCompl K13 = 3 := by unfold wpCompl; rw [sd_K13]; decide
example : wpCompl K13r = 3 := by unfold wpCompl; rw [sd_K13r]; decide
/-- Negative control: the off-by-one index `d_{k+1}` (over `k = 1..3`, where it is in range)
would give 2 for K_{1,3}. -/
example : ((Finset.Icc 1 3).filter (fun k => k + [1, 1, 1, 3].getD k 0 ≤ 4)).sup id = 2 := by
  decide

/-- Hand values of `A3`, `alphaA3`, `gamma2`. -/
example : A3 K3 = ∅ ∧ alphaA3 K3 = 0 := by unfold alphaA3; decide
example : A3 K4 = univ ∧ alphaA3 K4 = 1 := by unfold alphaA3; decide
example : A3 C5 = ∅ ∧ alphaA3 C5 = 0 := by unfold alphaA3; decide
example : A3 K13r = {3} ∧ alphaA3 K13r = 1 := by unfold alphaA3; decide
example : W213.gamma2 K3 = 2 := by rw [W213.Audit.gamma2_eq_gamma2c]; decide
example : W213.gamma2 K4 = 2 := by rw [W213.Audit.gamma2_eq_gamma2c]; decide
example : W213.gamma2 C5 = 3 := by rw [W213.Audit.gamma2_eq_gamma2c]; decide
example : W213.gamma2 P4 = 3 := by rw [W213.Audit.gamma2_eq_gamma2c]; decide
example : W213.gamma2 K13 = 3 := by rw [W213.Audit.gamma2_eq_gamma2c]; decide

/-- Non-triviality: the inequality of the statement holds on K_4 (2 ≤ 1 + 3) and K_{1,3}
(3 ≤ 3 + 3), so the formalised conjecture is not false for a trivial reason. -/
example : W213.gamma2 K4 ≤ wpCompl K4 + 3 / alphaA3 K4 := by
  rw [W213.Audit.gamma2_eq_gamma2c]; unfold wpCompl alphaA3; rw [sd_K4]; decide
example : W213.gamma2 K13 ≤ wpCompl K13 + 3 / alphaA3 K13 := by
  rw [W213.Audit.gamma2_eq_gamma2c]; unfold wpCompl alphaA3; rw [sd_K13]; decide

/-! ## 3. The graph F3 against the paper and the graph6 string -/

/-- Definition 2 of the paper with q = 3, written by vertex roles:
0,1,2 = x; 3,4,5 = l; 6,7,8 = k; 9 = w; 10,11 = y. -/
def isX (v : Fin 12) : Bool := v.val < 3
def isL (v : Fin 12) : Bool := 3 ≤ v.val ∧ v.val < 6
def isK (v : Fin 12) : Bool := 6 ≤ v.val ∧ v.val < 9
def isW (v : Fin 12) : Bool := v.val = 9
def isY (v : Fin 12) : Bool := 10 ≤ v.val

def paperAdj1 (u v : Fin 12) : Bool :=
  (isX u ∧ isL v ∧ v.val = u.val + 3) ∨      -- x_i l_i
  (isK u ∧ isK v ∧ u ≠ v) ∨                  -- K clique
  (isX u ∧ isK v) ∨                          -- all x_i k_j
  (isW u ∧ isK v) ∨                          -- all w k_j
  (isY u ∧ isX v)                            -- all y_a x_i

def paperAdj (u v : Fin 12) : Bool := paperAdj1 u v || paperAdj1 v u

theorem F3_adj_iff_paper : ∀ u v : Fin 12, F3.Adj u v ↔ paperAdj u v = true := by
  decide +kernel

/-- A graph6 decoder written here (upper triangle, column by column, 6 bits per byte, minus 63). -/
def g6bytes : List ℕ := "KCOfFFb?~?[?".toList.map Char.toNat

theorem g6bytes_eq : g6bytes = [75, 67, 79, 102, 70, 70, 98, 63, 126, 63, 91, 63] := by decide

/-- The first byte encodes `n` (here `75 - 63 = 12`); the edge bits start at the second byte. -/
def g6bits (bs : List ℕ) : List Bool :=
  bs.tail.flatMap (fun b => (List.range 6).map (fun i => ((b - 63) / 2 ^ (5 - i)) % 2 = 1))

/-- Bit index of the pair `i < j` in graph6 order: `j(j-1)/2 + i`. -/
def g6Adj (bs : List ℕ) (u v : Fin 12) : Bool :=
  let i := min u.val v.val
  let j := max u.val v.val
  i ≠ j && (g6bits bs).getD (j * (j - 1) / 2 + i) false

theorem g6_order : g6bytes.head? = some (63 + 12) := by decide

theorem F3_adj_iff_g6 : ∀ u v : Fin 12, F3.Adj u v ↔
    g6Adj [75, 67, 79, 102, 70, 70, 98, 63, 126, 63, 91, 63] u v = true := by
  decide +kernel

/-! ## 4. Instances, universes and arithmetic -/

/-- The values do not depend on the `DecidableRel` instance used (any instance gives the same
numbers, so the instance supplied to `Conjecture399bStatement` cannot matter). -/
example (inst : DecidableRel F3.Adj) :
    @W213.gamma2 _ _ _ F3 inst = 7 ∧ @wpCompl _ _ F3 inst = 6 ∧ @alphaA3 _ _ _ F3 inst = 4 := by
  refine ⟨?_, ?_, ?_⟩
  · convert gamma2_F3
  · convert wpCompl_F3
  · convert alphaA3_F3

/-- `F3.Adj` is the relation of the edge list, symmetric and irreflexive (definitional). -/
example (u v : Fin 12) : F3.Adj u v ↔
    u ≠ v ∧ ((u.val, v.val) ∈ edgesF3 ∨ (v.val, u.val) ∈ edgesF3) :=
  SimpleGraph.fromRel_adj _ u v

/-- `3 / a` (natural division) is the floor of the rational `3/a`, also for `a = 0`. -/
example (a : ℕ) : 3 / a = ⌊((3 : ℕ) : ℚ) / (a : ℚ)⌋₊ :=
  (Nat.floor_div_eq_div 3 a).symm

example : ⌊(3 : ℚ) / 4⌋₊ = 0 := by norm_num [Nat.floor_eq_zero]

/-- `0 < alphaA3 G` holds exactly when `A3` is nonempty (so the extra hypothesis only drops the
graphs where `alpha(G[A_3]) = 0` and the catalogue expression is undefined). -/
theorem alphaA3_pos_iff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : 0 < alphaA3 G ↔ (A3 G).Nonempty := by
  constructor
  · intro h
    obtain ⟨S, hS, -, hc⟩ := exists_alphaA3 G
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (hc ▸ h)
    exact ⟨x, hS hx⟩
  · rintro ⟨x, hx⟩
    have := card_le_alphaA3 G (S := {x}) (by simpa using hx)
      (by
        intro u hu v hv
        rw [Finset.mem_singleton] at hu hv; subst hu; subst hv; exact G.loopless.irrefl _)
    simp at this; omega

/-- The stronger statement without `0 < alphaA3 G` (Lean's `3 / 0 = 0`) is refuted too. -/
example : ¬ (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → 2 < Fintype.card V → W213.gamma2 G ≤ wpCompl G + 3 / alphaA3 G) := by
  intro h
  exact not_conjecture399b (fun V _ _ G _ hc hn _ => h V G hc hn)

/-- The refutation, re-derived here from the four values only. -/
example : ¬ Conjecture399bStatement := by
  intro h
  have := h (Fin 12) F3 F3_connected (by decide) (by rw [alphaA3_F3]; decide)
  rw [gamma2_F3, wpCompl_F3, alphaA3_F3] at this
  omega

#print axioms sortedDegrees_F3
#print axioms F3_adj_iff_paper
#print axioms F3_adj_iff_g6
#print axioms alphaA3_pos_iff

/-! ## 5. Program-only output (`#eval`, compiled code; for comparison with Python) -/

#eval sortedDegrees F3
#eval (wpCompl F3, A3 F3, alphaA3 F3)

/-- All labelled graphs on `n` vertices: `mask wpCompl alphaA3 gamma2c`. -/
def batch399 (n : ℕ) : List String :=
  (List.range (2 ^ (W213.Audit.pairs n).length)).map fun m =>
    let G := W213.Audit.graphOfMask n m
    s!"{m} {wpCompl G} {alphaA3 G} {W213.Audit.gamma2c G}"

end W399b.AuditCheck

/-
# Cross-check: the family member `F 3` (Family.lean) is the graph `F3` (Counterexample.lean)

`toFin12 : Vt 3 → Fin 12` uses the labelling of `Counterexample.lean`
(x = 0,1,2; l = 3,4,5; k = 6,7,8; w = 9; y = 10,11). `iso_F3` says it is a graph isomorphism
`F 3 ≃g F3`, checked by the kernel over all 144 pairs of `Fin 12`.

Working text for an unpublished project; nothing here has been published.
-/
import LeanWowii.W399b.Family
import LeanWowii.W399b.Counterexample

/-! Cross-check of `F 3` against `F3`. -/

namespace W399b.Family

def ofFin12 : Fin 12 → Vt 3
  | 0 => .x 0 | 1 => .x 1 | 2 => .x 2
  | 3 => .l 0 | 4 => .l 1 | 5 => .l 2
  | 6 => .k 0 | 7 => .k 1 | 8 => .k 2
  | 9 => .w | 10 => .y 0 | 11 => .y 1

def toFin12 : Vt 3 → Fin 12
  | .x i => i.castLE (by omega)
  | .l i => (i.castLE (by omega) : Fin 12) + 3
  | .k j => (j.castLE (by omega) : Fin 12) + 6
  | .w => 9
  | .y a => (a.castLE (by omega) : Fin 12) + 10

theorem to_of : ∀ a : Fin 12, toFin12 (ofFin12 a) = a := by decide

theorem of_to (v : Vt 3) : ofFin12 (toFin12 v) = v := by
  cases v with
  | x i => fin_cases i <;> rfl
  | l i => fin_cases i <;> rfl
  | k j => fin_cases j <;> rfl
  | w => rfl
  | y a => fin_cases a <;> rfl

set_option maxRecDepth 10000 in
theorem adj_check : ∀ a b : Fin 12, (F 3).Adj (ofFin12 a) (ofFin12 b) ↔ F3.Adj a b := by
  decide +kernel

/-- `F 3 ≃g F3`. -/
def iso_F3 : F 3 ≃g F3 where
  toFun := toFin12
  invFun := ofFin12
  left_inv := of_to
  right_inv := to_of
  map_rel_iff' {u v} := by
    change F3.Adj (toFin12 u) (toFin12 v) ↔ _
    rw [← adj_check, of_to, of_to]

end W399b.Family

#print axioms W399b.Family.iso_F3

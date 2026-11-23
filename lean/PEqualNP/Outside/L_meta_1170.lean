import Mathlib
import PEqualNP.Defs

namespace PEqualNP.MetaComplexity.L_meta_1170_aux

def circ : PEqualNP.CircuitLowerBounds.Circuit := { gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 14]⟩], output := 16 }

theorem circ_mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  simp [PEqualNP.MetaComplexity.Monotone2, circ]

theorem circ_eval : ∀ x : Fin 8 → Bool, circ.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7)) x := by
  decide +kernel

end PEqualNP.MetaComplexity.L_meta_1170_aux

theorem PEqualNP.Outside.L_meta_1170 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7)) x :=
  ⟨PEqualNP.MetaComplexity.L_meta_1170_aux.circ, PEqualNP.MetaComplexity.L_meta_1170_aux.circ_mono,
    by decide, PEqualNP.MetaComplexity.L_meta_1170_aux.circ_eval⟩

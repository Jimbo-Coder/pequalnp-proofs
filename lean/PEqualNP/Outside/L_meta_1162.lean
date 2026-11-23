import Mathlib
import PEqualNP.Defs

namespace PEqualNP.MetaComplexity.L_meta_1162_aux

def circ : PEqualNP.CircuitLowerBounds.Circuit := { gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩], output := 16 }

theorem circ_mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  simp [PEqualNP.MetaComplexity.Monotone2, circ]

theorem circ_eval : ∀ x : Fin 8 → Bool, circ.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 6 && x 7)) x := by
  decide +kernel

end PEqualNP.MetaComplexity.L_meta_1162_aux

theorem PEqualNP.Outside.L_meta_1162 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 6 && x 7)) x :=
  ⟨PEqualNP.MetaComplexity.L_meta_1162_aux.circ, PEqualNP.MetaComplexity.L_meta_1162_aux.circ_mono,
    by decide, PEqualNP.MetaComplexity.L_meta_1162_aux.circ_eval⟩

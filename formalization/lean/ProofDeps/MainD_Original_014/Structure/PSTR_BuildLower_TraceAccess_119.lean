module

public import Structure.PSTR_BuildLower_AccessBridge_116

/-! Proper-clock fetch/decode/access on ONE actual containing Word program.
Segments end ACTIVE, so the separate final HALT remains a real charged step.
Composition uses run_add with the identical physical ROM/program/state. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.TraceAccess
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawTreePreprocessingClaims
variable {bits : Nat}

def Safe (heapWords : Nat) (physical : PhysicalROM) (whole : List PackingOp)
    (state : WordState bits) (count : Nat) : Prop :=
  ∀ clock < count,
    let current := packingRun physical whole clock state
    current.halted = false ∧ current.pc.toNat + 4 < (packingCode whole).length ∧
      ∃ op, PackingOp.decode (fetch whole current) = some op ∧ packingAccessFits physical heapWords current op

theorem zero (heapWords : Nat) (physical : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    Safe heapWords physical whole state 0 := by
  intro clock hc
  omega

theorem add (heapWords : Nat) (physical : PhysicalROM) (whole : List PackingOp) (state : WordState bits)
    (first second : Nat) (front : Safe heapWords physical whole state first)
    (back : Safe heapWords physical whole (packingRun physical whole first state) second) :
    Safe heapWords physical whole state (first + second) := by
  intro clock hc
  by_cases he : clock < first
  · exact front clock he
  · have split : clock = first + (clock - first) := by omega
    have result := back (clock - first) (by omega)
    rw [split, PSTRWordSegments.run_add]
    exact result

theorem mono (heapWords : Nat) (physical : PhysicalROM) (whole : List PackingOp) (state : WordState bits)
    (first second : Nat) (hle : first ≤ second) (safe : Safe heapWords physical whole state second) :
    Safe heapWords physical whole state first := by
  intro clock hc
  exact safe clock (lt_of_lt_of_le hc hle)

theorem straight (physical : PhysicalROM) (left block right : List PackingOp) (heapWords : Nat)
    (state : WordState bits) (isStraight : StraightProgram block)
    (localSafe : PA17PackedTranslator034.PackedAccessSafe heapWords physical block state)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ block ++ right)))
    (hpcfit : Fits bits (5 * (left ++ block ++ right).length)) :
    Safe heapWords physical (left ++ block ++ right) state block.length :=
  AccessBridge.straight_safe physical left block right heapWords state isStraight localSafe hpc ha hcode hpcfit

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.TraceAccess

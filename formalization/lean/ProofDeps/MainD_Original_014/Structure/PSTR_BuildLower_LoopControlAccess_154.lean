module

public import Structure.PSTR_BuildLower_ControlAccess_124
public import Structure.PSTR_BuildLower_ControlPrefix_096

/-! Proper-clock fetch/decode/access for each actual countdown head5 and
tail9, including the real last jump. They use the containing whole program,
actual entryPC and finite runtime control-bank room. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.LoopControlAccess
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem head (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (counter : Nat) (hc : counter ≤ 512) (left body right : List PackingOp)
    (state : WordState (bits q full)) (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeLoopBlock counter left.length body ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeLoopBlock counter left.length body ++ right).length)) :
    TraceAccess.Safe (allocated q full) physical (left ++ relativeLoopBlock counter left.length body ++ right) state 5 := by
  let target := 5 * (left.length + body.length + 14)
  let lead := (relativeLoopHead counter target).take 4
  have shape : lead ++ [.jumpIfZero .value .fresh] = relativeLoopHead counter target := rfl
  have leadLength : lead.length + 1 = 5 := rfl
  have straight : StraightProgram lead := by
    simp [lead, relativeLoopHead, relativeRead, StraightProgram, StraightOp]
  have localSafe := ControlAccess.head_safe physical counter target (allocated q full) state
    (BankAccess.point_room q full hq state base counter hc)
  have result := AccessBridge.last_safe physical left lead (body ++ relativeLoopTail counter (5 * left.length) ++ right)
    (.jumpIfZero .value .fresh) (allocated q full) state straight
    (by rw [shape]; exact localSafe) hpc ha
    (by rw [shape]; simpa only [relativeLoopBlock, target, List.append_assoc] using hcode)
    (by rw [shape]; simpa only [relativeLoopBlock, target, List.append_assoc] using hpcfit)
  rw [shape, leadLength] at result
  simpa only [relativeLoopBlock, target, List.append_assoc] using result

theorem tail (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (counter : Nat) (hc : counter ≤ 512) (left body right : List PackingOp)
    (state : WordState (bits q full)) (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (hpc : state.pc = BitVec.ofNat _ (5 * (left.length + 5 + body.length))) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeLoopBlock counter left.length body ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeLoopBlock counter left.length body ++ right).length)) :
    TraceAccess.Safe (allocated q full) physical (left ++ relativeLoopBlock counter left.length body ++ right) state 9 := by
  let lead := (relativeLoopTail counter (5 * left.length)).take 8
  have shape : lead ++ [.jumpIfZero .flag .fresh] = relativeLoopTail counter (5 * left.length) := rfl
  have leadLength : lead.length + 1 = 9 := rfl
  have straight : StraightProgram lead := by
    simp [lead, relativeLoopTail, relativeRead, StraightProgram, StraightOp]
  have localSafe := ControlAccess.tail_safe physical counter (5 * left.length) (allocated q full) state
    (BankAccess.point_room q full hq state base counter hc)
  have result := AccessBridge.last_safe physical
    (left ++ relativeLoopHead counter (5 * (left.length + body.length + 14)) ++ body) lead right
    (.jumpIfZero .flag .fresh) (allocated q full) state straight
    (by rw [shape]; exact localSafe)
    (by simpa only [List.length_append, relativeLoopHead_length] using hpc) ha
    (by rw [shape]; simpa only [relativeLoopBlock, List.append_assoc] using hcode)
    (by rw [shape]; simpa only [relativeLoopBlock, List.append_assoc] using hpcfit)
  rw [shape, leadLength] at result
  simpa only [relativeLoopBlock, List.append_assoc] using result

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.LoopControlAccess

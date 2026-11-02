module

public import Structure.PSTR_HD_HeadsUniformDispatch_080

/-! Finite literal code-word bounds for the actual heads tail/dispatcher,
and transport from ONE actual query body's code. Every branch immediate is
a true static origin. The original w32 wrapper needs only a compile-time
body-length bound, never a new runtime input or a free relocation. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine

theorem heads_codeFit_append {bits : Nat} (left right : List PackingOp)
    (hl : WordsFit bits (packingCode left)) (hr : WordsFit bits (packingCode right)) :
    WordsFit bits (packingCode (left ++ right)) := by
  intro value hv
  rw [packingCode, List.flatMap_append] at hv
  rcases List.mem_append.mp hv with hv | hv
  · rcases List.mem_append.mp hv with hv | hv
    · exact hl value (List.mem_append.mpr (Or.inl hv))
    · exact hr value (List.mem_append.mpr (Or.inl hv))
  · exact hl value (List.mem_append.mpr (Or.inr hv))

theorem heads_tail_code_fit {bits : Nat} (origin : Nat) (hfit : Fits bits (5 * (origin + 111))) :
    WordsFit bits (packingCode (tailAt origin)) := by
  intro value hv
  have small : value ≤ 5 * (origin + 111) := by
    simp [packingCode, tailAt, endpointProgram, PSTRCountWorkspace.program, endpointTail, stageProbe,
      firstReturn, scanLead, successorGuard, advanceAndRepeat, headsCorrect, PSTRRuntimeAdvance.program,
      jumpBack, appendAndAdvance, headsAppend, initializeAndScan, headsInit, headsFinish,
      PackingOp.encode, Op.encodeWords, Instruction.encodeWords, PackingPrimitive.word,
      Register.word, Region.word, haltWords] at hv
    omega
  exact small.trans_lt hfit

theorem heads_dispatch_code_fit {bits : Nat} (origin : Nat) (hfit : Fits bits (5 * (origin + 119))) :
    WordsFit bits (packingCode (uniformDispatch origin)) := by
  intro value hv
  have small : value ≤ 5 * (origin + 119) := by
    simp [packingCode, uniformDispatch, dispatchLead, dispatchPadding,
      PackingOp.encode, Op.encodeWords, Instruction.encodeWords, PackingPrimitive.word,
      Register.word, Region.word, haltWords] at hv
    omega
  exact small.trans_lt hfit

theorem uniform_heads_code_fit {bits : Nat} (queryBody : List PackingOp)
    (body : WordsFit bits (packingCode queryBody))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length)) :
    WordsFit bits (packingCode (uniformHeadsProgram queryBody)) := by
  rw [uniformHeadsProgram_length] at hpcfit
  exact heads_codeFit_append _ _ (heads_codeFit_append _ _ body (heads_dispatch_code_fit queryBody.length hpcfit))
    (heads_tail_code_fit (queryBody.length + 8) (by simpa only [Nat.add_assoc] using hpcfit))

theorem original_uniform_heads_pc_fit (N q : Nat) (queryBody : List PackingOp) (hlen : queryBody.length ≤ 65536) :
    Fits (indexWidth 32 N q) (5 * (uniformHeadsProgram queryBody).length) := by
  have hc : 0 < Nat.clog 2 (N + q + 2) := Nat.clog_pos (by decide) (by omega)
  have hb : 32 ≤ indexWidth 32 N q := by unfold indexWidth; omega
  have hp : 4294967296 ≤ 2 ^ indexWidth 32 N q := show 2 ^ 32 ≤ 2 ^ indexWidth 32 N q from
    Nat.pow_le_pow_right (by decide) hb
  rw [uniformHeadsProgram_length]
  unfold Fits
  omega

theorem original_uniform_heads_code_fit (N q : Nat) (queryBody : List PackingOp) (hlen : queryBody.length ≤ 65536)
    (body : WordsFit (indexWidth 32 N q) (packingCode queryBody)) :
    WordsFit (indexWidth 32 N q) (packingCode (uniformHeadsProgram queryBody)) :=
  uniform_heads_code_fit queryBody body (original_uniform_heads_pc_fit N q queryBody hlen)

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

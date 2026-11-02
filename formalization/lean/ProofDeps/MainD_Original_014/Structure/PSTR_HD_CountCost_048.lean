module

public import Structure.PSTR_HD_CountAllPrefixes_047

/-! Literal code and actual charged trace bounds. The dynamic loop uses a
constant-size instruction array; its degree only controls execution time. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open PSTRCountWorkspace

theorem code_fit {bits : Nat} (origin : Nat) (hfit : Fits bits (1200 + 5 * origin)) :
    WordsFit bits (packingCode (programAt origin)) := by
  intro value hv
  have small : value ≤ 1200 + 5 * origin := by
    simp [packingCode, programAt, setup, bootstrap, PSTRCountWorkspace.program,
      PSTRCountWorkspace.spillProgram, PSTRStaticFields.program, saveField, clearLoop,
      PSTRStaticFields.treeFactor, PSTRStaticFields.edgeFactor, PSTRStaticFields.stageFactor,
      PSTRStaticFields.fixedOffset,
      testLead, bodyLead, childPosition, accumulate, footer, finishStores,
      PackingOp.encode, Op.encodeWords, Instruction.encodeWords,
      PackingPrimitive.word, Register.word, Region.word, haltWords] at hv
    omega
  exact small.trans_lt hfit

theorem standalone_code_fit {bits : Nat} (hb : 12 ≤ bits) : WordsFit bits (packingCode (programAt 0)) := by
  apply code_fit
  have hp : 4096 ≤ 2 ^ bits := show 2 ^ 12 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  change 1200 + 5 * 0 < 2 ^ bits
  omega

theorem standalone_pc_fit {bits : Nat} (hb : 12 ≤ bits) : Fits bits (5 * (programAt 0).length) := by
  have hp : 4096 ≤ 2 ^ bits := show 2 ^ 12 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  rw [programAt_length]
  unfold Fits
  omega

theorem original_code_fit (N q : Nat) : WordsFit (indexWidth 32 N q) (packingCode (programAt 0)) := by
  have hc : 0 < Nat.clog 2 (N + q + 2) := Nat.clog_pos (by decide) (by omega)
  apply standalone_code_fit
  unfold indexWidth
  omega

theorem original_pc_fit (N q : Nat) : Fits (indexWidth 32 N q) (5 * (programAt 0).length) := by
  have hc : 0 < Nat.clog 2 (N + q + 2) := Nat.clog_pos (by decide) (by omega)
  apply standalone_pc_fit
  unfold indexWidth
  omega

theorem active_trace_bound {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (degree : Nat) (initial : WordState bits) :
    (packingDynamicTrace rom containing (activeSteps degree) initial).length ≤ 2208 * (degree + 1) := by
  have ht := packingDynamicTrace_length_le rom containing (activeSteps degree) initial
  unfold activeSteps at ht ⊢
  omega

theorem halting_trace_bound {bits : Nat} (rom : PhysicalROM) (degree : Nat) (initial : WordState bits) :
    (packingDynamicTrace rom (programAt 0) (activeSteps degree + 1) initial).length ≤ 2220 * (degree + 1) := by
  have ht := packingDynamicTrace_length_le rom (programAt 0) (activeSteps degree + 1) initial
  unfold activeSteps at ht ⊢
  omega

theorem literal_cost_bound {bits : Nat} (rom : PhysicalROM) (degree : Nat) (initial : WordState bits) :
    (packingCode (programAt 0)).length +
      (packingDynamicTrace rom (programAt 0) (activeSteps degree + 1) initial).length + 8 ≤ 4096 * (degree + 1) := by
  have ht := halting_trace_bound rom degree initial
  rw [programAt_code_length]
  omega

end PaperProofs.Structure.LaminarTree.PSTRCountKernel

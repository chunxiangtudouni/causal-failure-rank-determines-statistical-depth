module

public import PaperProofs.Structure.PSTR_HD_ZeroHeads_003

/-! Original q=0 output specification and uniform no-overflow constants for
the actual single-run zero-tool head extractor. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRZeroHeads

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine RawIncidenceLaminarRAM
open PaperProofs.Common.Native.CompactPrice

theorem headWords_zero (full : List (Finset (Fin 0))) (used : Finset (Fin 0)) :
    headWords 0 full used = [depthWord full.length, full.length] ++ List.range full.length := by
  cases full with
  | nil => simp [headWords, criticalIndices, callback, encodeRank, depthWord]
  | cons eligible later =>
    simp [headWords, criticalIndices, callback, encodeRank, depthWord]

theorem outputHeap_low (heap : Nat → Nat) (N k address : Nat) (ha : address < 6) :
    outputHeap heap N k address = heap address := by
  have h8 : ¬8 ≤ address := by omega
  have h6 : address ≠ 6 := by omega
  have h7 : address ≠ 7 := by omega
  simp [outputHeap, h8, h6, h7]

theorem outputHeap_depth (heap : Nat → Nat) (N k : Nat) :
    outputHeap heap N k 6 = depthWord N := by simp [outputHeap]

theorem outputHeap_count (heap : Nat → Nat) (N k : Nat) :
    outputHeap heap N k 7 = N := by simp [outputHeap]

theorem outputHeap_index (heap : Nat → Nat) (N k index : Nat) (hi : index < k) :
    outputHeap heap N k (8 + index) = index := by simp [outputHeap, hi]

theorem outputHeap_frame (heap : Nat → Nat) (N k address : Nat)
    (h6 : address ≠ 6) (h7 : address ≠ 7) (hout : address < 8 ∨ 8 + k ≤ address) :
    outputHeap heap N k address = heap address := by
  have h : ¬(address - 8 < k ∧ 8 ≤ address) := by omega
  simp only [outputHeap, h, ↓reduceIte, Function.update_of_ne h7, Function.update_of_ne h6]

theorem program_code_length : (packingCode program).length = 120 := by
  rw [packingCode_length, program_length]

theorem program_code_fit {bits : Nat} (hb : 8 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  intro value hv
  have small : value < 256 := by
    simp [packingCode, program, startBlock, testLead, bodyLead, finishBlock,
      PackingOp.encode, Op.encodeWords, Instruction.encodeWords,
      PackingPrimitive.word, Register.word, Region.word, haltWords] at hv
    omega
  exact small.trans_le hpow

theorem trace_bound {bits : Nat} (rom : PhysicalROM) (heap : BitVec bits → BitVec bits)
    (N steps : Nat) (hs : steps ≤ 9 * N + 18) :
    (packingDynamicTrace rom program steps (packingInitial heap)).length ≤ 108 * N + 216 := by
  have hb := packingDynamicTrace_length_le rom program steps (packingInitial heap)
  omega

theorem callCost_bound {bits : Nat} (full : List (Finset (Fin 0)))
    (heap : BitVec bits → BitVec bits) (steps : Nat) (hs : steps ≤ 9 * full.length + 18) :
    callCost 0 full program .query steps heap ≤ 512 * headWork 0 full := by
  have ht := trace_bound (callInput 0 full .query) heap full.length steps hs
  simp only [callCost, program_code_length, headWork, liveWork, ↓reduceIte, Nat.mul_one]
  omega

end PaperProofs.Structure.LaminarTree.PSTRZeroHeads


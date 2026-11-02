module

public import PaperProofs.Structure.PSTR_UniformEntrySafe_110
public import PaperProofs.Structure.PSTR_QueryReturn_111
public import PaperProofs.Structure.PSTR_CountAllocation_102
public import PaperProofs.Structure.PSTR_HD_HeadsZeroQuery_096

/-! Actual original q0 QUERY from arbitrary entry registers: real18-step
raw entry/zero guard, existing23-op original reply, true3-op shared return.
ONE44-step run, every prefix whole-heap identity and properclock safety.
Positive query, wholecode assembly and command declarations remain open. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRUniformZeroQuery

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRUniformBootstrapCode PSTRCountKernel PSTRWordSegments

theorem actual_query (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (stage : Fin (full.length + 1)) (whole : List PackingOp) (zeroStart queryEnd : Nat)
    (cb : Contains whole zeroStart)
    (zs : PSTROuterCountCode.BlockAt whole zeroStart PSTRZeroLive.program)
    (bs : PSTROuterCountCode.BlockAt whole (zeroStart + 23) (PSTRCountControl.backBlock queryEnd))
    (hwords : WordsFit (indexWidth 32 full.length 0) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length 0) (5 * whole.length))
    (state : WordState (indexWidth 32 full.length 0))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length 0) 0) (ha : state.halted = false)
    (rep : HeapRepresents 0 full 0 ⟨stage.val, used, false⟩ state.heap) :
    let after := packingRun (callInput 0 full .query) whole 44 state
    after.pc = BitVec.ofNat (indexWidth 32 full.length 0) (5 * queryEnd) ∧ after.halted = false ∧
      after.heap = state.heap ∧ ReplyCorrect 0 (callback 0 full stage used) (replyState 0 0 after) ∧
      (∀ clock ≤ 44, (packingRun (callInput 0 full .query) whole clock state).heap = state.heap) ∧
      (∀ clock < 44, AtSafe (callInput 0 full .query) whole (PSTRCountAllocation.allocation full)
        (packingRun (callInput 0 full .query) whole clock state)) ∧
      (packingDynamicTrace (callInput 0 full .query) whole 44 state).length ≤ 528 := by
  let bits := indexWidth 32 full.length 0
  let rom := callInput 0 full .query
  let entered := packingRun rom whole 18 state
  let replied := packingRun rom whole 23 entered
  have hb := PSTROriginalCountRoom.word_lower full.length 0
  have entry := PSTRUniformWidthEntry.actual_entry full .query whole zeroStart cb hwords hpcfit state hp ha
  have epc : entered.pc = BitVec.ofNat bits (5 * zeroStart) := entry.2.1
  have active : entered.halted = false := entry.1
  have eheap : entered.heap = state.heap := entry.2.2.2.2
  have erep : HeapRepresents 0 full 0 ⟨stage.val, used, false⟩ entered.heap := by rw [eheap]; exact rep
  have hheap : 6 ≤ PSTRCountAllocation.allocation full := by
    unfold PSTRCountAllocation.allocation physicalHeaderWords
    omega
  have zero := PSTRHeadsRuntime.zero_query_segment full used stage whole zeroStart _ zs.bound zs.code hwords hpcfit
    entered epc active (by omega) hheap (PSTROriginalCountRoom.dimension_rooms full).1 erep
  have ret := PSTRQueryReturn.actual_return rom whole (zeroStart + 23) queryEnd bs hwords hpcfit
    replied zero.1 zero.2.1
  have run41 : packingRun rom whole 41 state = replied := by
    rw [show 41 = 18 + 23 by decide, run_add]
  have run44 : packingRun rom whole 44 state = packingRun rom whole 3 replied := by
    rw [show 44 = 41 + 3 by decide, run_add, run41]
  have prefixes (clock : Nat) (hc : clock ≤ 44) : (packingRun rom whole clock state).heap = state.heap := by
    by_cases hearly : clock ≤ 18
    · exact PSTRUniformEntrySafe.entry_prefix_heap full .query whole zeroStart cb hwords hpcfit state hp ha clock hearly
    · by_cases hbody : clock ≤ 41
      · rw [show clock = 18 + (clock - 18) by omega, run_add]
        exact (zero.2.2.2.2.1 (clock - 18) (by omega)).trans eheap
      · rw [show clock = 41 + (clock - 41) by omega, run_add, run41]
        exact (PSTRQueryReturn.prefix_heap rom whole (zeroStart + 23) queryEnd bs hwords hpcfit
          replied zero.1 zero.2.1 _ (by omega)).trans (zero.2.2.1.trans eheap)
  dsimp only
  refine ⟨?_, ?_, prefixes 44 le_rfl, ?_, prefixes, ?_, packingDynamicTrace_length_le rom whole 44 state⟩
  · rw [run44]
    exact ret.1
  · rw [run44]
    exact ret.2.1
  · rw [run44, PSTRCountControl.fetched_back rom whole (zeroStart + 23) queryEnd bs.bound bs.code
      hwords hpcfit replied zero.1 zero.2.1]
    exact (PSTRQueryReturn.reply_iff rom queryEnd 0 (callback 0 full stage used) replied).mpr zero.2.2.2.1
  · intro clock hc
    by_cases hearly : clock < 18
    · exact PSTRUniformEntrySafe.entry_safe full .query whole zeroStart _ cb hwords hpcfit state hp ha clock hearly
    · by_cases hbody : clock < 41
      · rw [show clock = 18 + (clock - 18) by omega, run_add]
        exact zero.2.2.2.2.2 (clock - 18) (by omega)
      · rw [show clock = 41 + (clock - 41) by omega, run_add, run41]
        exact PSTRQueryReturn.actual_safe rom whole (zeroStart + 23) queryEnd _ bs hwords hpcfit
          replied zero.1 zero.2.1 _ (by omega)

end PaperProofs.Structure.LaminarTree.PSTRUniformZeroQuery

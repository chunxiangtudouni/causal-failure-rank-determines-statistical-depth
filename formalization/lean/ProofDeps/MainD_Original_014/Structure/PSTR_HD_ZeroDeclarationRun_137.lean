module

public import Structure.PSTR_HD_ZeroCommandPost_136

/-! ORIGINAL Allowed correct/error execute raw18 + frozen live23 + true
return3 in ONE containing program/ROM/heap. Exact44 clocks, OLD reply and
real next cfg; the two actual heap writes occur at global clocks28 and33. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRZeroDeclaration
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel

theorem actual_declaration (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (command : Command) (declaration : command = .correct ∨ command = .error)
    (allowed : Allowed full configuration command) (whole : List PackingOp) (zeroStart queryEnd : Nat)
    (cb : PSTRUniformBootstrapCode.Contains whole zeroStart)
    (zs : PSTROuterCountCode.BlockAt whole zeroStart PSTRZeroLive.program)
    (bs : PSTROuterCountCode.BlockAt whole (zeroStart + 23) (PSTRCountControl.backBlock queryEnd))
    (hwords : WordsFit (indexWidth 32 full.length 0) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length 0) (5 * whole.length))
    (state : WordState (indexWidth 32 full.length 0))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length 0) 0) (ha : state.halted = false)
    (rep : HeapRepresents 0 full 0 configuration state.heap) :
    CommandPost full configuration command whole queryEnd state := by
  let bits := indexWidth 32 full.length 0
  let rom := callInput 0 full command
  let entered := packingRun rom whole 18 state
  let replied := packingRun rom whole 23 entered
  have hb : 8 ≤ bits := by have h := PSTROriginalCountRoom.word_lower full.length 0; omega
  have entry := PSTRUniformWidthEntry.actual_entry full command whole zeroStart cb hwords hpcfit state hp ha
  have entered_pc : entered.pc = BitVec.ofNat bits (5 * zeroStart) := entry.2.1
  have entered_active : entered.halted = false := entry.1
  have entered_heap : entered.heap = state.heap := entry.2.2.2.2
  have entered_rep : HeapRepresents 0 full 0 configuration entered.heap := by rw [entered_heap]; exact rep
  have heap_room : 6 ≤ PSTRCountAllocation.allocation full := by
    unfold PSTRCountAllocation.allocation physicalHeaderWords
    omega
  have body := declaration_segment full configuration command declaration allowed whole zeroStart _ zs.bound zs.code hwords hpcfit
    entered entered_pc entered_active hb heap_room (PSTROriginalCountRoom.dimension_rooms full).1 entered_rep
  have ret := PSTRQueryReturn.actual_return rom whole (zeroStart + 23) queryEnd bs hwords hpcfit replied body.1 body.2.1
  have run41 : packingRun rom whole 41 state = replied := by
    rw [show 41 = 18 + 23 from rfl, run_add]
  have run44 : packingRun rom whole 44 state = packingRun rom whole 3 replied := by
    rw [show 44 = 41 + 3 from rfl, run_add, run41]
  have body_heap : replied.heap = writeHeap configuration command state.heap := by
    change (packingRun rom whole 23 entered).heap = _
    rw [body.2.2.1, entered_heap]
    rfl
  have declaration_heap : declarationHeap command entered.heap = writeHeap configuration command state.heap := by
    rw [entered_heap]
    exact declarationHeap_eq_writeHeap configuration command state.heap (PSTRZeroLive.stage_word full configuration state.heap rep)
  have prefixes (clock : Nat) (hc : clock ≤ 44) :
      (packingRun rom whole clock state).heap = prefixHeap configuration command state.heap clock := by
    by_cases early : clock ≤ 18
    · rw [PSTRUniformEntrySafe.entry_prefix_heap full command whole zeroStart cb hwords hpcfit state hp ha clock early]
      simp only [prefixHeap, show clock < 28 by omega, ↓reduceIte]
    · by_cases inBody : clock ≤ 41
      · have runClock : packingRun rom whole clock state = packingRun rom whole (clock - 18) entered := by
          change packingRun rom whole clock state = packingRun rom whole (clock - 18) (packingRun rom whole 18 state)
          rw [← run_add]
          congr 1
          omega
        rw [runClock, fetched_prefix rom whole PSTRZeroLive.program zeroStart zs.bound zs.code PSTRZeroLive.program_straight
          hwords hpcfit entered entered_pc entered_active (clock - 18) (by change clock - 18 ≤ 23; omega),
          live_prefix_heap full command entered hb (clock - 18) (by omega)]
        by_cases beforeFail : clock < 28
        · simp only [show clock - 18 < 10 by omega, prefixHeap, beforeFail, ↓reduceIte]
          exact entered_heap
        · by_cases beforeStage : clock < 33
          · simp only [show ¬ clock - 18 < 10 by omega, show clock - 18 < 15 by omega,
              prefixHeap, beforeFail, beforeStage, ↓reduceIte]
            rw [entered_heap]
          · simp only [show ¬ clock - 18 < 10 by omega, show ¬ clock - 18 < 15 by omega,
              prefixHeap, beforeFail, beforeStage, ↓reduceIte]
            exact declaration_heap
      · have runClock : packingRun rom whole clock state = packingRun rom whole (clock - 41) replied := by
          rw [← run41, ← run_add]
          congr 1
          omega
        rw [runClock]
        have kept := PSTRQueryReturn.prefix_heap rom whole (zeroStart + 23) queryEnd bs hwords hpcfit replied body.1 body.2.1
          (clock - 41) (by omega)
        simp only [prefixHeap, show ¬ clock < 28 by omega, show ¬ clock < 33 by omega, ↓reduceIte]
        exact kept.trans body_heap
  apply commandPost_of_core full configuration command whole queryEnd state
  · rw [run44]
    exact ret.1
  · rw [run44]
    exact ret.2.1
  · rw [run44, ret.2.2.1]
    exact body.2.2.2.1
  · intro cursor
    rw [run44, PSTRCountControl.fetched_back rom whole (zeroStart + 23) queryEnd bs.bound bs.code
      hwords hpcfit replied body.1 body.2.1]
    exact (PSTRQueryReturn.reply_iff rom queryEnd 0 (callback 0 full ⟨configuration.stage, cursor⟩ configuration.used) replied).mpr
      (body.2.2.2.2.1 cursor)
  · exact prefixes
  · intro clock hc
    by_cases early : clock < 18
    · exact PSTRUniformEntrySafe.entry_safe full command whole zeroStart _ cb hwords hpcfit state hp ha clock early
    · by_cases inBody : clock < 41
      · rw [show clock = 18 + (clock - 18) by omega, run_add]
        exact body.2.2.2.2.2.1 (clock - 18) (by omega)
      · rw [show clock = 41 + (clock - 41) by omega, run_add, run41]
        exact PSTRQueryReturn.actual_safe rom whole (zeroStart + 23) queryEnd _ bs hwords hpcfit replied body.1 body.2.1
          (clock - 41) (by omega)

end PaperProofs.Structure.LaminarTree.PSTRZeroDeclaration

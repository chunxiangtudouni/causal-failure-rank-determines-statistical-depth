module

public import Structure.PSTR_HD_HeadsZeroReturnSafe_105

/-! q0 safety of the SAME actual8op persistent stage update and3op jump0.
No positive metadata is assumed. The protected high region is ALL Fits
physical addresses>=46, including spare words. Sequential safety transport
below only reassociates actual packingRun clocks; it executes no operation. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel

theorem heads_safe_add {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (heapWords first second : Nat) (state : WordState bits)
    (left : ∀ clock < first, AtSafe rom whole heapWords (packingRun rom whole clock state))
    (right : ∀ clock < second, AtSafe rom whole heapWords
      (packingRun rom whole clock (packingRun rom whole first state))) :
    ∀ clock < first + second, AtSafe rom whole heapWords (packingRun rom whole clock state) := by
  intro clock hc
  by_cases hfirst : clock < first
  · exact left clock hfirst
  · have hclock : clock = first + (clock - first) := by omega
    rw [hclock, run_add]
    exact right (clock - first) (by omega)

theorem zero_advance_prefix_safe {bits : Nat} (full : List (Finset (Fin 0)))
    (configuration : Configuration 0) (origin heapWords : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 configuration state.heap)
    (he : Fits bits 46) (hroom : 46 < heapWords)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 56))) (ha : state.halted = false)
    (clock : Nat) (hc : clock < 11) :
    AtSafe (callInput 0 full .query) whole heapWords (packingRun (callInput 0 full .query) whole clock state) ∧
    HeapFrame (fun physical => 46 ≤ physical) state.heap
      (packingRun (callInput 0 full .query) whole clock state).heap := by
  let rom := callInput 0 full .query
  let region := fun physical => 46 ≤ physical
  have hbefore : 4 + packedCapacityWords 0 0 bits < 46 := by
    rw [zero_packed_words bits (by omega)]
    decide
  have correctSafe : PrefixOK rom heapWords region headsCorrect state := by
    constructor
    · exact headsCorrect_prefix_access full configuration 0 heapWords state rep (hbefore.trans hroom)
    · intro count hcount physical hf hphysical
      exact headsCorrect_prefix_frame full configuration 0 46 state rep hbefore he physical hf hphysical count hcount
  have jumpSafe : PrefixOK rom heapWords region (jumpLead 0) (executeOps rom headsCorrect state) :=
    readOnly_prefixOK rom heapWords region (jumpLead 0) _ (by simp [jumpLead, ReadOnly]) (by
      intro count hcount
      change count < 2 at hcount
      interval_cases count <;> trivial)
  have leadSafe : PrefixOK rom heapWords region advanceLead state :=
    prefixOK_append rom heapWords region headsCorrect (jumpLead 0) state correctSafe jumpSafe
  have leadCode := tail_slice whole advanceLead origin 56 hbound hcode (by change 56 + 10 ≤ 111; decide) rfl
  exact branch_prefix_safe rom whole advanceLead heapWords (origin + 56) region
    (by have h := tailAt_length origin; rw [advanceLead_length]; omega) leadCode
    (hcode 66 (by change 66 < 111; decide)) advanceLead_straight hwords hpcfit state hp ha leadSafe clock
    (by rw [advanceLead_length]; omega)

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

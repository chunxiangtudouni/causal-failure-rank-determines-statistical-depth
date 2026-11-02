module

public import Structure.PSTR_HD_HeadsDecisionSafe_101

/-! All ten real instructions before the final actual HALT of the heads
tail: terminal test3 plus output-header store7. The last HALT is already
proved by068; here every preceding clock has an actual decoded instruction,
bounded access, in-code fetch and a physical prefix frame below endpoint. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel

theorem finish_prefix_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (origin endpoint heapWords : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 104))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits endpoint)
    (he : Fits bits (endpoint + 9)) (hroom : endpoint + 9 < heapWords)
    (clock : Nat) (hc : clock < 7) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) ∧
    HeapFrame (fun physical => physical < endpoint) state.heap (packingRun rom whole clock state).heap := by
  have safe : PrefixOK rom heapWords (fun physical => physical < endpoint) headsFinish state := by
    constructor
    · exact headsFinish_prefix_access rom endpoint heapWords state haddr hroom
    · intro count hcount physical hphysical hbelow
      exact headsFinish_prefix_frame rom endpoint state haddr he physical hphysical (by omega) count hcount
  exact straight_prefix_safe rom whole headsFinish heapWords (origin + 104) (fun physical => physical < endpoint)
    (by have h := tailAt_length origin; rw [headsFinish_length]; omega)
    (headsFinish_tail_code whole origin hbound hcode) headsFinish_straight hwords hpcfit state hp ha safe clock hc

theorem terminal_scan_prefix_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (origin endpoint N heapWords : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 40))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits endpoint)
    (hindex : state.register .index = BitVec.ofNat bits N) (hold : state.register .old = BitVec.ofNat bits N)
    (hN : Fits bits N) (he : Fits bits (endpoint + 9)) (hroom : endpoint + 9 < heapWords)
    (clock : Nat) (hc : clock < 10) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) ∧
    HeapFrame (fun physical => physical < endpoint) state.heap (packingRun rom whole clock state).heap := by
  by_cases hfirst : clock < 3
  · have h := terminal_decision_prefix_safe rom whole origin heapWords hbound hcode hwords hpcfit state hp ha clock hfirst
    refine ⟨h.1, ?_⟩
    intro physical hphysical hbelow
    rw [h.2]
  · let tested : WordState bits := {executeOps rom (terminalLead origin) state with pc := BitVec.ofNat bits (5 * (origin + 104))}
    have test_result := execute_terminalLead rom origin N N state hN hN hindex hold
    have run3 : packingRun rom whole 3 state = tested :=
      fetched_conditional rom whole (terminalLead origin) (origin + 40) (origin + 104) 0 .flag
        (by have h := tailAt_length origin; rw [terminalLead_length]; omega)
        (terminalLead_tail_code whole origin hbound hcode)
        (hcode 42 (by change 42 < 111; decide)) (terminalLead_straight origin) hwords hpcfit state hp ha
        (by simpa only [Nat.sub_self] using test_result.1) test_result.2.1 (by unfold Fits; positivity)
    have tested_heap : tested.heap = state.heap := test_result.2.2.2.2.2.2.2.1
    have tested_addr : tested.register .address = BitVec.ofNat bits endpoint := haddr
    have tested_halt : tested.halted = false := ha
    have hclock : clock = 3 + (clock - 3) := by omega
    rw [hclock, run_add, run3]
    have h := finish_prefix_safe rom whole origin endpoint heapWords hbound hcode hwords hpcfit
      tested rfl tested_halt tested_addr he hroom (clock - 3) (by omega)
    refine ⟨h.1, ?_⟩
    intro physical hphysical hbelow
    exact (h.2 physical hphysical hbelow).trans (congrFun tested_heap (BitVec.ofNat bits physical))

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

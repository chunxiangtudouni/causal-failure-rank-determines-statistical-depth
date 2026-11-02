module

public import Structure.PSTR_HD_HeadsDecisionRun_075

/-! Actual proper-clock safety for a read-only straight lead followed by a
literal conditional jump. The test/target registers are arbitrary, allowing
the real first-return test on .old as well as the rank tests on .flag.
The SAME fetched execution preserves the entire heap at every proper clock. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel
open RawTreePreprocessingClaims

theorem readonly_branch_prefix_safe {bits : Nat} (rom : PhysicalROM) (whole lead : List PackingOp)
    (heapWords start : Nat) (test target : Register)
    (hbound : start + lead.length + 1 ≤ whole.length)
    (hcode : ∀ i (hi : i < lead.length), whole[start + i]'(by omega) = lead[i])
    (hlast : whole[start + lead.length]'(by omega) = .jumpIfZero test target)
    (hs : StraightProgram lead) (ho : ∀ op ∈ lead, ReadOnly op)
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (access : ∀ count (hc : count < lead.length),
      packingAccessFits rom heapWords (executeOps rom (lead.take count) state) lead[count])
    (clock : Nat) (hc : clock ≤ lead.length) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) ∧
      (packingRun rom whole clock state).heap = state.heap := by
  have hr := fetched_prefix rom whole lead start (by omega) hcode hs hw hpcfit state hp ha clock hc
  have hpclock := fetched_prefix_pc rom whole lead start (by omega) hcode hs hw hpcfit state hp ha clock hc
  have hh : (packingRun rom whole clock state).heap = state.heap := by
    rw [hr]
    exact readOnly_prefix_heap rom lead state ho clock
  refine ⟨?_, hh⟩
  by_cases he : clock < lead.length
  · have safe : PrefixOK rom heapWords (fun _ => True) lead state :=
      readOnly_prefixOK rom heapWords (fun _ => True) lead state ho access
    exact (straight_prefix_safe rom whole lead heapWords start (fun _ => True)
      (by omega) hcode hs hw hpcfit state hp ha safe clock he).1
  · have heq : clock = lead.length := by omega
    subst clock
    have hi : start + lead.length < whole.length := by omega
    have hf : fetch whole (packingRun rom whole lead.length state) = natFetch whole (5 * (start + lead.length)) := by
      change physicalFetch bits (packingCode whole) _ = _
      rw [physicalFetch_eq bits _ _ hw, hpclock]
      rfl
    refine ⟨?_, ?_, .jumpIfZero test target, ?_, trivial⟩
    · rw [hr, executeOps_halted, ha]
    · rw [hpclock, packingCode_length]
      omega
    · rw [hf, natFetch_body whole (start + lead.length) hi, hlast, decode_encode]

theorem terminal_decision_prefix_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (origin heapWords : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 40))) (ha : state.halted = false)
    (clock : Nat) (hc : clock < 3) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) ∧
      (packingRun rom whole clock state).heap = state.heap := by
  exact readonly_branch_prefix_safe rom whole (terminalLead origin) heapWords (origin + 40) .flag .total
    (by have h := tailAt_length origin; rw [terminalLead_length]; omega)
    (terminalLead_tail_code whole origin hbound hcode) (hcode 42 (by change 42 < 111; decide))
    (terminalLead_straight origin) (by simp [terminalLead, ReadOnly]) hw hpcfit state hp ha
    (terminalLead_prefix_access rom origin heapWords state) clock (by rw [terminalLead_length]; omega)

theorem finite_decision_prefix_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (origin endpoint heapWords : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 43))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits endpoint) (hroom : endpoint + 3 < heapWords)
    (clock : Nat) (hc : clock < 5) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) ∧
      (packingRun rom whole clock state).heap = state.heap := by
  exact readonly_branch_prefix_safe rom whole (finiteLead origin) heapWords (origin + 43) .flag .total
    (by have h := tailAt_length origin; rw [finiteLead_length]; omega)
    (finiteLead_tail_code whole origin hbound hcode) (hcode 47 (by change 47 < 111; decide))
    (finiteLead_straight origin) (by simp [finiteLead, ReadOnly]) hw hpcfit state hp ha
    (finiteLead_prefix_access rom origin endpoint heapWords state haddr hroom)
    clock (by rw [finiteLead_length]; omega)

theorem guard_decision_prefix_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (origin endpoint heapWords : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 48))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits endpoint) (hroom : endpoint < heapWords)
    (clock : Nat) (hc : clock < 8) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) ∧
      (packingRun rom whole clock state).heap = state.heap := by
  exact readonly_branch_prefix_safe rom whole (guardLead origin) heapWords (origin + 48) .flag .total
    (by have h := tailAt_length origin; rw [guardLead_length]; omega)
    (guardLead_tail_code whole origin hbound hcode) (hcode 55 (by change 55 < 111; decide))
    (guardLead_straight origin) (by simp [guardLead, successorGuard, ReadOnly]) hw hpcfit state hp ha
    (guardLead_prefix_access rom origin endpoint heapWords state haddr hroom)
    clock (by rw [guardLead_length]; omega)

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

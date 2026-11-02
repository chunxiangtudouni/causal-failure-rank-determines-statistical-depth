module

public import PaperProofs.Structure.PSTR_OuterReadAccess_087

/-! Actual branch-prefix safety for the ORIGINAL named condition/target
registers. In particular .value/.fresh and .flag/.address are not silently
replaced by the inner-node kernel's .flag/.total branch. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBranchAccess

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open PSTRCountKernel PSTRWordSegments
open RawTreePreprocessingClaims

theorem branch_safe {bits : Nat} (rom : PhysicalROM) (whole lead : List PackingOp)
    (condition target : Register) (heapWords start : Nat) (region : Nat → Prop)
    (hbound : start + lead.length + 1 ≤ whole.length)
    (hcode : ∀ i (hi : i < lead.length), whole[start + i]'(by omega) = lead[i])
    (hlast : whole[start + lead.length]'(by omega) = .jumpIfZero condition target)
    (hs : StraightProgram lead) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (safe : PrefixOK rom heapWords region lead state) (count : Nat) (hc : count ≤ lead.length) :
    AtSafe rom whole heapWords (packingRun rom whole count state) ∧
      HeapFrame region state.heap (packingRun rom whole count state).heap := by
  by_cases he : count < lead.length
  · exact straight_prefix_safe rom whole lead heapWords start region (by omega) hcode hs hw hpcfit state hp ha safe count he
  · have heq : count = lead.length := by omega
    subst count
    have hr := fetched_prefix rom whole lead start (by omega) hcode hs hw hpcfit state hp ha lead.length le_rfl
    have hpc := fetched_prefix_pc rom whole lead start (by omega) hcode hs hw hpcfit state hp ha lead.length le_rfl
    have hi : start + lead.length < whole.length := by omega
    have hf : fetch whole (packingRun rom whole lead.length state) = natFetch whole (5 * (start + lead.length)) := by
      change physicalFetch bits (packingCode whole) _ = _
      rw [physicalFetch_eq bits _ _ hw, hpc]
      rfl
    refine ⟨⟨?_, ?_, .jumpIfZero condition target, ?_, trivial⟩, ?_⟩
    · rw [hr, List.take_length, executeOps_halted, ha]
    · rw [hpc, packingCode_length]
      omega
    · rw [hf, natFetch_body whole (start + lead.length) hi, hlast, decode_encode]
    · rw [hr]
      exact safe.frame lead.length le_rfl

theorem test_lead_access {bits : Nat} (rom : PhysicalROM) (heapWords exit : Nat) (state : WordState bits)
    (hroom : 0 < heapWords) (count : Nat) (hc : count < (PSTRCountControl.testLead exit).length) :
    packingAccessFits rom heapWords (executeOps rom ((PSTRCountControl.testLead exit).take count) state)
      (PSTRCountControl.testLead exit)[count] := by
  change count < 4 at hc
  interval_cases count <;> try exact True.intro
  simpa only [PSTRCountControl.testLead, List.take_succ_cons, List.take_zero, List.getElem_cons_succ,
    List.getElem_cons_zero, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, packingAccessFits, AccessFits, ↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mod] using hroom

theorem test_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start exit heapWords : Nat)
    (slice : PSTROuterCountCode.BlockAt whole start (PSTRCountControl.testBlock exit))
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (hroom : 0 < heapWords) (clock : Nat) (hclock : clock < 5) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) := by
  have safe : PrefixOK rom heapWords (fun _ => True) (PSTRCountControl.testLead exit) state := by
    apply readOnly_prefixOK
    · simp [PSTRCountControl.testLead, ReadOnly]
    · exact test_lead_access rom heapWords exit state hroom
  apply (branch_safe rom whole (PSTRCountControl.testLead exit) .flag .address heapWords start (fun _ => True)
    (by have hh := slice.bound; rw [PSTRCountControl.testBlock_length] at hh; rw [PSTRCountControl.testLead_length]; omega)
    ?_ ?_ (PSTRCountControl.testLead_straight exit) hw hpcfit state hp ha safe clock (by change clock ≤ 4; omega)).1
  · intro i hi
    exact (slice.code i (by rw [PSTRCountControl.testBlock_length]; rw [PSTRCountControl.testLead_length] at hi; omega)).trans
      (List.getElem_append_left hi)
  · exact (slice.code (PSTRCountControl.testLead exit).length
      (by rw [PSTRCountControl.testBlock_length, PSTRCountControl.testLead_length]; decide)).trans
      (List.getElem_append_right' (PSTRCountControl.testLead exit) (l₂ := [.jumpIfZero .flag .address]) (i := 0) (by decide))

theorem back_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start target heapWords : Nat)
    (slice : PSTROuterCountCode.BlockAt whole start (PSTRCountControl.backBlock target))
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 3) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) := by
  have safe : PrefixOK rom heapWords (fun _ => True) (PSTRCountControl.backLead target) state := by
    apply readOnly_prefixOK
    · simp [PSTRCountControl.backLead, ReadOnly]
    · intro count hc
      change count < 2 at hc
      interval_cases count <;> trivial
  apply (branch_safe rom whole (PSTRCountControl.backLead target) .flag .address heapWords start (fun _ => True)
    (by have hh := slice.bound; rw [PSTRCountControl.backBlock_length] at hh; rw [PSTRCountControl.backLead_length]; omega)
    ?_ ?_ (PSTRCountControl.backLead_straight target) hw hpcfit state hp ha safe clock (by change clock ≤ 2; omega)).1
  · intro i hi
    exact (slice.code i (by rw [PSTRCountControl.backBlock_length]; rw [PSTRCountControl.backLead_length] at hi; omega)).trans
      (List.getElem_append_left hi)
  · exact (slice.code (PSTRCountControl.backLead target).length
      (by rw [PSTRCountControl.backBlock_length, PSTRCountControl.backLead_length]; decide)).trans
      (List.getElem_append_right' (PSTRCountControl.backLead target) (l₂ := [.jumpIfZero .flag .address]) (i := 0) (by decide))

end PaperProofs.Structure.LaminarTree.PSTRBranchAccess

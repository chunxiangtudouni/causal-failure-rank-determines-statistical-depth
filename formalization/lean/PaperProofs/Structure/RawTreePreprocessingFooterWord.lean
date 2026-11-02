module

public import PaperProofs.Structure.RawTreePreprocessingRejectWord
public import PaperProofs.Structure.RawCandidateOrderingWord
import Mathlib.Tactic.IntervalCases

/-! The original raw constructor's thirteen final instructions and its
actual encoded HALT. Ordinary current header-word bounds suffice; mutable
heap cell eight is unrestricted. A halted run's proved invariant extends
to every later actual clock. -/

@[expose] public section

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.RawTreePreprocessingFooterWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawTreeSerialization
open RawTreePreprocessingWordInterface (SafePoint)
open RawCandidateOrderingWord (MacroSafe)
open RawCandidateWorkspaceBounds (workspaceLimit)

abbrev body := RawTreeOutputFinalizeRAM.program
abbrev whole := RawTreePreprocessingNat.program
abbrev paddingOp := RawTreeOutputFinalizeRAM.paddingOp

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hf : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hf reg

theorem prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hnodes : Fits (indexWidth 16 full.length q) (state.heap 5))
    (hlength : Fits (indexWidth 16 full.length q) (3 + state.heap 0 + state.heap 1 + state.heap 2))
    (count : Nat) (hc : count ≤ 13) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (body.take count) state) := by
  have h0 : Fits (indexWidth 16 full.length q) (state.heap 0) :=
    (show state.heap 0 ≤ 3 + state.heap 0 + state.heap 1 + state.heap 2 by omega).trans_lt hlength
  have h1 : Fits (indexWidth 16 full.length q) (state.heap 1) :=
    (show state.heap 1 ≤ 3 + state.heap 0 + state.heap 1 + state.heap 2 by omega).trans_lt hlength
  have h2 : Fits (indexWidth 16 full.length q) (state.heap 2) :=
    (show state.heap 2 ≤ 3 + state.heap 0 + state.heap 1 + state.heap 2 by omega).trans_lt hlength
  have h01 : Fits (indexWidth 16 full.length q) (state.heap 0 + state.heap 1) :=
    (show state.heap 0 + state.heap 1 ≤ 3 + state.heap 0 + state.heap 1 + state.heap 2 by omega).trans_lt hlength
  have h012 : Fits (indexWidth 16 full.length q) (state.heap 0 + state.heap 1 + state.heap 2) :=
    (show state.heap 0 + state.heap 1 + state.heap 2 ≤ 3 + state.heap 0 + state.heap 1 + state.heap 2 by omega).trans_lt hlength
  have hsmall (value : Nat) (hv : value ≤ 10450) := RawTreePreprocessingCodeBounds.constant_fits full.length q value hv
  induction count with
  | zero => exact hf
  | succ count ih =>
    have hlt : count < 13 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 13; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ (body[count]'(by change count < 13; exact hlt)) _)
    interval_cases count <;>
      simp only [body, RawTreeOutputFinalizeRAM.program, List.getElem_cons_zero, List.getElem_cons_succ,
        RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals apply fits_update hp
    · exact hsmall 5 (by decide)
    · simpa [body, RawTreeOutputFinalizeRAM.program, runOps, natExecuteOp, Op.execute, Instruction.execute] using hnodes
    · exact hsmall 0 (by decide)
    · simpa [body, RawTreeOutputFinalizeRAM.program, runOps, natExecuteOp, Op.execute, Instruction.execute] using h0
    · exact hsmall 1 (by decide)
    · simpa [body, RawTreeOutputFinalizeRAM.program, runOps, natExecuteOp, Op.execute, Instruction.execute] using h1
    · simpa [body, RawTreeOutputFinalizeRAM.program, runOps, natExecuteOp, Op.execute, Instruction.execute] using h01
    · exact hsmall 2 (by decide)
    · simpa [body, RawTreeOutputFinalizeRAM.program, runOps, natExecuteOp, Op.execute, Instruction.execute] using h2
    · simpa [body, RawTreeOutputFinalizeRAM.program, runOps, natExecuteOp, Op.execute, Instruction.execute] using h012
    · exact hsmall 3 (by decide)
    · simpa [body, RawTreeOutputFinalizeRAM.program, runOps, natExecuteOp, Op.execute, Instruction.execute,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlength
    · exact hsmall 1 (by decide)

theorem prefix_accessFits (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (count : Nat) (hc : count < 13) :
    RawIncidenceScanSafety.NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) (body.take count) state) (body.getD count paddingOp) := by
  have hcell (address : Nat) (ha : address ≤ 5) : address < workspaceLimit full.length q := by
    unfold workspaceLimit
    omega
  interval_cases count <;>
    simp [body, RawTreeOutputFinalizeRAM.program, runOps, natExecuteOp, Op.execute, Instruction.execute,
      RawIncidenceScanSafety.NatAccessFits, AccessFits, hcell 0 (by decide), hcell 1 (by decide),
      hcell 2 (by decide), hcell 5 (by decide)]

theorem macro_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hnodes : Fits (indexWidth 16 full.length q) (state.heap 5))
    (hlength : Fits (indexWidth 16 full.length q) (3 + state.heap 0 + state.heap 1 + state.heap 2)) :
    MacroSafe q full body state :=
  ⟨fun count hc => prefix_registersFit q full state hf hnodes hlength count hc,
    fun count hc => prefix_accessFits q full state count hc⟩

theorem whole_length : whole.length = 2089 := RawTreePreprocessingCostBounds.program_length

theorem footerFront_length : RawTreePreprocessingNat.footerFront.length = 2076 := by
  rw [RawTreePreprocessingNat.footerFront_length, RawTreePreprocessingNat.childrenStart_eq]

theorem footer_slice : 2076 + 13 ≤ whole.length ∧
    ∀ position < 13, whole.getD (2076 + position) paddingOp = body.getD position paddingOp := by
  refine ⟨by rw [whole_length], ?_⟩
  intro position hp
  change RawTreePreprocessingNat.program.getD (2076 + position) paddingOp = _
  rw [← RawTreePreprocessingNat.footer_program,
    List.getD_append_right _ _ _ _ (by rw [footerFront_length]; omega), footerFront_length,
    Nat.add_sub_cancel_left]

theorem footer_run_prefix (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 5 * 2076) (ha : state.halted = false) (count : Nat) (hc : count ≤ 13) :
    natRun (rawIncidenceROM q full) whole count state = runOps (rawIncidenceROM q full) (body.take count) state := by
  have ht : (body.take count).length = count := List.length_take_of_le (by change count ≤ 13; exact hc)
  conv_lhs => rw [← ht]
  apply natRun_of_straight_segment (rawIncidenceROM q full) whole (body.take count) 2076
    (by rw [ht]; have hh := footer_slice.1; omega) ?_ ?_ state hpc ha
  · intro position hp
    have hi : position < 13 := by rw [ht] at hp; omega
    have hh := footer_slice.2 position hi
    rw [List.getD_eq_getElem _ paddingOp (by have hh := footer_slice.1; omega),
      List.getD_eq_getElem _ paddingOp hi] at hh
    rw [List.getElem_take]
    exact hh
  · intro op hop
    exact RawTreeOutputFinalizeRAM.program_noJump op (List.mem_of_mem_take hop)

theorem footer_prefix_pc (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 5 * 2076) (ha : state.halted = false) (count : Nat) (hc : count ≤ 13) :
    (natRun (rawIncidenceROM q full) whole count state).pc = 5 * (2076 + count) := by
  rw [footer_run_prefix q full state hpc ha count hc,
    runOps_pc _ _ _ (fun op hop => RawTreeOutputFinalizeRAM.program_noJump op (List.mem_of_mem_take hop)),
    List.length_take_of_le (by change count ≤ 13; exact hc), hpc]
  omega

theorem footer_nat_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 5 * 2076) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hnodes : Fits (indexWidth 16 full.length q) (state.heap 5))
    (hlength : Fits (indexWidth 16 full.length q) (3 + state.heap 0 + state.heap 1 + state.heap 2)) :
    PrefixSafe (SafePoint q full) (rawIncidenceROM q full) whole state 13 ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) whole 13 state) ∧
      (natRun (rawIncidenceROM q full) whole 13 state).pc = 5 * whole.length ∧
      (natRun (rawIncidenceROM q full) whole 13 state).halted = false := by
  have m := macro_safe q full state hf hnodes hlength
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro count hc
    have hp := footer_prefix_pc q full state hpc ha count hc.le
    have hr := footer_run_prefix q full state hpc ha count hc.le
    refine ⟨?_, 2076 + count, by rw [whole_length]; omega, hp, ?_⟩
    · rw [hr]
      exact m.1 count hc.le
    · intro _
      have hd : PackingOp.decode (natFetch whole (natRun (rawIncidenceROM q full) whole count state).pc) =
          some (body.getD count paddingOp) := by
        rw [hp, natFetch_body whole (2076 + count) (by rw [whole_length]; omega), decode_encode]
        have hh := footer_slice.2 count hc
        rw [List.getD_eq_getElem _ paddingOp (by rw [whole_length]; omega)] at hh
        exact congrArg some hh
      rw [hd, hr]
      exact m.2 count hc
  · rw [footer_run_prefix q full state hpc ha 13 le_rfl]
    exact m.1 13 le_rfl
  · rw [footer_prefix_pc q full state hpc ha 13 le_rfl, whole_length]
  · rw [footer_run_prefix q full state hpc ha 13 le_rfl, runOps_halted, ha]

theorem prefixSafe_after_halt (P : NatState → Prop) (rom : PhysicalROM) (program : List PackingOp)
    (state : NatState) (stop : Nat)
    (hprefix : PrefixSafe P rom program state stop)
    (hstop : P (natRun rom program stop state))
    (hhalt : (natRun rom program stop state).halted = true) (count : Nat) :
    PrefixSafe P rom program state count := by
  intro clock _
  by_cases hsmall : clock < stop
  · exact hprefix clock hsmall
  · have heq : clock = stop + (clock - stop) := by omega
    rw [heq, natRun_after_halt rom program state stop hhalt]
    exact hstop

theorem footer_halts_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 5 * 2076) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hnodes : Fits (indexWidth 16 full.length q) (state.heap 5))
    (hlength : Fits (indexWidth 16 full.length q) (3 + state.heap 0 + state.heap 1 + state.heap 2)) :
    PrefixSafe (SafePoint q full) (rawIncidenceROM q full) whole state 14 ∧
      SafePoint q full (natRun (rawIncidenceROM q full) whole 14 state) ∧
      (natRun (rawIncidenceROM q full) whole 14 state).halted = true := by
  have hs := footer_nat_safe q full state hpc ha hf hnodes hlength
  let before := natRun (rawIncidenceROM q full) whole 13 state
  have hh : natRun (rawIncidenceROM q full) whole 14 state = { before with halted := true } := by
    rw [show 14 = 13 + 1 by decide, natRun_succ]
    exact natStep_halt _ whole before hs.2.2.1 hs.2.2.2
  have hlast : PrefixSafe (SafePoint q full) (rawIncidenceROM q full) whole before 1 := by
    intro clock hc
    have hz : clock = 0 := by omega
    rw [hz]
    exact RawTreePreprocessingRejectWord.safePoint_halt q full before hs.2.2.1 hs.2.1
  refine ⟨PrefixSafe.add _ _ _ _ 13 1 hs.1 hlast, ?_, ?_⟩
  · rw [hh]
    exact RawTreePreprocessingRejectWord.safePoint_halt q full _ hs.2.2.1 hs.2.1
  · rw [hh]

theorem footer_all_prefix_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 5 * 2076) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hnodes : Fits (indexWidth 16 full.length q) (state.heap 5))
    (hlength : Fits (indexWidth 16 full.length q) (3 + state.heap 0 + state.heap 1 + state.heap 2))
    (count : Nat) : PrefixSafe (SafePoint q full) (rawIncidenceROM q full) whole state count := by
  have hs := footer_halts_safe q full state hpc ha hf hnodes hlength
  exact prefixSafe_after_halt _ _ _ state 14 hs.1 hs.2.1 hs.2.2 count

theorem header_word_bounds (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (state : NatState)
    (headers : RawCandidateSerializedReady.HeaderSpec q full state) :
    Fits (indexWidth 16 full.length q) (state.heap 5) ∧
      Fits (indexWidth 16 full.length q) (3 + state.heap 0 + state.heap 1 + state.heap 2) := by
  have h0 : state.heap 0 = (givenTreeROM q full).input.length := by
    simpa only [List.getD_cons_zero, givenTreeROM_input_length] using headers 0 (by decide)
  have h1 : state.heap 1 = (givenTreeROM q full).internal.length := by
    simpa [givenTreeROM_internal_length] using headers 1 (by decide)
  have h2 : state.heap 2 = (givenTreeROM q full).children.length := by
    simpa [givenTreeROM_children_length q full hq hl] using headers 2 (by decide)
  constructor
  · rw [headers.count]
    exact (prepared_indexed_size_le q full).trans_lt (RawCandidateWorkspaceInit.candidateCount_fits full.length q)
  · have heq : 3 + state.heap 0 + state.heap 1 + state.heap 2 = (serializeROM (givenTreeROM q full)).length := by
      rw [h0, h1, h2, serializeROM_length, PhysicalROM.size]
      omega
    rw [heq]
    exact serialize_givenTreeROM_length_fits q full hq hl

theorem footer_headers_halts_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (state : NatState)
    (headers : RawCandidateSerializedReady.HeaderSpec q full state)
    (hpc : state.pc = 5 * 2076) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state) :
    PrefixSafe (SafePoint q full) (rawIncidenceROM q full) whole state 14 ∧
      SafePoint q full (natRun (rawIncidenceROM q full) whole 14 state) ∧
      (natRun (rawIncidenceROM q full) whole 14 state).halted = true := by
  have hb := header_word_bounds q full hq hl state headers
  exact footer_halts_safe q full state hpc ha hf hb.1 hb.2

theorem footer_word_run_eq_nat (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 5 * 2076) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hnodes : Fits (indexWidth 16 full.length q) (state.heap 5))
    (hlength : Fits (indexWidth 16 full.length q) (3 + state.heap 0 + state.heap 1 + state.heap 2))
    (count : Nat) :
    packingRun (rawIncidenceROM q full) whole count (state.toWord (indexWidth 16 full.length q)) =
      (natRun (rawIncidenceROM q full) whole count state).toWord (indexWidth 16 full.length q) := by
  apply natRun_toWord _ _ _ count (RawTreePreprocessingCostBounds.code_wordsFit full.length q)
  intro clock hc
  have hs := footer_all_prefix_safe q full state hpc ha hf hnodes hlength count clock hc
  exact ⟨hs.1, RawTreePreprocessingWordInterface.safePoint_pcFit q full _ hs⟩

theorem finish_headers_all_prefix_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (first : Nat)
    (hprefix : PrefixSafe (SafePoint q full) (rawIncidenceROM q full) whole natInitial first)
    (headers : RawCandidateSerializedReady.HeaderSpec q full (natRun (rawIncidenceROM q full) whole first natInitial))
    (hpc : (natRun (rawIncidenceROM q full) whole first natInitial).pc = 5 * 2076)
    (ha : (natRun (rawIncidenceROM q full) whole first natInitial).halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) whole first natInitial))
    (count : Nat) : PrefixSafe (SafePoint q full) (rawIncidenceROM q full) whole natInitial count := by
  have hs := footer_headers_halts_safe q full hq hl _ headers hpc ha hf
  have allSafe : PrefixSafe (SafePoint q full) (rawIncidenceROM q full) whole natInitial (first + 14) :=
    PrefixSafe.add _ _ _ _ first 14 hprefix hs.1
  have endpoint : SafePoint q full (natRun (rawIncidenceROM q full) whole (first + 14) natInitial) := by
    rw [natRun_add]
    exact hs.2.1
  have halted : (natRun (rawIncidenceROM q full) whole (first + 14) natInitial).halted = true := by
    rw [natRun_add]
    exact hs.2.2
  exact prefixSafe_after_halt _ _ _ natInitial (first + 14) allSafe endpoint halted count

/-- The rejection branch's invariant is derived from its actual gate run,
then extended beyond its real HALT. There is no supplied prefix certificate. -/
theorem rejects_all_prefix_safe (q : Nat) (full : List (Finset (Fin q)))
    (hl : ¬ LaminarSchedule full) (count : Nat) :
    PrefixSafe (SafePoint q full) (rawIncidenceROM q full) whole natInitial count := by
  obtain ⟨clock, _hclock, entry⟩ := RawTreePreprocessingStartWord.gate_entry q full
  let before := natRun (rawIncidenceROM q full) whole clock natInitial
  have hp : before.pc = 5 * whole.length := (entry.rejects hl).1
  have hh : natRun (rawIncidenceROM q full) whole (clock + 1) natInitial = { before with halted := true } := by
    rw [natRun_succ]
    exact natStep_halt _ whole before hp entry.active
  have hlast : PrefixSafe (SafePoint q full) (rawIncidenceROM q full) whole before 1 := by
    intro k hk
    have hz : k = 0 := by omega
    rw [hz]
    exact RawTreePreprocessingRejectWord.safePoint_halt q full before hp entry.fit
  have hsafe := PrefixSafe.add _ _ _ _ clock 1 entry.safe hlast
  have endpoint : SafePoint q full (natRun (rawIncidenceROM q full) whole (clock + 1) natInitial) := by
    rw [hh]
    exact RawTreePreprocessingRejectWord.safePoint_halt q full _ hp entry.fit
  have halted : (natRun (rawIncidenceROM q full) whole (clock + 1) natInitial).halted = true := by rw [hh]
  exact prefixSafe_after_halt _ _ _ natInitial (clock + 1) hsafe endpoint halted count

end PaperProofs.Structure.LaminarTree.RawTreePreprocessingFooterWord

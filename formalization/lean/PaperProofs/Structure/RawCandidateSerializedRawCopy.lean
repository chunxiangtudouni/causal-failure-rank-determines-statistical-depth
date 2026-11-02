module

public import PaperProofs.Structure.RawCandidateSerializedReady

/-! Actual fixed-code raw-incidence copying loop.  All bits are loaded
from the original readonly ROM, and workspace accesses recompute B.  This
component stops at nodeInit and does not execute the node/tool loops. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedRawCopy

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine
  RawIncidenceLaminarRAM RawCandidateWorkspaceInit RawCandidateSerializedInputRAM RawCandidateSerializedReady

def RawWords (q : Nat) (full : List (Finset (Fin q))) (upto : Nat) (state : NatState) : Prop :=
  ∀ position < upto, state.heap (6 + position) = (incidence full).getD position 0

private theorem raw_space (q : Nat) (full : List (Finset (Fin q))) :
    6 + full.length * q < workspaceBase full.length q := by
  have h := prefixLength_lt_base q full
  unfold prefixLength at h
  omega

private theorem raw_source (q : Nat) (full : List (Finset (Fin q))) (position : Nat) :
    (rawIncidenceROM q full).semantic.read .input (2 + position) = (incidence full).getD position 0 := by
  change ([full.length, q] ++ incidence full).getD (2 + position) 0 = _
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left]

private theorem stage_after_write (q : Nat) (full : List (Finset (Fin q)))
    {before after : NatState} {pointer nextPointer : Nat} (ready : StageReady q full pointer before)
    (offset value : Nat) (hsep : 6 + offset < workspaceBase full.length q)
    (hheap : after.heap = Function.update (Function.update before.heap (6 + offset) value)
      (workspaceBase full.length q + 1) (offset + 1))
    (hpc : after.pc = nextPointer) (hactive : after.halted = false) :
    StageReady q full nextPointer after := by
  have hbase := workspaceBase_ge full.length q
  have hframe : AboveFrame full.length q (workspaceBase full.length q) before after := by
    intro address ha h1 _h2 _h3
    rw [hheap]
    simp only [Function.update_of_ne h1, Function.update_of_ne (show address ≠ 6 + offset by omega)]
  refine ⟨?_, InputSpec.of_aboveFrame q full _ ready.input le_rfl hframe, ?_, hpc, hactive⟩
  · intro position hp
    rw [hheap]
    simpa only [Function.update_of_ne (show position ≠ workspaceBase full.length q + 1 by omega),
      Function.update_of_ne (show position ≠ 6 + offset by omega)] using ready.headers position hp
  · rw [hheap]
    simpa only [Function.update_of_ne (show workspaceBase full.length q + 3 ≠ workspaceBase full.length q + 1 by omega),
      Function.update_of_ne (show workspaceBase full.length q + 3 ≠ 6 + offset by omega)] using ready.raw_count

private theorem rawWords_step (q : Nat) (full : List (Finset (Fin q))) (offset : Nat)
    (hoffset : offset < full.length * q) {before after : NatState} (hwords : RawWords q full offset before)
    (hheap : after.heap = Function.update
      (Function.update before.heap (6 + offset) ((incidence full).getD offset 0))
      (workspaceBase full.length q + 1) (offset + 1)) : RawWords q full (offset + 1) after := by
  have hspace := raw_space q full
  intro position hp
  rw [hheap, Function.update_of_ne (show 6 + position ≠ workspaceBase full.length q + 1 by omega)]
  by_cases heq : position = offset
  · subst position
    exact Function.update_self _ _ _
  · rw [Function.update_of_ne (show 6 + position ≠ 6 + offset by omega)]
    exact hwords position (by omega)

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 443 ≤ containing.length)
  (hcode : ∀ position < 443, containing.getD (start + position) RawCandidateSerializedInputRAM.paddingOp =
    (programAt start).getD position RawCandidateSerializedInputRAM.paddingOp)

include hbound hcode

theorem raw_init (state : NatState) (ready : StageReady q full (5 * (start + 79)) state) :
    let result := natRun (rawIncidenceROM q full) containing 16 state
    RawReady q full 0 (5 * (start + 95)) result ∧
      AboveFrame full.length q (6 + full.length * q) state result := by
  rw [run_rawInit (rawIncidenceROM q full) containing start hbound hcode state ready.pc ready.active]
  have hbase := workspaceBase_ge full.length q
  have hh := setCache_heap q full 1 0 state
  have hf : AboveFrame full.length q (workspaceBase full.length q) state
      (runOps (rawIncidenceROM q full) (setCache 1 0) state) := by
    intro address _ha h1 _h2 _h3
    rw [hh, Function.update_of_ne h1]
  refine ⟨⟨⟨?_, InputSpec.of_aboveFrame q full _ ready.input le_rfl hf, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro position hp
    rw [hh, Function.update_of_ne (show position ≠ workspaceBase full.length q + 1 by omega)]
    exact ready.headers position hp
  · rw [hh, Function.update_of_ne (show workspaceBase full.length q + 3 ≠ workspaceBase full.length q + 1 by omega)]
    exact ready.raw_count
  · rw [runOps_pc _ _ _ (by simp [setCache, storeCache, RawCandidateWorkspaceBaseRAM.program, NoJump]),
      setCache_length, ready.pc]
    omega
  · rw [runOps_halted, ready.active]
  · rw [hh, Function.update_self]
  · intro address _ha h1 _h2 _h3
    rw [hh, Function.update_of_ne h1]

theorem raw_iteration (offset : Nat) (hoffset : offset < full.length * q) (state : NatState)
    (ready : RawReady q full offset (5 * (start + 95)) state) :
    let result := natRun (rawIncidenceROM q full) containing 89 state
    RawReady q full (offset + 1) (5 * (start + 95)) result ∧
      result.heap = Function.update
        (Function.update state.heap (6 + offset) ((incidence full).getD offset 0))
        (workspaceBase full.length q + 1) (offset + 1) ∧
      AboveFrame full.length q (6 + full.length * q) state result := by
  let rom := rawIncidenceROM q full
  let checked := runOps rom (rawTest (start + 184)) state
  have ht := rawTest_values q full (start + 184) state
  dsimp only at ht
  have hp : checked.pc = 5 * (start + 128) := by
    rw [ht.2.1, ready.stage.raw_count, ready.cursor,
      ite_eq_right (by omega : full.length * q - offset ≠ 0), ready.stage.pc]
    omega
  have ha : checked.halted = false := ht.2.2.trans ready.stage.active
  have hsep : 6 + checked.heap (workspaceBase full.length q + 1) < workspaceBase full.length q := by
    rw [ht.1, ready.cursor]
    have hspace := raw_space q full
    omega
  have hb := rawBody_values q full start checked hsep
  dsimp only at hb
  have hrun : natRun rom containing 89 state = runOps rom (rawBody start) checked := by
    rw [show 89 = 33 + 56 by decide, natRun_add,
      run_rawTest rom containing start hbound hcode state ready.stage.pc ready.stage.active]
    exact run_rawBody rom containing start hbound hcode checked hp ha
  have hheap : (natRun rom containing 89 state).heap = Function.update
      (Function.update state.heap (6 + offset) ((incidence full).getD offset 0))
      (workspaceBase full.length q + 1) (offset + 1) := by
    rw [hrun, hb.1, ht.1, ready.cursor, raw_source]
  have hpc : (natRun rom containing 89 state).pc = 5 * (start + 95) := by rw [hrun]; exact hb.2.1
  have hactive : (natRun rom containing 89 state).halted = false := by rw [hrun]; exact hb.2.2.trans ha
  have hspace := raw_space q full
  refine ⟨⟨stage_after_write q full ready.stage offset _ (by omega) hheap hpc hactive, ?_⟩, hheap, ?_⟩
  · rw [hheap, Function.update_self]
  · intro address hadr h1 _h2 _h3
    rw [hheap, Function.update_of_ne h1, Function.update_of_ne (show address ≠ 6 + offset by omega)]

theorem raw_exit (state : NatState) (ready : RawReady q full (full.length * q) (5 * (start + 95)) state) :
    let result := natRun (rawIncidenceROM q full) containing 33 state
    RawReady q full (full.length * q) (5 * (start + 184)) result ∧ result.heap = state.heap := by
  rw [run_rawTest (rawIncidenceROM q full) containing start hbound hcode state ready.stage.pc ready.stage.active]
  have ht := rawTest_values q full (start + 184) state
  dsimp only at ht
  refine ⟨⟨ready.stage.of_heap_eq ht.1 ?_ (ht.2.2.trans ready.stage.active), ?_⟩, ht.1⟩
  · rw [ht.2.1, ready.stage.raw_count, ready.cursor, Nat.sub_self]
    exact ite_eq_left rfl
  · rw [ht.1]
    exact ready.cursor

theorem raw_loop (offset : Nat) (hoffset : offset ≤ full.length * q) (state : NatState)
    (ready : RawReady q full offset (5 * (start + 95)) state) (hwords : RawWords q full offset state) :
    let result := natRun (rawIncidenceROM q full) containing (89 * (full.length * q - offset) + 33) state
    RawReady q full (full.length * q) (5 * (start + 184)) result ∧ RawWords q full (full.length * q) result ∧
      AboveFrame full.length q (6 + full.length * q) state result := by
  have solve : ∀ remaining offset, full.length * q - offset = remaining → offset ≤ full.length * q →
      ∀ state : NatState, RawReady q full offset (5 * (start + 95)) state → RawWords q full offset state →
      let result := natRun (rawIncidenceROM q full) containing (89 * remaining + 33) state
      RawReady q full (full.length * q) (5 * (start + 184)) result ∧ RawWords q full (full.length * q) result ∧
        AboveFrame full.length q (6 + full.length * q) state result := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining ih =>
      intro offset hremaining hoffset state ready hwords
      by_cases hlast : offset = full.length * q
      · subst offset
        have hz : remaining = 0 := by omega
        simp only [hz, Nat.mul_zero, Nat.zero_add]
        have hx := raw_exit q full containing start hbound hcode state ready
        refine ⟨hx.1, ?_, ?_⟩
        · intro position hp
          rw [hx.2]
          exact hwords position hp
        · intro address _ha _h1 _h2 _h3
          exact congrFun hx.2 address
      · have hlive : offset < full.length * q := by omega
        let next := natRun (rawIncidenceROM q full) containing 89 state
        have hstep := raw_iteration q full containing start hbound hcode offset hlive state ready
        have hnextWords := rawWords_step q full offset hlive hwords hstep.2.1
        have hsmall : full.length * q - (offset + 1) < remaining := by omega
        obtain ⟨rready, rwords, rframe⟩ := ih _ hsmall (offset + 1) rfl (by omega) next hstep.1 hnextWords
        have hsteps : 89 * remaining + 33 = 89 + (89 * (full.length * q - (offset + 1)) + 33) := by omega
        rw [hsteps, natRun_add]
        exact ⟨rready, rwords, AboveFrame.trans full.length q (6 + full.length * q) hstep.2.2 rframe⟩
  exact solve (full.length * q - offset) offset rfl hoffset state ready hwords

/-- The complete raw phase includes the real initialization and the final
exit test.  N*q=0 still executes 49 instructions and performs no bit read. -/
theorem copy_raw (state : NatState) (ready : StageReady q full (5 * (start + 79)) state) :
    let result := natRun (rawIncidenceROM q full) containing (89 * (full.length * q) + 49) state
    RawReady q full (full.length * q) (5 * (start + 184)) result ∧ RawWords q full (full.length * q) result ∧
      AboveFrame full.length q (6 + full.length * q) state result := by
  let initialized := natRun (rawIncidenceROM q full) containing 16 state
  have hi := raw_init q full containing start hbound hcode state ready
  have hw : RawWords q full 0 initialized := fun _ hp => by omega
  have hl := raw_loop q full containing start hbound hcode 0 (Nat.zero_le _) initialized hi.1 hw
  have hsteps : 89 * (full.length * q) + 49 = 16 + (89 * (full.length * q - 0) + 33) := by omega
  rw [hsteps, natRun_add]
  exact ⟨hl.1, hl.2.1, AboveFrame.trans full.length q (6 + full.length * q) hi.2 hl.2.2⟩

end Linked

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedRawCopy

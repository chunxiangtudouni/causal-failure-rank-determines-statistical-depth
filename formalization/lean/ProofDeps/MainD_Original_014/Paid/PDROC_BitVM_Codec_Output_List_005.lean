module

public import Paid.PDROC_BitVM_Codec_Output_List_004
public import Paid.PDROC_BitVM_Native_WorkReturn_008
public import Common.PSTR_TM_NativeIncrement_021

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

abbrev CountLabel := Fin 4
abbrev CountStore := BoolOnStacks.Store 51 × Option Bool
abbrev CountState := TM2.Cfg (fun _ : EmitStack => Bool) CountLabel CountStore
abbrev CountStatement := TM2.Stmt (fun _ : EmitStack => Bool) CountLabel CountStore

/-- Work roles 0/2 are physically reused only after the final Cell emit.
Role 1 is the accumulated reverse output; role 3 contains real ticks. -/
def countWork : Fin 2 ↪ EmitStack :=
  ⟨fun role => if role = 0 then 0 else 2, by
    intro left right equal
    fin_cases left <;> fin_cases right <;> simp_all⟩

def countCapture (store : CountStore) (symbol : Option Bool) : CountStore :=
  (store.1, symbol)

def countReset (store : CountStore) : CountStore := ((0, false), store.2)

/-- The loop tests a REAL pop of the unary data stack, resets the finite
old arithmetic control by a REAL load, and calls the existing 52-label
native increment. Local arithmetic HALT really jumps back to the gate.
Label 2 really clears the last loaded Cell before pushing literal zero. -/
def countProgram (label : CountLabel) : CountStatement :=
  if label = 0 then
    .pop 3 countCapture
      (.branch (fun store => store.2.isSome)
        (.load countReset (.goto (fun _ => 1))) .halt)
  else if label = 1 then
    PDROC.BitVM.Native.Inline.statement (fun _ : Unit => 1) 0
      (PDROC.BitVM.Native.workstackMachine countWork
        PSTRTMNativeIncrement021.nativeIncrementMachine ())
  else if label = 2 then
    .pop 0 countCapture
      (.branch (fun store => store.2.isSome) (.goto (fun _ => 2))
        (.push 0 (fun _ => false) (.push 0 (fun _ => false)
          (.push 0 (fun _ => true) (.goto (fun _ => 0))))))
  else .halt

def countTape (state : CountState) : Tape Bool :=
  BoolOnStacks.representedTape (PDROC.BitVM.Native.Lift.cfg countWork
    (⟨none, state.var.1, state.stk⟩ :
      TM2.Cfg (fun _ : EmitStack => Bool) Unit (BoolOnStacks.Store 51)))

def countCall (state : CountState) (bit : Bool) (rest : List Bool) : CountState :=
  ⟨some 1, ((0, false), some bit), Function.update state.stk 3 rest⟩

def countStop (state : CountState) : CountState :=
  ⟨none, (state.var.1, none), Function.update state.stk 3 []⟩

theorem count_gate_cons (before : CountState) (bit : Bool) (rest : List Bool)
    (position : before.l = some 0) (ticks : before.stk 3 = bit :: rest) :
    TM2.step countProgram before = some (countCall before bit rest) := by
  rcases before with ⟨label, store, contents⟩
  change label = some 0 at position
  change contents 3 = bit :: rest at ticks
  subst label
  simp only [TM2.step, countProgram, ↓reduceIte, TM2.stepAux, ticks,
    List.head?_cons, List.tail_cons, countCapture, countReset,
    Option.isSome_some, Bool.cond_true]
  rfl

theorem count_gate_nil (before : CountState) (position : before.l = some 0)
    (ticks : before.stk 3 = []) :
    TM2.step countProgram before = some (countStop before) := by
  rcases before with ⟨label, store, contents⟩
  change label = some 0 at position
  change contents 3 = [] at ticks
  subst label
  simp only [TM2.step, countProgram, ↓reduceIte, TM2.stepAux, ticks,
    List.head?_nil, List.tail_nil, countCapture, Option.isSome_none, Bool.cond_false]
  rfl

theorem countCall_tape (before : CountState) (bit : Bool) (rest : List Bool) :
    countTape (countCall before bit rest) = countTape before := by
  change Tape.mk₂ ((Function.update before.stk 3 rest) 2)
    ((Function.update before.stk 3 rest) 0) = Tape.mk₂ (before.stk 2) (before.stk 0)
  simp only [Function.update_of_ne (by decide : (2 : EmitStack) ≠ 3),
    Function.update_of_ne (by decide : (0 : EmitStack) ≠ 3)]

/-- Exact whole-tape increment, using the already proved original native
trace and its actual final head. The value occurs only in this run proof. -/
theorem count_native_run (value : ℕ) :
    ∃ (run : List (MachineState 51)) (final : MachineState 51),
      Runs PSTRTMNativeIncrement021.nativeIncrementMachine (encodeNat value) run final ∧
      final.Tape = Tape.mk₁ (encodeNat (value + 1)) ∧
      run.length ≤ 512 * (natBits value + 1) ^ 2 := by
  refine ⟨PSTRTMNativeIncrement021.nativeTrace (PSTRTMNatValue017.rawPayload value),
    PSTRTMNativeIncrement021.nativeFinal (PSTRTMNatValue017.rawPayload value), ?_, ?_, ?_⟩
  · simpa [PSTRTMUnblockTrace019.rawWord, PSTRTMNatValue017.rawPayload, encodeNat] using
      PSTRTMNativeIncrement021.native_runs (PSTRTMNatValue017.rawPayload value)
  · change Tape.mk₂ [false]
      (PSTRTMUnblockTrace019.rawWord
        (PSTRTMIncrement009.bumpDigits (PSTRTMNatValue017.rawPayload value))) = _
    rw [PSTRTMCanonical020.rawWord_bump]
    change Tape.mk' (ListBlank.mk [false]) (ListBlank.mk (encodeNat (value + 1))) =
      Tape.mk' (ListBlank.mk []) (ListBlank.mk (encodeNat (value + 1)))
    rw [PSTRTMRawNat010.blank_single_false]
  · calc
      _ ≤ 2 * (PSTRTMNatValue017.rawPayload value).length ^ 2 +
          32 * (PSTRTMNatValue017.rawPayload value).length + 29 :=
        PSTRTMNativeIncrement021.native_length_le _
      _ ≤ 512 * (natBits value + 1) ^ 2 := by
        simp only [PSTRTMNatValue017.rawPayload, List.length_ofFn]
        nlinarith

/-- One actual nonempty tick iteration: the input count is already present
on the real work tape. The caller's reverse output is framed unchanged. -/
theorem count_iteration (before : CountState) (value : ℕ) (bit : Bool) (rest : List Bool)
    (position : before.l = some 0) (ticks : before.stk 3 = bit :: rest)
    (tape : countTape before = Tape.mk₁ (encodeNat value)) :
    ∃ (run : List CountState) (after : CountState),
      run.head? = some before ∧
      run.IsChain (fun a b => TM2.step countProgram a = some b) ∧
      run.getLast? = some after ∧ after.l = some 0 ∧
      countTape after = Tape.mk₁ (encodeNat (value + 1)) ∧
      after.stk 3 = rest ∧ after.stk 1 = before.stk 1 ∧
      run.length ≤ 512 * (natBits value + 1) ^ 2 + 2 := by
  obtain ⟨oldRun, oldFinal, oldActual, oldTape, oldLength⟩ := count_native_run value
  let start : TM2.Cfg (fun _ : EmitStack => Bool) Unit (BoolOnStacks.Store 51) :=
    ⟨some (), (0, false), Function.update before.stk 3 rest⟩
  have represented : BoolOnStacks.representedState
      (PDROC.BitVM.Native.Lift.cfg countWork start) = TM0.init (encodeNat value) := by
    change (⟨0, countTape (countCall before bit rest)⟩ : MachineState 51) = _
    rw [countCall_tape, tape]
    rfl
  obtain ⟨run, after, head, chain, last, returned, result, _store, size, frame⟩ :=
    PDROC.BitVM.Native.actual_workstack_return countWork
      PSTRTMNativeIncrement021.nativeIncrementMachine 1 0 countProgram
      (by rfl) start (some bit) oldRun
      (TM0.init (encodeNat value)) oldFinal rfl represented
      oldActual.1 oldActual.2.1 oldActual.2.2.1 oldActual.2.2.2.1
  have first : run.head? = some (countCall before bit rest) := head
  have tailTicks : after.stk 3 = rest := by
    simpa [start] using frame 3 (by intro role; fin_cases role <;> decide)
  have output : after.stk 1 = before.stk 1 := by
    simpa [start] using frame 1 (by intro role; fin_cases role <;> decide)
  have afterTape : countTape after = Tape.mk₁ (encodeNat (value + 1)) := by
    have same := congrArg TM0.Cfg.Tape result
    exact same.trans oldTape
  have pair : [before, countCall before bit rest].IsChain
      (fun a b => TM2.step countProgram a = some b) :=
    List.isChain_cons_cons.mpr ⟨count_gate_cons before bit rest position ticks,
      List.isChain_singleton _⟩
  have actual := PDROC.BitVM.Log.TwoStack.join_chain
    [before, countCall before bit rest] run (countCall before bit rest) pair chain rfl first
  have glued : [before, countCall before bit rest] ++ run.tail = before :: run := by
    change before :: ([countCall before bit rest] ++ run.tail) = before :: run
    exact congrArg (List.cons before) (List.cons_head?_tail (by rw [first]; rfl))
  rw [glued] at actual
  refine ⟨before :: run, after, rfl, actual,
    ?_, returned, afterTape, tailTicks, output, ?_⟩
  · rw [List.getLast?_cons, last]
    rfl
  · simp only [List.length_cons]
    omega

end PDROC.BitVM.Codec.OutputList

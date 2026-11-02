module

public import Paid.PDROC_BitVM_Codec_Output_List_003
public import Paid.PDROC_BitVM_Native_Return_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing PDROC.BitVM.Log.TwoStack

abbrev EmitStack := Fin 4
abbrev EmitLabel := Fin 4
abbrev EmitStore := Store × Unit
abbrev EmitState := TM2.Cfg (fun _ : EmitStack => Bool) EmitLabel EmitStore
abbrev EmitStatement := TM2.Stmt (fun _ : EmitStack => Bool) EmitLabel EmitStore

def copyRoles : Stack ↪ EmitStack :=
  ⟨fun role => ⟨role.val, Nat.lt_trans role.isLt (by decide)⟩,
    fun _ _ equal => Fin.ext (congrArg (fun role : EmitStack => role.val) equal)⟩

def copyLabels : Label → EmitLabel :=
  fun label => ⟨label.val, Nat.lt_trans label.isLt (by decide)⟩

/-- Local HALT is a real return jump to label 3. Only that next actual
instruction pushes the emission tick. All choices inspect fixed labels
or the finite Option Bool store, never the emitted word or its length. -/
def emitProgram (label : EmitLabel) : EmitStatement :=
  if small : label.val < 3 then
    PDROC.BitVM.Native.Inline.statement copyLabels 3
      (PDROC.BitVM.Native.Lift.statement copyRoles
        (copyReverseProgram ⟨label.val, small⟩))
  else .push 3 (fun _ => true) .halt

def emitSlots (word target scratch ticks : List Bool) : EmitStack → List Bool :=
  fun role => if role = 0 then word else if role = 1 then target
    else if role = 2 then scratch else ticks

def emitBefore (word target ticks : List Bool) : EmitState :=
  ⟨some 0, (none, ()), emitSlots word target [] ticks⟩

def emitMiddle (word target ticks : List Bool) : EmitState :=
  ⟨some 3, (none, ()), emitSlots word (word.reverse ++ target) [] ticks⟩

def emitAfter (word target ticks : List Bool) : EmitState :=
  ⟨none, (none, ()), emitSlots word (word.reverse ++ target) [] (true :: ticks)⟩

theorem emitProgram_agrees (label : Label) :
    emitProgram (copyLabels label) =
      PDROC.BitVM.Native.Inline.statement copyLabels 3
        (PDROC.BitVM.Native.Lift.machine copyRoles copyReverseProgram label) := by
  fin_cases label <;> rfl

theorem emit_tick (word target ticks : List Bool) :
    TM2.step emitProgram (emitMiddle word target ticks) =
      some (emitAfter word target ticks) := by
  change (some ⟨none, (none, ()), Function.update
    (emitSlots word (word.reverse ++ target) [] ticks) 3 (true :: ticks)⟩ : Option EmitState) = _
  have same : Function.update (emitSlots word (word.reverse ++ target) [] ticks) 3
      (true :: ticks) = emitSlots word (word.reverse ++ target) [] (true :: ticks) := by
    funext role
    fin_cases role <;> simp [emitSlots]
  rw [same]
  rfl

/-- ONE selected real path copies the actual Cell word and then updates
the unary count. Its arbitrary previous output and ticks are caller data.
This component does not supply, evaluate or assume a numeric count. -/
theorem emit_runs (word target ticks : List Bool) :
    ∃ run : List EmitState,
      run.head? = some (emitBefore word target ticks) ∧
      run.IsChain (fun a b => TM2.step emitProgram a = some b) ∧
      run.getLast? = some (emitAfter word target ticks) ∧
      TM2.step emitProgram (emitAfter word target ticks) = none ∧
      run.length = 2 * word.length + 4 ∧
      (emitAfter word target ticks).stk 0 = word ∧
      (emitAfter word target ticks).stk 1 = word.reverse ++ target ∧
      (emitAfter word target ticks).stk 2 = [] ∧
      (emitAfter word target ticks).stk 3 = true :: ticks := by
  let start : TM2.Cfg (fun _ : EmitStack => Bool) Label Store :=
    ⟨some 0, none, emitSlots word target [] ticks⟩
  have entry : PDROC.BitVM.Native.Lift.cfg copyRoles start =
      copyState (some 0) none word target [] := by
    have same : PDROC.BitVM.Native.Lift.slots copyRoles (emitSlots word target [] ticks) =
        threeStacks word target [] := by
      funext role
      fin_cases role <;> rfl
    change (⟨some 0, none, _⟩ : State) = _
    rw [same]
    rfl
  obtain ⟨source, localFinal, head, chain, last, halt, represented, size, frame⟩ :=
    copyReverse_work_runs copyRoles start word target entry
  have localSlots : localFinal.stk = emitSlots word (word.reverse ++ target) [] ticks := by
    funext role
    fin_cases role
    · exact congrArg (fun state : State => state.stk 0) represented
    · exact congrArg (fun state : State => state.stk 1) represented
    · exact congrArg (fun state : State => state.stk 2) represented
    · exact frame 3 (by intro role; fin_cases role <;> decide)
  have localVar : localFinal.var = none := congrArg (fun state : State => state.var) represented
  obtain ⟨run, middle, first, actual, middleLast, returned, stackData, store, length⟩ :=
    PDROC.BitVM.Native.Inline.actual_return_trace copyLabels 3
      (PDROC.BitVM.Native.Lift.machine copyRoles copyReverseProgram) emitProgram
      emitProgram_agrees source start localFinal () head chain last halt
  have first' : run.head? = some (emitBefore word target ticks) := first
  have middleEq : middle = emitMiddle word target ticks := by
    rcases middle with ⟨label, finiteStore, contents⟩
    change label = some 3 at returned
    change contents = localFinal.stk at stackData
    change finiteStore = (localFinal.var, ()) at store
    rw [localVar] at store
    subst label
    subst finiteStore
    rw [stackData, localSlots]
    rfl
  rw [middleEq] at middleLast
  have lastPair : [emitMiddle word target ticks, emitAfter word target ticks].IsChain
      (fun a b => TM2.step emitProgram a = some b) :=
    List.isChain_cons_cons.mpr ⟨emit_tick word target ticks, List.isChain_singleton _⟩
  refine ⟨run ++ [emitAfter word target ticks], ?_, ?_, ?_, rfl, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [List.head?_append, first', Option.some_or]
  · simpa only [List.tail_cons, List.tail_nil] using
      join_chain run [emitMiddle word target ticks, emitAfter word target ticks]
        (emitMiddle word target ticks) actual lastPair middleLast rfl
  · exact List.getLast?_append_cons run (emitAfter word target ticks) []
  · simp only [List.length_append, List.length_singleton, length, size]

end PDROC.BitVM.Codec.OutputList

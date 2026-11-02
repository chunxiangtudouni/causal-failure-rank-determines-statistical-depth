module

public import Paid.PDROC_BitVM_Codec_RatAssembler_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Codec.RatAssembler

open Turing PDROC.BitVM.Native

abbrev NatState := TM2.Cfg (fun _ : Fin 3 => Bool) PDROC.BitVM.Kernel.NatMarshal.Label (Option Bool)

def natBefore (word target : List Bool) (saved : Option Bool) : NatState :=
  ⟨some 0, saved, PDROC.BitVM.Log.TwoStack.threeStacks (false :: word) target []⟩

def natAfter (word target : List Bool) : NatState :=
  ⟨none, none, PDROC.BitVM.Log.TwoStack.threeStacks (false :: word) (word ++ target) []⟩

/-- The existing complete Nat Cell tag/copy/restore path, transported only
through a fixed finite-store isomorphism. No Nat or Rat is read by host. -/
theorem nat_runs (word target : List Bool) (saved : Option Bool) :
    ∃ run : List NatState,
      run.head? = some (natBefore word target saved) ∧
      run.IsChain (fun a b => TM2.step natProgram a = some b) ∧
      run.getLast? = some (natAfter word target) ∧
      TM2.step natProgram (natAfter word target) = none ∧
      run.length = 2 * word.length + 5 := by
  obtain ⟨source, sourceHead, sourceChain, sourceLast, sourceHalt, sourceTime,
    _original, _target, _scratch⟩ := PDROC.BitVM.Kernel.NatMarshal.marshal_runs word target saved
  obtain ⟨run, after, head, chain, last, halt, position, finalStore, data, time⟩ :=
    StoreIso.actual_trace natStoreIso PDROC.BitVM.Kernel.NatMarshal.program source
      (PDROC.BitVM.Kernel.NatMarshal.before word target saved)
      (PDROC.BitVM.Kernel.NatMarshal.final word target)
      sourceHead sourceChain sourceLast sourceHalt
  have final : after = natAfter word target := by
    rcases after with ⟨label, store, contents⟩
    change label = none at position
    change store = none at finalStore
    change contents = PDROC.BitVM.Log.TwoStack.threeStacks (false :: word) (word ++ target) [] at data
    subst label
    subst store
    subst contents
    rfl
  rw [final] at last halt
  exact ⟨run, head, chain, last, halt, time.trans sourceTime⟩

/-- A genuine clear call on one selected physical role, including every
old FALSE byte. Its input finite store may be arbitrary; the caller Bool
sign is preserved by the actual Inline map. -/
theorem clear_call (caller : Label → Statement) (start finish : Label) (embed : Fin 3 ↪ Stack)
    (role : Fin 3)
    (agrees : ∀ label : Unit, caller start = Inline.statement (fun _ : Unit => start) finish
      (Lift.machine embed (NatWriter.clearProgram role) label))
    (contents : Stack → List Bool) (saved : Option Bool) (sign : Bool) :
    ∃ path : RatMarshal.Trace caller (⟨some start, (saved, sign), contents⟩ : State)
      (⟨some finish, (none, sign), Function.update contents (embed role) []⟩ : State),
      path.states.length = (contents (embed role)).length + 2 := by
  let localContents := Lift.slots embed contents
  obtain ⟨run, head, chain, last, _halt, time, _frame⟩ := NatWriter.clear_runs role localContents saved
  obtain ⟨path, length⟩ := RatMarshal.call_three embed (NatWriter.clearProgram role) caller
    (fun _ : Unit => start) finish agrees
    (⟨some (), saved, localContents⟩ : NatWriter.ClearState)
    (⟨none, none, Function.update localContents role []⟩ : NatWriter.ClearState)
    run head chain last rfl contents (Function.update contents (embed role) []) sign rfl
    (Lift.slots_update embed contents role [])
    (by
      intro other outside
      exact Function.update_of_ne (outside role) _ _)
  exact ⟨path, length.trans time⟩

/-- The target retains its existing actual bare suffix. In the real
den-first/num-second sequence this forms numeratorWord++denominatorWord,
while each complete source Nat Cell is restored byte-for-byte. -/
theorem nat_call (caller : Label → Statement)
    (labels : PDROC.BitVM.Kernel.NatMarshal.Label → Label) (finish : Label)
    (temp : Fin 7) (target : Register)
    (agrees : ∀ label, caller (labels label) = Inline.statement labels finish
      (Lift.machine (embedding temp target) natProgram label))
    (contents : Stack → List Bool) (word : List Bool) (sign : Bool)
    (sourceWord : contents (RatMarshal.tempSlot temp) = false :: word)
    (scratch : contents 24 = []) :
    ∃ path : RatMarshal.Trace caller (⟨some (labels 0), (none, sign), contents⟩ : State)
      (⟨some finish, (none, sign), Function.update contents
        (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target)
        (word ++ contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target))⟩ : State),
      path.states.length = 2 * word.length + 5 := by
  let targetWord := contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target)
  obtain ⟨run, head, chain, last, _halt, time⟩ := nat_runs word targetWord none
  have beforeData := RatMarshal.three_selected (embedding temp target) contents
    (false :: word) targetWord [] sourceWord rfl scratch
  have afterData : Lift.slots (embedding temp target)
      (Function.update contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target) (word ++ targetWord)) =
        PDROC.BitVM.Log.TwoStack.threeStacks (false :: word) (word ++ targetWord) [] := by
    change Lift.slots (embedding temp target)
      (Function.update contents ((embedding temp target) 1) (word ++ targetWord)) = _
    rw [Lift.slots_update, beforeData, Copy.update_second]
  obtain ⟨path, length⟩ := RatMarshal.call_three (embedding temp target) natProgram caller labels finish agrees
    (natBefore word targetWord none) (natAfter word targetWord) run head chain last rfl contents
    (Function.update contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target) (word ++ targetWord))
    sign beforeData afterData
    (by
      intro other outside
      exact Function.update_of_ne (outside 1) _ _)
  exact ⟨path, length.trans time⟩

theorem tag_step (target : Register) (num den : Fin 7) (contents : Stack → List Bool)
    (saved : Option Bool) (sign : Bool) :
    TM2.step (program target num den) (⟨some 12, (saved, sign), contents⟩ : State) =
      some (⟨none, (saved, sign), Function.update contents
        (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target)
        (true :: sign :: contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target))⟩ : State) := by
  change some (TM2.stepAux
    (.push (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target) (fun saved : Store => saved.2)
      (.push (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target) (fun _ => true) .halt))
    (saved, sign) contents) = _
  simp only [TM2.stepAux, Function.update_self]
  have same : Function.update
      (Function.update contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target)
        (sign :: contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target)))
      (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target)
      (true :: sign :: contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target)) =
      Function.update contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target)
        (true :: sign :: contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target)) := by
    funext role
    by_cases selected : role = PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target <;> simp_all
  rw [same]

end PDROC.BitVM.Codec.RatAssembler

module

public import Common.PSTR_WordVM_KeyCompare_010

/-! Coherent actual miss-value and physical-front restoration blocks of
the ONE fixed bank source. PhaseRun records the explicit SAME path/count;
its count is not a runtime store field or an externally supplied oracle. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.UniqueStore.BankSegments

open Turing KeyCompare

structure PhaseRun (caller : Statement) (path : List State) (first last : State) (steps : Nat) : Prop where
  head : path.head? = some first
  chain : path.IsChain (fun before after => TM2.step (program caller) before = some after)
  last : path.getLast? = some last
  length : path.length = steps + 1

theorem PhaseRun.nonempty {caller : Statement} {path : List State} {first last : State} {steps : Nat}
    (run : PhaseRun caller path first last steps) : path ≠ [] := by
  intro same
  have head := run.head
  rw [same] at head
  cases head

theorem PhaseRun.prepend {caller : Statement} {path : List State} {first middle last : State} {steps : Nat}
    (edge : TM2.step (program caller) first = some middle)
    (run : PhaseRun caller path middle last steps) : PhaseRun caller (first :: path) first last (steps + 1) := by
  refine ⟨rfl, FieldCopy.prepend_chain _ _ _ _ run.head edge run.chain, ?_, ?_⟩
  · rw [FieldCopy.last_cons_of_nonempty _ _ run.nonempty]
    exact run.last
  · simpa only [List.length_cons] using congrArg (fun count => count + 1) run.length

theorem PhaseRun.decomp {caller : Statement} {path : List State} {first last : State} {steps : Nat}
    (run : PhaseRun caller path first last steps) : first :: path.tail = path := by
  cases path with
  | nil => have head := run.head; cases head
  | cons head tail =>
    have same := Option.some.inj run.head
    subst head
    rfl

theorem PhaseRun.join {caller : Statement} {left right : List State} {first middle last : State} {a b : Nat}
    (leftRun : PhaseRun caller left first middle a) (rightRun : PhaseRun caller right middle last b) :
    PhaseRun caller (left ++ right.tail) first last (a + b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.head?_append, leftRun.head]
    rfl
  · have rightChain := rightRun.chain
    rw [← rightRun.decomp] at rightChain
    exact PSTRWordBool.NativeTrace.join_chain _ middle _ leftRun.last leftRun.chain rightChain
  · rw [PSTRWordBool.NativeTrace.join_last _ middle _ leftRun.last, rightRun.decomp]
    exact rightRun.last
  · simp only [List.length_append, List.length_tail, leftRun.length, rightRun.length]
    omega

theorem skip_bit (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields)
    (oldBit : Bool) (bankTail widthTail : List Bool) :
    TM2.step (program caller) (state background 5 (saved, (e, flags))
      { fields with bank := oldBit :: bankTail, width := true :: widthTail }) =
      some (state background 5 ((true, oldBit), (e, flags))
        { fields with bank := bankTail, width := widthTail, front := oldBit :: fields.front, used := true :: fields.used }) := by
  simp [state, program, widthBranch, TM2.step, TM2.stepAux, captureWidth, captureData,
    present, bit, jump, at_width, at_bank, at_front, at_used,
    update_width, update_bank, update_front, update_used]

theorem skip_done (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) :
    TM2.step (program caller) (state background 5 (saved, (e, flags)) { fields with width := [] }) =
      some (state background 6 ((false, saved.2), (e, flags)) { fields with width := [] }) := by
  simp [state, program, widthBranch, TM2.step, TM2.stepAux, captureWidth, present, jump,
    at_width, update_width]

def skipStart (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (oldValue tail : List Bool) (fields : Fields) : State :=
  state background 5 (saved, (e, flags))
    { fields with bank := oldValue ++ tail, width := List.replicate oldValue.length true }

def skipped (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (oldValue tail : List Bool) (fields : Fields) : State :=
  state background 6 ((false, FieldCopy.lastRead saved oldValue), (e, flags))
    { fields with bank := tail, width := [], front := oldValue.reverse ++ fields.front, used := List.replicate oldValue.length true ++ fields.used }

def skipTrace (background : Stack → List Bool) (e : Bool) (flags : CallerFlags) :
    FieldCopy.Store → List Bool → List Bool → Fields → List State
  | saved, [], tail, fields => [skipStart background saved e flags [] tail fields,
      skipped background saved e flags [] tail fields]
  | saved, oldBit :: later, tail, fields =>
      skipStart background saved e flags (oldBit :: later) tail fields ::
        skipTrace background e flags (true, oldBit) later tail
          { fields with front := oldBit :: fields.front, used := true :: fields.used }

theorem skip_run (caller : Statement) (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (oldValue tail : List Bool) (fields : Fields) :
    PhaseRun caller (skipTrace background e flags saved oldValue tail fields)
      (skipStart background saved e flags oldValue tail fields)
      (skipped background saved e flags oldValue tail fields) (oldValue.length + 1) := by
  induction oldValue generalizing saved fields with
  | nil =>
    refine ⟨rfl, ?_, rfl, rfl⟩
    apply List.isChain_cons_cons.mpr
    refine ⟨?_, List.isChain_singleton _⟩
    simpa only [skipStart, skipped, FieldCopy.lastRead, List.nil_append, List.reverse_nil,
      List.length_nil, List.replicate_zero] using
      skip_done caller background saved e flags { fields with bank := tail }
  | cons oldBit later ih =>
    have rest := ih (true, oldBit)
      { fields with front := oldBit :: fields.front, used := true :: fields.used }
    have edge : TM2.step (program caller) (skipStart background saved e flags (oldBit :: later) tail fields) =
        some (skipStart background (true, oldBit) e flags later tail
          { fields with front := oldBit :: fields.front, used := true :: fields.used }) := by
      simpa only [skipStart, List.cons_append, List.length_cons, List.replicate_succ] using
        skip_bit caller background saved e flags fields oldBit (later ++ tail) (List.replicate later.length true)
    have full := PhaseRun.prepend edge rest
    simpa only [skipTrace, skipped, FieldCopy.lastRead, List.length_cons, List.replicate_succ',
      List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using full

theorem width_bit (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) (tail : List Bool) :
    TM2.step (program caller) (state background 6 (saved, (e, flags)) { fields with used := true :: tail }) =
      some (state background 6 ((true, saved.2), (e, flags))
        { fields with used := tail, width := true :: fields.width }) := by
  simp [state, program, TM2.step, TM2.stepAux, captureWidth, present, jump, at_used,
    at_width, update_used, update_width]

theorem width_done (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) :
    TM2.step (program caller) (state background 6 (saved, (e, flags)) { fields with used := [] }) =
      some (state background 0 ((false, saved.2), (e, flags)) { fields with used := [] }) := by
  simp [state, program, TM2.step, TM2.stepAux, captureWidth, present, jump, at_used, update_used]

def widthStart (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (amount : Nat) (fields : Fields) : State :=
  state background 6 (saved, (e, flags)) { fields with used := List.replicate amount true }

def widthRestored (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (amount : Nat) (fields : Fields) : State :=
  state background 0 ((false, saved.2), (e, flags))
    { fields with used := [], width := List.replicate amount true ++ fields.width }

def widthTrace (background : Stack → List Bool) (e : Bool) (flags : CallerFlags) :
    FieldCopy.Store → Nat → Fields → List State
  | saved, 0, fields => [widthStart background saved e flags 0 fields, widthRestored background saved e flags 0 fields]
  | saved, amount + 1, fields => widthStart background saved e flags (amount + 1) fields ::
      widthTrace background e flags (true, saved.2) amount { fields with width := true :: fields.width }

theorem width_run (caller : Statement) (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (amount : Nat) (fields : Fields) :
    PhaseRun caller (widthTrace background e flags saved amount fields)
      (widthStart background saved e flags amount fields)
      (widthRestored background saved e flags amount fields) (amount + 1) := by
  induction amount generalizing saved fields with
  | zero =>
    refine ⟨rfl, ?_, rfl, rfl⟩
    apply List.isChain_cons_cons.mpr
    refine ⟨?_, List.isChain_singleton _⟩
    simpa only [widthStart, widthRestored, List.replicate_zero, List.nil_append] using
      width_done caller background saved e flags fields
  | succ amount ih =>
    have rest := ih (true, saved.2) { fields with width := true :: fields.width }
    have edge : TM2.step (program caller) (widthStart background saved e flags (amount + 1) fields) =
        some (widthStart background (true, saved.2) e flags amount { fields with width := true :: fields.width }) := by
      simpa only [widthStart, List.replicate_succ] using
        width_bit caller background saved e flags fields (List.replicate amount true)
    have full := PhaseRun.prepend edge rest
    simpa only [widthTrace, widthRestored, List.replicate_succ',
      List.append_assoc, List.cons_append, List.nil_append] using full

theorem write_bit (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields)
    (oldBit newBit : Bool) (oldTail newTail widthTail : List Bool) :
    TM2.step (program caller) (state background 3 (saved, (e, flags))
      { fields with bank := oldBit :: oldTail, value := newBit :: newTail, width := true :: widthTail }) =
      some (state background 3 ((true, newBit), (e, flags))
        { fields with bank := oldTail, value := newTail, width := widthTail, front := newBit :: fields.front, valueSaved := newBit :: fields.valueSaved, used := true :: fields.used }) := by
  simp [state, program, widthBranch, TM2.step, TM2.stepAux, captureWidth, captureData,
    present, bit, jump, at_width, at_bank, at_value, at_front, at_valueSaved, at_used,
    update_width, update_bank, update_value, update_front, update_valueSaved, update_used]

theorem write_done (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) :
    TM2.step (program caller) (state background 3 (saved, (e, flags)) { fields with width := [] }) =
      some (state background 4 ((false, saved.2), (e, flags)) { fields with width := [] }) := by
  simp [state, program, widthBranch, TM2.step, TM2.stepAux, captureWidth, present, jump,
    at_width, update_width]

def writeStart (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (oldValue newValue tail : List Bool) (fields : Fields) : State :=
  state background 3 (saved, (e, flags))
    { fields with bank := oldValue ++ tail, value := newValue, width := List.replicate newValue.length true }

def writeStopped (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (oldValue tail : List Bool) (fields : Fields) : State :=
  state background 4 ((false, saved.2), (e, flags))
    { fields with bank := oldValue ++ tail, value := [], width := [] }

def written (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (newValue tail : List Bool) (fields : Fields) : State :=
  state background 4 ((false, FieldCopy.lastRead saved newValue), (e, flags))
    { fields with bank := tail, value := [], width := [], front := newValue.reverse ++ fields.front, valueSaved := newValue.reverse ++ fields.valueSaved, used := List.replicate newValue.length true ++ fields.used }

def writeTrace (background : Stack → List Bool) (e : Bool) (flags : CallerFlags) :
    FieldCopy.Store → List Bool → List Bool → List Bool → Fields → List State
  | saved, oldValue, [], tail, fields => [writeStart background saved e flags oldValue [] tail fields,
      writeStopped background saved e flags oldValue tail fields]
  | saved, oldValue, newBit :: later, tail, fields =>
      writeStart background saved e flags oldValue (newBit :: later) tail fields ::
        writeTrace background e flags (true, newBit) oldValue.tail later tail
          { fields with front := newBit :: fields.front, valueSaved := newBit :: fields.valueSaved, used := true :: fields.used }

theorem write_run (caller : Statement) (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (oldValue newValue tail : List Bool) (fields : Fields)
    (lengths : oldValue.length = newValue.length) :
    PhaseRun caller (writeTrace background e flags saved oldValue newValue tail fields)
      (writeStart background saved e flags oldValue newValue tail fields)
      (written background saved e flags newValue tail fields) (newValue.length + 1) := by
  induction newValue generalizing saved oldValue fields with
  | nil =>
    cases oldValue with
    | nil =>
      refine ⟨rfl, ?_, ?_, rfl⟩
      · apply List.isChain_cons_cons.mpr
        refine ⟨?_, List.isChain_singleton _⟩
        simpa only [writeStart, writeStopped, FieldCopy.lastRead, List.nil_append, List.reverse_nil,
          List.length_nil, List.replicate_zero] using
          write_done caller background saved e flags { fields with bank := tail, value := [] }
      · simp only [writeTrace, List.getLast?_cons_cons, List.getLast?_singleton, writeStopped,
          written, FieldCopy.lastRead, List.reverse_nil, List.length_nil, List.replicate_zero, List.nil_append]
    | cons _ _ => simp at lengths
  | cons newBit later ih =>
    cases oldValue with
    | nil => simp at lengths
    | cons oldBit restOld =>
      have smaller : restOld.length = later.length := by
        simp only [List.length_cons] at lengths
        omega
      have rest := ih (true, newBit) restOld
        { fields with front := newBit :: fields.front, valueSaved := newBit :: fields.valueSaved, used := true :: fields.used } smaller
      have edge : TM2.step (program caller) (writeStart background saved e flags
          (oldBit :: restOld) (newBit :: later) tail fields) =
          some (writeStart background (true, newBit) e flags restOld later tail
            { fields with front := newBit :: fields.front, valueSaved := newBit :: fields.valueSaved, used := true :: fields.used }) := by
        simpa only [writeStart, List.cons_append, List.length_cons, List.replicate_succ] using
          write_bit caller background saved e flags fields oldBit newBit (restOld ++ tail)
            later (List.replicate later.length true)
      have full := PhaseRun.prepend edge rest
      simpa only [writeTrace, written, FieldCopy.lastRead, List.length_cons, List.replicate_succ',
        List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append, List.tail_cons] using full

theorem value_back_bit (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields)
    (newBit : Bool) (valueTail usedTail : List Bool) :
    TM2.step (program caller) (state background 4 (saved, (e, flags))
      { fields with valueSaved := newBit :: valueTail, used := true :: usedTail }) =
      some (state background 4 ((true, newBit), (e, flags))
        { fields with value := newBit :: fields.value, width := true :: fields.width, valueSaved := valueTail, used := usedTail }) := by
  simp [state, program, restoreWidth, TM2.step, TM2.stepAux, captureData, present, bit, jump,
    at_valueSaved, at_value, at_used, at_width, update_valueSaved, update_value, update_used, update_width]

theorem value_back_done (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) :
    TM2.step (program caller) (state background 4 (saved, (e, flags)) { fields with valueSaved := [] }) =
      some (state background 11 ((false, false), (e, flags)) { fields with valueSaved := [] }) := by
  simp [state, program, TM2.step, TM2.stepAux, captureData, present, jump, at_valueSaved, update_valueSaved]

def valueBackStart (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (reversed : List Bool) (fields : Fields) : State :=
  state background 4 (saved, (e, flags))
    { fields with valueSaved := reversed, used := List.replicate reversed.length true }

def valueRestored (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (reversed : List Bool) (fields : Fields) : State :=
  state background 11 ((false, false), (e, flags))
    { fields with value := reversed.reverse ++ fields.value, width := List.replicate reversed.length true ++ fields.width, valueSaved := [], used := [] }

def valueBackTrace (background : Stack → List Bool) (e : Bool) (flags : CallerFlags) :
    FieldCopy.Store → List Bool → Fields → List State
  | saved, [], fields => [valueBackStart background saved e flags [] fields, valueRestored background e flags [] fields]
  | saved, newBit :: later, fields => valueBackStart background saved e flags (newBit :: later) fields ::
      valueBackTrace background e flags (true, newBit) later
        { fields with value := newBit :: fields.value, width := true :: fields.width }

theorem value_back_run (caller : Statement) (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (reversed : List Bool) (fields : Fields) :
    PhaseRun caller (valueBackTrace background e flags saved reversed fields)
      (valueBackStart background saved e flags reversed fields)
      (valueRestored background e flags reversed fields) (reversed.length + 1) := by
  induction reversed generalizing saved fields with
  | nil =>
    refine ⟨rfl, ?_, rfl, rfl⟩
    apply List.isChain_cons_cons.mpr
    refine ⟨?_, List.isChain_singleton _⟩
    simpa only [valueBackStart, valueRestored, List.reverse_nil, List.length_nil, List.replicate_zero,
      List.nil_append] using value_back_done caller background saved e flags { fields with used := [] }
  | cons newBit later ih =>
    have rest := ih (true, newBit)
      { fields with value := newBit :: fields.value, width := true :: fields.width }
    have edge : TM2.step (program caller) (valueBackStart background saved e flags (newBit :: later) fields) =
        some (valueBackStart background (true, newBit) e flags later
          { fields with value := newBit :: fields.value, width := true :: fields.width }) := by
      simpa only [valueBackStart, List.length_cons, List.replicate_succ] using
        value_back_bit caller background saved e flags fields newBit later (List.replicate later.length true)
    have full := PhaseRun.prepend edge rest
    simpa only [valueBackTrace, valueRestored, List.reverse_cons, List.length_cons,
      List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append] using full

theorem front_bit (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields)
    (oldBit : Bool) (tail : List Bool) :
    TM2.step (program caller) (state background 11 (saved, (e, flags)) { fields with front := oldBit :: tail }) =
      some (state background 11 ((true, oldBit), (e, flags))
        { fields with front := tail, bank := oldBit :: fields.bank }) := by
  simp [state, program, TM2.step, TM2.stepAux, captureData, present, bit, jump,
    at_front, at_bank, update_front, update_bank]

theorem front_done (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) :
    TM2.step (program caller) (state background 11 (saved, (e, flags)) { fields with front := [] }) =
      some (state background 12 ((false, false), (e, flags)) { fields with front := [] }) := by
  simp [state, program, TM2.step, TM2.stepAux, captureData, present, jump, at_front, update_front]

def frontStart (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (frontPart : List Bool) (fields : Fields) : State :=
  state background 11 (saved, (e, flags)) { fields with front := frontPart }

def frontRestored (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (frontPart : List Bool) (fields : Fields) : State :=
  state background 12 ((false, false), (e, flags))
    { fields with front := [], bank := frontPart.reverse ++ fields.bank }

def frontTrace (background : Stack → List Bool) (e : Bool) (flags : CallerFlags) :
    FieldCopy.Store → List Bool → Fields → List State
  | saved, [], fields => [frontStart background saved e flags [] fields, frontRestored background e flags [] fields]
  | saved, oldBit :: later, fields => frontStart background saved e flags (oldBit :: later) fields ::
      frontTrace background e flags (true, oldBit) later { fields with bank := oldBit :: fields.bank }

theorem front_run (caller : Statement) (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (frontPart : List Bool) (fields : Fields) :
    PhaseRun caller (frontTrace background e flags saved frontPart fields)
      (frontStart background saved e flags frontPart fields)
      (frontRestored background e flags frontPart fields) (frontPart.length + 1) := by
  induction frontPart generalizing saved fields with
  | nil =>
    refine ⟨rfl, ?_, rfl, rfl⟩
    apply List.isChain_cons_cons.mpr
    refine ⟨?_, List.isChain_singleton _⟩
    simpa only [frontStart, frontRestored, List.reverse_nil, List.nil_append] using
      front_done caller background saved e flags fields
  | cons oldBit later ih =>
    have rest := ih (true, oldBit) { fields with bank := oldBit :: fields.bank }
    have edge := front_bit caller background saved e flags fields oldBit later
    have full := PhaseRun.prepend edge rest
    simpa only [frontTrace, frontStart, frontRestored, List.reverse_cons, List.length_cons,
      List.append_assoc, List.cons_append, List.nil_append] using full

/-- The final port-to-caller edge is actual program12, not a renamed HALT. -/
def frontReturnTrace (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (frontPart : List Bool) (fields : Fields) : List State :=
  frontTrace background e flags saved frontPart fields ++
    [⟨some 13, ((false, false), (e, flags)),
      (frontRestored background e flags frontPart fields).stk⟩]

theorem front_return_run (caller : Statement) (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (frontPart : List Bool) (fields : Fields) :
    PhaseRun caller (frontReturnTrace background e flags saved frontPart fields)
      (frontStart background saved e flags frontPart fields)
      ⟨some 13, ((false, false), (e, flags)), (frontRestored background e flags frontPart fields).stk⟩
      (frontPart.length + 2) := by
  have before := front_run caller background e flags saved frontPart fields
  refine ⟨?_, ?_, List.getLast?_append_cons _ _ [], ?_⟩
  · rw [frontReturnTrace, List.head?_append, before.head]
    rfl
  · apply PSTRWordBool.NativeTrace.join_chain _ (frontRestored background e flags frontPart fields) _ before.last before.chain
    exact List.isChain_cons_cons.mpr ⟨actual_return caller _ _, List.isChain_singleton _⟩
  · simp only [frontReturnTrace, List.length_append, before.length, List.length_cons, List.length_nil]

end PaperProofs.Common.Native.PSTRWordVM.UniqueStore.BankSegments

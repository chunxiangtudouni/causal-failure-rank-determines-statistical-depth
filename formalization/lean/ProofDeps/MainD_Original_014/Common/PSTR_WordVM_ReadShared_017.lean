module

public import Common.PSTR_WordVM_BankReadCode_016

/-! Reuse of frozen actual search paths in the real reader. The transport
checks syntax at EVERY proper source state of the SAME list; endpoints
are not executed for free. Copy hits use the real FieldCopy prefix and
constant readRole, not a semantic lookup oracle or a second run. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.UniqueRead

open Turing UniqueStore UniqueStore.KeyCompare UniqueStore.BankSegments UniqueStore.RecordSegments

def SourceShared (current : State) : Prop :=
  ∃ point, current.l = some point ∧ Shared point

theorem Run.decomp {caller : Statement} {path : List State} {first last : State} {steps : Nat}
    (actual : Run caller path first last steps) : first :: path.tail = path := by
  cases path with
  | nil => have head := actual.head; cases head
  | cons head tail =>
    have same := Option.some.inj actual.head
    subst head
    rfl

theorem Run.join {caller : Statement} {left right : List State} {first middle last : State} {a b : Nat}
    (leftRun : Run caller left first middle a) (rightRun : Run caller right middle last b) :
    Run caller (left ++ right.tail) first last (a + b) := by
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

/-- This internal premise is discharged below by the concrete frozen
trace descriptions. It is never an original caller performance premise. -/
theorem shared_run (caller : Statement) (path : List State) (first last : State) (steps : Nat)
    (old : PhaseRun caller path first last steps)
    (proper : ∀ current ∈ path.dropLast, SourceShared current) :
    Run caller path first last steps := by
  refine ⟨old.head, ?_, old.last, old.length⟩
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro before after left right decomp
  have edge := List.isChain_iff_forall_rel_of_append_cons_cons.mp old.chain decomp
  have member : before ∈ path.dropLast := by
    rw [decomp, List.dropLast_append_cons, List.dropLast_cons_cons]
    simp
  obtain ⟨point, same, shared⟩ := proper before member
  rcases before with ⟨position, memory, bankSlots⟩
  change position = some point at same
  subst position
  rw [shared_step caller point memory bankSlots shared]
  exact edge

theorem compare_shared (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (key query tail : List Bool) (fields : Fields) :
    ∀ current ∈ compareTrace background flags saved e key query tail fields, SourceShared current := by
  induction query generalizing saved e key fields with
  | nil =>
    intro current present
    simp only [compareTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact ⟨1, rfl, Or.inl rfl⟩
    · exact ⟨2, rfl, Or.inr (Or.inl rfl)⟩
  | cons bit later ih =>
    intro current present
    rcases List.mem_cons.mp present with same | after
    · subst current
      exact ⟨1, rfl, Or.inl rfl⟩
    · exact ih _ _ _ _ current after

theorem restore_proper (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (reversed : List Bool) (fields : Fields) :
    ∀ current ∈ (restoreTrace background e flags saved reversed fields).dropLast, SourceShared current := by
  induction reversed generalizing saved fields with
  | nil =>
    intro current present
    simp only [restoreTrace, List.dropLast_cons_cons, List.dropLast_singleton, List.mem_singleton] at present
    subst current
    exact ⟨2, rfl, Or.inr (Or.inl rfl)⟩
  | cons bit later ih =>
    intro current present
    rw [restoreTrace, List.dropLast_cons_of_ne_nil (restoreTrace_nonempty _ _ _ _ _ _)] at present
    rcases List.mem_cons.mp present with same | after
    · subst current
      exact ⟨2, rfl, Or.inr (Or.inl rfl)⟩
    · exact ih _ _ current after

theorem skip_shared (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (oldValue tail : List Bool) (fields : Fields) :
    ∀ current ∈ skipTrace background e flags saved oldValue tail fields, SourceShared current := by
  induction oldValue generalizing saved fields with
  | nil =>
    intro current present
    simp only [skipTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact ⟨5, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨6, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  | cons bit later ih =>
    intro current present
    rcases List.mem_cons.mp present with same | after
    · subst current
      exact ⟨5, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ih _ _ current after

theorem width_proper (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (amount : Nat) (fields : Fields) :
    ∀ current ∈ (widthTrace background e flags saved amount fields).dropLast, SourceShared current := by
  induction amount generalizing saved fields with
  | zero =>
    intro current present
    simp only [widthTrace, List.dropLast_cons_cons, List.dropLast_singleton, List.mem_singleton] at present
    subst current
    exact ⟨6, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  | succ amount ih =>
    have nonempty : widthTrace background e flags (true, saved.2) amount
        { fields with width := true :: fields.width } ≠ [] := by
      cases amount <;> intro empty <;> cases empty
    intro current present
    rw [widthTrace, List.dropLast_cons_of_ne_nil nonempty] at present
    rcases List.mem_cons.mp present with same | after
    · subst current
      exact ⟨6, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · exact ih _ _ current after

theorem front_shared (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (frontPart : List Bool) (fields : Fields) :
    ∀ current ∈ frontTrace background e flags saved frontPart fields, SourceShared current := by
  induction frontPart generalizing saved fields with
  | nil =>
    intro current present
    simp only [frontTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact ⟨11, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
    · exact ⟨12, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
  | cons bit later ih =>
    intro current present
    rcases List.mem_cons.mp present with same | after
    · subst current
      exact ⟨11, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
    · exact ih _ _ current after

theorem front_return_run (caller : Statement) (background : Stack → List Bool) (e : Bool)
    (flags : CallerFlags) (saved : FieldCopy.Store) (frontPart : List Bool) (fields : Fields) :
    Run caller (frontReturnTrace background e flags saved frontPart fields)
      (frontStart background saved e flags frontPart fields)
      ⟨some 13, ((false, false), (e, flags)), (frontRestored background e flags frontPart fields).stk⟩
      (frontPart.length + 2) := by
  apply shared_run caller _ _ _ _ (BankSegments.front_return_run caller background e flags saved frontPart fields)
  intro current present
  rw [frontReturnTrace, List.dropLast_append_cons, List.dropLast_singleton, List.append_nil] at present
  exact front_shared background e flags saved frontPart fields current present

theorem key_run (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (key query value tail frontPart : List Bool) (lengths : key.length = query.length) :
    Run caller (RecordSegments.keyTrace background flags saved key query value tail frontPart)
      (RecordSegments.keyStart background flags saved key query value tail frontPart)
      (keyEnd background flags key query value tail frontPart) (2 * query.length + 2) := by
  let beforeFields := workFields query value tail frontPart
  have forwardOld : PhaseRun caller (compareTrace background flags saved true key query tail beforeFields)
      (compareStart background saved true flags key query tail beforeFields)
      (compared background saved true flags key query tail beforeFields) (query.length + 1) :=
    ⟨compareTrace_head _ _ _ _ _ _ _ _, compareTrace_chain caller _ _ _ _ _ _ _ _ lengths,
      compareTrace_last _ _ _ _ _ _ _ _ lengths, compareTrace_length _ _ _ _ _ _ _ _⟩
  have forward := shared_run caller _ _ _ _ forwardOld
    (fun current present => compare_shared background flags saved true key query tail beforeFields current
      (List.dropLast_subset _ present))
  let middleFields := keyMiddle key value tail frontPart
  have backOld : PhaseRun caller
      (restoreTrace background (eqBits key query) flags (false, FieldCopy.lastRead saved query) query.reverse middleFields)
      (restoreStart background (false, FieldCopy.lastRead saved query) (eqBits key query) flags query.reverse middleFields)
      (restored background (eqBits key query) flags query.reverse middleFields) (query.reverse.length + 1) :=
    ⟨restoreTrace_head _ _ _ _ _ _, restoreTrace_chain caller _ _ _ _ _ _,
      restoreTrace_last _ _ _ _ _ _, restoreTrace_length _ _ _ _ _ _⟩
  have back := shared_run caller _ _ _ _ backOld
    (restore_proper background (eqBits key query) flags (false, FieldCopy.lastRead saved query) query.reverse middleFields)
  have sameBack : Run caller
      (restoreTrace background (eqBits key query) flags (false, FieldCopy.lastRead saved query) query.reverse middleFields)
      (compared background saved true flags key query tail beforeFields)
      (keyEnd background flags key query value tail frontPart) (query.length + 1) := by
    simpa [restoreStart, compared, keyEnd, beforeFields, middleFields, keyMiddle, workFields] using back
  have actual := forward.join sameBack
  have count : (query.length + 1) + (query.length + 1) = 2 * query.length + 2 := by omega
  simpa only [RecordSegments.keyTrace, RecordSegments.keyStart, beforeFields, middleFields, count] using actual

theorem miss_run (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (query value oldValue tail frontPart : List Bool) :
    Run caller (missTrace background flags query value oldValue tail frontPart)
      (missStart background flags query value oldValue tail frontPart)
      (missEnd background flags query value oldValue tail frontPart) (2 * oldValue.length + 2) := by
  have forwardOld := skip_run caller background false flags (false, false) oldValue tail
    (workFields query value tail frontPart)
  have forward := shared_run caller _ _ _ _ forwardOld
    (fun current present => skip_shared background false flags (false, false) oldValue tail
      (workFields query value tail frontPart) current (List.dropLast_subset _ present))
  have backOld := width_run caller background false flags (false, FieldCopy.lastRead (false, false) oldValue)
    oldValue.length (missRestoreFields query value oldValue tail frontPart)
  have back := shared_run caller _ _ _ _ backOld
    (width_proper background false flags (false, FieldCopy.lastRead (false, false) oldValue)
      oldValue.length (missRestoreFields query value oldValue tail frontPart))
  have sameBack : Run caller
      (widthTrace background false flags (false, FieldCopy.lastRead (false, false) oldValue) oldValue.length
        (missRestoreFields query value oldValue tail frontPart))
      (skipped background (false, false) false flags oldValue tail (workFields query value tail frontPart))
      (missEnd background flags query value oldValue tail frontPart) (oldValue.length + 1) := by
    simpa [widthStart, skipped, missEnd, missRestoreFields, workFields] using back
  have actual := forward.join sameBack
  have count : (oldValue.length + 1) + (oldValue.length + 1) = 2 * oldValue.length + 2 := by omega
  simpa only [missTrace, missStart, count] using actual

def copyTrace (background : Stack → List Bool) (flags : TransportFlags) (saved : FieldCopy.Store)
    (word suffix target : List Bool) : List State :=
  (FieldCopy.copyPortTrace saved word suffix target).map
    (FieldTransport.configuration readRole readLabels background flags)

def copyStart (background : Stack → List Bool) (flags : TransportFlags) (saved : FieldCopy.Store)
    (word suffix target : List Bool) : State :=
  FieldTransport.configuration readRole readLabels background flags (FieldCopy.copyStart saved word suffix target)

def copyEnd (background : Stack → List Bool) (flags : TransportFlags)
    (word suffix target : List Bool) : State :=
  FieldTransport.configuration readRole readLabels background flags (FieldCopy.copyPort word suffix target)

theorem copy_run (caller : Statement) (background : Stack → List Bool) (flags : TransportFlags)
    (saved : FieldCopy.Store) (word suffix target : List Bool) :
    Run caller (copyTrace background flags saved word suffix target)
      (copyStart background flags saved word suffix target) (copyEnd background flags word suffix target)
      (2 * word.length + 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [copyTrace, copyStart, List.head?_map, FieldCopy.copyPortTrace_head, Option.map_some]
  · exact FieldTransport.portTrace_chain readRole readRole_injective readLabels (program caller)
      (copy_syntax caller) background flags saved word suffix target
  · simp only [copyTrace, copyEnd, List.getLast?_map, FieldCopy.copyPortTrace_last, Option.map_some]
  · simp only [copyTrace, List.length_map, FieldCopy.copyPortTrace_length]

end PaperProofs.Common.Native.PSTRWordVM.UniqueRead

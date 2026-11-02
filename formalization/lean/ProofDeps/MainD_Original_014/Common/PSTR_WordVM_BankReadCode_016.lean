module

public import Common.PSTR_WordVM_UniqueWorkspace_015

/-! Actual finite unique-bank reader, sharing the fixed search/miss/front
syntax of the frozen upsert. Hit copies the real bank field; absent emits
FALSE data with the real TRUE width tally. Neither w/U nor an answer is
in the finite store. This module supplies actual clear/fill/restore paths;
whole recursive lookup and original raw/Word semantics remain separate. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.UniqueRead

open Turing UniqueStore UniqueStore.KeyCompare

/-- Compile-time constants: bank source, output, width, backup, used. -/
def readRole (point : FieldCopy.Stack) : Stack :=
  if point = 0 then 10 else if point = 1 then 3 else
    if point = 2 then 11 else if point = 3 then 7 else 12

def readLabels (point : FieldCopy.Label) : Label :=
  if point = 0 then 3 else if point = 1 then 4 else 11

theorem readRole_injective : Function.Injective readRole := by decide

def program (caller : Statement) (point : Label) : Statement :=
  if point = 0 then
    .pop 10 captureData
      (.branch bit
        (.push 0 (fun _ => true) (.load initializeEqual (jump 1)))
        (.push 10 (fun _ => false) (jump 8)))
  else if point = 3 then FieldTransport.statement readRole readLabels (FieldCopy.program 0)
  else if point = 4 then FieldTransport.statement readRole readLabels (FieldCopy.program 1)
  else if point = 7 then
    .pop 3 captureData (.branch present (jump 7) (jump 0))
  else if point = 8 then
    widthBranch (.push 3 (fun _ => false) (.push 12 (fun _ => true) (jump 8))) (jump 9)
  else if point = 9 then
    .pop 12 captureWidth (.branch present (.push 11 (fun _ => true) (jump 9)) (jump 11))
  else UniqueStore.program caller point

theorem supports (caller : Statement) :
    TM2.Supports (program caller) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _, fun point _ => statement_supports (program caller point)⟩

theorem copy_syntax (caller : Statement) (point : FieldCopy.Label) (notTerminal : point ≠ 2) :
    program caller (readLabels point) =
      FieldTransport.statement readRole readLabels (FieldCopy.program point) := by
  fin_cases point
  · rfl
  · rfl
  · exact (notTerminal rfl).elim

def Shared (point : Label) : Prop :=
  point = 1 ∨ point = 2 ∨ point = 5 ∨ point = 6 ∨ point = 11 ∨ point = 12

theorem shared_syntax (caller : Statement) (point : Label) (shared : Shared point) :
    program caller point = UniqueStore.program caller point := by
  rcases shared with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem shared_step (caller : Statement) (point : Label) (memory : Store)
    (bankSlots : Stack → List Bool) (shared : Shared point) :
    TM2.step (program caller) ⟨some point, memory, bankSlots⟩ =
      TM2.step (UniqueStore.program caller) ⟨some point, memory, bankSlots⟩ := by
  change some (TM2.stepAux (program caller point) memory bankSlots) = _
  rw [shared_syntax caller point shared]
  rfl

structure Run (caller : Statement) (path : List State) (first last : State) (steps : Nat) : Prop where
  head : path.head? = some first
  chain : path.IsChain (fun before after => TM2.step (program caller) before = some after)
  last : path.getLast? = some last
  length : path.length = steps + 1

theorem Run.prepend {caller : Statement} {path : List State} {first middle last : State} {steps : Nat}
    (edge : TM2.step (program caller) first = some middle) (rest : Run caller path middle last steps) :
    Run caller (first :: path) first last (steps + 1) := by
  have nonempty : path ≠ [] := by intro empty; subst path; cases rest.head
  refine ⟨rfl, FieldCopy.prepend_chain _ _ _ _ rest.head edge rest.chain, ?_, ?_⟩
  · exact (FieldCopy.last_cons_of_nonempty first path nonempty).trans rest.last
  · simp only [List.length_cons, rest.length]

theorem clear_bit (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields)
    (oldBit : Bool) (later : List Bool) :
    TM2.step (program caller) (state background 7 (saved, (e, flags)) { fields with value := oldBit :: later }) =
      some (state background 7 ((true, oldBit), (e, flags)) { fields with value := later }) := by
  simp [program, state, TM2.step, TM2.stepAux, captureData, present, jump, at_value, update_value]

theorem clear_done (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) :
    TM2.step (program caller) (state background 7 (saved, (e, flags)) { fields with value := [] }) =
      some (state background 0 ((false, false), (e, flags)) { fields with value := [] }) := by
  simp [program, state, TM2.step, TM2.stepAux, captureData, present, jump, at_value, update_value]

def clearStart (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (word : List Bool) (fields : Fields) : State :=
  state background 7 (saved, (e, flags)) { fields with value := word }

def clearEnd (background : Stack → List Bool) (e : Bool) (flags : CallerFlags) (fields : Fields) : State :=
  state background 0 ((false, false), (e, flags)) { fields with value := [] }

def clearTrace (background : Stack → List Bool) (e : Bool) (flags : CallerFlags) :
    FieldCopy.Store → List Bool → Fields → List State
  | saved, [], fields => [clearStart background saved e flags [] fields, clearEnd background e flags fields]
  | saved, oldBit :: later, fields => clearStart background saved e flags (oldBit :: later) fields ::
      clearTrace background e flags (true, oldBit) later fields

theorem clear_run (caller : Statement) (background : Stack → List Bool) (e : Bool)
    (flags : CallerFlags) (saved : FieldCopy.Store) (word : List Bool) (fields : Fields) :
    Run caller (clearTrace background e flags saved word fields)
      (clearStart background saved e flags word fields) (clearEnd background e flags fields) (word.length + 1) := by
  induction word generalizing saved with
  | nil =>
    refine ⟨rfl, ?_, rfl, rfl⟩
    exact List.isChain_cons_cons.mpr ⟨clear_done caller background saved e flags fields, List.isChain_singleton _⟩
  | cons oldBit later ih =>
    have full := Run.prepend (clear_bit caller background saved e flags fields oldBit later) (ih (true, oldBit))
    simpa only [clearTrace, clearStart, List.length_cons] using full

theorem fill_bit (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) (later : List Bool) :
    TM2.step (program caller) (state background 8 (saved, (e, flags)) { fields with width := true :: later }) =
      some (state background 8 ((true, saved.2), (e, flags))
        { fields with width := later, value := false :: fields.value, used := true :: fields.used }) := by
  simp [program, state, TM2.step, TM2.stepAux, widthBranch, captureWidth, present, jump,
    at_width, at_value, at_used, update_width, update_value, update_used]

theorem fill_done (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) :
    TM2.step (program caller) (state background 8 (saved, (e, flags)) { fields with width := [] }) =
      some (state background 9 ((false, saved.2), (e, flags)) { fields with width := [] }) := by
  simp [program, state, TM2.step, TM2.stepAux, widthBranch, captureWidth, present, jump, at_width, update_width]

def fillStart (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (amount : Nat) (fields : Fields) : State :=
  state background 8 (saved, (e, flags)) { fields with width := List.replicate amount true }

def fillEnd (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (amount : Nat) (fields : Fields) : State :=
  state background 9 ((false, saved.2), (e, flags))
    { fields with width := [], value := List.replicate amount false ++ fields.value, used := List.replicate amount true ++ fields.used }

def fillTrace (background : Stack → List Bool) (e : Bool) (flags : CallerFlags) :
    FieldCopy.Store → Nat → Fields → List State
  | saved, 0, fields => [fillStart background saved e flags 0 fields, fillEnd background saved e flags 0 fields]
  | saved, amount + 1, fields => fillStart background saved e flags (amount + 1) fields ::
      fillTrace background e flags (true, saved.2) amount
        { fields with value := false :: fields.value, used := true :: fields.used }

theorem fill_run (caller : Statement) (background : Stack → List Bool) (e : Bool)
    (flags : CallerFlags) (saved : FieldCopy.Store) (amount : Nat) (fields : Fields) :
    Run caller (fillTrace background e flags saved amount fields)
      (fillStart background saved e flags amount fields) (fillEnd background saved e flags amount fields) (amount + 1) := by
  induction amount generalizing saved fields with
  | zero =>
    refine ⟨rfl, ?_, rfl, rfl⟩
    apply List.isChain_cons_cons.mpr
    refine ⟨?_, List.isChain_singleton _⟩
    simpa only [fillStart, fillEnd, List.replicate_zero, List.nil_append] using fill_done caller background saved e flags fields
  | succ amount ih =>
    have rest := ih (true, saved.2) { fields with value := false :: fields.value, used := true :: fields.used }
    have edge : TM2.step (program caller) (fillStart background saved e flags (amount + 1) fields) =
        some (fillStart background (true, saved.2) e flags amount
          { fields with value := false :: fields.value, used := true :: fields.used }) := by
      simpa only [fillStart, List.replicate_succ] using fill_bit caller background saved e flags fields (List.replicate amount true)
    have full := Run.prepend edge rest
    simpa only [fillTrace, fillEnd, List.replicate_succ', List.append_assoc,
      List.cons_append, List.nil_append] using full

theorem tally_bit (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) (later : List Bool) :
    TM2.step (program caller) (state background 9 (saved, (e, flags)) { fields with used := true :: later }) =
      some (state background 9 ((true, saved.2), (e, flags))
        { fields with used := later, width := true :: fields.width }) := by
  simp [program, state, TM2.step, TM2.stepAux, captureWidth, present, jump, at_used,
    at_width, update_used, update_width]

theorem tally_done (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) :
    TM2.step (program caller) (state background 9 (saved, (e, flags)) { fields with used := [] }) =
      some (state background 11 ((false, saved.2), (e, flags)) { fields with used := [] }) := by
  simp [program, state, TM2.step, TM2.stepAux, captureWidth, present, jump, at_used, update_used]

def tallyStart (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (amount : Nat) (fields : Fields) : State :=
  state background 9 (saved, (e, flags)) { fields with used := List.replicate amount true }

def tallyEnd (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (amount : Nat) (fields : Fields) : State :=
  state background 11 ((false, saved.2), (e, flags))
    { fields with used := [], width := List.replicate amount true ++ fields.width }

def tallyTrace (background : Stack → List Bool) (e : Bool) (flags : CallerFlags) :
    FieldCopy.Store → Nat → Fields → List State
  | saved, 0, fields => [tallyStart background saved e flags 0 fields, tallyEnd background saved e flags 0 fields]
  | saved, amount + 1, fields => tallyStart background saved e flags (amount + 1) fields ::
      tallyTrace background e flags (true, saved.2) amount { fields with width := true :: fields.width }

theorem tally_run (caller : Statement) (background : Stack → List Bool) (e : Bool)
    (flags : CallerFlags) (saved : FieldCopy.Store) (amount : Nat) (fields : Fields) :
    Run caller (tallyTrace background e flags saved amount fields)
      (tallyStart background saved e flags amount fields) (tallyEnd background saved e flags amount fields) (amount + 1) := by
  induction amount generalizing saved fields with
  | zero =>
    refine ⟨rfl, ?_, rfl, rfl⟩
    apply List.isChain_cons_cons.mpr
    refine ⟨?_, List.isChain_singleton _⟩
    simpa only [tallyStart, tallyEnd, List.replicate_zero, List.nil_append] using tally_done caller background saved e flags fields
  | succ amount ih =>
    have rest := ih (true, saved.2) { fields with width := true :: fields.width }
    have edge : TM2.step (program caller) (tallyStart background saved e flags (amount + 1) fields) =
        some (tallyStart background (true, saved.2) e flags amount { fields with width := true :: fields.width }) := by
      simpa only [tallyStart, List.replicate_succ] using tally_bit caller background saved e flags fields (List.replicate amount true)
    have full := Run.prepend edge rest
    simpa only [tallyTrace, tallyEnd, List.replicate_succ', List.append_assoc,
      List.cons_append, List.nil_append] using full

/-- Clear never grows a physical stack, while actual FALSE generation
uses the pre-existing width tally and grows total mass by at most w. -/
theorem clear_mass (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (word : List Bool) (fields : Fields) :
    ∀ current ∈ clearTrace background e flags saved word fields,
      Workspace.occupied current ≤ Workspace.occupied (clearStart background saved e flags word fields) := by
  induction word generalizing saved with
  | nil =>
    intro current present
    simp only [clearTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> exact Nat.le_refl _
  | cons oldBit later ih =>
    intro current present
    rcases List.mem_cons.mp present with same | after
    · subst current
      exact Nat.le_refl _
    · have bound := ih (true, oldBit) current after
      simp only [clearStart, Workspace.occupied_state, Workspace.fieldMass, List.length_cons] at bound ⊢
      omega

theorem fill_mass (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (amount : Nat) (fields : Fields) :
    ∀ current ∈ fillTrace background e flags saved amount fields,
      Workspace.occupied current ≤ Workspace.occupied (fillStart background saved e flags amount fields) + amount := by
  induction amount generalizing saved fields with
  | zero =>
    intro current present
    simp only [fillTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> exact Nat.le_refl _
  | succ amount ih =>
    intro current present
    rcases List.mem_cons.mp present with same | after
    · subst current
      omega
    · have bound := ih (true, saved.2) { fields with value := false :: fields.value, used := true :: fields.used } current after
      simp only [fillStart, Workspace.occupied_state, Workspace.fieldMass, List.length_cons,
        List.length_replicate] at bound ⊢
      omega

theorem tally_mass (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (amount : Nat) (fields : Fields) :
    ∀ current ∈ tallyTrace background e flags saved amount fields,
      Workspace.occupied current = Workspace.occupied (tallyStart background saved e flags amount fields) := by
  induction amount generalizing saved fields with
  | zero =>
    intro current present
    simp only [tallyTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> rfl
  | succ amount ih =>
    intro current present
    rcases List.mem_cons.mp present with same | after
    · subst current
      rfl
    · have bound := ih (true, saved.2) { fields with width := true :: fields.width } current after
      simp only [tallyStart, Workspace.occupied_state, Workspace.fieldMass, List.length_cons,
        List.length_replicate] at bound ⊢
      omega

end PaperProofs.Common.Native.PSTRWordVM.UniqueRead

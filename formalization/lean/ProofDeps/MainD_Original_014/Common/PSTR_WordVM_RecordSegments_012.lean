module

public import Common.PSTR_WordVM_BankSegments_011
public import Common.PSTR_WordVM_InsertFields_009

/-! Coherent record-level SAME-path blocks for the fixed UniqueStore.
All data below are trace descriptors. No data/width/address is added to
the finite control. The code's key verdict is read from actual compared
bits, and every concatenation uses the identical physical middle state. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.UniqueStore.RecordSegments

open Turing KeyCompare BankSegments

def workFields (query value bank frontPart : List Bool) : Fields :=
  ⟨bank, frontPart, query, value, List.replicate query.length true, [], [], []⟩

def keyMiddle (recordKey value tail frontPart : List Bool) : Fields :=
  workFields [] value tail (recordKey.reverse ++ frontPart)

def keyStart (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (recordKey query value tail frontPart : List Bool) : State :=
  compareStart background saved true flags recordKey query tail (workFields query value tail frontPart)

def keyEnd (background : Stack → List Bool) (flags : CallerFlags)
    (recordKey query value tail frontPart : List Bool) : State :=
  restored background (eqBits recordKey query) flags query.reverse
    (keyMiddle recordKey value tail frontPart)

def keyTrace (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (recordKey query value tail frontPart : List Bool) : List State :=
  compareTrace background flags saved true recordKey query tail (workFields query value tail frontPart) ++
    (restoreTrace background (eqBits recordKey query) flags (false, FieldCopy.lastRead saved query)
      query.reverse (keyMiddle recordKey value tail frontPart)).tail

theorem key_end_fields (background : Stack → List Bool) (flags : CallerFlags)
    (recordKey query value tail frontPart : List Bool) :
    keyEnd background flags recordKey query value tail frontPart =
      state background (if eqBits recordKey query then 3 else 5)
        ((false, false), (eqBits recordKey query, flags))
        (workFields query value tail (recordKey.reverse ++ frontPart)) := by
  simp [keyEnd, restored, keyMiddle, workFields]

theorem key_run (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (recordKey query value tail frontPart : List Bool)
    (lengths : recordKey.length = query.length) :
    PhaseRun caller (keyTrace background flags saved recordKey query value tail frontPart)
      (keyStart background flags saved recordKey query value tail frontPart)
      (keyEnd background flags recordKey query value tail frontPart) (2 * query.length + 2) := by
  let startFields := workFields query value tail frontPart
  have forward : PhaseRun caller (compareTrace background flags saved true recordKey query tail startFields)
      (compareStart background saved true flags recordKey query tail startFields)
      (compared background saved true flags recordKey query tail startFields) (query.length + 1) :=
    ⟨compareTrace_head background flags saved true recordKey query tail startFields,
      compareTrace_chain caller background flags saved true recordKey query tail startFields lengths,
      compareTrace_last background flags saved true recordKey query tail startFields lengths,
      compareTrace_length background flags saved true recordKey query tail startFields⟩
  let middleFields := keyMiddle recordKey value tail frontPart
  have backward : PhaseRun caller
      (restoreTrace background (eqBits recordKey query) flags (false, FieldCopy.lastRead saved query) query.reverse middleFields)
      (restoreStart background (false, FieldCopy.lastRead saved query) (eqBits recordKey query) flags query.reverse middleFields)
      (restored background (eqBits recordKey query) flags query.reverse middleFields) (query.reverse.length + 1) :=
    ⟨restoreTrace_head background (eqBits recordKey query) flags (false, FieldCopy.lastRead saved query) query.reverse middleFields,
      restoreTrace_chain caller background (eqBits recordKey query) flags (false, FieldCopy.lastRead saved query) query.reverse middleFields,
      restoreTrace_last background (eqBits recordKey query) flags (false, FieldCopy.lastRead saved query) query.reverse middleFields,
      restoreTrace_length background (eqBits recordKey query) flags (false, FieldCopy.lastRead saved query) query.reverse middleFields⟩
  have sameBackward : PhaseRun caller
      (restoreTrace background (eqBits recordKey query) flags (false, FieldCopy.lastRead saved query) query.reverse middleFields)
      (compared background saved true flags recordKey query tail startFields)
      (keyEnd background flags recordKey query value tail frontPart) (query.length + 1) := by
    simpa [restoreStart, compared, keyEnd, startFields, middleFields, keyMiddle, workFields] using backward
  have full := forward.join sameBackward
  have count : (query.length + 1) + (query.length + 1) = 2 * query.length + 2 := by omega
  simpa only [keyTrace, keyStart, count, startFields, middleFields] using full

def missRestoreFields (query value oldValue tail frontPart : List Bool) : Fields :=
  { workFields query value tail (oldValue.reverse ++ frontPart) with width := [] }

def missStart (background : Stack → List Bool) (flags : CallerFlags)
    (query value oldValue tail frontPart : List Bool) : State :=
  skipStart background (false, false) false flags oldValue tail (workFields query value tail frontPart)

def missEnd (background : Stack → List Bool) (flags : CallerFlags)
    (query value oldValue tail frontPart : List Bool) : State :=
  widthRestored background (false, FieldCopy.lastRead (false, false) oldValue) false flags oldValue.length
    (missRestoreFields query value oldValue tail frontPart)

def missTrace (background : Stack → List Bool) (flags : CallerFlags)
    (query value oldValue tail frontPart : List Bool) : List State :=
  skipTrace background false flags (false, false) oldValue tail (workFields query value tail frontPart) ++
    (widthTrace background false flags (false, FieldCopy.lastRead (false, false) oldValue) oldValue.length
      (missRestoreFields query value oldValue tail frontPart)).tail

theorem miss_start_fields (background : Stack → List Bool) (flags : CallerFlags)
    (query value oldValue tail frontPart : List Bool) (lengths : oldValue.length = query.length) :
    missStart background flags query value oldValue tail frontPart =
      state background 5 ((false, false), (false, flags))
        (workFields query value (oldValue ++ tail) frontPart) := by
  simp [missStart, skipStart, workFields, lengths]

theorem miss_end_fields (background : Stack → List Bool) (flags : CallerFlags)
    (query value oldValue tail frontPart : List Bool) (lengths : oldValue.length = query.length) :
    missEnd background flags query value oldValue tail frontPart =
      state background 0 ((false, FieldCopy.lastRead (false, false) oldValue), (false, flags))
        (workFields query value tail (oldValue.reverse ++ frontPart)) := by
  simp [missEnd, widthRestored, missRestoreFields, workFields, lengths]

theorem miss_run (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (query value oldValue tail frontPart : List Bool) :
    PhaseRun caller (missTrace background flags query value oldValue tail frontPart)
      (missStart background flags query value oldValue tail frontPart)
      (missEnd background flags query value oldValue tail frontPart) (2 * oldValue.length + 2) := by
  have forward := skip_run caller background false flags (false, false) oldValue tail
    (workFields query value tail frontPart)
  have backward := width_run caller background false flags
    (false, FieldCopy.lastRead (false, false) oldValue) oldValue.length
    (missRestoreFields query value oldValue tail frontPart)
  have sameBackward : PhaseRun caller
      (widthTrace background false flags (false, FieldCopy.lastRead (false, false) oldValue) oldValue.length
        (missRestoreFields query value oldValue tail frontPart))
      (skipped background (false, false) false flags oldValue tail (workFields query value tail frontPart))
      (missEnd background flags query value oldValue tail frontPart) (oldValue.length + 1) := by
    simpa [widthStart, skipped, missEnd, missRestoreFields, workFields] using backward
  have full := forward.join sameBackward
  have count : (oldValue.length + 1) + (oldValue.length + 1) = 2 * oldValue.length + 2 := by omega
  simpa only [missTrace, missStart, count] using full

def hitBackFields (query newValue tail frontPart : List Bool) : Fields :=
  { workFields query [] tail (newValue.reverse ++ frontPart) with width := [] }

def hitFrontFields (query newValue tail : List Bool) : Fields :=
  { workFields query newValue tail [] with width := List.replicate newValue.length true }

def hitStart (background : Stack → List Bool) (flags : CallerFlags)
    (query oldValue newValue tail frontPart : List Bool) : State :=
  writeStart background (false, false) true flags oldValue newValue tail (workFields query newValue tail frontPart)

def hitEnd (background : Stack → List Bool) (flags : CallerFlags)
    (query newValue tail frontPart : List Bool) : State :=
  ⟨some 13, ((false, false), (true, flags)),
    (frontRestored background true flags (newValue.reverse ++ frontPart)
      (hitFrontFields query newValue tail)).stk⟩

def hitTrace (background : Stack → List Bool) (flags : CallerFlags)
    (query oldValue newValue tail frontPart : List Bool) : List State :=
  writeTrace background true flags (false, false) oldValue newValue tail (workFields query newValue tail frontPart) ++
    (valueBackTrace background true flags (false, FieldCopy.lastRead (false, false) newValue) newValue.reverse
      (hitBackFields query newValue tail frontPart)).tail ++
    (frontReturnTrace background true flags (false, false) (newValue.reverse ++ frontPart)
      (hitFrontFields query newValue tail)).tail

theorem hit_start_fields (background : Stack → List Bool) (flags : CallerFlags)
    (query oldValue newValue tail frontPart : List Bool) (lengths : newValue.length = query.length) :
    hitStart background flags query oldValue newValue tail frontPart =
      state background 3 ((false, false), (true, flags))
        (workFields query newValue (oldValue ++ tail) frontPart) := by
  simp [hitStart, writeStart, workFields, lengths]

theorem hit_end_fields (background : Stack → List Bool) (flags : CallerFlags)
    (query newValue tail frontPart : List Bool) (lengths : newValue.length = query.length) :
    hitEnd background flags query newValue tail frontPart =
      state background 13 ((false, false), (true, flags))
        (workFields query newValue (frontPart.reverse ++ newValue ++ tail) []) := by
  simp [hitEnd, frontRestored, hitFrontFields, workFields, state, List.reverse_append, List.append_assoc, lengths]

theorem hit_run (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (query oldValue newValue tail frontPart : List Bool) (lengths : oldValue.length = newValue.length) :
    PhaseRun caller (hitTrace background flags query oldValue newValue tail frontPart)
      (hitStart background flags query oldValue newValue tail frontPart)
      (hitEnd background flags query newValue tail frontPart) (3 * newValue.length + frontPart.length + 4) := by
  have forward := write_run caller background true flags (false, false) oldValue newValue tail
    (workFields query newValue tail frontPart) lengths
  have back := value_back_run caller background true flags
    (false, FieldCopy.lastRead (false, false) newValue) newValue.reverse
    (hitBackFields query newValue tail frontPart)
  have sameBack : PhaseRun caller
      (valueBackTrace background true flags (false, FieldCopy.lastRead (false, false) newValue) newValue.reverse
        (hitBackFields query newValue tail frontPart))
      (written background (false, false) true flags newValue tail (workFields query newValue tail frontPart))
      (valueRestored background true flags newValue.reverse (hitBackFields query newValue tail frontPart))
      (newValue.length + 1) := by
    simpa [valueBackStart, written, hitBackFields, workFields] using back
  have restoring := front_return_run caller background true flags (false, false) (newValue.reverse ++ frontPart)
    (hitFrontFields query newValue tail)
  have sameRestoring : PhaseRun caller
      (frontReturnTrace background true flags (false, false) (newValue.reverse ++ frontPart)
        (hitFrontFields query newValue tail))
      (valueRestored background true flags newValue.reverse (hitBackFields query newValue tail frontPart))
      (hitEnd background flags query newValue tail frontPart) ((newValue.reverse ++ frontPart).length + 2) := by
    simpa [frontStart, valueRestored, hitEnd, hitFrontFields, hitBackFields, workFields] using restoring
  have full := (forward.join sameBack).join sameRestoring
  have count : (newValue.length + 1 + (newValue.length + 1)) + ((newValue.reverse ++ frontPart).length + 2) =
      3 * newValue.length + frontPart.length + 4 := by
    simp only [List.length_append, List.length_reverse]
    omega
  simpa only [hitTrace, hitStart, count, List.append_assoc] using full

theorem value_start_fields (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (saved : FieldCopy.Store) (query value frontPart : List Bool) (lengths : value.length = query.length) :
    UniqueStore.valueStart (bankSlots background (workFields query value [false] frontPart))
      (e, flags) saved value [] [false] =
      state background 7 (saved, (e, flags)) (workFields query value [false] frontPart) := by
  unfold UniqueStore.valueStart FieldTransport.configuration FieldCopy.copyStart FieldCopy.readStart FieldCopy.state state
  simp only [Option.map_some, List.append_nil]
  rw [lengths]
  congr 1
  funext point
  fin_cases point <;> rfl

theorem value_port_fields (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (query value frontPart : List Bool) (lengths : value.length = query.length) :
    UniqueStore.valuePort (bankSlots background (workFields query value [false] frontPart))
      (e, flags) value [] [false] =
      state background 9 ((false, false), (e, flags))
        (workFields query value (value ++ [false]) frontPart) := by
  unfold UniqueStore.valuePort FieldTransport.configuration FieldCopy.copyPort FieldCopy.state state
  simp only [Option.map_some, List.append_nil]
  rw [lengths]
  congr 1
  funext point
  fin_cases point <;> rfl

theorem key_insert_start_fields (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (query value frontPart : List Bool) :
    UniqueStore.keyStart (bankSlots background (workFields query value (value ++ [false]) frontPart))
      (e, flags) (false, false) query [] (value ++ [false]) =
      state background 9 ((false, false), (e, flags))
        (workFields query value (value ++ [false]) frontPart) := by
  unfold UniqueStore.keyStart FieldTransport.configuration FieldCopy.copyStart FieldCopy.readStart FieldCopy.state state
  simp only [Option.map_some, List.append_nil]
  congr 1
  funext point
  fin_cases point <;> rfl

theorem key_insert_tagged_fields (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (query value frontPart : List Bool) :
    UniqueStore.tagged (bankSlots background (workFields query value (value ++ [false]) frontPart))
      (e, flags) query [] (value ++ [false]) =
      state background 11 ((false, false), (e, flags))
        (workFields query value (true :: (query ++ value ++ [false])) frontPart) := by
  unfold UniqueStore.tagged UniqueStore.keyPort FieldTransport.configuration FieldCopy.copyPort FieldCopy.state state
  simp only [List.append_nil, List.append_assoc]
  congr 1
  funext point
  fin_cases point <;> rfl

def insertedFields (query value : List Bool) : Fields :=
  workFields query value (true :: (query ++ value ++ [false])) []

def insertStart (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (saved : FieldCopy.Store) (query value frontPart : List Bool) : State :=
  state background 7 (saved, (e, flags)) (workFields query value [false] frontPart)

def insertEnd (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (query value frontPart : List Bool) : State :=
  ⟨some 13, ((false, false), (e, flags)),
    (frontRestored background e flags frontPart (insertedFields query value)).stk⟩

def insertTrace (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (saved : FieldCopy.Store) (query value frontPart : List Bool) : List State :=
  UniqueStore.valueTrace (bankSlots background (workFields query value [false] frontPart))
    (e, flags) saved value [] [false] ++
    (UniqueStore.keyTaggedTrace (bankSlots background (workFields query value (value ++ [false]) frontPart))
      (e, flags) (false, false) query [] (value ++ [false])).tail ++
    (frontReturnTrace background e flags (false, false) frontPart (insertedFields query value)).tail

theorem insert_end_fields (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (query value frontPart : List Bool) :
    insertEnd background flags e query value frontPart =
      state background 13 ((false, false), (e, flags))
        (workFields query value (frontPart.reverse ++ true :: (query ++ value ++ [false])) []) := by
  simp [insertEnd, insertedFields, frontRestored, workFields, state]

theorem insert_run (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (saved : FieldCopy.Store) (query value frontPart : List Bool) (lengths : value.length = query.length) :
    PhaseRun caller (insertTrace background flags e saved query value frontPart)
      (insertStart background flags e saved query value frontPart)
      (insertEnd background flags e query value frontPart) (4 * query.length + frontPart.length + 7) := by
  let valueBackground := bankSlots background (workFields query value [false] frontPart)
  let keyBackground := bankSlots background (workFields query value (value ++ [false]) frontPart)
  have valuesRaw : PhaseRun caller (UniqueStore.valueTrace valueBackground (e, flags) saved value [] [false])
      (UniqueStore.valueStart valueBackground (e, flags) saved value [] [false])
      (UniqueStore.valuePort valueBackground (e, flags) value [] [false]) (2 * value.length + 2) :=
    ⟨UniqueStore.valueTrace_head valueBackground (e, flags) saved value [] [false],
      UniqueStore.valueTrace_chain caller valueBackground (e, flags) saved value [] [false],
      UniqueStore.valueTrace_last valueBackground (e, flags) saved value [] [false],
      UniqueStore.valueTrace_length valueBackground (e, flags) saved value [] [false]⟩
  have values : PhaseRun caller (UniqueStore.valueTrace valueBackground (e, flags) saved value [] [false])
      (insertStart background flags e saved query value frontPart)
      (state background 9 ((false, false), (e, flags)) (workFields query value (value ++ [false]) frontPart))
      (2 * value.length + 2) := by
    simpa only [valueBackground, insertStart, value_start_fields background flags e saved query value frontPart lengths,
      value_port_fields background flags e query value frontPart lengths] using valuesRaw
  have keysRaw : PhaseRun caller
      (UniqueStore.keyTaggedTrace keyBackground (e, flags) (false, false) query [] (value ++ [false]))
      (UniqueStore.keyStart keyBackground (e, flags) (false, false) query [] (value ++ [false]))
      (UniqueStore.tagged keyBackground (e, flags) query [] (value ++ [false])) (2 * query.length + 3) := by
    refine ⟨?_, UniqueStore.keyTaggedTrace_chain caller keyBackground (e, flags) (false, false) query [] (value ++ [false]),
      List.getLast?_append_cons _ _ [], UniqueStore.keyTaggedTrace_length keyBackground (e, flags) (false, false) query [] (value ++ [false])⟩
    rw [UniqueStore.keyTaggedTrace, List.head?_append, UniqueStore.keyTrace_head]
    rfl
  have keys : PhaseRun caller
      (UniqueStore.keyTaggedTrace keyBackground (e, flags) (false, false) query [] (value ++ [false]))
      (state background 9 ((false, false), (e, flags)) (workFields query value (value ++ [false]) frontPart))
      (state background 11 ((false, false), (e, flags)) (workFields query value (true :: (query ++ value ++ [false])) frontPart))
      (2 * query.length + 3) := by
    simpa only [keyBackground, key_insert_start_fields, key_insert_tagged_fields] using keysRaw
  have restoring := front_return_run caller background e flags (false, false) frontPart (insertedFields query value)
  have sameRestoring : PhaseRun caller (frontReturnTrace background e flags (false, false) frontPart (insertedFields query value))
      (state background 11 ((false, false), (e, flags)) (workFields query value (true :: (query ++ value ++ [false])) frontPart))
      (insertEnd background flags e query value frontPart) (frontPart.length + 2) := by
    simpa [frontStart, insertEnd, insertedFields, workFields] using restoring
  have full := (values.join keys).join sameRestoring
  have count : (2 * value.length + 2 + (2 * query.length + 3)) + (frontPart.length + 2) =
      4 * query.length + frontPart.length + 7 := by omega
  simpa only [insertTrace, valueBackground, keyBackground, count, List.append_assoc] using full

end PaperProofs.Common.Native.PSTRWordVM.UniqueStore.RecordSegments

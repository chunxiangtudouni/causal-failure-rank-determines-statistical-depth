module

public import Common.PSTR_WordVM_BankLookup_019

/-! Real first bank access from the physically empty bank stack. The
existing fixed programs really pop none, capture FALSE, and push the
FALSE EOF cell. No preinstalled sentinel or zero-init oracle is assumed.
The Word/raw frontend still has to produce query/width and clear front0. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.BlankBank

open Turing UniqueStore UniqueStore.KeyCompare UniqueStore.BankSegments UniqueStore.RecordSegments

theorem store_edge (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) :
    TM2.step (UniqueStore.program caller) (state background 0 (saved, (e, flags)) { fields with bank := [] }) =
      some (state background 7 ((false, false), (e, flags)) { fields with bank := [false] }) := by
  simp [UniqueStore.program, state, TM2.step, TM2.stepAux, captureData, bit, jump, at_bank, update_bank]

theorem read_edge (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) :
    TM2.step (UniqueRead.program caller) (state background 0 (saved, (e, flags)) { fields with bank := [] }) =
      some (state background 8 ((false, false), (e, flags)) { fields with bank := [false] }) := by
  simp [UniqueRead.program, state, TM2.step, TM2.stepAux, captureData, bit, jump, at_bank, update_bank]

def storeStart (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (e : Bool) (query value frontPart : List Bool) : State :=
  state background 0 (saved, (e, flags)) (workFields query value [] frontPart)

def storeTrace (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (e : Bool) (query value frontPart : List Bool) : List State :=
  storeStart background flags saved e query value frontPart ::
    insertTrace background flags e (false, false) query value frontPart

theorem store_run (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (query value frontPart : List Bool)
    (lengths : value.length = query.length) :
    PhaseRun caller (storeTrace background flags saved e query value frontPart)
      (storeStart background flags saved e query value frontPart)
      (WholeUpsert.finish background flags e query value [] frontPart)
      (4 * query.length + frontPart.length + 8) := by
  have inserting := insert_run caller background flags e (false, false) query value frontPart lengths
  have sameInsert : PhaseRun caller (insertTrace background flags e (false, false) query value frontPart)
      (insertStart background flags e (false, false) query value frontPart)
      (WholeUpsert.finish background flags e query value [] frontPart)
      (4 * query.length + frontPart.length + 7) := by
    simpa [WholeUpsert.finish, WholeUpsert.endEqual, upsert, encodeRecords, insert_end_fields] using inserting
  have edge : TM2.step (UniqueStore.program caller) (storeStart background flags saved e query value frontPart) =
      some (insertStart background flags e (false, false) query value frontPart) := by
    simpa [storeStart, insertStart, workFields] using
      store_edge caller background saved e flags (workFields query value [] frontPart)
  simpa only [storeTrace] using PhaseRun.prepend edge sameInsert

theorem store_mass (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (e : Bool) (query value frontPart : List Bool) (lengths : value.length = query.length) :
    ∀ current ∈ storeTrace background flags saved e query value frontPart,
      Workspace.occupied current ≤ Workspace.outside background + frontPart.length + 5 * query.length + 2 := by
  intro current present
  rcases List.mem_cons.mp present with same | inserting
  · subst current
    simp only [storeStart, Workspace.work_mass, List.length_nil]
    omega
  · exact Workspace.insert_mass background flags e (false, false) query value frontPart lengths current inserting

/-- The real width pop overwrites the presence bit, so the same fixed
zero block works after an empty bank pop, whose captured isSome is FALSE. -/
theorem zero_run (caller : Statement) (background : Stack → List Bool) (e : Bool)
    (flags : CallerFlags) (query frontPart : List Bool) :
    UniqueRead.Run caller (UniqueRead.zeroTrace background e flags (false, false) query frontPart)
      (UniqueRead.zeroStart background (false, false) e flags query frontPart)
      (UniqueRead.zeroEnd background e flags query frontPart) (2 * query.length + frontPart.length + 4) := by
  have filling := UniqueRead.fill_run caller background e flags (false, false) query.length (workFields query [] [false] frontPart)
  have returning := UniqueRead.tally_run caller background e flags (false, false) query.length (UniqueRead.zeroFields query frontPart)
  have sameReturn : UniqueRead.Run caller
      (UniqueRead.tallyTrace background e flags (false, false) query.length (UniqueRead.zeroFields query frontPart))
      (UniqueRead.fillEnd background (false, false) e flags query.length (workFields query [] [false] frontPart))
      (state background 11 ((false, false), (e, flags))
        (workFields query (List.replicate query.length false) [false] frontPart)) (query.length + 1) := by
    simpa [UniqueRead.fillEnd, UniqueRead.tallyStart, UniqueRead.tallyEnd, UniqueRead.zeroFields, workFields] using returning
  have restoring := UniqueRead.front_return_run caller background e flags (false, false) frontPart
    (workFields query (List.replicate query.length false) [false] [])
  have sameRestore : UniqueRead.Run caller
      (frontReturnTrace background e flags (false, false) frontPart
        (workFields query (List.replicate query.length false) [false] []))
      (state background 11 ((false, false), (e, flags))
        (workFields query (List.replicate query.length false) [false] frontPart))
      (UniqueRead.zeroEnd background e flags query frontPart) (frontPart.length + 2) := by
    simpa [frontStart, frontRestored, UniqueRead.zeroEnd, workFields, state] using restoring
  have actual := (filling.join sameReturn).join sameRestore
  have count : (query.length + 1 + (query.length + 1)) + (frontPart.length + 2) =
      2 * query.length + frontPart.length + 4 := by omega
  simpa only [UniqueRead.zeroTrace, UniqueRead.zeroStart, count] using actual

theorem zero_mass (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (query frontPart : List Bool) :
    ∀ current ∈ UniqueRead.zeroTrace background e flags (false, false) query frontPart,
      Workspace.occupied current ≤ Workspace.outside background + frontPart.length + 3 * query.length + 1 := by
  intro current present
  simp only [UniqueRead.zeroTrace, List.mem_append] at present
  rcases present with (filling | returning) | restoring
  · have bound := UniqueRead.fill_mass background e flags (false, false) query.length
      (workFields query [] [false] frontPart) current filling
    simp only [UniqueRead.fillStart, Workspace.occupied_state, Workspace.fieldMass, workFields,
      List.length_replicate, List.length_nil, List.length_cons] at bound
    omega
  · have conserved := UniqueRead.tally_mass background e flags (false, false) query.length
      (UniqueRead.zeroFields query frontPart) current (List.mem_of_mem_tail returning)
    simp only [UniqueRead.tallyStart, UniqueRead.zeroFields, workFields, Workspace.occupied_state, Workspace.fieldMass,
      List.length_replicate, List.length_nil, List.length_cons] at conserved
    omega
  · have conserved := Workspace.front_return_mass background e flags (false, false) frontPart
      (workFields query (List.replicate query.length false) [false] []) current (List.mem_of_mem_tail restoring)
    simp only [frontStart, workFields, Workspace.occupied_state, Workspace.fieldMass,
      List.length_replicate, List.length_nil, List.length_cons] at conserved
    omega

def readStart (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (e : Bool) (query frontPart : List Bool) : State :=
  state background 0 (saved, (e, flags)) (workFields query [] [] frontPart)

def readTrace (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (e : Bool) (query frontPart : List Bool) : List State :=
  readStart background flags saved e query frontPart :: UniqueRead.zeroTrace background e flags (false, false) query frontPart

theorem read_run (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (query frontPart : List Bool) :
    UniqueRead.Run caller (readTrace background flags saved e query frontPart)
      (readStart background flags saved e query frontPart)
      (UniqueRead.Lookup.finish background flags e query [] frontPart)
      (2 * query.length + frontPart.length + 5) := by
  have zeros := zero_run caller background e flags query frontPart
  have sameZero : UniqueRead.Run caller (UniqueRead.zeroTrace background e flags (false, false) query frontPart)
      (UniqueRead.zeroStart background (false, false) e flags query frontPart)
      (UniqueRead.Lookup.finish background flags e query [] frontPart)
      (2 * query.length + frontPart.length + 4) := by
    simpa [UniqueRead.Lookup.finish, UniqueRead.zeroEnd, UniqueRead.Lookup.valueOf,
      WholeUpsert.endEqual, encodeRecords] using zeros
  have edge : TM2.step (UniqueRead.program caller) (readStart background flags saved e query frontPart) =
      some (UniqueRead.zeroStart background (false, false) e flags query frontPart) := by
    simpa [readStart, UniqueRead.zeroStart, UniqueRead.fillStart, workFields] using
      read_edge caller background saved e flags (workFields query [] [] frontPart)
  simpa only [readTrace] using UniqueRead.Run.prepend edge sameZero

theorem read_mass (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (e : Bool) (query frontPart : List Bool) :
    ∀ current ∈ readTrace background flags saved e query frontPart,
      Workspace.occupied current ≤ Workspace.outside background + frontPart.length + 3 * query.length + 1 := by
  intro current present
  rcases List.mem_cons.mp present with same | filling
  · subst current
    simp only [readStart, Workspace.work_mass, List.length_nil]
    omega
  · exact zero_mass background e flags query frontPart current filling

def readEntry (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (e : Bool) (query oldOutput frontPart : List Bool) : State :=
  UniqueRead.clearStart background saved e flags oldOutput (workFields query oldOutput [] frontPart)

def actualReadTrace (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (e : Bool) (query oldOutput frontPart : List Bool) : List State :=
  UniqueRead.clearTrace background e flags saved oldOutput (workFields query oldOutput [] frontPart) ++
    (readTrace background flags (false, false) e query frontPart).tail

theorem actual_read_run (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (query oldOutput frontPart : List Bool) :
    UniqueRead.Run caller (actualReadTrace background flags saved e query oldOutput frontPart)
      (readEntry background flags saved e query oldOutput frontPart)
      (UniqueRead.Lookup.finish background flags e query [] frontPart)
      (oldOutput.length + 1 + (2 * query.length + frontPart.length + 5)) := by
  have clearing := UniqueRead.clear_run caller background e flags saved oldOutput (workFields query oldOutput [] frontPart)
  have reading := read_run caller background flags (false, false) e query frontPart
  have sameRead : UniqueRead.Run caller (readTrace background flags (false, false) e query frontPart)
      (UniqueRead.clearEnd background e flags (workFields query oldOutput [] frontPart))
      (UniqueRead.Lookup.finish background flags e query [] frontPart)
      (2 * query.length + frontPart.length + 5) := by
    simpa [UniqueRead.clearEnd, readStart, workFields] using reading
  exact clearing.join sameRead

theorem actual_read_mass (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (e : Bool) (query oldOutput frontPart : List Bool) :
    ∀ current ∈ actualReadTrace background flags saved e query oldOutput frontPart,
      Workspace.occupied current ≤ Workspace.outside background + frontPart.length +
        3 * query.length + oldOutput.length + 1 := by
  intro current present
  rcases List.mem_append.mp present with clearing | reading
  · have bound := UniqueRead.clear_mass background e flags saved oldOutput
      (workFields query oldOutput [] frontPart) current clearing
    simp only [UniqueRead.clearStart, workFields, Workspace.occupied_state, Workspace.fieldMass,
      List.length_replicate, List.length_nil] at bound
    omega
  · have bound := read_mass background flags (false, false) e query frontPart current (List.mem_of_mem_tail reading)
    omega

end PaperProofs.Common.Native.PSTRWordVM.BlankBank

module

public import Common.PSTR_WordVM_ReadShared_017

/-! Real hit-field copy and absent-zero generation in the SAME fixed
reader program. Bank10 is preserved; the output word is stack3. Clearing
that standalone output, unlike clearing bank10, cannot erase bank tail.
Whole recursive lookup consumes these two actual blocks. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.UniqueRead

open Turing UniqueStore UniqueStore.KeyCompare UniqueStore.BankSegments UniqueStore.RecordSegments

theorem tag_true (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) (tail : List Bool) :
    TM2.step (program caller) (state background 0 (saved, (e, flags)) { fields with bank := true :: tail }) =
      some (state background 1 ((true, true), (true, flags))
        { fields with bank := tail, front := true :: fields.front }) := by
  simp [program, state, TM2.step, TM2.stepAux, captureData, initializeEqual, bit, jump,
    at_bank, at_front, update_bank, update_front]

theorem tag_eof (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) (tail : List Bool) :
    TM2.step (program caller) (state background 0 (saved, (e, flags)) { fields with bank := false :: tail }) =
      some (state background 8 ((true, false), (e, flags)) { fields with bank := false :: tail }) := by
  simp [program, state, TM2.step, TM2.stepAux, captureData, bit, jump, at_bank, update_bank]

theorem hit_copy_start (background : Stack → List Bool) (flags : CallerFlags)
    (query word tail frontPart : List Bool) (lengths : word.length = query.length) :
    copyStart (bankSlots background (workFields query [] (word ++ tail) frontPart))
      (true, flags) (false, false) word tail [] =
      state background 3 ((false, false), (true, flags)) (workFields query [] (word ++ tail) frontPart) := by
  unfold copyStart FieldTransport.configuration FieldCopy.copyStart FieldCopy.readStart FieldCopy.state state
  simp only [Option.map_some]
  rw [lengths]
  congr 1
  funext point
  fin_cases point <;> rfl

theorem hit_copy_end (background : Stack → List Bool) (flags : CallerFlags)
    (query word tail frontPart : List Bool) (lengths : word.length = query.length) :
    copyEnd (bankSlots background (workFields query [] (word ++ tail) frontPart)) (true, flags) word tail [] =
      state background 11 ((false, false), (true, flags)) (workFields query word (word ++ tail) frontPart) := by
  unfold copyEnd FieldTransport.configuration FieldCopy.copyPort FieldCopy.state state
  simp only [Option.map_some, List.append_nil]
  rw [lengths]
  congr 1
  funext point
  fin_cases point <;> rfl

def hitStart (background : Stack → List Bool) (flags : CallerFlags)
    (query word tail frontPart : List Bool) : State :=
  state background 3 ((false, false), (true, flags)) (workFields query [] (word ++ tail) frontPart)

def hitEnd (background : Stack → List Bool) (flags : CallerFlags)
    (query word tail frontPart : List Bool) : State :=
  state background 13 ((false, false), (true, flags))
    (workFields query word (frontPart.reverse ++ word ++ tail) [])

def hitTrace (background : Stack → List Bool) (flags : CallerFlags)
    (query word tail frontPart : List Bool) : List State :=
  copyTrace (bankSlots background (workFields query [] (word ++ tail) frontPart))
    (true, flags) (false, false) word tail [] ++
    (frontReturnTrace background true flags (false, false) frontPart (workFields query word (word ++ tail) [])).tail

theorem hit_run (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (query word tail frontPart : List Bool) (lengths : word.length = query.length) :
    Run caller (hitTrace background flags query word tail frontPart)
      (hitStart background flags query word tail frontPart) (hitEnd background flags query word tail frontPart)
      (2 * word.length + frontPart.length + 4) := by
  have copying := copy_run caller (bankSlots background (workFields query [] (word ++ tail) frontPart))
    (true, flags) (false, false) word tail []
  have sameCopy : Run caller
      (copyTrace (bankSlots background (workFields query [] (word ++ tail) frontPart))
        (true, flags) (false, false) word tail [])
      (hitStart background flags query word tail frontPart)
      (state background 11 ((false, false), (true, flags)) (workFields query word (word ++ tail) frontPart))
      (2 * word.length + 2) := by
    simpa only [hitStart, hit_copy_start background flags query word tail frontPart lengths,
      hit_copy_end background flags query word tail frontPart lengths] using copying
  have restoring := front_return_run caller background true flags (false, false) frontPart
    (workFields query word (word ++ tail) [])
  have sameRestore : Run caller
      (frontReturnTrace background true flags (false, false) frontPart (workFields query word (word ++ tail) []))
      (state background 11 ((false, false), (true, flags)) (workFields query word (word ++ tail) frontPart))
      (hitEnd background flags query word tail frontPart) (frontPart.length + 2) := by
    simpa [frontStart, frontRestored, hitEnd, workFields, state, List.append_assoc] using restoring
  have actual := sameCopy.join sameRestore
  have count : (2 * word.length + 2) + (frontPart.length + 2) = 2 * word.length + frontPart.length + 4 := by omega
  simpa only [hitTrace, count] using actual

def zeroFields (query frontPart : List Bool) : Fields :=
  { workFields query (List.replicate query.length false) [false] frontPart with width := [] }

def zeroStart (background : Stack → List Bool) (saved : FieldCopy.Store) (e : Bool)
    (flags : CallerFlags) (query frontPart : List Bool) : State :=
  fillStart background saved e flags query.length (workFields query [] [false] frontPart)

def zeroEnd (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (query frontPart : List Bool) : State :=
  state background 13 ((false, false), (e, flags))
    (workFields query (List.replicate query.length false) (frontPart.reverse ++ [false]) [])

def zeroTrace (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (query frontPart : List Bool) : List State :=
  fillTrace background e flags saved query.length (workFields query [] [false] frontPart) ++
    (tallyTrace background e flags (false, saved.2) query.length (zeroFields query frontPart)).tail ++
    (frontReturnTrace background e flags (false, false) frontPart
      (workFields query (List.replicate query.length false) [false] [])).tail

theorem zero_run (caller : Statement) (background : Stack → List Bool) (e : Bool)
    (flags : CallerFlags) (query frontPart : List Bool) :
    Run caller (zeroTrace background e flags (true, false) query frontPart)
      (zeroStart background (true, false) e flags query frontPart)
      (zeroEnd background e flags query frontPart) (2 * query.length + frontPart.length + 4) := by
  have filling := fill_run caller background e flags (true, false) query.length (workFields query [] [false] frontPart)
  have returning := tally_run caller background e flags (false, false) query.length (zeroFields query frontPart)
  have sameReturn : Run caller
      (tallyTrace background e flags (false, false) query.length (zeroFields query frontPart))
      (fillEnd background (true, false) e flags query.length (workFields query [] [false] frontPart))
      (state background 11 ((false, false), (e, flags))
        (workFields query (List.replicate query.length false) [false] frontPart)) (query.length + 1) := by
    simpa [fillEnd, tallyStart, tallyEnd, zeroFields, workFields] using returning
  have restoring := front_return_run caller background e flags (false, false) frontPart
    (workFields query (List.replicate query.length false) [false] [])
  have sameRestore : Run caller
      (frontReturnTrace background e flags (false, false) frontPart
        (workFields query (List.replicate query.length false) [false] []))
      (state background 11 ((false, false), (e, flags))
        (workFields query (List.replicate query.length false) [false] frontPart))
      (zeroEnd background e flags query frontPart) (frontPart.length + 2) := by
    simpa [frontStart, frontRestored, zeroEnd, workFields, state] using restoring
  have actual := (filling.join sameReturn).join sameRestore
  have count : (query.length + 1 + (query.length + 1)) + (frontPart.length + 2) =
      2 * query.length + frontPart.length + 4 := by omega
  simpa only [zeroTrace, zeroStart, count] using actual

theorem copy_configuration_mass (background : Stack → List Bool) (flags : TransportFlags)
    (small : FieldCopy.State) :
    Workspace.occupied (FieldTransport.configuration readRole readLabels background flags small) =
      Workspace.valueOutside background + FieldCopy.occupied small := by
  unfold Workspace.occupied FieldTransport.configuration FieldTransport.slots readRole
    Workspace.valueOutside FieldCopy.occupied
  dsimp
  omega

theorem copy_mass (background : Stack → List Bool) (flags : TransportFlags)
    (saved : FieldCopy.Store) (word suffix target : List Bool) :
    ∀ current ∈ copyTrace background flags saved word suffix target,
      Workspace.occupied current ≤ Workspace.valueOutside background + 3 * word.length + suffix.length + target.length := by
  intro current present
  obtain ⟨small, inside, rfl⟩ := List.mem_map.mp present
  rw [copy_configuration_mass]
  have bound := FieldCopy.copyPortTrace_mass saved word suffix target small inside
  omega

theorem hit_mass (background : Stack → List Bool) (flags : CallerFlags)
    (query word tail frontPart : List Bool) (lengths : word.length = query.length) :
    ∀ current ∈ hitTrace background flags query word tail frontPart,
      Workspace.occupied current ≤ Workspace.outside background + word.length + tail.length +
        frontPart.length + 3 * query.length := by
  intro current present
  rcases List.mem_append.mp present with copying | restoring
  · have bound := copy_mass (bankSlots background (workFields query [] (word ++ tail) frontPart))
      (true, flags) (false, false) word tail [] current copying
    rw [Workspace.value_outside_work] at bound
    simp only [List.length_nil] at bound
    omega
  · have conserved := Workspace.front_return_mass background true flags (false, false) frontPart
      (workFields query word (word ++ tail) []) current (List.mem_of_mem_tail restoring)
    simp only [frontStart, workFields, Workspace.occupied_state, Workspace.fieldMass,
      List.length_replicate, List.length_append, List.length_nil] at conserved
    omega

theorem zero_mass (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (query frontPart : List Bool) :
    ∀ current ∈ zeroTrace background e flags (true, false) query frontPart,
      Workspace.occupied current ≤ Workspace.outside background + frontPart.length + 3 * query.length + 1 := by
  intro current present
  simp only [zeroTrace, List.mem_append] at present
  rcases present with (filling | returning) | restoring
  · have bound := fill_mass background e flags (true, false) query.length
      (workFields query [] [false] frontPart) current filling
    simp only [fillStart, Workspace.occupied_state, Workspace.fieldMass, workFields,
      List.length_replicate, List.length_nil, List.length_cons] at bound
    omega
  · have conserved := tally_mass background e flags (false, false) query.length
      (zeroFields query frontPart) current (List.mem_of_mem_tail returning)
    simp only [tallyStart, zeroFields, workFields, Workspace.occupied_state, Workspace.fieldMass,
      List.length_replicate, List.length_nil, List.length_cons] at conserved
    omega
  · have conserved := Workspace.front_return_mass background e flags (false, false) frontPart
      (workFields query (List.replicate query.length false) [false] []) current (List.mem_of_mem_tail restoring)
    simp only [frontStart, workFields, Workspace.occupied_state, Workspace.fieldMass,
      List.length_replicate, List.length_nil, List.length_cons] at conserved
    omega

end PaperProofs.Common.Native.PSTRWordVM.UniqueRead

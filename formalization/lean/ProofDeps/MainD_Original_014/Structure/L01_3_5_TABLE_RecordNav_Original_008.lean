module

public import Structure.L01_3_5_TABLE_RecordNav_Link_007

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000

namespace PaperProofs.Common.Native.L01_3_5_TABLE_RecordNavLink007

open Turing
open PaperProofs.Common
open PaperProofs.Common.Native
open PaperProofs.Common.Native.PSTRWordVM
open PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation
open PSTRSymbolicNaturalExport
open PSTRSymbolicNaturalExport.Joined
open PSTRSymbolicDualStream

theorem finite_entry_same_left (records : List Nat)
    (before after : Slot → List Bool) (same : after 1 = before 1)
    (entry : FiniteEntry records before) : FiniteEntry records after := by
  unfold FiniteEntry at entry ⊢
  rw [same]
  exact entry

noncomputable def originalInitial {C : Type*} (context : C) (background : Slot → List Bool)
    (bits : List Bool) : State C :=
  LabelMap.configuration L01_3_5_TABLE_RecordNavLink007.oldLabel
    (PSTRSymbolicNaturalExport.Joined.initial context background bits)

theorem actual_original_navigation {C : Type*} {I : Instance}
    (context : C) (background : Slot → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (available : Finset I.Tool)
    (budget : Rat) (history : List (VisibleEvent I)) :
    let records := PSTRQueryRecords.nativeRecords available history
    let bits := CompactPrice.plannerInput input contract available budget history records
    let parseBound := VirtualReturn.outside background + 65536*(bits.length+1)^3
    let bound := 3*parseBound+9
    ∃ (firstDigits secondDigits : List Bool) (path : List (State C)) (final parsed : State C),
      path.head? = some (originalInitial context background bits) ∧
      path.IsChain (fun before after => TM2.step L01_3_5_TABLE_RecordNavLink007.program before = some after) ∧
      path.getLast? = some final ∧ parsed ∈ path ∧ parsed.l = some 1 ∧
      Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0)) =
        recordEndTape (PSTRTablePlannerStreams.firstData input contract available budget history)
          firstDigits records secondDigits ∧
      final.l = some 10 ∧ final.var.1.1 = context ∧
      final.stk = Function.update parsed.stk 15 (selectedOutput records ++ false :: false :: background 15) ∧
      (∀ slot, slot ≠ 0 → slot ≠ 1 → parsed.stk slot = background slot) ∧
      path.length ≤ 16385*(bits.length+1)^3+3*parseBound+6+3*bound+8 ∧
      (∀ current ∈ path, current.var.1.1 = context ∧
        VirtualReturn.occupiedSlots current.stk ≤ 2*bound+1) ∧
      ∀ current ∈ path, ∀ label, current.l = some label →
        (∀ node ∈ AuxWorkspace.nodes (L01_3_5_TABLE_RecordNavLink007.program label) current.var current.stk,
          VirtualReturn.occupiedSlots node.2 ≤ 16*(2*bound+8)) ∧
        ScannerStatement.clock (L01_3_5_TABLE_RecordNavLink007.program label) current.var current.stk ≤
          18*(2*bound+9) := by
  dsimp only
  let records := PSTRQueryRecords.nativeRecords available history
  let bits := CompactPrice.plannerInput input contract available budget history records
  let parseBound := VirtualReturn.outside background + 65536*(bits.length+1)^3
  let bound := 3*parseBound+9
  obtain ⟨firstDigits,secondDigits,oldPath,oldFinal,oldParsed,oldFirst,oldChain,oldLast,
    parsedMember,parsedPort,tape,oldPort,oldContext,oldOutput,oldFrame,oldTime,oldResources,_oldNodes⟩ :=
    actual_original_getter context background input contract available budget history
  have oldActive : oldFinal.l ≠ none := by rw [oldPort]; intro impossible; cases impossible
  have wholeLeft := congrArg Tape.left tape
  change ListBlank.mk (oldParsed.stk 1) = _ at wholeLeft
  have parsedEntry : FiniteEntry records oldParsed.stk :=
    record_finite_entry _ _ _ _ _ (native_records_domain available history) wholeLeft
  have sameLeft : oldFinal.stk 1 = oldParsed.stk 1 := by
    rw [oldOutput]
    simp only [Function.update_of_ne (by decide : (1 : Slot) ≠ 15)]
  have finalEntry : FiniteEntry records oldFinal.stk := finite_entry_same_left records _ _ sameLeft parsedEntry
  obtain ⟨tailPath,tailFinal,tailFirst,tailChain,tailLast,tailPort,tailContext,tailBank,tailTime,tailResources⟩ :=
    actual_tail records oldFinal.var oldFinal.stk finalEntry
  have oldShared : LabelMap.configuration L01_3_5_TABLE_RecordNavLink007.oldLabel oldFinal =
      tailInitial records oldFinal.var oldFinal.stk := by
    cases oldFinal with
    | mk position memory bank =>
        change position = some (if records = [] then 4 else 5) at oldPort
        change (⟨position.map L01_3_5_TABLE_RecordNavLink007.oldLabel,memory,bank⟩ : State C) = _
        rw [oldPort]
        rfl
  rw [← oldShared] at tailFirst
  let mapped := oldPath.map (LabelMap.configuration L01_3_5_TABLE_RecordNavLink007.oldLabel)
  let parsed := LabelMap.configuration L01_3_5_TABLE_RecordNavLink007.oldLabel oldParsed
  have mappedFirst : mapped.head? = some (originalInitial context background bits) := by
    rw [List.head?_map,oldFirst,Option.map_some]
    rfl
  have mappedLast : mapped.getLast? = some
      (LabelMap.configuration L01_3_5_TABLE_RecordNavLink007.oldLabel oldFinal) := by
    rw [List.getLast?_map,oldLast,Option.map_some]
  have mappedChain := old_lift oldPath oldFinal oldChain oldLast oldActive
  have oldMass : VirtualReturn.occupiedSlots oldFinal.stk ≤ bound :=
    (oldResources oldFinal (List.mem_of_getLast? oldLast)).2
  cases tailShape : tailPath with
  | nil => rw [tailShape] at tailFirst; cases tailFirst
  | cons shared rest =>
      rw [tailShape] at tailFirst tailChain tailLast tailTime tailResources
      have sharedEq : shared = LabelMap.configuration L01_3_5_TABLE_RecordNavLink007.oldLabel oldFinal :=
        Option.some.inj tailFirst
      subst shared
      let path := mapped ++ rest
      have first : path.head? = some (originalInitial context background bits) := by
        simp only [path,List.head?_append,mappedFirst,Option.some_or]
      have chain : path.IsChain (fun before after =>
          TM2.step L01_3_5_TABLE_RecordNavLink007.program before = some after) :=
        NativeTrace.join_chain mapped _ rest mappedLast mappedChain tailChain
      have last : path.getLast? = some tailFinal :=
        (NativeTrace.join_last mapped _ rest mappedLast).trans tailLast
      have resources : ∀ current ∈ path, current.var.1.1 = context ∧
          VirtualReturn.occupiedSlots current.stk ≤ 2*bound+1 := by
        intro current present
        rcases List.mem_append.mp present with inOld | inTail
        · obtain ⟨source,member,rfl⟩ := List.mem_map.mp inOld
          have kept := oldResources source member
          exact ⟨kept.1,by
            change VirtualReturn.occupiedSlots source.stk ≤ _
            have cap := kept.2
            change VirtualReturn.occupiedSlots source.stk ≤ bound at cap
            omega⟩
        · have kept := tailResources current (List.mem_cons_of_mem _ inTail)
          exact ⟨(congrArg Prod.fst kept.1).trans oldContext,by have cap := kept.2; omega⟩
      refine ⟨firstDigits,secondDigits,path,tailFinal,parsed,first,chain,last,?_,?_,tape,
        tailPort,(congrArg Prod.fst tailContext).trans oldContext,tailBank.trans oldOutput,oldFrame,?_,resources,?_⟩
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨oldParsed,parsedMember,rfl⟩
      · change oldParsed.l.map L01_3_5_TABLE_RecordNavLink007.oldLabel = some 1
        rw [parsedPort,Option.map_some]
        rfl
      · change (mapped ++ rest).length ≤ _
        rw [List.length_append]
        change mapped.length + rest.length ≤ 16385*(bits.length+1)^3+3*parseBound+6+3*bound+8
        have mappedLength : mapped.length = oldPath.length := List.length_map _
        change oldPath.length ≤ 16385*(bits.length+1)^3+3*parseBound+6 at oldTime
        simp only [List.length_cons] at tailTime
        omega
      · intro current present label _active
        exact node_resources label current.var current.stk (2*bound+1) (resources current present).2

end PaperProofs.Common.Native.L01_3_5_TABLE_RecordNavLink007

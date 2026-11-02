module

public import Common.PSTR_SYM_NaturalExportJoined_091

/-! The actual original two-stream020 parser AND086 getter in ONE fixed
six-label Bool TM2 program, from the same original plannerInput. No supplied
finite archive/field/width/answer is an original input. The real parser
return enters the getter; source1, old7 and every other stack except15
are restored exactly at the active final ZERO4/POS5 return port. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport.Joined

open Turing PaperProofs.Common PaperProofs.Common.Native PSTRWordVM PSTRWordBool
open PSTRSymbolicDualStream

def seed : Store := (false,false,false)

def parserConfiguration {C : Type*} (before : PSTRSymbolicDualStack.State (C × Store)) : GlobalState C :=
  LabelMap.configuration oldLabel (StoreIso.configuration (exchange C) before)

noncomputable def initial {C : Type*} (context : C) (background : Slot → List Bool) (bits : List Bool) : GlobalState C :=
  parserConfiguration (VirtualReturn.configuration (context,seed) background
    (TM2.init (Γ := PushPop.Alphabet) (Λ := Unit) (σ := PSTRSymbolicDualStack.Store) 0 bits))

theorem parser_chain_transport {C : Type*}
    (path : List (PSTRSymbolicDualStack.State (C × Store))) (final : PSTRSymbolicDualStack.State (C × Store))
    (chain : path.IsChain (fun before after => TM2.step (PSTRSymbolicDualStack.program .halt) before = some after))
    (last : path.getLast? = some final) (active : final.l = some 1) :
    (path.map parserConfiguration).IsChain
      (fun before after => TM2.step (combinedProgram (C := C)) before = some after) := by
  have storeChain : (path.map (StoreIso.configuration (exchange C))).IsChain
      (fun before after => TM2.step parserProgram before = some after) := by
    apply StoreIso.chain_configuration_on (exchange C) (PSTRSymbolicDualStack.program .halt) parserProgram path chain
    intro _current _present _label _position
    rfl
  have storeLast : (path.map (StoreIso.configuration (exchange C))).getLast? =
      some (StoreIso.configuration (exchange C) final) := by
    rw [List.getLast?_map,last,Option.map_some]
  have storeActive : (StoreIso.configuration (exchange C) final).l = some 1 := active
  have lifted := parser_lift _ _ storeChain storeLast storeActive
  change (path.map (fun before => LabelMap.configuration oldLabel
    (StoreIso.configuration (exchange C) before))).IsChain _
  simpa only [List.map_map,Function.comp_def] using lifted

theorem shared_configuration {C : Type*} (before : GlobalState C) (active : before.l = some 1) :
    LabelMap.configuration exportLabel
      (⟨some 0,before.var,before.stk⟩ : State (C × PSTRSymbolicDualStack.Store)) = before := by
  cases before with
  | mk position memory bank =>
    change position = some 1 at active
    subst position
    rfl

theorem combined_node_resources {C : Type*} (label : GlobalLabel) (memory : GlobalMemory C)
    (bank : Slot → List Bool) (bound : Nat) (mass : VirtualReturn.occupiedSlots bank ≤ bound) :
    (∀ node ∈ AuxWorkspace.nodes (combinedProgram label) memory bank,
      VirtualReturn.occupiedSlots node.2 ≤ 16*(bound+7)) ∧
    ScannerStatement.clock (combinedProgram label) memory bank ≤ 18*(bound+8) := by
  have bounded : ∀ slot, (bank slot).length ≤ bound := fun slot => (slot_mass bank slot).trans mass
  constructor
  · intro node present
    have perSlot := AuxWorkspace.node_bound (combinedProgram label) memory bank bound bounded node present
    have cap := combined_pushes (C := C) label
    have s0 := perSlot 0; have s1 := perSlot 1; have s2 := perSlot 2; have s3 := perSlot 3
    have s4 := perSlot 4; have s5 := perSlot 5; have s6 := perSlot 6; have s7 := perSlot 7
    have s8 := perSlot 8; have s9 := perSlot 9; have s10 := perSlot 10; have s11 := perSlot 11
    have s12 := perSlot 12; have s13 := perSlot 13; have s14 := perSlot 14; have s15 := perSlot 15
    simp only [VirtualReturn.occupiedSlots]
    omega
  · have clock := ScannerClock.clock_bound (combinedProgram label) memory bank bound bounded
    have actions := combined_actions (C := C) label
    have pushes := combined_pushes (C := C) label
    have first := Nat.mul_le_mul_right (bound + AuxWorkspace.pushes (combinedProgram (C := C) label) + 1)
      (Nat.mul_le_mul_left 2 actions)
    have second := Nat.mul_le_mul_left 18
      (show bound + AuxWorkspace.pushes (combinedProgram (C := C) label) + 1 ≤ bound + 8 by omega)
    exact clock.trans (first.trans second)

theorem actual_original_getter {C : Type*} {I : Instance}
    (context : C) (background : Slot → List Bool) (input : StatisticalInput I) (contract : Contract I)
    (available : Finset I.Tool) (budget : Rat) (history : List (VisibleEvent I)) :
    let records := PSTRQueryRecords.nativeRecords available history
    let bits := CompactPrice.plannerInput input contract available budget history records
    let parseBound := VirtualReturn.outside background + 65536*(bits.length+1)^3
    ∃ (firstDigits secondDigits : List Bool) (path : List (GlobalState C)) (final parsed : GlobalState C),
      path.head? = some (initial context background bits) ∧
      path.IsChain (fun before after => TM2.step combinedProgram before = some after) ∧
      path.getLast? = some final ∧
      parsed ∈ path ∧ parsed.l = some 1 ∧
      Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0)) =
        recordEndTape (PSTRTablePlannerStreams.firstData input contract available budget history) firstDigits records secondDigits ∧
      final.l = some (if records = [] then 4 else 5) ∧ final.var.1.1 = context ∧
      final.stk = Function.update parsed.stk 15 (selectedOutput records ++ false :: false :: background 15) ∧
      (∀ slot, slot ≠ 0 → slot ≠ 1 → parsed.stk slot = background slot) ∧
      path.length ≤ 16385*(bits.length+1)^3 + 3*parseBound+6 ∧
      (∀ current ∈ path, current.var.1.1 = context ∧
        VirtualReturn.occupiedSlots current.stk ≤ 3*parseBound+9) ∧
      ∀ current ∈ path, ∀ label, current.l = some label →
        (∀ node ∈ AuxWorkspace.nodes (combinedProgram label) current.var current.stk,
          VirtualReturn.occupiedSlots node.2 ≤ 16*(3*parseBound+16)) ∧
        ScannerStatement.clock (combinedProgram label) current.var current.stk ≤ 18*(3*parseBound+17) := by
  dsimp only
  let records := PSTRQueryRecords.nativeRecords available history
  let bits := CompactPrice.plannerInput input contract available budget history records
  let parseBound := VirtualReturn.outside background+65536*(bits.length+1)^3
  obtain ⟨firstDigits,secondDigits,oldPath,oldFinal,oldFirst,oldChain,oldLast,oldPort,oldTape,_right,
    _firstValue,_width,_secondValue,oldTime,oldFrames,oldMass,_oldNodes⟩ :=
    PSTRSymbolicDualStack.actual_dual_stack_resources (.halt : PSTRSymbolicDualStack.Statement (C × Store))
      (context,seed) background input contract available budget history
  change oldPath.length ≤ 16385*(bits.length+1)^3 at oldTime
  change ∀ current ∈ oldPath, VirtualReturn.occupiedSlots current.stk ≤ parseBound at oldMass
  let parsed := parserConfiguration oldFinal
  let parsedPath := oldPath.map parserConfiguration
  have parsedFirst : parsedPath.head? = some (initial context background bits) := by
    change (oldPath.map parserConfiguration).head? = _
    rw [List.head?_map,oldFirst,Option.map_some]
    rfl
  have parsedChain : parsedPath.IsChain (fun before after => TM2.step combinedProgram before = some after) :=
    parser_chain_transport oldPath oldFinal oldChain oldLast oldPort
  have parsedLast : parsedPath.getLast? = some parsed := by
    change (oldPath.map parserConfiguration).getLast? = _
    rw [List.getLast?_map,oldLast,Option.map_some]
  have parsedPort : parsed.l = some 1 := by
    change oldFinal.l.map oldLabel = some 1
    rw [oldPort]
    rfl
  have parsedFrame := (oldFrames oldFinal (List.mem_of_getLast? oldLast)).2
  have parsedContext : parsed.var.1.1 = context :=
    congrArg Prod.fst (oldFrames oldFinal (List.mem_of_getLast? oldLast)).1
  have parsedMass : VirtualReturn.occupiedSlots parsed.stk ≤ parseBound :=
    oldMass oldFinal (List.mem_of_getLast? oldLast)
  have wholeLeft := congrArg Tape.left oldTape
  change ListBlank.mk (parsed.stk 1) = _ at wholeLeft
  have entry : FiniteEntry records parsed.stk :=
    record_finite_entry _ _ _ _ _ (native_records_domain available history) wholeLeft
  obtain ⟨getterPath,getterFinal,getterRun⟩ := actual_finite_getter records parsed.var parsed.stk entry
  obtain ⟨getterFirst,getterChain,getterLast,getterPort,getterContext,getterOutput,getterTime,getterResources,_getterNodes⟩ := getterRun
  let returned := LabelMap.configuration exportLabel getterFinal
  let exported := getterPath.map (LabelMap.configuration exportLabel)
  have shared : LabelMap.configuration exportLabel
      (⟨some 0,parsed.var,parsed.stk⟩ : State (C × PSTRSymbolicDualStack.Store)) = parsed :=
    shared_configuration parsed parsedPort
  have exportedFirst : exported.head? = some parsed := by
    change (getterPath.map (LabelMap.configuration exportLabel)).head? = _
    rw [List.head?_map,getterFirst,Option.map_some,shared]
  have exportedChain : exported.IsChain (fun before after => TM2.step combinedProgram before = some after) :=
    getter_lift getterPath getterChain
  have exportedLast : exported.getLast? = some returned := by
    change (getterPath.map (LabelMap.configuration exportLabel)).getLast? = _
    rw [List.getLast?_map,getterLast,Option.map_some]
  have returnedPort : returned.l = some (if records = [] then 4 else 5) := by
    change getterFinal.l.map exportLabel = _
    rw [getterPort]
    split <;> rfl
  have returnedContext : returned.var.1.1 = context := (congrArg Prod.fst getterContext).trans parsedContext
  have targetOld : parsed.stk 15 = background 15 := parsedFrame 15 (by decide) (by decide)
  have returnedOutput : returned.stk = Function.update parsed.stk 15
      (selectedOutput records ++ false :: false :: background 15) := by
    change getterFinal.stk = _
    rw [getterOutput,targetOld]
  have exportedResources : ∀ current ∈ exported, current.var.1.1 = context ∧
      VirtualReturn.occupiedSlots current.stk ≤ 3*parseBound+9 := by
    intro current present
    obtain ⟨old,member,rfl⟩ := List.mem_map.mp present
    have actual := getterResources old member
    have oldContext : old.var.1 = parsed.var.1 := actual.1
    have outside_le : outside parsed.stk ≤ VirtualReturn.occupiedSlots parsed.stk := by rw [bank_mass]; omega
    exact ⟨(congrArg Prod.fst oldContext).trans parsedContext,by
      change VirtualReturn.occupiedSlots old.stk ≤ _
      have mass := actual.2.2
      omega⟩
  have parsedResources : ∀ current ∈ parsedPath, current.var.1.1 = context ∧
      VirtualReturn.occupiedSlots current.stk ≤ 3*parseBound+9 := by
    intro current present
    obtain ⟨old,member,rfl⟩ := List.mem_map.mp present
    exact ⟨congrArg Prod.fst (oldFrames old member).1,(oldMass old member).trans (by omega)⟩
  cases exportedShape : exported with
  | nil =>
    rw [exportedShape] at exportedFirst
    cases exportedFirst
  | cons sharedState rest =>
    rw [exportedShape] at exportedFirst exportedChain exportedLast exportedResources
    have sharedEq : sharedState = parsed := Option.some.inj exportedFirst
    subst sharedState
    let path := parsedPath ++ rest
    have chain : path.IsChain (fun before after => TM2.step combinedProgram before = some after) :=
      NativeTrace.join_chain parsedPath parsed rest parsedLast parsedChain exportedChain
    have first : path.head? = some (initial context background bits) := by
      cases shape : parsedPath with
      | nil => simp only [shape,List.head?_nil] at parsedFirst; cases parsedFirst
      | cons head tail =>
        simpa only [path,shape,List.cons_append,List.head?_cons] using parsedFirst
    have last : path.getLast? = some returned :=
      (NativeTrace.join_last parsedPath parsed rest parsedLast).trans exportedLast
    have allResources : ∀ current ∈ path, current.var.1.1 = context ∧
        VirtualReturn.occupiedSlots current.stk ≤ 3*parseBound+9 := by
      intro current present
      rcases List.mem_append.mp present with inParsed | inRest
      · exact parsedResources current inParsed
      · exact exportedResources current (List.mem_cons_of_mem parsed inRest)
    refine ⟨firstDigits,secondDigits,path,returned,parsed,first,chain,last,
      List.mem_append_left _ (List.mem_of_getLast? parsedLast),parsedPort,oldTape,
      returnedPort,returnedContext,returnedOutput,parsedFrame,?_,allResources,?_⟩
    · have lengthParsed : parsedPath.length = oldPath.length := List.length_map _
      have lengthExported : (parsed :: rest).length = getterPath.length := by
        have length : exported.length = getterPath.length := List.length_map (LabelMap.configuration exportLabel)
        rw [exportedShape] at length
        exact length
      have sourceMass := slot_mass parsed.stk 1
      change path.length ≤ 16385*(bits.length+1)^3+3*parseBound+6
      dsimp only [path]
      rw [List.length_append,lengthParsed]
      simp only [List.length_cons] at lengthExported
      omega
    · intro current present label _active
      exact combined_node_resources label current.var current.stk (3*parseBound+9) (allResources current present).2

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport.Joined

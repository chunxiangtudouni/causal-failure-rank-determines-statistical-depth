module

public import Common.PSTR_SYM_WordPriorJoined_098

/-! Original wordInput -> frozen215 parser -> concrete093 signed prior
packet, in ONE fixed six-label Bool TM2 program. Actual parser return,
both copies, sign and restoration are charged in the SAME path. Source1,
afterPrior0 and old7 are restored;13/14 and every other stack except15 are
framed. Raw Rat serialization/arithmetic remain the parent's next callee. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRatExport.Joined

open Turing PaperProofs.Common.Native PaperProofs.Statistics PSTRWordVM PSTRWordBool
open PSTRSymbolicNaturalExport PA17TMRatArithmeticParse002 PSTRTMWordPriorFront215

def seed : Store := (false,false,false)

def parserConfiguration {C : Type*} (before : PSTRSymbolicWordPriorStack.State (C × Store)) : GlobalState C :=
  LabelMap.configuration oldLabel (StoreIso.configuration (exchange C) before)

def initial {C : Type*} (context : C) (background : Slot → List Bool) (bits : List Bool) : GlobalState C :=
  parserConfiguration (VirtualReturn.configuration (context,seed) background
    (TM2.init (Γ := PushPop.Alphabet) (Λ := Unit) (σ := PSTRSymbolicWordPriorStack.Store) 0 bits))

theorem parser_chain_transport {C : Type*}
    (path : List (PSTRSymbolicWordPriorStack.State (C × Store))) (final : PSTRSymbolicWordPriorStack.State (C × Store))
    (chain : path.IsChain (fun before after => TM2.step (PSTRSymbolicWordPriorStack.program .halt) before = some after))
    (last : path.getLast? = some final) (active : final.l = some 1) :
    (path.map parserConfiguration).IsChain
      (fun before after => TM2.step (combinedProgram (C := C)) before = some after) := by
  have storeChain : (path.map (StoreIso.configuration (exchange C))).IsChain
      (fun before after => TM2.step parserProgram before = some after) := by
    apply StoreIso.chain_configuration_on (exchange C) (PSTRSymbolicWordPriorStack.program .halt) parserProgram path chain
    intro _current _present _label _position
    rfl
  have storeLast : (path.map (StoreIso.configuration (exchange C))).getLast? =
      some (StoreIso.configuration (exchange C) final) := by rw [List.getLast?_map,last,Option.map_some]
  have storeActive : (StoreIso.configuration (exchange C) final).l = some 1 := active
  have lifted := parser_lift _ _ storeChain storeLast storeActive
  change (path.map (fun before => LabelMap.configuration oldLabel
    (StoreIso.configuration (exchange C) before))).IsChain _
  simpa only [List.map_map,Function.comp_def] using lifted

theorem shared_configuration {C : Type*} (before : GlobalState C) (active : before.l = some 1) :
    LabelMap.configuration exportLabel
      (⟨some 0,before.var,before.stk⟩ : State (C × PSTRSymbolicWordPriorStack.Store)) = before := by
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
    have first := Nat.mul_le_mul_right (bound+AuxWorkspace.pushes (combinedProgram (C := C) label)+1)
      (Nat.mul_le_mul_left 2 actions)
    have second := Nat.mul_le_mul_left 18
      (show bound+AuxWorkspace.pushes (combinedProgram (C := C) label)+1 ≤ bound+8 by omega)
    exact clock.trans (first.trans second)

theorem actual_original_word_prior {C : Type*} (context : C) (background : Slot → List Bool)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    let bits := wordInput E target word
    let parseBound := VirtualReturn.outside background+128*(bits.length+1)^2
    ∃ (path : List (GlobalState C)) (final parsed : GlobalState C),
      path.head? = some (initial context background bits) ∧
      path.IsChain (fun before after => TM2.step combinedProgram before = some after) ∧
      path.getLast? = some final ∧ parsed ∈ path ∧ parsed.l = some 1 ∧
      Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0)) = Tape.mk₂
        (bothLeft (false :: sign E.priorOne :: priorBase E target word)
          (numeratorDigits E.priorOne) (denominatorDigits E.priorOne)) (afterPrior E target word) ∧
      final.l = some 5 ∧ final.var.1.1 = context ∧
      final.stk = Function.update parsed.stk 15
        (packet (sign E.priorOne) (numeratorDigits E.priorOne) (denominatorDigits E.priorOne) (background 15)) ∧
      (∀ slot, slot ≠ 0 → slot ≠ 1 → parsed.stk slot = background slot) ∧
      path.length ≤ 33*(bits.length+1)^2+3*parseBound+9 ∧
      (∀ current ∈ path, current.var.1.1 = context ∧
        (∀ slot, slot ≠ 0 → slot ≠ 1 → slot ≠ 7 → slot ≠ 15 → current.stk slot = background slot) ∧
        VirtualReturn.occupiedSlots current.stk ≤ 3*parseBound+15) ∧
      ∀ current ∈ path, ∀ label, current.l = some label →
        (∀ node ∈ AuxWorkspace.nodes (combinedProgram label) current.var current.stk,
          VirtualReturn.occupiedSlots node.2 ≤ 16*(3*parseBound+22)) ∧
        ScannerStatement.clock (combinedProgram label) current.var current.stk ≤ 18*(3*parseBound+23) := by
  dsimp only
  let bits := wordInput E target word
  let parseBound := VirtualReturn.outside background+128*(bits.length+1)^2
  obtain ⟨oldPath,oldFinal,oldFirst,oldChain,oldLast,oldPort,oldTape,oldTime,oldFrames,oldMass⟩ :=
    PSTRSymbolicWordPriorStack.actual_original_prior_stack
      (.halt : PSTRSymbolicWordPriorStack.Statement (C × Store)) (context,seed) background E target word
  change oldPath.length ≤ 33*(bits.length+1)^2 at oldTime
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
  have parsedMass : VirtualReturn.occupiedSlots parsed.stk ≤ parseBound := oldMass oldFinal (List.mem_of_getLast? oldLast)
  have wholeLeft := congrArg Tape.left oldTape
  change ListBlank.mk (parsed.stk 1) = ListBlank.mk
    (bothLeft (false :: sign E.priorOne :: priorBase E target word)
      (numeratorDigits E.priorOne) (denominatorDigits E.priorOne)) at wholeLeft
  have entry : PriorEntry E parsed.stk := prior_finite_entry E target word parsed.stk wholeLeft
  obtain ⟨getterPath,getterFinal,getterRun⟩ := actual_current_prior E parsed.var parsed.stk entry
  obtain ⟨getterFirst,getterChain,getterLast,getterPort,getterContext,getterOutput,getterTime,getterResources⟩ := getterRun
  let returned := LabelMap.configuration exportLabel getterFinal
  let exported := getterPath.map (LabelMap.configuration exportLabel)
  have shared : LabelMap.configuration exportLabel
      (⟨some 0,parsed.var,parsed.stk⟩ : State (C × PSTRSymbolicWordPriorStack.Store)) = parsed :=
    shared_configuration parsed parsedPort
  have exportedFirst : exported.head? = some parsed := by
    change (getterPath.map (LabelMap.configuration exportLabel)).head? = _
    rw [List.head?_map,getterFirst,Option.map_some,shared]
  have exportedChain : exported.IsChain (fun before after => TM2.step combinedProgram before = some after) :=
    getter_lift getterPath getterChain
  have exportedLast : exported.getLast? = some returned := by
    change (getterPath.map (LabelMap.configuration exportLabel)).getLast? = _
    rw [List.getLast?_map,getterLast,Option.map_some]
  have returnedPort : returned.l = some 5 := by
    change getterFinal.l.map exportLabel = _
    rw [getterPort]
    rfl
  have returnedContext : returned.var.1.1 = context := (congrArg Prod.fst getterContext).trans parsedContext
  have targetOld : parsed.stk 15 = background 15 := parsedFrame 15 (by decide) (by decide)
  have returnedOutput : returned.stk = Function.update parsed.stk 15
      (packet (sign E.priorOne) (numeratorDigits E.priorOne) (denominatorDigits E.priorOne) (background 15)) := by
    change getterFinal.stk = _
    rw [getterOutput,targetOld]
  have exportedResources : ∀ current ∈ exported, current.var.1.1 = context ∧
      (∀ slot, slot ≠ 0 → slot ≠ 1 → slot ≠ 7 → slot ≠ 15 → current.stk slot = background slot) ∧
      VirtualReturn.occupiedSlots current.stk ≤ 3*parseBound+15 := by
    intro current present
    obtain ⟨old,member,rfl⟩ := List.mem_map.mp present
    have actual := getterResources old member
    have outside_le : outside parsed.stk ≤ VirtualReturn.occupiedSlots parsed.stk := by rw [bank_mass]; omega
    refine ⟨(congrArg Prod.fst actual.1).trans parsedContext,?_,?_⟩
    · intro slot notR notL notScratch notTarget
      exact (actual.2.1 slot notL notScratch notTarget).trans (parsedFrame slot notR notL)
    · change VirtualReturn.occupiedSlots old.stk ≤ _
      have mass := actual.2.2
      omega
  have parsedResources : ∀ current ∈ parsedPath, current.var.1.1 = context ∧
      (∀ slot, slot ≠ 0 → slot ≠ 1 → slot ≠ 7 → slot ≠ 15 → current.stk slot = background slot) ∧
      VirtualReturn.occupiedSlots current.stk ≤ 3*parseBound+15 := by
    intro current present
    obtain ⟨old,member,rfl⟩ := List.mem_map.mp present
    refine ⟨congrArg Prod.fst (oldFrames old member).1,?_,(oldMass old member).trans (by omega)⟩
    intro slot notR notL _notScratch _notTarget
    exact (oldFrames old member).2 slot notR notL
  cases exportedShape : exported with
  | nil => rw [exportedShape] at exportedFirst; cases exportedFirst
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
      | cons head tail => simpa only [path,shape,List.cons_append,List.head?_cons] using parsedFirst
    have last : path.getLast? = some returned :=
      (NativeTrace.join_last parsedPath parsed rest parsedLast).trans exportedLast
    have allResources : ∀ current ∈ path, current.var.1.1 = context ∧
        (∀ slot, slot ≠ 0 → slot ≠ 1 → slot ≠ 7 → slot ≠ 15 → current.stk slot = background slot) ∧
        VirtualReturn.occupiedSlots current.stk ≤ 3*parseBound+15 := by
      intro current present
      rcases List.mem_append.mp present with inParsed | inRest
      · exact parsedResources current inParsed
      · exact exportedResources current (List.mem_cons_of_mem parsed inRest)
    refine ⟨path,returned,parsed,first,chain,last,List.mem_append_left _ (List.mem_of_getLast? parsedLast),
      parsedPort,oldTape,returnedPort,returnedContext,returnedOutput,parsedFrame,?_,allResources,?_⟩
    · have lengthParsed : parsedPath.length = oldPath.length := List.length_map _
      have lengthExported : (parsed :: rest).length = getterPath.length := by
        have length : exported.length = getterPath.length := List.length_map (LabelMap.configuration exportLabel)
        rw [exportedShape] at length
        exact length
      have sourceMass := slot_mass parsed.stk 1
      change path.length ≤ 33*(bits.length+1)^2+3*parseBound+9
      dsimp only [path]
      rw [List.length_append,lengthParsed]
      simp only [List.length_cons] at lengthExported
      omega
    · intro current present label _active
      exact combined_node_resources label current.var current.stk (3*parseBound+15) (allResources current present).2.2

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRatExport.Joined

module

public import Common.PSTR_WordBool_RatOutputResources_081

/-! Actual old Raw trace -> native reset/body/return -> paid Rat reader.
This join is instantiated by BOTH concrete original Mul/Div callees in the
same batch. It neither produces pair input nor assumes finite-tape equality. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatMulDiv

open Turing PSTRWordVM RationalControllerComputation
open PA17TMRatArithmeticParse002 RatOutput.Link

abbrev Label := RatOutput.Link.Label
abbrev Statement (C : Type*) (states : Nat) := RatOutput.Link.Statement C states
abbrev State (C : Type*) (states : Nat) := RatOutput.Link.State C states

variable {C : Type*} {states : Nat}

def budget (background : RatOutput.Stack → List Bool) (bound : Nat) : Nat :=
  IsolatedRat.outside background + bound

structure BoundaryFacts (machine : Machine states) (caller : Statement C states)
    (context : C) (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store states)
    (background : RatOutput.Stack → List Bool) (input : List Bool) (value : Rat) (bound : Nat)
    (trace : List (State C states)) (final : State C states) : Prop where
  first : trace.head? = some (nativeConfiguration
    (IsolatedRat.entry (context,readerMemory) nativeMemory background input))
  chain : trace.IsChain (fun a b => TM2.step (program machine caller) a = some b)
  last : trace.getLast? = some final
  active : final.l = some 10
  context_eq : final.var.1.1 = context
  right : final.stk 13 = []
  left : final.stk 14 = []
  counter : final.stk 7 = background 7
  output : final.stk 15 = PSTRSymbolicRatExport.packet
    (sign value) (numeratorDigits value) (denominatorDigits value) (background 15)
  frame : ∀ slot, slot ≠ 13 → slot ≠ 14 → slot ≠ 15 → final.stk slot = background slot
  time : trace.length ≤ 4 * budget background bound + 20
  boundaries : ∀ current ∈ trace, current.var.1.1 = context ∧
    (∀ slot, slot ≠ 13 → slot ≠ 14 → slot ≠ 7 → slot ≠ 15 → current.stk slot = background slot) ∧
    RatOutput.occupied current.stk ≤ budget background bound + 8
  caller_unexecuted : ∀ current ∈ trace.dropLast, current.l ≠ some 10

def Call (machine : Machine states) (caller : Statement C states)
    (context : C) (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store states)
    (background : RatOutput.Stack → List Bool) (input : List Bool) (value : Rat) (bound : Nat) : Prop :=
  ∃ (trace : List (State C states)) (final : State C states),
    BoundaryFacts machine caller context readerMemory nativeMemory background input value bound trace final ∧
    (∀ current ∈ trace, ∀ point : Label, point ≠ 10 →
      (∀ node ∈ AuxWorkspace.nodes (program machine caller point) current.var current.stk,
        (∀ slot, (node.2 slot).length ≤ budget background bound + 11) ∧
        ∀ slot, slot ≠ 13 → slot ≠ 14 → slot ≠ 7 → slot ≠ 15 → node.2 slot = background slot) ∧
      ScannerStatement.clock (program machine caller point) current.var current.stk ≤
        16 * (budget background bound + 12)) ∧
    ∀ point : Label, point ≠ 10 →
      ScannerClock.actions (program machine caller point) ≤ 8 ∧
      AuxWorkspace.pushes (program machine caller point) ≤ 3

private theorem native_call (machine : Machine states) (caller : IsolatedRat.Statement C states)
    (context : C) (memory : BoolOnStacks.Store states) (background : RatOutput.Stack → List Bool)
    (input : List Bool) (value : Rat) (bound : Nat)
    (old : List (MachineState states)) (oldFinal : MachineState states)
    (actual : Runs machine input old oldFinal) (whole : oldFinal.Tape = Tape.mk₁ (encode [.rational value]))
    (time : old.length ≤ bound) (space : visitedSpace machine input.length old ≤ bound) :
    ∃ (trace : List (IsolatedRat.State C states)) (final : IsolatedRat.State C states),
      trace.head? = some (IsolatedRat.entry context memory background input) ∧
      trace.IsChain (fun a b => TM2.step (IsolatedRat.program machine caller) a = some b) ∧
      trace.getLast? = some final ∧ final.l = some 2 ∧
      (IsolatedRat.represented final).Tape = Tape.mk₁ (encode [.rational value]) ∧
      trace.length ≤ bound + 2 ∧
      ∀ current ∈ trace, current.var.1 = context ∧
        (∀ slot, slot ≠ 13 → slot ≠ 14 → current.stk slot = background slot) ∧
        IsolatedRat.occupied current.stk ≤ budget background bound := by
  obtain ⟨trace,final,head,chain,last,active,represented,count,bounds,_proper,_internal⟩ :=
    IsolatedRat.actual_old_call machine caller context memory background input old oldFinal
      actual.1 actual.2.1 actual.2.2.1 actual.2.2.2.1
  refine ⟨trace,final,head,chain,last,active,?_,?_,?_⟩
  · rw [represented]
    exact whole
  · omega
  · intro current member
    have oldBound := bounds current member
    exact ⟨oldBound.1,oldBound.2.1,oldBound.2.2.trans (Nat.add_le_add_left space _)⟩

theorem actual_boundary (machine : Machine states) (caller : Statement C states)
    (context : C) (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store states)
    (background : RatOutput.Stack → List Bool) (input : List Bool) (value : Rat) (bound : Nat)
    (old : List (MachineState states)) (oldFinal : MachineState states)
    (actual : Runs machine input old oldFinal) (whole : oldFinal.Tape = Tape.mk₁ (encode [.rational value]))
    (time : old.length ≤ bound) (space : visitedSpace machine input.length old ≤ bound) :
    ∃ (trace : List (State C states)) (final : State C states),
      BoundaryFacts machine caller context readerMemory nativeMemory background input value bound trace final := by
  obtain ⟨native,rawFinal,nHead,nChain,nLast,nActive,nTape,nCount,nBounds⟩ :=
    native_call machine (.halt : IsolatedRat.Statement (C × RatOutput.Store) states)
      (context,readerMemory) nativeMemory background input value bound old oldFinal actual whole time space
  have finalBound := nBounds rawFinal (List.mem_of_getLast? nLast)
  have finalContext : rawFinal.var.1.1 = context := congrArg Prod.fst finalBound.1
  have nativeMass : RatOutput.occupied rawFinal.stk ≤ budget background bound := finalBound.2.2
  have sameRight : ListBlank.mk (rawFinal.stk 13) = ListBlank.mk (encode [.rational value]) := by
    have tape := congrArg Tape.right₀ nTape
    simpa only [IsolatedRat.represented,Tape.mk₁,Tape.mk₂,Tape.mk'_right₀] using tape
  let rBefore := RatOutput.state rawFinal.stk 0 (rawFinal.var.1.1,rawFinal.var.2) rawFinal.var.1.2
    (rawFinal.stk 13) (rawFinal.stk 14) (rawFinal.stk 7) (rawFinal.stk 15)
  let result := PSTRSymbolicRatExport.packet (sign value) (numeratorDigits value) (denominatorDigits value) (rawFinal.stk 15)
  let rFinal := RatOutput.state rawFinal.stk 8 (rawFinal.var.1.1,rawFinal.var.2) (false,false) [] [] (rawFinal.stk 7) result
  obtain ⟨reader,rHead,rChain,rLast,rCount,rBounds⟩ := RatOutput.actual_singleton_reader
    (.halt : RatOutput.Statement (C × BoolOnStacks.Store states)) rawFinal.stk
    (rawFinal.var.1.1,rawFinal.var.2) rawFinal.var.1.2 value
    (rawFinal.stk 13) (rawFinal.stk 14) (rawFinal.stk 7) (rawFinal.stk 15) sameRight
  have readHead : reader.head? = some rBefore := rHead
  have readLast : reader.getLast? = some rFinal := rLast
  have shared : readerConfiguration rBefore = nativeConfiguration rawFinal := shared_configuration rawFinal nActive
  have linkedN := native_path machine caller native _ rawFinal nHead nChain nLast nActive
  have linkedR := reader_path machine caller reader rBefore rFinal readHead rChain readLast rfl
  have decomposed : nativeConfiguration rawFinal :: (reader.map readerConfiguration).tail = reader.map readerConfiguration := by
    have head : (reader.map readerConfiguration).head? = some (nativeConfiguration rawFinal) :=
      linkedR.1.trans (congrArg some shared)
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp head
    rw [same]
    rfl
  let trace := native.map nativeConfiguration ++ (reader.map readerConfiguration).tail
  have actualPath : ∀ finish : Statement C states,
      trace.IsChain (fun a b => TM2.step (program machine finish) a = some b) := by
    intro finish
    have front := native_path machine finish native _ rawFinal nHead nChain nLast nActive
    have back := reader_path machine finish reader rBefore rFinal readHead rChain readLast rfl
    exact NativeTrace.join_chain _ _ _ front.2.2 front.2.1 (decomposed.symm ▸ back.2.1)
  have last : trace.getLast? = some (readerConfiguration rFinal) :=
    (NativeTrace.join_last _ _ _ linkedN.2.2).trans (decomposed.symm ▸ linkedR.2.2)
  have active : (readerConfiguration rFinal).l = some 10 := rfl
  have frames : ∀ current ∈ trace, current.var.1.1 = context ∧
      (∀ slot, slot ≠ 13 → slot ≠ 14 → slot ≠ 7 → slot ≠ 15 → current.stk slot = background slot) ∧
      RatOutput.occupied current.stk ≤ budget background bound + 8 := by
    intro current member
    rcases List.mem_append.mp member with front | back
    · obtain ⟨oldPoint,oldMember,rfl⟩ := List.mem_map.mp front
      have source := nBounds oldPoint oldMember
      refine ⟨congrArg Prod.fst source.1,?_,?_⟩
      · intro slot notR notL _notC _notT
        exact source.2.1 slot notR notL
      · exact source.2.2.trans (Nat.le_add_right _ _)
    · obtain ⟨oldPoint,oldMember,rfl⟩ := List.mem_map.mp (List.mem_of_mem_tail back)
      have source := rBounds oldPoint oldMember
      refine ⟨(congrArg Prod.fst source.1).trans finalContext,?_,?_⟩
      · intro slot notR notL notC notT
        exact (source.2.1 slot notR notL notC notT).trans (finalBound.2.1 slot notR notL)
      · have mass := source.2.2
        rw [mass_self] at mass
        exact mass.trans (Nat.add_le_add_right nativeMass 8)
  refine ⟨trace,readerConfiguration rFinal,?_,actualPath caller,last,active,finalContext,rfl,rfl,?_,?_,?_,?_,frames,
    NativeMulLink.no_early_halt_port (program machine .halt) 10 rfl trace _ (actualPath .halt) last active⟩
  · rw [List.head?_append,linkedN.1]
    rfl
  · exact finalBound.2.1 7 (by decide) (by decide)
  · exact congrArg (PSTRSymbolicRatExport.packet (sign value) (numeratorDigits value) (denominatorDigits value))
      (finalBound.2.1 15 (by decide) (by decide))
  · intro slot notR notL notT
    by_cases atC : slot = 7
    · subst slot
      exact finalBound.2.1 7 (by decide) (by decide)
    · change RatOutput.cells rawFinal.stk [] [] (rawFinal.stk 7) result slot = background slot
      simp only [RatOutput.cells,notR,notL,atC,notT,ite_false]
      exact finalBound.2.1 slot notR notL
  · have rightSize := (point_mass rawFinal.stk 13).trans nativeMass
    have leftSize := (point_mass rawFinal.stk 14).trans nativeMass
    have base : bound ≤ budget background bound := Nat.le_add_left _ _
    dsimp only [trace]
    simp only [List.length_append,List.length_map,List.length_tail]
    omega

theorem actual_call (machine : Machine states) (caller : Statement C states)
    (context : C) (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store states)
    (background : RatOutput.Stack → List Bool) (input : List Bool) (value : Rat) (bound : Nat)
    (old : List (MachineState states)) (oldFinal : MachineState states)
    (actual : Runs machine input old oldFinal) (whole : oldFinal.Tape = Tape.mk₁ (encode [.rational value]))
    (time : old.length ≤ bound) (space : visitedSpace machine input.length old ≤ bound) :
    Call machine caller context readerMemory nativeMemory background input value bound := by
  obtain ⟨trace,final,facts⟩ := actual_boundary machine caller context readerMemory nativeMemory background
    input value bound old oldFinal actual whole time space
  refine ⟨trace,final,facts,?_,?_⟩
  · intro current member point proper
    have data := facts.boundaries current member
    have resource := RatOutput.Link.internal_bound machine caller background current
      (budget background bound + 8) data.2.2 data.2.1 point proper
    simpa only [Nat.add_assoc] using resource
  · intro point proper
    exact ⟨RatOutput.Link.program_actions machine caller point proper,
      RatOutput.Link.program_pushes machine caller point proper⟩

theorem caller_port (machine : Machine states) (caller : Statement C states) :
    program machine caller 10 = caller := by simp [program]

end PaperProofs.Common.Native.PSTRWordBool.RatMulDiv

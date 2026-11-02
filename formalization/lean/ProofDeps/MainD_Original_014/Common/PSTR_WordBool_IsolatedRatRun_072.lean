module

public import Common.PSTR_WordBool_IsolatedRatCode_071

/-! Actual fixed body/reset/return path, with background at every boundary
and internal statement node. The original old Runs is consumed internally
by073; it is not an additional input to the original arithmetic problem. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.IsolatedRat

open Turing PSTRWordVM
open RationalControllerComputation

variable {C : Type*} {states : Nat}

theorem frame_configuration (background : Stack → List Bool)
    (before : VirtualReturn.State C (BoolOnStacks.Store states))
    (frame : ∀ slot, slot ≠ 0 → slot ≠ 1 → before.stk slot = pulled background slot) :
    ∀ slot, slot ≠ 13 → slot ≠ 14 → (configuration before).stk slot = background slot := by
  intro slot notR notL
  change before.stk (roles.symm slot) = background slot
  fin_cases slot
  all_goals first
    | exact False.elim (notR rfl)
    | exact False.elim (notL rfl)
    | exact (frame _ (by decide) (by decide)).trans (by rfl)

theorem native_path (machine : Machine states) (caller : Statement C states)
    (trace : List (VirtualReturn.State C (BoolOnStacks.Store states)))
    (before final : VirtualReturn.State C (BoolOnStacks.Store states))
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun a b => TM2.step (VirtualReturn.program (VirtualBool.source machine) .halt) a = some b))
    (last : trace.getLast? = some final) (active : final.l = some 1) :
    (trace.map configuration).head? = some (configuration before) ∧
    (trace.map configuration).IsChain (fun a b => TM2.step (program machine caller) a = some b) ∧
    (trace.map configuration).getLast? = some (configuration final) := by
  let oldProgram := VirtualReturn.program (C := C) (VirtualBool.source machine) .halt
  let renamed := fun point => StackIso.statement roles (oldProgram point)
  have renamedChain := StackIso.chain_configuration_on roles oldProgram renamed trace chain
    (by intro current member point selected; rfl)
  have renamedLast : (trace.map (StackIso.configuration roles)).getLast? =
      some (StackIso.configuration roles final) := by
    rw [List.getLast?_map, last, Option.map_some]
  have proper := NativeMulLink.no_early_halt_port renamed 1 rfl _ _ renamedChain renamedLast active
  have mapped := LabelMap.actual_path_on port renamed (program machine caller)
    (trace.map (StackIso.configuration roles)) (StackIso.configuration roles before)
    (StackIso.configuration roles final) (by rw [List.head?_map, first, Option.map_some])
    renamedChain renamedLast (by
      intro current member point selected
      have different : point ≠ 1 := by
        intro same
        subst point
        exact proper current member selected
      fin_cases point
      · rfl
      · exact False.elim (different rfl))
  have maps : (trace.map (StackIso.configuration roles)).map (LabelMap.configuration port) =
      trace.map configuration := by rw [List.map_map]; rfl
  rw [maps] at mapped
  exact ⟨mapped.1, mapped.2.1, mapped.2.2.1⟩

theorem actual_old_call (machine : Machine states) (caller : Statement C states)
    (context : C) (memory : BoolOnStacks.Store states) (background : Stack → List Bool) (input : List Bool)
    (oldTrace : List (MachineState states)) (oldFinal : MachineState states)
    (first : oldTrace.head? = some (TM0.init input))
    (chain : oldTrace.IsChain (fun a b => TM0.step machine a = some b))
    (last : oldTrace.getLast? = some oldFinal) (halt : TM0.step machine oldFinal = none) :
    ∃ (trace : List (State C states)) (final : State C states),
      trace.head? = some (entry context memory background input) ∧
      trace.IsChain (fun a b => TM2.step (program machine caller) a = some b) ∧
      trace.getLast? = some final ∧ final.l = some 2 ∧
      represented final = oldFinal ∧ trace.length = oldTrace.length + 2 ∧
      (∀ current ∈ trace, current.var.1 = context ∧
        (∀ slot, slot ≠ 13 → slot ≠ 14 → current.stk slot = background slot) ∧
        occupied current.stk ≤ outside background + visitedSpace machine input.length oldTrace) ∧
      (∀ current ∈ trace.dropLast, current.l ≠ some 2) ∧
      ∀ current ∈ trace, ∀ point : Label, point ≠ 2 →
        (∀ node ∈ AuxWorkspace.nodes (program machine caller point) current.var current.stk,
          (∀ slot, (node.2 slot).length ≤ outside background + visitedSpace machine input.length oldTrace + 2) ∧
          ∀ slot, slot ≠ 13 → slot ≠ 14 → node.2 slot = background slot) ∧
        ScannerStatement.clock (program machine caller point) current.var current.stk ≤
          8 * (outside background + visitedSpace machine input.length oldTrace + 3) := by
  obtain ⟨native, nativeFinal, nativeFirst, nativeChain, nativeLast, nativeActive,
      nativeRepresented, _nativeOrder, nativeLength, _finalContext, frames, space⟩ :=
    VirtualBool.same_old_run machine .halt context (pulled background) input oldTrace oldFinal first chain last halt
  have nativeEntry : native.head? = some (original context background input) := nativeFirst
  have linked := native_path machine caller native _ nativeFinal nativeEntry nativeChain nativeLast nativeActive
  let trace := entry context memory background input :: native.map configuration
  have joined : ∀ finish : Statement C states,
      trace.IsChain (fun a b => TM2.step (program machine finish) a = some b) := by
    intro finish
    have actual := native_path machine finish native _ nativeFinal nativeEntry nativeChain nativeLast nativeActive
    apply List.isChain_cons.mpr
    refine ⟨?_, actual.2.1⟩
    intro next member
    rw [actual.1] at member
    have same : next = configuration (original context background input) := (Option.mem_some_iff.mp member).symm
    subst next
    exact enter_step machine finish context memory background input
  have nonempty : native.map configuration ≠ [] := by
    intro empty
    rw [empty] at linked
    cases linked.1
  have traceLast : trace.getLast? = some (configuration nativeFinal) := by
    rw [List.getLast?_cons_of_ne_nil nonempty]
    exact linked.2.2
  have returnActive : (configuration nativeFinal).l = some 2 := by
    change nativeFinal.l.map port = _
    rw [nativeActive]
    rfl
  have initialMember : original (states := states) context background input ∈ native := by
    obtain ⟨rest, same⟩ := List.head?_eq_some_iff.mp nativeEntry
    rw [same]
    exact List.mem_cons_self
  have traceBounds : ∀ current ∈ trace, current.var.1 = context ∧
      (∀ slot, slot ≠ 13 → slot ≠ 14 → current.stk slot = background slot) ∧
      occupied current.stk ≤ outside background + visitedSpace machine input.length oldTrace := by
    intro current member
    rcases List.mem_cons.mp member with same | later
    · subst current
      refine ⟨rfl, ?_, ?_⟩
      · intro slot notR notL
        simp only [entry, cells, notR, notL, ite_false]
      · change occupied (cells background input []) ≤ _
        rw [← original_cells (states := states) context background input, occupied_configuration]
        exact space _ initialMember
    · obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp later
      refine ⟨(frames old oldMember).1, frame_configuration background old (frames old oldMember).2, ?_⟩
      rw [occupied_configuration]
      exact space old oldMember
  refine ⟨trace, configuration nativeFinal, rfl, joined caller, traceLast, returnActive,
    (represented_configuration nativeFinal).trans nativeRepresented, ?_, traceBounds,
    NativeMulLink.no_early_halt_port (program machine .halt) 2 rfl trace _ (joined .halt) traceLast returnActive, ?_⟩
  · simp only [trace, List.length_cons, List.length_map, nativeLength]
  · intro current member point proper
    have bounds := traceBounds current member
    obtain ⟨nodes, clock⟩ := internal_bound machine caller current point proper _ bounds.2.2
    refine ⟨?_, clock⟩
    intro node present
    refine ⟨(nodes node present).1, ?_⟩
    intro slot notR notL
    exact ((nodes node present).2 slot notR notL).trans (bounds.2.1 slot notR notL)

end PaperProofs.Common.Native.PSTRWordBool.IsolatedRat

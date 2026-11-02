module

public import PSTR_WordBool_RatBinary_Code_001

/-! Actual path transport into the single binary instruction. Every
callee's active return port is preserved as an unexecuted shared state. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatBinary

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*} {states : Nat}

theorem pair_path (machine : Machine states) (caller : Statement C states)
    (trace : List (RatPair.State ((C×BoolOnStacks.Store states)×RatOutput.Store)))
    (before final : RatPair.State ((C×BoolOnStacks.Store states)×RatOutput.Store))
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (RatPair.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some RatPair.done) :
    (trace.map pairConfiguration).head?=some (pairConfiguration before) ∧
    (trace.map pairConfiguration).IsChain (fun a b=>TM2.step (program machine caller) a=some b) ∧
    (trace.map pairConfiguration).getLast?=some (pairConfiguration final) := by
  let old:=RatPair.program (C:=(C×BoolOnStacks.Store states)×RatOutput.Store) .halt
  let isoProgram:=StoreIso.machine (pairStoreMap C states) old
  have iso:=StoreIso.actual_path_on (pairStoreMap C states) old isoProgram trace before final first chain last
    (by intro current member point selected;rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram RatPair.done rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on pairLabel isoProgram (program machine caller) _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
    intro current member point selected
    exact program_pair machine caller point (by intro same;subst point;exact proper current member selected))
  have maps : (trace.map (StoreIso.configuration (pairStoreMap C states))).map (LabelMap.configuration pairLabel)=
      trace.map pairConfiguration := by rw [List.map_map];rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem arith_path (machine : Machine states) (caller : Statement C states)
    (trace : List (RatOutput.Link.State (RatPair.Store C) states))
    (before final : RatOutput.Link.State (RatPair.Store C) states)
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (RatOutput.Link.program machine .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some 10) :
    (trace.map arithConfiguration).head?=some (arithConfiguration before) ∧
    (trace.map arithConfiguration).IsChain (fun a b=>TM2.step (program machine caller) a=some b) ∧
    (trace.map arithConfiguration).getLast?=some (arithConfiguration final) := by
  have proper:=NativeMulLink.no_early_halt_port (RatOutput.Link.program machine .halt) 10 rfl trace final chain last active
  have mapped:=LabelMap.actual_path_on arithLabel (RatOutput.Link.program machine .halt) (program machine caller)
    trace before final first chain last (by
      intro current member point selected
      exact program_arith machine caller point (by intro same;subst point;exact proper current member selected))
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem drop_path (machine : Machine states) (caller : Statement C states)
    (trace : List (RatDrop.State (RatPair.Store C×BoolOnStacks.Store states)))
    (before final : RatDrop.State (RatPair.Store C×BoolOnStacks.Store states))
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (RatDrop.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some 10) :
    (trace.map dropConfiguration).head?=some (dropConfiguration before) ∧
    (trace.map dropConfiguration).IsChain (fun a b=>TM2.step (program machine caller) a=some b) ∧
    (trace.map dropConfiguration).getLast?=some (dropConfiguration final) := by
  have proper:=NativeMulLink.no_early_halt_port (RatDrop.program .halt) 10 rfl trace final chain last active
  have mapped:=LabelMap.actual_path_on dropLabel (RatDrop.program .halt) (program machine caller)
    trace before final first chain last (by
      intro current member point selected
      exact program_drop machine caller point (by intro same;subst point;exact proper current member selected))
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem pair_to_arith (before : RatPair.State ((C×BoolOnStacks.Store states)×RatOutput.Store))
    (input : List Bool) (active : before.l=some RatPair.done) (right : before.stk 13=input) (left : before.stk 14=[]) :
    arithConfiguration (RatOutput.Link.nativeConfiguration (IsolatedRat.entry
      ((pairStoreMap C states before.var).1.1,(pairStoreMap C states before.var).2)
      (pairStoreMap C states before.var).1.2 before.stk input))=pairConfiguration before := by
  cases before with
  | mk position memory contents =>
    change position=some RatPair.done at active
    subst position
    dsimp [arithConfiguration,RatOutput.Link.nativeConfiguration,IsolatedRat.entry,pairConfiguration,
      LabelMap.configuration,StoreIso.configuration,pairLabel,arithLabel]
    congr 1
    funext slot
    fin_cases slot <;> first | rfl | exact right.symm | exact left.symm

theorem cells_self (contents : RatInput.Stack→List Bool) (source : List Bool)
    (atSource : contents 15=source) (empty : contents 3=[]) : RatDrop.cells contents source []=contents := by
  funext slot
  fin_cases slot <;> first | rfl | exact atSource.symm | exact empty.symm

theorem arith_to_drop (before : RatOutput.Link.State (RatPair.Store C) states)
    (result x y : Rat) (tail : List Bool) (active : before.l=some 10)
    (source : before.stk 15=RatDrop.source result x y tail) (empty : before.stk 3=[]) :
    dropConfiguration (RatDrop.entry before.stk before.var.1 before.var.2 result x y tail)=arithConfiguration before := by
  cases before with
  | mk position memory contents =>
    change position=some 10 at active
    subst position
    dsimp [dropConfiguration,RatDrop.entry,RatDrop.state,arithConfiguration,LabelMap.configuration,dropLabel,arithLabel]
    rw [cells_self contents _ source empty]

end PaperProofs.Common.Native.PSTRWordBool.RatBinary

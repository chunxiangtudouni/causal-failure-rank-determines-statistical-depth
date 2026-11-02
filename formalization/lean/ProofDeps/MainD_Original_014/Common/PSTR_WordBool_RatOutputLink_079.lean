module

public import Common.PSTR_WordBool_RatOutputMeaning_078

/-! One fixed native/output program. The native ACTIVE2 is the actual
reader entry0 after static label/store transport; no reset or data move
occurs at this shared configuration. The final ACTIVE10 is unexecuted. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatOutput.Link

open Turing PSTRWordVM

variable {C : Type*} {states : Nat}

abbrev Label := Fin 11
abbrev Store (C : Type*) (states : Nat) := (C × BoolOnStacks.Store states) × RatOutput.Store
abbrev Statement (C : Type*) (states : Nat) := TM2.Stmt RatOutput.Alphabet Label (Store C states)
abbrev State (C : Type*) (states : Nat) := TM2.Cfg RatOutput.Alphabet Label (Store C states)

def exchange (C : Type*) (states : Nat) : ((C × RatOutput.Store) × BoolOnStacks.Store states) ≃ Store C states :=
  StoreIso.exchange C RatOutput.Store (BoolOnStacks.Store states)

def nativeLabel (point : IsolatedRat.Label) : Label := ⟨point.val,by omega⟩
def readerLabel (point : RatOutput.Label) : Label := ⟨point.val+2,by omega⟩

def program (machine : TM0.Machine Bool (Fin (states+1))) (caller : Statement C states) (point : Label) : Statement C states :=
  if native : point.val < 2 then
    LabelMap.statement nativeLabel (StoreIso.statement (exchange C states)
      (IsolatedRat.program (C := C × RatOutput.Store) machine .halt ⟨point.val,by omega⟩))
  else if done : point = 10 then caller else
    LabelMap.statement readerLabel
      (RatOutput.program (C := C × BoolOnStacks.Store states) .halt ⟨point.val-2,by omega⟩)

def nativeConfiguration (before : IsolatedRat.State (C × RatOutput.Store) states) : State C states :=
  LabelMap.configuration nativeLabel (StoreIso.configuration (exchange C states) before)

def readerConfiguration (before : RatOutput.State (C × BoolOnStacks.Store states)) : State C states :=
  LabelMap.configuration readerLabel before

theorem program_native (machine : TM0.Machine Bool (Fin (states+1))) (caller : Statement C states)
    (point : IsolatedRat.Label) (proper : point ≠ 2) :
    program machine caller (nativeLabel point) = LabelMap.statement nativeLabel
      (StoreIso.statement (exchange C states) (IsolatedRat.program (C := C × RatOutput.Store) machine .halt point)) := by
  fin_cases point
  · rfl
  · rfl
  · exact False.elim (proper rfl)

theorem program_reader (machine : TM0.Machine Bool (Fin (states+1))) (caller : Statement C states)
    (point : RatOutput.Label) (proper : point ≠ 8) :
    program machine caller (readerLabel point) = LabelMap.statement readerLabel
      (RatOutput.program (C := C × BoolOnStacks.Store states) .halt point) := by
  fin_cases point
  all_goals first | exact False.elim (proper rfl) | rfl

theorem native_path (machine : TM0.Machine Bool (Fin (states+1))) (caller : Statement C states)
    (trace : List (IsolatedRat.State (C × RatOutput.Store) states))
    (before final : IsolatedRat.State (C × RatOutput.Store) states)
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun a b => TM2.step (IsolatedRat.program machine .halt) a = some b))
    (last : trace.getLast? = some final) (active : final.l = some 2) :
    (trace.map nativeConfiguration).head? = some (nativeConfiguration before) ∧
    (trace.map nativeConfiguration).IsChain (fun a b => TM2.step (program machine caller) a = some b) ∧
    (trace.map nativeConfiguration).getLast? = some (nativeConfiguration final) := by
  let isoProgram := StoreIso.machine (exchange C states) (IsolatedRat.program machine .halt)
  have iso := StoreIso.actual_path_on (exchange C states) (IsolatedRat.program machine .halt)
    isoProgram trace before final first chain last (by intro current member point selected; rfl)
  have proper := NativeMulLink.no_early_halt_port isoProgram 2 rfl
    (trace.map (StoreIso.configuration (exchange C states))) (StoreIso.configuration (exchange C states) final)
    iso.2.1 iso.2.2.1 active
  have mapped := LabelMap.actual_path_on nativeLabel isoProgram (program machine caller)
    (trace.map (StoreIso.configuration (exchange C states))) _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      exact program_native machine caller point (by intro same; subst point; exact proper current member selected))
  have maps : (trace.map (StoreIso.configuration (exchange C states))).map (LabelMap.configuration nativeLabel) =
      trace.map nativeConfiguration := by rw [List.map_map]; rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem reader_path (machine : TM0.Machine Bool (Fin (states+1))) (caller : Statement C states)
    (trace : List (RatOutput.State (C × BoolOnStacks.Store states)))
    (before final : RatOutput.State (C × BoolOnStacks.Store states))
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun a b => TM2.step (RatOutput.program .halt) a = some b))
    (last : trace.getLast? = some final) (active : final.l = some 8) :
    (trace.map readerConfiguration).head? = some (readerConfiguration before) ∧
    (trace.map readerConfiguration).IsChain (fun a b => TM2.step (program machine caller) a = some b) ∧
    (trace.map readerConfiguration).getLast? = some (readerConfiguration final) := by
  have proper := NativeMulLink.no_early_halt_port (RatOutput.program .halt) 8 rfl trace final chain last active
  have mapped := LabelMap.actual_path_on readerLabel (RatOutput.program .halt) (program machine caller)
    trace before final first chain last (by
      intro current member point selected
      exact program_reader machine caller point (by intro same; subst point; exact proper current member selected))
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem cells_self (contents : RatOutput.Stack → List Bool) :
    RatOutput.cells contents (contents 13) (contents 14) (contents 7) (contents 15) = contents := by
  funext point; fin_cases point <;> rfl

theorem shared_configuration (before : IsolatedRat.State (C × RatOutput.Store) states) (active : before.l = some 2) :
    readerConfiguration (RatOutput.state before.stk 0 (before.var.1.1,before.var.2) before.var.1.2
      (before.stk 13) (before.stk 14) (before.stk 7) (before.stk 15)) = nativeConfiguration before := by
  cases before with
  | mk position memory contents =>
    change position = some 2 at active
    subst position
    dsimp [readerConfiguration,nativeConfiguration,RatOutput.state,LabelMap.configuration,StoreIso.configuration,exchange,StoreIso.exchange]
    rw [cells_self]
    rfl

end PaperProofs.Common.Native.PSTRWordBool.RatOutput.Link

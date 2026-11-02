module

public import Common.PSTR_WordBool_TM2Native_040

/-! Reuse an actual TM2 component inside a larger fixed store. The ONE lifted
machine preserves its caller context on every real source step, including
internal snapshots. No runtime value selects a different machine. When this
is compiled by 040, the entire context/store must be fixed and finite before
input. This future006 source is excluded from batch005. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.ContextLift

open Turing

variable {K : Type*} {Γ : K → Type*} {Λ σ C : Type*}

def statement : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ (C × σ)
  | .push slot value tail => .push slot (fun store => value store.2) (statement tail)
  | .peek slot value tail =>
      .peek slot (fun store bit => (store.1, value store.2 bit)) (statement tail)
  | .pop slot value tail =>
      .pop slot (fun store bit => (store.1, value store.2 bit)) (statement tail)
  | .load value tail => .load (fun store => (store.1, value store.2)) (statement tail)
  | .branch test yes no => .branch (fun store => test store.2) (statement yes) (statement no)
  | .goto target => .goto (fun store => target store.2)
  | .halt => .halt

def machine (source : Λ → TM2.Stmt Γ Λ σ) (label : Λ) : TM2.Stmt Γ Λ (C × σ) :=
  statement (source label)

def configuration (context : C) (source : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ (C × σ) :=
  ⟨source.l, (context, source.var), source.stk⟩

def projection (source : TM2.Cfg Γ Λ (C × σ)) : TM2.Cfg Γ Λ σ :=
  ⟨source.l, source.var.2, source.stk⟩

theorem projection_configuration (context : C) (source : TM2.Cfg Γ Λ σ) :
    projection (configuration context source) = source := rfl

theorem statement_actions (source : TM2.Stmt Γ Λ σ) :
    ScannerClock.actions (statement (C := C) source) = ScannerClock.actions source := by
  induction source with
  | push slot value tail ih | peek slot value tail ih | pop slot value tail ih =>
    exact congrArg (· + 1) ih
  | load value tail ih => exact ih
  | branch test yes no ihYes ihNo => exact congrArg₂ max ihYes ihNo
  | goto target => rfl
  | halt => rfl

theorem statement_pushes (source : TM2.Stmt Γ Λ σ) :
    AuxWorkspace.pushes (statement (C := C) source) = AuxWorkspace.pushes source := by
  induction source with
  | push slot value tail ih => exact congrArg (· + 1) ih
  | peek slot value tail ih | pop slot value tail ih | load value tail ih => exact ih
  | branch test yes no ihYes ihNo => exact congrArg₂ max ihYes ihNo
  | goto target => rfl
  | halt => rfl

theorem statement_supports (source : TM2.Stmt Γ Λ σ) (support : Finset Λ)
    (closed : TM2.SupportsStmt support source) : TM2.SupportsStmt support (statement (C := C) source) := by
  revert closed
  induction source with
  | push slot value tail ih | peek slot value tail ih | pop slot value tail ih | load value tail ih =>
    intro closed
    exact ih closed
  | branch test yes no ihYes ihNo =>
    intro closed
    exact ⟨ihYes closed.1, ihNo closed.2⟩
  | goto target => intro closed store; exact closed store.2
  | halt => intro _; trivial

theorem machine_supports [Inhabited Λ] (source : Λ → TM2.Stmt Γ Λ σ) (support : Finset Λ)
    (closed : TM2.Supports source support) : TM2.Supports (machine (C := C) source) support :=
  ⟨closed.1, fun label present => statement_supports (source label) support (closed.2 label present)⟩

section Execution

variable [DecidableEq K]

theorem stepAux_configuration (source : TM2.Stmt Γ Λ σ) (context : C)
    (store : σ) (slots : ∀ slot, List (Γ slot)) :
    TM2.stepAux (statement source) (context, store) slots =
      configuration context (TM2.stepAux source store slots) := by
  induction source generalizing store slots with
  | push slot value tail ih => exact ih store (Function.update slots slot (value store :: slots slot))
  | peek slot value tail ih => exact ih (value store (slots slot).head?) slots
  | pop slot value tail ih => exact ih (value store (slots slot).head?) (Function.update slots slot (slots slot).tail)
  | load value tail ih => exact ih (value store) slots
  | branch test yes no ihYes ihNo =>
    cases choice : test store
    · simpa only [statement, TM2.stepAux, choice, Bool.cond_false] using ihNo store slots
    · simpa only [statement, TM2.stepAux, choice, Bool.cond_true] using ihYes store slots
  | goto target => rfl
  | halt => rfl

theorem step_configuration (source : Λ → TM2.Stmt Γ Λ σ) (context : C) (state : TM2.Cfg Γ Λ σ) :
    TM2.step (machine source) (configuration context state) =
      (TM2.step source state).map (configuration context) := by
  cases state with
  | mk label store slots =>
    cases label with
    | none => rfl
    | some label =>
      change some (TM2.stepAux (statement (source label)) (context, store) slots) =
        some (configuration context (TM2.stepAux (source label) store slots))
      rw [stepAux_configuration]

theorem step_configuration_on (source : Λ → TM2.Stmt Γ Λ σ)
    (target : Λ → TM2.Stmt Γ Λ (C × σ)) (context : C) (state : TM2.Cfg Γ Λ σ)
    (same : ∀ label, state.l = some label → target label = statement (source label)) :
    TM2.step target (configuration context state) =
      (TM2.step source state).map (configuration context) := by
  cases state with
  | mk label store slots =>
    cases label with
    | none => rfl
    | some label =>
      change some (TM2.stepAux (target label) (context, store) slots) = _
      rw [same label rfl, stepAux_configuration]
      rfl

theorem chain_configuration_on (source : Λ → TM2.Stmt Γ Λ σ)
    (target : Λ → TM2.Stmt Γ Λ (C × σ)) (context : C) (trace : List (TM2.Cfg Γ Λ σ))
    (chain : trace.IsChain (fun before after => TM2.step source before = some after))
    (same : ∀ state ∈ trace.dropLast, ∀ label, state.l = some label → target label = statement (source label)) :
    (trace.map (configuration context)).IsChain (fun before after => TM2.step target before = some after) := by
  induction trace with
  | nil => exact List.isChain_nil
  | cons first rest ih =>
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons next rest =>
      obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
      have firstSame : ∀ label, first.l = some label → target label = statement (source label) := by
        intro label active
        exact same first (by rw [List.dropLast_cons_cons]; exact List.mem_cons_self) label active
      have tailSame : ∀ state ∈ (next :: rest).dropLast, ∀ label, state.l = some label →
          target label = statement (source label) := by
        intro state present label active
        apply same state _ label active
        rw [List.dropLast_cons_cons]
        exact List.mem_cons_of_mem _ present
      apply List.isChain_cons_cons.mpr
      refine ⟨?_, ih tailChain tailSame⟩
      rw [step_configuration_on source target context first firstSame, edge, Option.map_some]

def snapshot (context : C) (source : AuxWorkspace.Snapshot (Γ := Γ) (σ := σ)) :
    AuxWorkspace.Snapshot (Γ := Γ) (σ := C × σ) := ((context, source.1), source.2)

theorem nodes_configuration (source : TM2.Stmt Γ Λ σ) (context : C)
    (store : σ) (slots : ∀ slot, List (Γ slot)) :
    AuxWorkspace.nodes (statement source) (context, store) slots =
      (AuxWorkspace.nodes source store slots).map (snapshot context) := by
  induction source generalizing store slots with
  | push slot value tail ih =>
    simpa only [statement, AuxWorkspace.nodes, List.map_cons, snapshot] using
      congrArg (List.cons ((context, store), slots))
        (ih store (Function.update slots slot (value store :: slots slot)))
  | peek slot value tail ih =>
    simpa only [statement, AuxWorkspace.nodes, List.map_cons, snapshot] using
      congrArg (List.cons ((context, store), slots)) (ih (value store (slots slot).head?) slots)
  | pop slot value tail ih =>
    simpa only [statement, AuxWorkspace.nodes, List.map_cons, snapshot] using
      congrArg (List.cons ((context, store), slots))
        (ih (value store (slots slot).head?) (Function.update slots slot (slots slot).tail))
  | load value tail ih =>
    simpa only [statement, AuxWorkspace.nodes, List.map_cons, snapshot] using
      congrArg (List.cons ((context, store), slots)) (ih (value store) slots)
  | branch test yes no ihYes ihNo =>
    cases choice : test store
    · simpa only [statement, AuxWorkspace.nodes, List.map_cons, snapshot, choice, Bool.false_eq_true,
        ite_false] using congrArg (List.cons ((context, store), slots)) (ihNo store slots)
    · simpa only [statement, AuxWorkspace.nodes, List.map_cons, snapshot, choice, ite_true] using
        congrArg (List.cons ((context, store), slots)) (ihYes store slots)
  | goto target => rfl
  | halt => rfl

theorem actual_path (source : Λ → TM2.Stmt Γ Λ σ) (context : C)
    (trace : List (TM2.Cfg Γ Λ σ)) (before final : TM2.Cfg Γ Λ σ)
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun before after => TM2.step source before = some after))
    (last : trace.getLast? = some final) :
    (trace.map (configuration context)).head? = some (configuration context before) ∧
      (trace.map (configuration context)).IsChain
        (fun before after => TM2.step (machine source) before = some after) ∧
      (trace.map (configuration context)).getLast? = some (configuration context final) ∧
      (trace.map (configuration context)).length = trace.length ∧
      (trace.map (configuration context)).map projection = trace ∧
      ∀ current ∈ trace.map (configuration context), current.var.1 = context ∧
        ∃ old ∈ trace, projection current = old ∧ current.stk = old.stk := by
  refine ⟨?_, ?_, ?_, List.length_map (configuration context), ?_, ?_⟩
  · rw [List.head?_map, first, Option.map_some]
  · apply List.isChain_map_of_isChain (configuration context) _ chain
    intro current next edge
    rw [step_configuration, edge, Option.map_some]
  · rw [List.getLast?_map, last, Option.map_some]
  · rw [List.map_map]
    change trace.map id = trace
    rw [List.map_id]
  · intro current present
    obtain ⟨old, member, same⟩ := List.mem_map.mp present
    subst current
    exact ⟨rfl, old, member, rfl, rfl⟩

theorem actual_halt (source : Λ → TM2.Stmt Γ Λ σ) (context : C) (final : TM2.Cfg Γ Λ σ)
    (halt : TM2.step source final = none) : TM2.step (machine source) (configuration context final) = none := by
  rw [step_configuration, halt, Option.map_none]

theorem actual_path_on (source : Λ → TM2.Stmt Γ Λ σ)
    (target : Λ → TM2.Stmt Γ Λ (C × σ)) (context : C)
    (trace : List (TM2.Cfg Γ Λ σ)) (before final : TM2.Cfg Γ Λ σ)
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun before after => TM2.step source before = some after))
    (last : trace.getLast? = some final)
    (same : ∀ state ∈ trace.dropLast, ∀ label, state.l = some label → target label = statement (source label)) :
    (trace.map (configuration context)).head? = some (configuration context before) ∧
      (trace.map (configuration context)).IsChain (fun before after => TM2.step target before = some after) ∧
      (trace.map (configuration context)).getLast? = some (configuration context final) ∧
      (trace.map (configuration context)).length = trace.length ∧
      (trace.map (configuration context)).map projection = trace ∧
      ∀ current ∈ trace.map (configuration context), current.var.1 = context ∧
        ∃ old ∈ trace, projection current = old ∧ current.stk = old.stk := by
  obtain ⟨head, _oldChain, endState, length, projected, frames⟩ :=
    actual_path source context trace before final first chain last
  exact ⟨head, chain_configuration_on source target context trace chain same,
    endState, length, projected, frames⟩

omit [DecidableEq K] in
theorem actual_bounds (context : C) (trace : List (TM2.Cfg Γ Λ σ)) (bound : Nat)
    (bounded : ∀ state ∈ trace, ∀ slot, (state.stk slot).length ≤ bound) :
    ∀ state ∈ trace.map (configuration context), ∀ slot, (state.stk slot).length ≤ bound := by
  intro state present slot
  obtain ⟨old, member, same⟩ := List.mem_map.mp present
  subst state
  exact bounded old member slot

omit [DecidableEq K] in
theorem actual_counts (source : Λ → TM2.Stmt Γ Λ σ) (context : C)
    (trace : List (TM2.Cfg Γ Λ σ)) (actionBound pushBound : Nat)
    (counts : ∀ state ∈ trace, ∀ label, state.l = some label →
      ScannerClock.actions (source label) ≤ actionBound ∧ AuxWorkspace.pushes (source label) ≤ pushBound) :
    ∀ state ∈ trace.map (configuration context), ∀ label, state.l = some label →
      ScannerClock.actions (machine (C := C) source label) ≤ actionBound ∧
        AuxWorkspace.pushes (machine (C := C) source label) ≤ pushBound := by
  intro state present label active
  obtain ⟨old, member, same⟩ := List.mem_map.mp present
  subst state
  have sourceCounts := counts old member label active
  simpa only [machine, statement_actions, statement_pushes] using sourceCounts

end Execution

end PaperProofs.Common.Native.PSTRWordBool.ContextLift

module

public import Common.PSTR_WordBool_ContextLift_041
public import Mathlib.Logic.Equiv.Prod

/-! Compile-time conjugation by ONE fixed control-store equivalence. This
transports actual instructions, paths and internal stack snapshots. It does
not reset control, select a runtime machine, drop a final step or move data.
Consumers use fixed finite product reassociation/commutation before input. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.StoreIso

open Turing

variable {K : Type*} {Γ : K → Type*} {Λ σ τ : Type*}

def statement (equivalence : σ ≃ τ) : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ τ
  | .push slot value tail =>
      .push slot (fun memory => value (equivalence.symm memory)) (statement equivalence tail)
  | .peek slot value tail =>
      .peek slot (fun memory bit => equivalence (value (equivalence.symm memory) bit))
        (statement equivalence tail)
  | .pop slot value tail =>
      .pop slot (fun memory bit => equivalence (value (equivalence.symm memory) bit))
        (statement equivalence tail)
  | .load value tail =>
      .load (fun memory => equivalence (value (equivalence.symm memory))) (statement equivalence tail)
  | .branch test yes no =>
      .branch (fun memory => test (equivalence.symm memory))
        (statement equivalence yes) (statement equivalence no)
  | .goto target => .goto (fun memory => target (equivalence.symm memory))
  | .halt => .halt

def machine (equivalence : σ ≃ τ) (source : Λ → TM2.Stmt Γ Λ σ) (label : Λ) : TM2.Stmt Γ Λ τ :=
  statement equivalence (source label)

def configuration (equivalence : σ ≃ τ) (source : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ τ :=
  ⟨source.l, equivalence source.var, source.stk⟩

theorem configuration_symm (equivalence : σ ≃ τ) (source : TM2.Cfg Γ Λ σ) :
    configuration equivalence.symm (configuration equivalence source) = source := by
  cases source
  simp only [configuration, Equiv.symm_apply_apply]

def exchange (A B D : Type*) : ((A × B) × D) ≃ ((A × D) × B) :=
  ((Equiv.prodAssoc A B D).trans
    (Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm B D))).trans (Equiv.prodAssoc A D B).symm

theorem exchange_apply {A B D : Type*} (value : (A × B) × D) :
    exchange A B D value = ((value.1.1, value.2), value.1.2) := rfl

theorem statement_actions (equivalence : σ ≃ τ) (source : TM2.Stmt Γ Λ σ) :
    ScannerClock.actions (statement equivalence source) = ScannerClock.actions source := by
  induction source with
  | push slot value tail ih | peek slot value tail ih | pop slot value tail ih =>
    exact congrArg (· + 1) ih
  | load value tail ih => exact ih
  | branch test yes no ihYes ihNo => exact congrArg₂ max ihYes ihNo
  | goto target => rfl
  | halt => rfl

theorem statement_pushes (equivalence : σ ≃ τ) (source : TM2.Stmt Γ Λ σ) :
    AuxWorkspace.pushes (statement equivalence source) = AuxWorkspace.pushes source := by
  induction source with
  | push slot value tail ih => exact congrArg (· + 1) ih
  | peek slot value tail ih | pop slot value tail ih | load value tail ih => exact ih
  | branch test yes no ihYes ihNo => exact congrArg₂ max ihYes ihNo
  | goto target => rfl
  | halt => rfl

theorem statement_supports (equivalence : σ ≃ τ) (source : TM2.Stmt Γ Λ σ) (support : Finset Λ)
    (closed : TM2.SupportsStmt support source) : TM2.SupportsStmt support (statement equivalence source) := by
  revert closed
  induction source with
  | push slot value tail ih | peek slot value tail ih | pop slot value tail ih | load value tail ih =>
    intro closed
    exact ih closed
  | branch test yes no ihYes ihNo =>
    intro closed
    exact ⟨ihYes closed.1, ihNo closed.2⟩
  | goto target => intro closed memory; exact closed (equivalence.symm memory)
  | halt => intro _; trivial

theorem machine_supports [Inhabited Λ] (equivalence : σ ≃ τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (support : Finset Λ) (closed : TM2.Supports source support) :
    TM2.Supports (machine equivalence source) support :=
  ⟨closed.1, fun label present => statement_supports equivalence (source label) support (closed.2 label present)⟩

section Execution

variable [DecidableEq K]

theorem stepAux_configuration (equivalence : σ ≃ τ) (source : TM2.Stmt Γ Λ σ)
    (memory : σ) (slots : ∀ slot, List (Γ slot)) :
    TM2.stepAux (statement equivalence source) (equivalence memory) slots =
      configuration equivalence (TM2.stepAux source memory slots) := by
  induction source generalizing memory slots with
  | push slot value tail ih =>
    simpa only [statement, TM2.stepAux, Equiv.symm_apply_apply] using
      ih memory (Function.update slots slot (value memory :: slots slot))
  | peek slot value tail ih =>
    simpa only [statement, TM2.stepAux, Equiv.symm_apply_apply] using
      ih (value memory (slots slot).head?) slots
  | pop slot value tail ih =>
    simpa only [statement, TM2.stepAux, Equiv.symm_apply_apply] using
      ih (value memory (slots slot).head?) (Function.update slots slot (slots slot).tail)
  | load value tail ih =>
    simpa only [statement, TM2.stepAux, Equiv.symm_apply_apply] using ih (value memory) slots
  | branch test yes no ihYes ihNo =>
    cases choice : test memory
    · simpa only [statement, TM2.stepAux, Equiv.symm_apply_apply, choice, Bool.cond_false] using ihNo memory slots
    · simpa only [statement, TM2.stepAux, Equiv.symm_apply_apply, choice, Bool.cond_true] using ihYes memory slots
  | goto target => simp only [statement, TM2.stepAux, configuration, Equiv.symm_apply_apply]
  | halt => rfl

theorem step_configuration (equivalence : σ ≃ τ) (source : Λ → TM2.Stmt Γ Λ σ)
    (state : TM2.Cfg Γ Λ σ) :
    TM2.step (machine equivalence source) (configuration equivalence state) =
      (TM2.step source state).map (configuration equivalence) := by
  cases state with
  | mk label memory slots =>
    cases label with
    | none => rfl
    | some label =>
      change some (TM2.stepAux (statement equivalence (source label)) (equivalence memory) slots) = _
      rw [stepAux_configuration]
      rfl

theorem step_configuration_on (equivalence : σ ≃ τ) (source : Λ → TM2.Stmt Γ Λ σ)
    (target : Λ → TM2.Stmt Γ Λ τ) (state : TM2.Cfg Γ Λ σ)
    (same : ∀ label, state.l = some label → target label = statement equivalence (source label)) :
    TM2.step target (configuration equivalence state) =
      (TM2.step source state).map (configuration equivalence) := by
  cases state with
  | mk label memory slots =>
    cases label with
    | none => rfl
    | some label =>
      change some (TM2.stepAux (target label) (equivalence memory) slots) = _
      rw [same label rfl, stepAux_configuration]
      rfl

theorem chain_configuration_on (equivalence : σ ≃ τ) (source : Λ → TM2.Stmt Γ Λ σ)
    (target : Λ → TM2.Stmt Γ Λ τ) (trace : List (TM2.Cfg Γ Λ σ))
    (chain : trace.IsChain (fun before after => TM2.step source before = some after))
    (same : ∀ state ∈ trace.dropLast, ∀ label, state.l = some label → target label = statement equivalence (source label)) :
    (trace.map (configuration equivalence)).IsChain (fun before after => TM2.step target before = some after) := by
  induction trace with
  | nil => exact List.isChain_nil
  | cons first rest ih =>
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons next rest =>
      obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
      have firstSame : ∀ label, first.l = some label → target label = statement equivalence (source label) := by
        intro label active
        exact same first (by rw [List.dropLast_cons_cons]; exact List.mem_cons_self) label active
      have tailSame : ∀ state ∈ (next :: rest).dropLast, ∀ label, state.l = some label →
          target label = statement equivalence (source label) := by
        intro state present label active
        apply same state _ label active
        rw [List.dropLast_cons_cons]
        exact List.mem_cons_of_mem _ present
      apply List.isChain_cons_cons.mpr
      refine ⟨?_, ih tailChain tailSame⟩
      rw [step_configuration_on equivalence source target first firstSame, edge, Option.map_some]

def snapshot (equivalence : σ ≃ τ) (source : AuxWorkspace.Snapshot (Γ := Γ) (σ := σ)) :
    AuxWorkspace.Snapshot (Γ := Γ) (σ := τ) := (equivalence source.1, source.2)

theorem nodes_configuration (equivalence : σ ≃ τ) (source : TM2.Stmt Γ Λ σ)
    (memory : σ) (slots : ∀ slot, List (Γ slot)) :
    AuxWorkspace.nodes (statement equivalence source) (equivalence memory) slots =
      (AuxWorkspace.nodes source memory slots).map (snapshot equivalence) := by
  induction source generalizing memory slots with
  | push slot value tail ih =>
    simpa only [statement, AuxWorkspace.nodes, Equiv.symm_apply_apply, List.map_cons, snapshot] using
      congrArg (List.cons (equivalence memory, slots))
        (ih memory (Function.update slots slot (value memory :: slots slot)))
  | peek slot value tail ih =>
    simpa only [statement, AuxWorkspace.nodes, Equiv.symm_apply_apply, List.map_cons, snapshot] using
      congrArg (List.cons (equivalence memory, slots)) (ih (value memory (slots slot).head?) slots)
  | pop slot value tail ih =>
    simpa only [statement, AuxWorkspace.nodes, Equiv.symm_apply_apply, List.map_cons, snapshot] using
      congrArg (List.cons (equivalence memory, slots))
        (ih (value memory (slots slot).head?) (Function.update slots slot (slots slot).tail))
  | load value tail ih =>
    simpa only [statement, AuxWorkspace.nodes, Equiv.symm_apply_apply, List.map_cons, snapshot] using
      congrArg (List.cons (equivalence memory, slots)) (ih (value memory) slots)
  | branch test yes no ihYes ihNo =>
    cases choice : test memory
    · simpa only [statement, AuxWorkspace.nodes, Equiv.symm_apply_apply, List.map_cons, snapshot,
        choice, Bool.false_eq_true, ite_false] using congrArg (List.cons (equivalence memory, slots)) (ihNo memory slots)
    · simpa only [statement, AuxWorkspace.nodes, Equiv.symm_apply_apply, List.map_cons, snapshot,
        choice, ite_true] using congrArg (List.cons (equivalence memory, slots)) (ihYes memory slots)
  | goto target => rfl
  | halt => rfl

theorem actual_path_on (equivalence : σ ≃ τ) (source : Λ → TM2.Stmt Γ Λ σ)
    (target : Λ → TM2.Stmt Γ Λ τ) (trace : List (TM2.Cfg Γ Λ σ)) (before final : TM2.Cfg Γ Λ σ)
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun before after => TM2.step source before = some after))
    (last : trace.getLast? = some final)
    (same : ∀ state ∈ trace.dropLast, ∀ label, state.l = some label → target label = statement equivalence (source label)) :
    (trace.map (configuration equivalence)).head? = some (configuration equivalence before) ∧
      (trace.map (configuration equivalence)).IsChain (fun before after => TM2.step target before = some after) ∧
      (trace.map (configuration equivalence)).getLast? = some (configuration equivalence final) ∧
      (trace.map (configuration equivalence)).length = trace.length ∧
      (trace.map (configuration equivalence)).map (configuration equivalence.symm) = trace ∧
      ∀ current ∈ trace.map (configuration equivalence),
        ∃ old ∈ trace, current = configuration equivalence old ∧ current.stk = old.stk := by
  refine ⟨?_, chain_configuration_on equivalence source target trace chain same, ?_,
    List.length_map (configuration equivalence), ?_, ?_⟩
  · rw [List.head?_map, first, Option.map_some]
  · rw [List.getLast?_map, last, Option.map_some]
  · rw [List.map_map]
    have identical : configuration equivalence.symm ∘ configuration equivalence =
        (id : TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ) := by
      funext old
      exact configuration_symm equivalence old
    rw [identical, List.map_id]
  · intro current present
    obtain ⟨old, member, identical⟩ := List.mem_map.mp present
    subst current
    exact ⟨old, member, rfl, rfl⟩

end Execution

end PaperProofs.Common.Native.PSTRWordBool.StoreIso

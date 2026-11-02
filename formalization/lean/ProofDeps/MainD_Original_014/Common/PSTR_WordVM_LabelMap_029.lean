module

public import Common.PSTR_WordVM_VirtualReturn_024

/-! Static label transport for actual callee/caller linkage. Only goto
targets and configuration labels are mapped; store and every stack are
identical, including every internal snapshot. The REAL return goto stays
in the executed path. Code agreement is required only at actually executed
proper trace points, so the final active callee port may contain a caller.
This does not manufacture a default initial configuration or reset data. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.LabelMap

open Turing

variable {K : Type*} {Γ : K → Type*} {Λ Ω σ : Type*}

def statement (labelMap : Λ → Ω) : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Ω σ
  | .push slot value tail => .push slot value (statement labelMap tail)
  | .peek slot value tail => .peek slot value (statement labelMap tail)
  | .pop slot value tail => .pop slot value (statement labelMap tail)
  | .load value tail => .load value (statement labelMap tail)
  | .branch test yes no => .branch test (statement labelMap yes) (statement labelMap no)
  | .goto target => .goto (fun memory => labelMap (target memory))
  | .halt => .halt

def configuration (labelMap : Λ → Ω) (source : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Ω σ :=
  ⟨source.l.map labelMap, source.var, source.stk⟩

theorem configuration_active (labelMap : Λ → Ω) (source : TM2.Cfg Γ Λ σ) (point : Λ)
    (active : source.l = some point) :
    (configuration labelMap source).l = some (labelMap point) := by
  change source.l.map labelMap = _
  rw [active, Option.map_some]

theorem configuration_stopped (labelMap : Λ → Ω) (source : TM2.Cfg Γ Λ σ)
    (stopped : source.l = none) : (configuration labelMap source).l = none := by
  change source.l.map labelMap = _
  rw [stopped, Option.map_none]

theorem statement_actions (labelMap : Λ → Ω) (source : TM2.Stmt Γ Λ σ) :
    PSTRWordBool.ScannerClock.actions (statement labelMap source) =
      PSTRWordBool.ScannerClock.actions source := by
  induction source with
  | push slot value tail ih | peek slot value tail ih | pop slot value tail ih =>
    exact congrArg (· + 1) ih
  | load value tail ih => exact ih
  | branch test yes no ihYes ihNo => exact congrArg₂ max ihYes ihNo
  | goto target => rfl
  | halt => rfl

theorem statement_pushes (labelMap : Λ → Ω) (source : TM2.Stmt Γ Λ σ) :
    PSTRWordBool.AuxWorkspace.pushes (statement labelMap source) =
      PSTRWordBool.AuxWorkspace.pushes source := by
  induction source with
  | push slot value tail ih => exact congrArg (· + 1) ih
  | peek slot value tail ih | pop slot value tail ih | load value tail ih => exact ih
  | branch test yes no ihYes ihNo => exact congrArg₂ max ihYes ihNo
  | goto target => rfl
  | halt => rfl

theorem statement_supports (labelMap : Λ → Ω) (source : TM2.Stmt Γ Λ σ)
    (oldSupport : Finset Λ) (newSupport : Finset Ω)
    (closed : TM2.SupportsStmt oldSupport source)
    (maps : ∀ point ∈ oldSupport, labelMap point ∈ newSupport) :
    TM2.SupportsStmt newSupport (statement labelMap source) := by
  revert closed
  induction source with
  | push slot value tail ih | peek slot value tail ih | pop slot value tail ih | load value tail ih =>
    intro closed
    exact ih closed
  | branch test yes no ihYes ihNo =>
    intro closed
    exact ⟨ihYes closed.1, ihNo closed.2⟩
  | goto target => intro closed memory; exact maps (target memory) (closed memory)
  | halt => intro _; trivial

section Execution

variable [DecidableEq K]

theorem stepAux_configuration (labelMap : Λ → Ω) (source : TM2.Stmt Γ Λ σ)
    (memory : σ) (slots : ∀ slot, List (Γ slot)) :
    TM2.stepAux (statement labelMap source) memory slots =
      configuration labelMap (TM2.stepAux source memory slots) := by
  induction source generalizing memory slots with
  | push slot value tail ih => exact ih memory (Function.update slots slot (value memory :: slots slot))
  | peek slot value tail ih => exact ih (value memory (slots slot).head?) slots
  | pop slot value tail ih =>
    exact ih (value memory (slots slot).head?)
      (Function.update slots slot (slots slot).tail)
  | load value tail ih => exact ih (value memory) slots
  | branch test yes no ihYes ihNo =>
    cases choice : test memory
    · simpa only [statement, TM2.stepAux, choice, Bool.cond_false] using ihNo memory slots
    · simpa only [statement, TM2.stepAux, choice, Bool.cond_true] using ihYes memory slots
  | goto target => rfl
  | halt => rfl

theorem step_configuration_on (labelMap : Λ → Ω) (source : Λ → TM2.Stmt Γ Λ σ)
    (target : Ω → TM2.Stmt Γ Ω σ) (before : TM2.Cfg Γ Λ σ)
    (same : ∀ point, before.l = some point → target (labelMap point) = statement labelMap (source point)) :
    TM2.step target (configuration labelMap before) =
      (TM2.step source before).map (configuration labelMap) := by
  cases before with
  | mk position memory slots =>
    cases position with
    | none => rfl
    | some point =>
      change some (TM2.stepAux (target (labelMap point)) memory slots) = _
      rw [same point rfl, stepAux_configuration]
      rfl

theorem chain_configuration_on (labelMap : Λ → Ω) (source : Λ → TM2.Stmt Γ Λ σ)
    (target : Ω → TM2.Stmt Γ Ω σ) (trace : List (TM2.Cfg Γ Λ σ))
    (chain : trace.IsChain (fun before after => TM2.step source before = some after))
    (same : ∀ before ∈ trace.dropLast, ∀ point, before.l = some point →
      target (labelMap point) = statement labelMap (source point)) :
    (trace.map (configuration labelMap)).IsChain (fun before after => TM2.step target before = some after) := by
  induction trace with
  | nil => exact List.isChain_nil
  | cons first rest ih =>
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons next rest =>
      obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
      have firstSame : ∀ point, first.l = some point →
          target (labelMap point) = statement labelMap (source point) := by
        intro point active
        exact same first (by rw [List.dropLast_cons_cons]; exact List.mem_cons_self) point active
      have tailSame : ∀ before ∈ (next :: rest).dropLast, ∀ point, before.l = some point →
          target (labelMap point) = statement labelMap (source point) := by
        intro before present point active
        apply same before _ point active
        rw [List.dropLast_cons_cons]
        exact List.mem_cons_of_mem _ present
      apply List.isChain_cons_cons.mpr
      refine ⟨?_, ih tailChain tailSame⟩
      rw [step_configuration_on labelMap source target first firstSame, edge, Option.map_some]

theorem nodes_statement (labelMap : Λ → Ω) (source : TM2.Stmt Γ Λ σ)
    (memory : σ) (slots : ∀ slot, List (Γ slot)) :
    PSTRWordBool.AuxWorkspace.nodes (statement labelMap source) memory slots =
      PSTRWordBool.AuxWorkspace.nodes source memory slots := by
  induction source generalizing memory slots with
  | push slot value tail ih =>
    exact congrArg (List.cons (memory, slots))
      (ih memory (Function.update slots slot (value memory :: slots slot)))
  | peek slot value tail ih =>
    exact congrArg (List.cons (memory, slots))
      (ih (value memory (slots slot).head?) slots)
  | pop slot value tail ih =>
    exact congrArg (List.cons (memory, slots))
      (ih (value memory (slots slot).head?) (Function.update slots slot (slots slot).tail))
  | load value tail ih => exact congrArg (List.cons (memory, slots)) (ih (value memory) slots)
  | branch test yes no ihYes ihNo =>
    cases choice : test memory
    · simpa only [statement, PSTRWordBool.AuxWorkspace.nodes, choice, Bool.false_eq_true, ite_false] using
        congrArg (List.cons (memory, slots)) (ihNo memory slots)
    · simpa only [statement, PSTRWordBool.AuxWorkspace.nodes, choice, ite_true] using
        congrArg (List.cons (memory, slots)) (ihYes memory slots)
  | goto target => rfl
  | halt => rfl

theorem actual_path_on (labelMap : Λ → Ω) (source : Λ → TM2.Stmt Γ Λ σ)
    (target : Ω → TM2.Stmt Γ Ω σ) (trace : List (TM2.Cfg Γ Λ σ))
    (before final : TM2.Cfg Γ Λ σ) (first : trace.head? = some before)
    (chain : trace.IsChain (fun before after => TM2.step source before = some after))
    (last : trace.getLast? = some final)
    (same : ∀ current ∈ trace.dropLast, ∀ point, current.l = some point →
      target (labelMap point) = statement labelMap (source point)) :
    (trace.map (configuration labelMap)).head? = some (configuration labelMap before) ∧
    (trace.map (configuration labelMap)).IsChain (fun before after => TM2.step target before = some after) ∧
    (trace.map (configuration labelMap)).getLast? = some (configuration labelMap final) ∧
    (trace.map (configuration labelMap)).length = trace.length ∧
    ∀ current ∈ trace.map (configuration labelMap),
      ∃ old ∈ trace, current = configuration labelMap old ∧ current.var = old.var ∧ current.stk = old.stk := by
  refine ⟨?_, chain_configuration_on labelMap source target trace chain same, ?_,
    List.length_map (configuration labelMap), ?_⟩
  · rw [List.head?_map, first, Option.map_some]
  · rw [List.getLast?_map, last, Option.map_some]
  · intro current present
    obtain ⟨old, member, rfl⟩ := List.mem_map.mp present
    exact ⟨old, member, rfl, rfl, rfl⟩

end Execution

end PaperProofs.Common.Native.PSTRWordVM.LabelMap

module

public import RootB234_PrepEntry_MainExponentChannels_093
public import RootB234_PrepExponent_GlobalFrame046

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.MainExponent
open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM B23_4_RatWordPrep RootB234.PrepExponent RootL01.SymbolicSource
variable {C : Type*}

private theorem readonly_comp {σ Λ D : Type*} (f : D → C) (project : σ → D)
    (body : TM2.Stmt RatInput.Alphabet Λ σ) (good : RawGetter.Readonly project body) :
    RawGetter.Readonly (fun memory => f (project memory)) body := by
  induction body with
  | push _ _ _ ih => exact ih good
  | pop _ _ _ ih | peek _ _ _ ih => exact ⟨fun memory value => congrArg f (good.1 memory value),ih good.2⟩
  | load _ _ ih => exact ⟨fun memory => congrArg f (good.1 memory),ih good.2⟩
  | branch _ _ _ yes no => exact ⟨yes good.1,no good.2⟩
  | goto _ | halt => trivial

private theorem readonly_label {σ Λ Δ : Type*} (rename : Λ → Δ) (project : σ → C)
    (body : TM2.Stmt RatInput.Alphabet Λ σ) (good : RawGetter.Readonly project body) :
    RawGetter.Readonly project (LabelMap.statement rename body) := by
  induction body with
  | push _ _ _ ih => exact ih good
  | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ⟨good.1,ih good.2⟩
  | branch _ _ _ yes no => exact ⟨yes good.1,no good.2⟩
  | goto _ | halt => trivial

private theorem readonly_stack {σ Λ : Type*} (roles : RatInput.Stack ≃ RatInput.Stack) (project : σ → C)
    (body : TM2.Stmt RatInput.Alphabet Λ σ) (good : RawGetter.Readonly project body) :
    RawGetter.Readonly project (StackIso.statement roles body) := by
  induction body with
  | push _ _ _ ih => exact ih good
  | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ⟨good.1,ih good.2⟩
  | branch _ _ _ yes no => exact ⟨yes good.1,no good.2⟩
  | goto _ | halt => trivial

private theorem readonly_iso {σ τ Λ : Type*} (iso : σ ≃ τ) (project : τ → C)
    (body : TM2.Stmt RatInput.Alphabet Λ σ) (good : RawGetter.Readonly (fun memory => project (iso memory)) body) :
    RawGetter.Readonly project (StoreIso.statement iso body) := by
  induction body with
  | push _ _ _ ih => exact ih good
  | pop _ _ _ ih | peek _ _ _ ih =>
    refine ⟨?_,ih good.2⟩
    intro memory value
    simpa only [Equiv.apply_symm_apply] using good.1 (iso.symm memory) value
  | load _ _ ih =>
    refine ⟨?_,ih good.2⟩
    intro memory
    simpa only [Equiv.apply_symm_apply] using good.1 (iso.symm memory)
  | branch _ _ _ yes no => exact ⟨yes good.1,no good.2⟩
  | goto _ | halt => trivial

private theorem readonly_context {σ D Λ : Type*} (project : D → C) (body : TM2.Stmt RatInput.Alphabet Λ σ) :
    RawGetter.Readonly (fun memory : D×σ => project memory.1) (ContextLift.statement body) := by
  induction body with
  | push _ _ _ ih => exact ih
  | pop _ _ _ ih | peek _ _ _ ih => exact ⟨by intros; rfl,ih⟩
  | load _ _ ih => exact ⟨by intros; rfl,ih⟩
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto _ | halt => trivial

private theorem readonly_lift {σ D Λ : Type*} (project : σ → C) (body : TM2.Stmt RatInput.Alphabet Λ σ)
    (good : RawGetter.Readonly project body) :
    RawGetter.Readonly (fun memory : D×σ => project memory.2) (ContextLift.statement body) := by
  induction body with
  | push _ _ _ ih => exact ih good
  | pop _ _ _ ih | peek _ _ _ ih => exact ⟨fun memory value => good.1 memory.2 value,ih good.2⟩
  | load _ _ ih => exact ⟨fun memory => good.1 memory.2,ih good.2⟩
  | branch _ _ _ yes no => exact ⟨yes good.1,no good.2⟩
  | goto _ | halt => trivial

theorem program_readonly (point : Label) : RawGetter.Readonly (callerContext (C:=C)) (program .halt point) := by
  cases point with
  | budget point =>
    apply readonly_label
    exact readonly_comp (fun memory : Global.Store (StageChannels.Store C) => StageChannels.callerContext (QLoop.rootContext memory))
      Budget.callerContext _ (Budget.program_readonly point)
  | exponent point =>
    apply readonly_label
    apply readonly_iso
    exact readonly_comp (fun memory : ExponentContext C => StageChannels.callerContext memory.2)
      QLoop.rootContext _ (Global.Frame.program_readonly point)
  | natural point =>
    apply readonly_label
    apply readonly_iso
    apply readonly_stack
    exact readonly_comp (fun memory : ExponentCore C => StageChannels.callerContext memory.1.1.2.2)
      Prod.fst _ (NatPacket.program_readonly false point)
  | clear point =>
    apply readonly_label
    apply readonly_iso
    apply readonly_stack
    exact readonly_comp (fun memory : ExponentCore C => StageChannels.callerContext memory.1.1.2.2)
      Prod.fst _ (Cells.program_readonly .clear0 point)
  | channels point =>
    apply readonly_label
    apply readonly_iso
    exact readonly_lift StageChannels.callerContext _ (StageChannels.program_readonly point)
  | done => trivial

theorem step_context (before after : State C) (edge : TM2.step (program .halt) before=some after) :
    callerContext after.var=callerContext before.var := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact RawGetter.nodes_readonly callerContext _ (program_readonly point) memory contents _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (trace : List (State C)) (before : State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b)) :
    ∀ current∈trace,callerContext current.var=callerContext before.var := by
  induction trace generalizing before with
  | nil => simp
  | cons start rest ih =>
    have same : start=before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have same:=List.mem_singleton.mp member
      subst current
      rfl
    | cons next rest =>
      obtain ⟨edge,tailChain⟩:=List.isChain_cons_cons.mp chain
      intro current member
      rcases List.mem_cons.mp member with rfl|later
      · rfl
      · exact (ih next rfl tailChain current later).trans (step_context before next edge)


theorem entry_context (context : C) (bits : List Bool) : callerContext (entry context bits).var=context := rfl

end RootB234.PrepEntry.MainExponent

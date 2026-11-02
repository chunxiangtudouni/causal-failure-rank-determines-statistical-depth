module

public import RootB234_PrepEntry_StageChannelsLoop_060

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageChannels

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*}

/--15 contains real temporary getter packets above its saved old tail.
The fixed N8/J9 and unused3/5 are framed even at internal AST nodes. -/
def ActiveWork (slot : RatInput.Stack) : Prop := slot≠3 ∧ slot≠5 ∧ slot≠8 ∧ slot≠9
instance (slot : RatInput.Stack) : Decidable (ActiveWork slot) := by unfold ActiveWork; infer_instance

theorem program_accesses (point : Label) : Frame.AccessesOnly ActiveWork (program (C := C) .halt point) := by
  cases point
  all_goals repeat' first
    | (rename_i point; fin_cases point)
    | (rename_i point; cases point)
  all_goals exact of_decide_eq_true rfl

theorem program_actions (point : Label) : ScannerClock.actions (program (C := C) .halt point)≤16 := by
  cases point
  all_goals repeat' first
    | (rename_i point; fin_cases point)
    | (rename_i point; cases point)
  all_goals exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C := C) .halt point)≤16 := by
  cases point
  all_goals repeat' first
    | (rename_i point; fin_cases point)
    | (rename_i point; cases point)
  all_goals exact of_decide_eq_true rfl

private theorem accesses_writes {Λ σ : Type*} (allowed : RatInput.Stack → Prop)
    (body : TM2.Stmt RatInput.Alphabet Λ σ) (good : Frame.AccessesOnly allowed body) :
    StackIso.WritesOnly allowed body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih => exact ⟨good.1,ih good.2⟩
  | peek _ _ _ ih => exact ih good.2
  | load _ _ ih => exact ih good
  | branch _ _ _ yes no => exact ⟨yes good.1,no good.2⟩
  | goto _ | halt => trivial

theorem program_writes (point : Label) : StackIso.WritesOnly ActiveWork (program (C := C) .halt point) :=
  accesses_writes ActiveWork _ (program_accesses point)

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

private theorem loop_readonly (point : Channels.Label) :
    RawGetter.Readonly (fun memory : Channels.Store (StageFront.Store C) =>
      StageFront.callerContext (OriginalPrelude.callerContext memory.2)) (loopSource .halt point) := by
  cases point with
  | prelude _ | build _ | done => trivial
  | round point =>
    apply readonly_label
    apply readonly_iso
    exact readonly_context (fun memory : Channels.RoundContext (StageFront.Store C) =>
      StageFront.callerContext (OriginalPrelude.callerContext memory.2)) _
  | read point =>
    apply readonly_label
    apply readonly_iso
    exact readonly_comp (fun memory : Channels.RawContext (StageFront.Store C) =>
      StageFront.callerContext (OriginalPrelude.callerContext memory.2)) _ _ (RawGetter.program_readonly point)
  | move point =>
    apply readonly_label
    apply readonly_iso
    apply readonly_stack
    exact readonly_comp (fun memory : Channels.PacketContext (StageFront.Store C) =>
      StageFront.callerContext (OriginalPrelude.callerContext memory.2)) _ _ (RootB234.RatPacketTransport.program_readonly false point)

theorem program_readonly (point : Label) : RawGetter.Readonly (callerContext (C := C)) (program .halt point) := by
  cases point with
  | front point =>
    apply readonly_label
    exact readonly_lift StageFront.callerContext _ (StageFront.program_readonly point)
  | select | done => trivial
  | buildLeft point | buildRight point =>
    apply readonly_label
    apply readonly_iso
    apply readonly_stack
    apply readonly_stack
    exact readonly_comp (fun memory : Channels.PacketContext (StageFront.Store C) =>
      StageFront.callerContext (OriginalPrelude.callerContext memory.2)) _ _ (RootB234.RuntimeCounter.Builder.program_readonly false point)
  | left point | right point =>
    apply readonly_label
    apply readonly_iso
    apply readonly_stack
    exact loop_readonly point

theorem entry_slots (context : C) (background : RatInput.Stack → List Bool) (bits : List Bool) :
    (entry context background bits).stk=(fun slot => if slot=0 then bits else if slot=1 then [] else background slot) :=
  StageFront.entry_slots context background bits

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto _ => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C := C) .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

end RootB234.PrepEntry.StageChannels

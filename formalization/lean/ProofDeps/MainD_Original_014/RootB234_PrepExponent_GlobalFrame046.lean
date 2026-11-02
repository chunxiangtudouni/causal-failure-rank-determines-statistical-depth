module

public import RootB234_PrepExponent_GlobalPublic044
public import RootB234_PrepEntry_StageArithmeticSyntax_086

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.PrepExponent.Global.Frame
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM RootL01.SymbolicSource B23_4_RatWordPrep
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

private theorem packet_readonly (roles : Stack ≃ Stack) (copy : Bool) (point : RatPacketTransport.Label) :
    RawGetter.Readonly (QLoop.rootContext (C:=C))
      (StackIso.statement roles (RatPacketTransport.program copy .halt point)) := by
  apply readonly_stack
  exact readonly_comp (fun memory : PacketUnary.Store (Arithmetic.Aux×C) => memory.1.1.2) _ _
    (RatPacketTransport.program_readonly copy point)

private theorem clear_readonly (point : Cells.Label) :
    RawGetter.Readonly (QLoop.rootContext (C:=C))
      (StackIso.statement QLoop.clearRoles (Cells.Public.clear0 point)) := by
  apply readonly_stack
  exact readonly_comp (fun memory : PacketUnary.Store (Arithmetic.Aux×C) => memory.1.1.2) _ _
    (Cells.program_readonly .clear0 point)

private theorem binary_readonly (multiply : Bool) (point : RatBinary.Label) :
    RawGetter.Readonly (QLoop.rootContext (C:=C))
      (StoreIso.statement (QLoop.arithmeticIso C)
        (if multiply then Arithmetic.mulProgram point else Arithmetic.subProgram point)) :=
  RootB234.PrepEntry.StageArithmetic.binary_readonly multiply point

private theorem q_prepend_readonly (slot : Stack) (bits : List Bool) (body : QLoop.Statement C)
    (good : RawGetter.Readonly (QLoop.rootContext (C:=C)) body) :
    RawGetter.Readonly (QLoop.rootContext (C:=C)) (QLoop.prepend slot bits body) := by
  induction bits generalizing body with
  | nil => exact good
  | cons bit later ih => exact ih _ good

private theorem q_readonly (point : QLoop.Label) :
    RawGetter.Readonly (QLoop.rootContext (C:=C)) (QLoop.program .halt point) := by
  cases point with
  | budget point | copyQ point | discardOld point | parkNew point =>
    apply readonly_label
    exact packet_readonly _ _ point
  | literalQ | literalTwo => exact q_prepend_readonly _ _ _ trivial
  | count point =>
    apply readonly_label
    exact readonly_comp Prod.snd _ _ (NCount.program_readonly point)
  | take => exact ⟨by intros;rfl,⟨trivial,trivial⟩⟩
  | mul point =>
    apply readonly_label
    exact binary_readonly true point
  | clearOld point =>
    apply readonly_label
    exact clear_readonly point
  | done => trivial

private theorem reader_readonly {D : Type*} (point : RatCmp.Reader.Label) :
    RawGetter.Readonly (fun memory : D×RatCmp.Reader.Store => memory.1) (RatCmp.Reader.program .halt point) := by
  fin_cases point
  all_goals dsimp [RatCmp.Reader.program,RatCmp.Reader.keep,RatCmp.Reader.captureSign,
    RatCmp.Reader.captureFlag,RatCmp.Reader.captureNum,RawGetter.Readonly]
  all_goals repeat' constructor
  all_goals intros;rfl

private theorem prepend_readonly (slot : Stack) (bits : List Bool) (body : Statement C)
    (good : RawGetter.Readonly (QLoop.rootContext (C:=C)) body) :
    RawGetter.Readonly (QLoop.rootContext (C:=C)) (prepend slot bits body) := by
  induction bits generalizing body with
  | nil => exact good
  | cons bit later ih => exact ih _ good

/-- Every statement of the existing full E source preserves the opaque
caller context, including all primitive nodes. No source is changed. -/
theorem program_readonly (point : Label) :
    RawGetter.Readonly (QLoop.rootContext (C:=C)) (program .halt point) := by
  cases point with
  | q point =>
    apply readonly_label
    exact q_readonly point
  | packet site point =>
    apply readonly_label
    exact packet_readonly _ _ point
  | nat point =>
    apply readonly_label
    exact readonly_comp (fun memory : PacketUnary.Store (Arithmetic.Aux×C) => memory.1.1.2) _ _
      (NatToRat.program_readonly point)
  | literal site | seedE => exact prepend_readonly _ _ _ trivial
  | mul site point =>
    apply readonly_label
    exact binary_readonly true point
  | subtract point =>
    apply readonly_label
    exact binary_readonly false point
  | reader point =>
    apply readonly_label
    apply readonly_iso
    exact readonly_comp (fun memory : Arithmetic.ReaderContext (PacketUnary.Store C) => memory.2.1.1.1) _ _
      (reader_readonly point)
  | branch => exact ⟨by intros;rfl,⟨trivial,trivial⟩⟩
  | clear site point =>
    apply readonly_label
    exact clear_readonly point
  | increment point =>
    apply readonly_label
    exact readonly_comp (fun memory : PacketUnary.Store (Arithmetic.Aux×C) => memory.1.1.2) _ _
      (NatIncrement.program_readonly point)
  | done => trivial

theorem step_context (before after : State C) (edge : TM2.step (program .halt) before=some after) :
    QLoop.rootContext after.var=QLoop.rootContext before.var := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact RawGetter.nodes_readonly (QLoop.rootContext (C:=C)) _ (program_readonly point) memory contents
        _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (trace : List (State C)) (before : State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b)) :
    ∀ current∈trace,QLoop.rootContext current.var=QLoop.rootContext before.var := by
  induction trace generalizing before with
  | nil => simp
  | cons start rest ih =>
    have same : start=before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have same := List.mem_singleton.mp member
      subst current
      rfl
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      intro current member
      rcases List.mem_cons.mp member with rfl|later
      · rfl
      · exact (ih next rfl tailChain current later).trans (step_context before next edge)

/-- Attach frames to the parent's already selected actual witness. -/
theorem segment_frames {before final : State C} (part : Segment .halt before final) :
    (∀ current∈part.trace,QLoop.rootContext current.var=QLoop.rootContext before.var) ∧
    ∀ current∈part.trace,∀ point,current.l=some point →
      ∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
        QLoop.rootContext node.1=QLoop.rootContext before.var := by
  have frames := trace_context part.trace before part.first part.chain
  refine ⟨frames,?_⟩
  intro current member point _active node present
  exact (RawGetter.nodes_readonly (QLoop.rootContext (C:=C)) _ (program_readonly point)
    current.var current.stk node present).trans (frames current member)

end RootB234.PrepExponent.Global.Frame

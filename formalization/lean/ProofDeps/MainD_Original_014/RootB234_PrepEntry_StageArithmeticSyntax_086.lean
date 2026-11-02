module

public import RootB234_PrepEntry_StageArithmeticTime_085

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageArithmetic
open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM RootB234.PrepExponent RootL01.SymbolicSource
open B23_4_RatWordPrep
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

private theorem output_readonly (point : RatOutput.Label) :
    RawGetter.Readonly (fun memory : C×RatOutput.Store => memory.1) (RatOutput.program .halt point) := by
  fin_cases point
  all_goals dsimp [RatOutput.program,RatOutput.capture,RatOutput.keep,RatOutput.jump,RawGetter.Readonly]
  all_goals repeat' constructor
  all_goals intros;rfl

private theorem natural_readonly (point : PSTRSymbolicNaturalExport.Label) :
    RawGetter.Readonly (fun memory : PSTRSymbolicNaturalExport.Memory C => memory.1)
      (PSTRSymbolicNaturalExport.program point) := by
  fin_cases point
  all_goals dsimp [PSTRSymbolicNaturalExport.program,PSTRSymbolicNaturalExport.captureBit,
    PSTRSymbolicNaturalExport.captureFlag,PSTRSymbolicNaturalExport.captureMode,RawGetter.Readonly]
  all_goals repeat' constructor
  all_goals intros;rfl

private theorem input_readonly (point : RatInput.Label) :
    RawGetter.Readonly (fun memory : RatInput.Memory C => memory.1) (RatInput.program .halt point) := by
  fin_cases point
  all_goals first
  | (change RawGetter.Readonly _ (LabelMap.statement _ (StackIso.statement _ (PSTRSymbolicNaturalExport.program (C:=C) 2)))
     apply readonly_label
     apply readonly_stack
     exact natural_readonly 2)
  | (dsimp [RatInput.program,RatInput.fieldBody,PSTRSymbolicNaturalExport.captureBit,
       PSTRSymbolicNaturalExport.captureFlag,PSTRSymbolicNaturalExport.captureMode,RawGetter.Readonly]
     repeat' constructor
     all_goals intros;rfl)

private theorem word_readonly (point : WordNatIO.Label) :
    RawGetter.Readonly (fun memory : C×WordNatIO.Store => memory.1) (WordNatIO.callerProgram .halt point) := by
  unfold WordNatIO.callerProgram
  split_ifs
  · trivial
  · exact readonly_context id _

private theorem encoder_readonly (point : RatInput.Encoder.Label) :
    RawGetter.Readonly (fun memory : RatInput.Encoder.Store C => memory.1.1)
      (RatInput.Encoder.program .halt point) := by
  cases point with
  | collect point =>
    rw [RatInput.Encoder.program]
    apply readonly_label
    apply readonly_iso
    exact readonly_comp (fun context : C×WordNatIO.Store => context.1)
      (fun memory : RatInput.Memory (C×WordNatIO.Store) => memory.1) _ (input_readonly point)
  | reverseNum | reverseDen =>
    rw [RatInput.Encoder.program]
    apply readonly_label
    apply readonly_stack
    exact readonly_comp Prod.fst _ _ (output_readonly 7)
  | den point | num point =>
    rw [RatInput.Encoder.program]
    apply readonly_label
    apply readonly_stack
    exact readonly_comp Prod.fst _ _ (word_readonly point)
  | finish =>
    change RawGetter.Readonly _ RatInput.Encoder.finishBody
    dsimp [RatInput.Encoder.finishBody,RatInput.Encoder.putPrefix,RatInput.Encoder.prefixBits,RawGetter.Readonly]
    trivial
  | done => trivial

private theorem collector_readonly (point : RatPair.Collector.Label) :
    RawGetter.Readonly (fun memory : RatPair.Collector.Store C => memory.1.1.1)
      (RatPair.Collector.program .halt point) := by
  fin_cases point
  all_goals first
  | (change RawGetter.Readonly _ (RatPair.Collector.fieldBody _ _)
     unfold RatPair.Collector.fieldBody
     apply readonly_label
     apply readonly_iso
     apply readonly_stack
     exact readonly_comp (fun context : (C×Bool×Bool)×WordNatIO.Store => context.1.1) _ _ (input_readonly _))
  | (change RawGetter.Readonly _ RatPair.Collector.restoreBody
     unfold RatPair.Collector.restoreBody RatInput.restoreBody
     apply readonly_label
     apply readonly_iso
     apply readonly_label
     apply readonly_stack
     exact readonly_comp (fun context : (C×Bool×Bool)×WordNatIO.Store => context.1.1) _ _ (natural_readonly 2))
  | (dsimp [RatPair.Collector.program,RatPair.Collector.headerBody,RatPair.Collector.captureBit,
       RatPair.Collector.captureMode,RatPair.Collector.saveSign,RawGetter.Readonly]
     repeat' constructor
     all_goals intros;rfl)

private theorem dropPrefix_readonly (bits : List Bool) (body : RatPair.Serializer.Statement C)
    (good : RawGetter.Readonly (fun memory : RatPair.Serializer.Store C => memory.1.1.1) body) :
    RawGetter.Readonly (fun memory : RatPair.Serializer.Store C => memory.1.1.1)
      (RatPair.Serializer.dropPrefix bits body) := by
  induction bits with
  | nil => exact good
  | cons bit tail ih => exact ⟨by intros;rfl,ih⟩

private theorem putBits_readonly (bits : List Bool) (body : RatPair.Serializer.Statement C)
    (good : RawGetter.Readonly (fun memory : RatPair.Serializer.Store C => memory.1.1.1) body) :
    RawGetter.Readonly (fun memory : RatPair.Serializer.Store C => memory.1.1.1)
      (RatPair.Serializer.putBits bits body) := by
  induction bits generalizing body with
  | nil => exact good
  | cons bit tail ih => exact ih _ good

private theorem serializer_readonly (point : RatPair.Serializer.Label) :
    RawGetter.Readonly (fun memory : RatPair.Serializer.Store C => memory.1.1.1)
      (RatPair.Serializer.program2 .halt point) := by
  cases point with
  | boot mode =>
    cases mode <;> dsimp [RatPair.Serializer.program2,RatPair.Serializer.program,RawGetter.Readonly]
    all_goals exact ⟨by intros;rfl,trivial⟩
  | phase mode point =>
    change RawGetter.Readonly _ (LabelMap.statement _ (StackIso.statement _ (RatInput.Encoder.program .halt point)))
    apply readonly_label
    apply readonly_stack
    exact readonly_comp (fun memory : C×Bool×Bool => memory.1) _ _ (encoder_readonly point)
  | trim mode =>
    cases mode
    · exact dropPrefix_readonly _ _ trivial
    · apply dropPrefix_readonly
      exact putBits_readonly _ _ trivial
  | done => trivial

private theorem pair_readonly (point : RatPair.Label) :
    RawGetter.Readonly (fun memory : RatPair.Store C => memory.1.1.1) (RatPair.program .halt point) := by
  cases point with
  | collect point =>
    apply readonly_label
    exact collector_readonly point
  | serialize point =>
    change RawGetter.Readonly _ (if point=.done then .halt else LabelMap.statement _ (RatPair.Serializer.program2 .halt point))
    split_ifs
    · trivial
    · apply readonly_label
      exact serializer_readonly point

private theorem isolated_readonly {states : Nat} (machine : Machine states) (point : IsolatedRat.Label) :
    RawGetter.Readonly (fun memory : IsolatedRat.Store C states => memory.1) (IsolatedRat.program machine .halt point) := by
  fin_cases point
  · apply readonly_label
    apply readonly_stack
    exact readonly_context id _
  · exact ⟨by intros;rfl,trivial⟩
  · trivial

private theorem linked_readonly {states : Nat} (machine : Machine states) (point : RatOutput.Link.Label) :
    RawGetter.Readonly (fun memory : RatOutput.Link.Store C states => memory.1.1)
      (RatOutput.Link.program machine .halt point) := by
  unfold RatOutput.Link.program
  split_ifs
  · apply readonly_label
    apply readonly_iso
    exact readonly_comp (fun context : C×RatOutput.Store => context.1)
      (fun memory : IsolatedRat.Store (C×RatOutput.Store) states => memory.1) _ (isolated_readonly machine _)
  · trivial
  · apply readonly_label
    exact readonly_comp Prod.fst _ _ (output_readonly _)

private theorem drop_readonly (point : RatDrop.Label) :
    RawGetter.Readonly (fun memory : RatDrop.Store C => memory.1) (RatDrop.program .halt point) := by
  fin_cases point
  all_goals first
  | (change RawGetter.Readonly _ (LabelMap.statement _ (StackIso.statement _ (RatOutput.program .halt 7)))
     apply readonly_label
     apply readonly_stack
     exact output_readonly 7)
  | (dsimp [RatDrop.program,RatDrop.headerBody,RatDrop.fieldBody,RatDrop.put,RatDrop.capture,RawGetter.Readonly]
     repeat' constructor
     all_goals intros;rfl)

theorem raw_readonly {states : Nat} (machine : Machine states) (point : RatBinary.Label) :
    RawGetter.Readonly (fun memory : RatBinary.Store C states => memory.1.1.1.1.1)
      (RatBinary.program machine .halt point) := by
  cases point with
  | pair point =>
    rw [RatBinary.program]
    apply readonly_label
    apply readonly_iso
    exact readonly_comp (fun context : (C×BoolOnStacks.Store states)×RatOutput.Store => context.1.1) _ _ (pair_readonly point)
  | arith point =>
    rw [RatBinary.program]
    apply readonly_label
    exact readonly_comp (fun context : RatPair.Store C => context.1.1.1) _ _ (linked_readonly machine point)
  | drop point =>
    rw [RatBinary.program]
    apply readonly_label
    exact readonly_comp (fun context : RatPair.Store C×BoolOnStacks.Store states => context.1.1.1.1) _ _ (drop_readonly point)
  | done => trivial

theorem binary_readonly (multiply : Bool) (point : RatBinary.Label) :
    RawGetter.Readonly (QLoop.rootContext (C:=C)) (binary multiply point) := by
  unfold binary
  apply readonly_iso
  cases multiply with
  | true =>
    unfold Arithmetic.mulProgram Arithmetic.binaryProgram
    apply readonly_iso
    apply readonly_stack
    exact readonly_comp (fun context : Arithmetic.MulContext (PacketUnary.Store C) => context.2.1.1.1) _ _
      (raw_readonly RatMulDiv.mulSource point)
  | false =>
    unfold Arithmetic.subProgram Arithmetic.binaryProgram
    apply readonly_iso
    apply readonly_stack
    exact readonly_comp (fun context : Arithmetic.SubContext (PacketUnary.Store C) => context.2.1.1.1) _ _
      (raw_readonly RatAddSub.subSource point)

theorem program_readonly (multiply : Bool) (point : Label) :
    RawGetter.Readonly (QLoop.rootContext (C:=C)) (program multiply .halt point) := by
  cases point with
  | stash point | restore point =>
    apply readonly_label
    exact readonly_comp (fun memory : Core C => memory.1.1.2) _ _ (StageStash.source_readonly point)
  | binary point =>
    apply readonly_label
    exact binary_readonly multiply point
  | done => trivial

theorem program_actions (multiply : Bool) (point : Label) : ScannerClock.actions (program multiply (C:=C) .halt point)≤32 := by
  cases point with
  | stash point | restore point =>
    rw [program,LabelMap.statement_actions]
    exact (StageStash.source_actions point).trans (by decide)
  | binary point =>
    rw [program,LabelMap.statement_actions,binary,StoreIso.statement_actions]
    cases multiply
    all_goals simp only [Bool.false_eq_true,ite_false,ite_true]
    all_goals change ScannerClock.actions (StoreIso.statement _ (StackIso.statement _ (RatBinary.program _ .halt point)))≤32
    all_goals rw [StoreIso.statement_actions,StackIso.statement_actions]
    all_goals exact RatBinary.program_actions _ point
  | done => exact Nat.zero_le _

theorem program_pushes (multiply : Bool) (point : Label) : AuxWorkspace.pushes (program multiply (C:=C) .halt point)≤32 := by
  cases point with
  | stash point | restore point =>
    rw [program,LabelMap.statement_pushes]
    exact (StageStash.source_pushes point).trans (by decide)
  | binary point =>
    rw [program,LabelMap.statement_pushes,binary,StoreIso.statement_pushes]
    cases multiply
    all_goals simp only [Bool.false_eq_true,ite_false,ite_true]
    all_goals change AuxWorkspace.pushes (StoreIso.statement _ (StackIso.statement _ (RatBinary.program _ .halt point)))≤32
    all_goals rw [StoreIso.statement_pushes,StackIso.statement_pushes]
    all_goals exact RatBinary.program_pushes _ point
  | done => exact Nat.zero_le _

end RootB234.PrepEntry.StageArithmetic


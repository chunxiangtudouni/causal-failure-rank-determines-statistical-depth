module

public import Paid.PDROC_BitVM_Kernel_NatInstruction_013
public import Paid.PDROC_BitVM_Codec_NatWriter_Global_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.NatInstruction

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.RationalControllerComputation

abbrev WriterLabel := PDROC.BitVM.Codec.NatWriter.Label
abbrev WriterStore := PDROC.BitVM.Codec.NatWriter.Store
abbrev WriterState := PDROC.BitVM.Codec.NatWriter.Global.State
abbrev FullLabel := NatOp.Label ⊕ (WriterLabel ⊕ Unit)
abbrev FullStore (operation : PaperProofs.Paid.Computation.NatOp) := NatOp.Store operation × WriterStore
abbrev FullState (operation : PaperProofs.Paid.Computation.NatOp) := TM2.Cfg Alphabet FullLabel (FullStore operation)

theorem target_not_right (target : Register) : registerSlot target ≠ 0 := by cases target <;> decide
theorem target_not_left (target : Register) : registerSlot target ≠ 24 := by cases target <;> decide

def writerMachine (target : Register) := PDROC.BitVM.Codec.NatWriter.Global.machine
  (registerSlot target) (target_not_right target) (target_not_left target)

def computeLabels : NatOp.Label → FullLabel := Sum.inl
def writerLabels (label : WriterLabel) : FullLabel := .inr (.inl label)
def writerStart : FullLabel := writerLabels 0
def doneLabel : FullLabel := .inr (.inr ())

/-- The operation/register choices are part of the original fixed source
code. Actual register reads, native execution and canonical Cell writeback
all run in this one finite-control machine; no Nat/Rat value is in control. -/
def program (operation : PaperProofs.Paid.Computation.NatOp) (target left right : Register) :
    FullLabel → TM2.Stmt Alphabet FullLabel (FullStore operation)
  | .inl label => Inline.statement computeLabels writerStart (NatOp.program operation left right label)
  | .inr (.inl label) => StoreIso.statement (Equiv.prodComm _ _)
      (Inline.statement writerLabels doneLabel (writerMachine target label))
  | .inr (.inr _) => .halt

theorem compute_agrees (operation : PaperProofs.Paid.Computation.NatOp) (target left right : Register) :
    ∀ label,program operation target left right (computeLabels label)=
      Inline.statement computeLabels writerStart (NatOp.program operation left right label) := by intro label;rfl

def writerCfg (operation : PaperProofs.Paid.Computation.NatOp) (saved : NatOp.Store operation)
    (source : WriterState) : FullState operation :=
  StoreIso.cfg (Equiv.prodComm _ _) (Inline.cfg writerLabels doneLabel saved source)

theorem writer_edge (operation : PaperProofs.Paid.Computation.NatOp) (target left right : Register)
    (before final : WriterState) (saved : NatOp.Store operation)
    (edge : TM2.step (writerMachine target) before=some final) :
    TM2.step (program operation target left right) (writerCfg operation saved before)=
      some (writerCfg operation saved final) := by
  rcases before with ⟨label,store,contents⟩
  cases label with
  | none => cases edge
  | some label =>
    have actual : TM2.stepAux (writerMachine target label) store contents=final := Option.some.inj edge
    change some (TM2.stepAux (StoreIso.statement (Equiv.prodComm _ _)
      (Inline.statement writerLabels doneLabel (writerMachine target label))) (saved,store) contents)=_
    have reordered : TM2.stepAux (StoreIso.statement (Equiv.prodComm _ _)
        (Inline.statement writerLabels doneLabel (writerMachine target label))) (saved,store) contents=
        StoreIso.cfg (Equiv.prodComm _ _)
          (TM2.stepAux (Inline.statement writerLabels doneLabel (writerMachine target label)) (store,saved) contents) :=
      StoreIso.stepAux_map (Equiv.prodComm _ _) (Inline.statement writerLabels doneLabel (writerMachine target label))
        (store,saved) contents
    rw [reordered,Inline.stepAux_map,actual]
    rfl

def before (operation : PaperProofs.Paid.Computation.NatOp) (contents : Stack → List Bool)
    (store : Option Bool) : FullState operation :=
  Inline.cfg computeLabels writerStart (none,()) (NatOp.before operation contents store)

def budget (operation : PaperProofs.Paid.Computation.NatOp) (left right : Register)
    (contents : Stack → List Bool) (a b : ℕ) : ℕ :=
  computeBudget a b+32*(3*(dataSize contents+computePushCap operation left right*computeBudget a b)+1)+1

/-- Complete actual refinement of an ORIGINAL successful natural RAM
instruction, including destination aliases, real old-target/padding cleanup,
exact canonical Cell, empty native work stacks, true HALT and actual time.
The result parameter describes the source success; it is never machine input. -/
theorem instruction_runs (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (operation : PaperProofs.Paid.Computation.NatOp) (target left right : Register) (a b result : ℕ)
    (contents : Stack → List Bool) (store : Option Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (leftNat : logical.register left=.natural a) (rightNat : logical.register right=.natural b)
    (success : operation.eval a b=some result) (emptyRight : contents 0=[]) (emptyLeft : contents 24=[]) :
    ∃ (run : List (FullState operation)) (lastState : FullState operation),
      Instruction.execute input (.natOp operation target left right) logical=some (after logical target result) ∧ 
      run.head?=some (before operation contents store) ∧ 
      run.IsChain (fun x y=>TM2.step (program operation target left right) x=some y) ∧ 
      run.getLast?=some lastState ∧ TM2.step (program operation target left right) lastState=none ∧ 
      RegistersRepresent (after logical target result) lastState ∧ lastState.stk 0=[] ∧ lastState.stk 24=[] ∧ 
      run.length ≤ budget operation left right contents a b ∧ 
      ∀ other,other ≠ 0 → other ≠ 24 → other ≠ registerSlot target → lastState.stk other=contents other := by
  obtain ⟨compute,computed,computeHead,computeChain,computeLast,computeHalt,computedRegs,
    nativeResult,computeTime,occupied,computeFrame⟩ :=
    compute_resources operation logical left right a b contents store represented leftNat rightNat emptyRight emptyLeft
  have member : computed ∈ compute := List.mem_of_mem_getLast? (by rw [computeLast];rfl)
  let ceiling := dataSize contents+computePushCap operation left right*computeBudget a b
  have bound0 : (computed.stk 0).length ≤ ceiling := occupied computed member 0
  have bound24 : (computed.stk 24).length ≤ ceiling := occupied computed member 24
  have boundTarget : (computed.stk (registerSlot target)).length ≤ ceiling := occupied computed member (registerSlot target)
  obtain ⟨first,ready,firstHead,firstChain,firstLast,readyLabel,readyStacks,readyStore,firstLength⟩ :=
    Inline.actual_return_trace computeLabels writerStart (NatOp.program operation left right)
      (program operation target left right) (compute_agrees operation target left right) compute
      (NatOp.before operation contents store) computed (none,()) computeHead computeChain computeLast computeHalt
  have readyWriter : ready.var.2=(none,()) := by rw [readyStore]
  have representation : ListBlank.mk (ready.stk 0)=ListBlank.mk (encodeNat result) := by
    rw [readyStacks]
    rw [NatOp.value_of_success operation a b result success] at nativeResult
    exact nativeResult
  obtain ⟨writer,written,writerHead,writerChain,writerLast,writerHalt,work0,work24,exactCell,writerTime,writerFrame⟩ :=
    PDROC.BitVM.Codec.NatWriter.Global.runs (registerSlot target) (target_not_right target) (target_not_left target)
      result ready.stk none representation
  have writeTime : writer.length ≤ 32*(3*ceiling+1) := by
    rw [readyStacks] at writerTime
    omega
  have boundary : writerCfg operation ready.var.1
      (PDROC.BitVM.Codec.NatWriter.Global.before ready.stk none)=ready := by
    rcases ready with ⟨label,⟨computeVar,writerVar⟩,physical⟩
    change label=some writerStart at readyLabel
    change writerVar=(none,()) at readyWriter
    subst label
    subst writerVar
    rfl
  let second := writer.map (writerCfg operation ready.var.1)
  let returned := writerCfg operation ready.var.1 written
  have secondHead : second.head?=some ready := by
    simp only [second,List.head?_map,writerHead,Option.map_some,boundary]
  have secondChain : second.IsChain (fun x y=>TM2.step (program operation target left right) x=some y) :=
    List.isChain_map_of_isChain _ (fun x y edge=>writer_edge operation target left right x y ready.var.1 edge) writerChain
  have secondLast : second.getLast?=some returned := by
    simp only [second,List.getLast?_map,writerLast,Option.map_some]
    rfl
  have writtenLabel : written.l=none := by
    rcases written with ⟨label,finiteStore,physical⟩
    cases label with
    | none => rfl
    | some label => cases writerHalt
  have returnedLabel : returned.l=some doneLabel := by
    change some (written.l.map writerLabels |>.getD doneLabel)=some doneLabel
    rw [writtenLabel]
    rfl
  have secondLength : second.length=writer.length := List.length_map _
  have oldFrame : ∀ other,other ≠ 0 → other ≠ 24 → computed.stk other=contents other := by
    intro other not0 not24
    by_cases isLeft : other=registerSlot left
    · subst other
      exact (computedRegs left).trans (represented left).symm
    by_cases isRight : other=registerSlot right
    · subst other
      exact (computedRegs right).trans (represented right).symm
    apply computeFrame other
    · intro index
      fin_cases index
      · exact isLeft
      · exact not0
      · exact not24
    · intro index
      fin_cases index
      · exact isRight
      · exact not0
      · exact not24
    · intro index
      fin_cases index
      · exact not0
      · exact not24
  have regAfter : RegistersRepresent (after logical target result) returned := by
    apply write_represents logical target result ready returned
    · intro reg
      change ready.stk (registerSlot reg)=_
      rw [readyStacks]
      exact computedRegs reg
    · exact exactCell
    · intro reg different
      exact writerFrame (registerSlot reg) (target_not_right reg) (target_not_left reg)
        (fun equal=>different (registerSlot_injective equal))
  have completeFrame : ∀ other,other ≠ 0 → other ≠ 24 → other ≠ registerSlot target → returned.stk other=contents other := by
    intro other not0 not24 notTarget
    change written.stk other=_
    rw [writerFrame other not0 not24 notTarget,readyStacks]
    exact oldFrame other not0 not24
  let final : FullState operation := ⟨none,returned.var,returned.stk⟩
  have finalEdge : TM2.step (program operation target left right) returned=some final := by
    rcases returned with ⟨label,finiteStore,physical⟩
    change label=some doneLabel at returnedLabel
    subst label
    rfl
  have finalPair : [returned,final].IsChain (fun x y=>TM2.step (program operation target left right) x=some y) :=
    List.isChain_cons_cons.mpr ⟨finalEdge,List.isChain_singleton _⟩
  have joined := PDROC.BitVM.Log.TwoStack.join_chain first second ready firstChain secondChain firstLast secondHead
  generalize _secondEq : second=secondRun at secondHead secondLast secondChain secondLength joined
  cases secondRun with
  | nil => simp only [List.head?_nil,reduceCtorEq] at secondHead
  | cons start rest =>
    have same : start=ready := Option.some.inj secondHead
    subst start
    cases rest with
    | nil =>
      have same : ready=returned := Option.some.inj secondLast
      have wrong := congrArg TM2.Cfg.l same
      rw [readyLabel,returnedLabel] at wrong
      change some (.inr (.inl 0) : FullLabel)=some (.inr (.inr ())) at wrong
      cases wrong
    | cons next later =>
      have last : (first++next::later).getLast?=some returned := by
        rw [List.getLast?_append_cons]
        simpa only [List.getLast?_cons_cons] using secondLast
      have actual := PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain
        (first++next::later) returned [final] last joined finalPair
      refine ⟨(first++next::later)++[final],final,execute input logical operation target left right a b result
        leftNat rightNat success,?_,actual,List.getLast?_append_cons (first++next::later) final [],rfl,
        regAfter,work0,work24,?_,completeFrame⟩
      · simp only [List.head?_append,firstHead,Option.some_or]
        rfl
      · simp only [List.length_append,List.length_cons,List.length_nil] at secondLength ⊢
        dsimp only [budget,ceiling] at writeTime ⊢
        omega

theorem supports (operation : PaperProofs.Paid.Computation.NatOp) (target left right : Register) :
    TM2.Supports (program operation target left right) (Finset.univ : Finset FullLabel) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    rcases label with compute | (writer | marker)
    · exact Inline.supports_statement computeLabels writerStart Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _)
        (NatOp.program operation left right compute) ((NatOp.program_supports operation left right).2 compute (Finset.mem_univ _))
    · exact StoreIso.supports_statement (Equiv.prodComm _ _) Finset.univ _
        (Inline.supports_statement writerLabels doneLabel Finset.univ Finset.univ
          (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _) (writerMachine target writer)
          ((PDROC.BitVM.Codec.NatWriter.Global.supports (registerSlot target)
            (target_not_right target) (target_not_left target)).2 writer (Finset.mem_univ _)))
    · trivial

end PDROC.BitVM.Kernel.NatInstruction

module

public import Paid.PDROC_BitVM_Kernel_NatMarshal_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Kernel.NatPair

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

abbrev Label := Fin 11
abbrev Store := NatMarshal.Store × Unit
abbrev State := TM2.Cfg RegisterGlobal.Alphabet Label Store

def firstLabel (label : NatMarshal.Label) : Label := ⟨label.val,by omega⟩
def secondLabel (label : NatMarshal.Label) : Label := ⟨label.val+5,by omega⟩

/-- Compile-time choices of the two source registers. No distinctness
condition is needed: both actual calls restore their source Cell bytes. -/
def program (left right : Register) (label : Label) :
    TM2.Stmt RegisterGlobal.Alphabet Label Store :=
  if h : label.val<5 then
    Inline.statement firstLabel 5 (NatMarshalGlobal.machine right ⟨label.val,h⟩)
  else if h : label.val<10 then
    Inline.statement secondLabel 10 (NatMarshalGlobal.machine left ⟨label.val-5,by omega⟩)
  else .halt

theorem first_agrees (left right : Register) : ∀ label,
    program left right (firstLabel label)=
      Inline.statement firstLabel 5 (NatMarshalGlobal.machine right label) := by
  intro label
  fin_cases label <;> rfl

theorem second_agrees (left right : Register) : ∀ label,
    program left right (secondLabel label)=
      Inline.statement secondLabel 10 (NatMarshalGlobal.machine left label) := by
  intro label
  fin_cases label <;> rfl

def before (contents : RegisterGlobal.Stack → List Bool) (store : Option Bool) : State :=
  ⟨some 0,((store,()),()),contents⟩

def lower (contents : RegisterGlobal.Stack → List Bool) (store : Option Bool) : NatMarshalGlobal.State :=
  ⟨some 0,(store,()),contents⟩

/-- ONE actual finite-control path assembles the exact binary input for
the frozen native arithmetic machines from two original RAM registers.
All registers, heap, readonly input and output storage remain framed.
Empty work stacks are caller invariants that must be established by code. -/
theorem pair_runs (logical : PaperProofs.Paid.Computation.State) (left right : Register)
    (a b : ℕ) (contents : RegisterGlobal.Stack → List Bool) (store : Option Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (leftNat : logical.register left=.natural a) (rightNat : logical.register right=.natural b)
    (emptyRight : contents 0=[]) (emptyScratch : contents 24=[]) :
    ∃ (run : List State) (lastState : State),
      run.head?=some (before contents store) ∧
      run.IsChain (fun x y=>TM2.step (program left right) x=some y) ∧
      run.getLast?=some lastState ∧ TM2.step (program left right) lastState=none ∧
      lastState.l=none ∧ lastState.var=((none,()),()) ∧ RegistersRepresent logical lastState ∧
      lastState.stk 0=encodeNatBits a++encodeNatBits b ∧ lastState.stk 24=[] ∧
      run.length=2*(encodeNatBits a).length+2*(encodeNatBits b).length+10 ∧
      ∀ other,(∀ index,other≠NatMarshalGlobal.embedding left index)→
        (∀ index,other≠NatMarshalGlobal.embedding right index)→lastState.stk other=contents other := by
  obtain ⟨rightRun,rightLast,rightHead,rightChain,rightEnd,rightHalt,_rightLabel,
    _rightStore,rightReg,rightWord,rightScratch,rightLength,rightFrame⟩ :=
    NatMarshalGlobal.register_runs logical right b [] (lower contents store) store rfl rfl
      represented rightNat emptyRight emptyScratch
  obtain ⟨first,middle,firstHead,firstChain,firstLast,middleLabel,middleStack,middleStore,firstLength⟩ :=
    Inline.actual_return_trace firstLabel 5 (NatMarshalGlobal.machine right) (program left right)
      (first_agrees left right) rightRun (lower contents store) rightLast ()
      rightHead rightChain rightEnd rightHalt
  have middleReg : RegistersRepresent logical (lower middle.stk none) := by
    intro reg
    change middle.stk (registerSlot reg)=_
    rw [middleStack]
    exact rightReg reg
  have middleWord : middle.stk 0=encodeNatBits b := by
    rw [middleStack,rightWord,List.append_nil]
  have middleScratch : middle.stk 24=[] := by rw [middleStack,rightScratch]
  obtain ⟨leftRun,leftLast,leftHead,leftChain,leftEnd,leftHalt,_leftLabel,
    leftStore,leftReg,leftWord,leftScratch,leftLength,leftFrame⟩ :=
    NatMarshalGlobal.register_runs logical left a (encodeNatBits b) (lower middle.stk none) none rfl rfl
      middleReg leftNat middleWord middleScratch
  obtain ⟨second,returned,secondHead,secondChain,secondLast,returnedLabel,returnedStack,returnedStore,secondLength⟩ :=
    Inline.actual_return_trace secondLabel 10 (NatMarshalGlobal.machine left) (program left right)
      (second_agrees left right) leftRun (lower middle.stk none) leftLast ()
      leftHead leftChain leftEnd leftHalt
  have middleSaved : middle.var=((none,()),()) := by
    rw [middleStore,_rightStore]
  have secondStart : Inline.cfg secondLabel 10 () (lower middle.stk none)=middle := by
    rcases middle with ⟨label,saved,localContents⟩
    change label=some 5 at middleLabel
    change saved=((none,()),()) at middleSaved
    subst label
    subst saved
    rfl
  rw [secondStart] at secondHead
  let final : State := ⟨none,returned.var,returned.stk⟩
  have finishStep : TM2.step (program left right) returned=some final := by
    rcases returned with ⟨label,saved,localContents⟩
    change label=some 10 at returnedLabel
    subst label
    rfl
  have finishChain : [returned,final].IsChain (fun x y=>TM2.step (program left right) x=some y) :=
    List.isChain_cons_cons.mpr ⟨finishStep,List.isChain_singleton _⟩
  have combined := PDROC.BitVM.Log.TwoStack.join_chain first second middle
    firstChain secondChain firstLast secondHead
  cases second with
  | nil => simp only [List.head?_nil,reduceCtorEq] at secondHead
  | cons start rest =>
    have startEq : start=middle := Option.some.inj secondHead
    subst start
    cases rest with
    | nil =>
      simp only [List.length_cons,List.length_nil] at secondLength
      omega
    | cons next later =>
      have prefixLast : (first++next::later).getLast?=some returned := by
        rw [List.getLast?_append_cons]
        simpa only [List.getLast?_cons_cons] using secondLast
      have wholeChain := PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain
        (first++next::later) returned [final] prefixLast combined finishChain
      refine ⟨(first++next::later)++[final],final,?_,wholeChain,
        List.getLast?_append_cons (first++next::later) final [],rfl,rfl,?_,?_,?_,?_,?_,?_⟩
      · simp only [List.head?_append,firstHead,Option.some_or]
        rfl
      · change returned.var=((none,()),())
        rw [returnedStore,leftStore]
      · intro reg
        change returned.stk (registerSlot reg)=_
        rw [returnedStack]
        exact leftReg reg
      · change returned.stk 0=_
        rw [returnedStack,leftWord]
      · change returned.stk 24=[]
        rw [returnedStack,leftScratch]
      · simp only [List.length_append,List.length_cons,List.length_nil] at secondLength ⊢
        omega
      · intro other outsideLeft outsideRight
        change returned.stk other=contents other
        rw [returnedStack]
        exact (leftFrame other outsideLeft).trans
          ((congrFun middleStack other).trans (rightFrame other outsideRight))

theorem supports (left right : Register) :
    TM2.Supports (program left right) (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label
    all_goals first
    | exact Inline.supports_statement firstLabel 5 Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _)
        (NatMarshalGlobal.machine right _) ((NatMarshalGlobal.supports right).2 _ (Finset.mem_univ _))
    | exact Inline.supports_statement secondLabel 10 Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _)
        (NatMarshalGlobal.machine left _) ((NatMarshalGlobal.supports left).2 _ (Finset.mem_univ _))
    | trivial

end PDROC.BitVM.Kernel.NatPair

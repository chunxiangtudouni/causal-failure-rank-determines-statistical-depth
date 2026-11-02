module

public import Paid.PDROC_BitVM_Kernel_CellRead_027

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.CellPair

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

abbrev Label := Fin 8
abbrev Store := CellRead.Store × Unit
abbrev State := TM2.Cfg Alphabet Label Store

def firstLabel (label : CellRead.Label) : Label := ⟨label.val+1,by omega⟩
def secondLabel (label : CellRead.Label) : Label := ⟨label.val+4,by omega⟩

/-- Fixed two-Cell RAW list producer. Footer and count-two header are
literal source-code writes; the two complete Cell words are really read
from their original registers, and both registers are restored. -/
def program (left right : Register) (label : Label) : TM2.Stmt Alphabet Label Store :=
  if label=0 then .push 0 (fun _=>true) (.load (fun _=>(none,())) (.goto (fun _=>1)))
  else if h : label.val<4 then Inline.statement firstLabel 4 (CellRead.program right ⟨label.val-1,by omega⟩)
  else if h : label.val<7 then Inline.statement secondLabel 7 (CellRead.program left ⟨label.val-4,by omega⟩)
  else .push 0 (fun _=>true) (.push 0 (fun _=>false) (.push 0 (fun _=>false)
    (.push 0 (fun _=>true) (.push 0 (fun _=>true) .halt))))

def before (contents : Stack → List Bool) (store : Option Bool) : State := ⟨some 0,(store,()),contents⟩

theorem register_not_right (reg : Register) : registerSlot reg ≠ 0 := by cases reg <;> decide

theorem first_agrees (left right : Register) : ∀ label,
    program left right (firstLabel label)=Inline.statement firstLabel 4 (CellRead.program right label) := by
  intro label
  fin_cases label <;> rfl

theorem second_agrees (left right : Register) : ∀ label,
    program left right (secondLabel label)=Inline.statement secondLabel 7 (CellRead.program left label) := by
  intro label
  fin_cases label <;> rfl

theorem read_frame (logical : PaperProofs.Paid.Computation.State) (source : Register)
    (contents : Stack → List Bool) (final : CellRead.State)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (regs : RegistersRepresent logical final)
    (frame : ∀ other,(∀ index,other ≠ NatMarshalGlobal.embedding source index) → final.stk other=contents other) :
    ∀ other,other ≠ 0 → other ≠ 24 → final.stk other=contents other := by
  intro other not0 not24
  by_cases same : other=registerSlot source
  · subst other
    exact (regs source).trans (represented source).symm
  · apply frame other
    intro index
    fin_cases index
    · exact same
    · exact not0
    · exact not24

theorem runs (logical : PaperProofs.Paid.Computation.State) (left right : Register)
    (contents : Stack → List Bool) (store : Option Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (emptyRight : contents 0=[]) (emptyScratch : contents 24=[]) :
    ∃ (run : List State) (final : State),
      run.head?=some (before contents store) ∧
      run.IsChain (fun x y=>TM2.step (program left right) x=some y) ∧
      run.getLast?=some final ∧ TM2.step (program left right) final=none ∧
      RegistersRepresent logical final ∧
      final.stk 0=encodeBits [logical.register left,logical.register right] ∧ final.stk 24=[] ∧
      run.length=2*(encodeCellBits (logical.register left)).length+
        2*(encodeCellBits (logical.register right)).length+7 ∧
      ∀ other,other ≠ 0 → other ≠ 24 → final.stk other=contents other := by
  let footerData := Function.update contents (0 : Stack) [true]
  let ready : State := ⟨some 1,(none,()),footerData⟩
  have prepare : TM2.step (program left right) (before contents store)=some ready := by
    change some (⟨some 1,(none,()),Function.update contents 0 (true::contents 0)⟩ : State)=_
    rw [emptyRight]
  have footerRegs : ∀ reg,footerData (registerSlot reg)=encodeCellBits (logical.register reg) := by
    intro reg
    change Function.update contents 0 [true] (registerSlot reg)=_
    rw [Function.update_of_ne (register_not_right reg)]
    exact represented reg
  have footerRight : footerData 0=[true] := Function.update_self _ _ _
  have footerScratch : footerData 24=[] := by
    change Function.update contents 0 [true] 24=[]
    rw [Function.update_of_ne (by decide : (24 : Stack) ≠ 0)]
    exact emptyScratch
  obtain ⟨rightRun,rightLast,rightHead,rightChain,rightEnd,rightHalt,_rightLabel,rightStore,
    rightRegs,rightWord,rightScratch,rightTime,rightFrame⟩ :=
    CellRead.runs logical right [true] footerData footerRegs footerRight footerScratch
  have rightFrameAll := read_frame logical right footerData rightLast footerRegs rightRegs rightFrame
  obtain ⟨first,middle,firstHead,firstChain,firstLast,middleLabel,middleData,middleStore,firstTime⟩ :=
    Inline.actual_return_trace firstLabel 4 (CellRead.program right) (program left right)
      (first_agrees left right) rightRun (CellRead.before footerData) rightLast ()
      rightHead rightChain rightEnd rightHalt
  have firstReady : Inline.cfg firstLabel 4 () (CellRead.before footerData)=ready := rfl
  rw [firstReady] at firstHead
  have middleRegs : ∀ reg,middle.stk (registerSlot reg)=encodeCellBits (logical.register reg) := by
    intro reg
    rw [middleData]
    exact rightRegs reg
  have middleWord : middle.stk 0=encodeCellBits (logical.register right)++[true] := by
    rw [middleData,rightWord]
  have middleScratch : middle.stk 24=[] := by rw [middleData,rightScratch]
  obtain ⟨leftRun,leftLast,leftHead,leftChain,leftEnd,leftHalt,_leftLabel,leftStore,
    leftRegs,leftWord,leftScratch,leftTime,leftFrame⟩ :=
    CellRead.runs logical left (encodeCellBits (logical.register right)++[true]) middle.stk
      middleRegs middleWord middleScratch
  have leftFrameAll := read_frame logical left middle.stk leftLast middleRegs leftRegs leftFrame
  obtain ⟨second,returned,secondHead,secondChain,secondLast,returnedLabel,returnedData,returnedStore,secondTime⟩ :=
    Inline.actual_return_trace secondLabel 7 (CellRead.program left) (program left right)
      (second_agrees left right) leftRun (CellRead.before middle.stk) leftLast ()
      leftHead leftChain leftEnd leftHalt
  have middleSaved : middle.var=(none,()) := by rw [middleStore,rightStore]
  have secondStart : Inline.cfg secondLabel 7 () (CellRead.before middle.stk)=middle := by
    rcases middle with ⟨label,saved,physical⟩
    change label=some 4 at middleLabel
    change saved=(none,()) at middleSaved
    subst label
    subst saved
    rfl
  rw [secondStart] at secondHead
  let final : State := ⟨none,returned.var,Function.update returned.stk 0
    (encodeNatBits 2++returned.stk 0)⟩
  have finalStep : TM2.step (program left right) returned=some final := by
    rcases returned with ⟨label,saved,physical⟩
    change label=some 7 at returnedLabel
    subst label
    change some (⟨none,saved,Function.update
      (Function.update (Function.update (Function.update (Function.update physical 0 (true::physical 0))
        0 (false::true::physical 0)) 0 (false::false::true::physical 0))
        0 (true::false::false::true::physical 0)) 0 (true::true::false::false::true::physical 0)⟩ : State)=_
    simp only [Function.update_idem]
    rfl
  have firstBridge : [before contents store,ready].IsChain (fun x y=>TM2.step (program left right) x=some y) :=
    List.isChain_cons_cons.mpr ⟨prepare,List.isChain_singleton _⟩
  have beginChain := PDROC.BitVM.Log.TwoStack.join_chain
    [before contents store,ready] first ready firstBridge firstChain rfl firstHead
  have lastBridge : [returned,final].IsChain (fun x y=>TM2.step (program left right) x=some y) :=
    List.isChain_cons_cons.mpr ⟨finalStep,List.isChain_singleton _⟩
  generalize _firstEq : first=front at firstHead firstLast firstTime beginChain firstChain
  generalize _secondEq : second=back at secondHead secondLast secondTime secondChain
  cases front with
  | nil => simp only [List.head?_nil,reduceCtorEq] at firstHead
  | cons start rest =>
    have same : start=ready := Option.some.inj firstHead
    subst start
    have firstSegmentLast : (before contents store::ready::rest).getLast?=some middle := by
      simpa only [List.getLast?_cons_cons] using firstLast
    have firstSegment : (before contents store::ready::rest).IsChain (fun x y=>TM2.step (program left right) x=some y) := by
      simpa only [List.tail_cons,List.cons_append,List.nil_append] using beginChain
    have wholeJoined := PDROC.BitVM.Log.TwoStack.join_chain
      (before contents store::ready::rest) back middle firstSegment secondChain firstSegmentLast secondHead
    cases back with
    | nil => simp only [List.head?_nil,reduceCtorEq] at secondHead
    | cons start tail =>
      have same : start=middle := Option.some.inj secondHead
      subst start
      cases tail with
      | nil =>
        simp only [List.length_cons,List.length_nil] at secondTime
        omega
      | cons next later =>
        let prefixRun := (before contents store::ready::rest)++next::later
        have prefixLast : prefixRun.getLast?=some returned := by
          rw [List.getLast?_append_cons]
          simpa only [List.getLast?_cons_cons] using secondLast
        have actual := PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain
          prefixRun returned [final] prefixLast wholeJoined lastBridge
        refine ⟨prefixRun++[final],final,?_,actual,List.getLast?_append_cons prefixRun final [],rfl,?_,?_,?_,?_,?_⟩
        · simp only [prefixRun,List.head?_append,List.head?_cons,Option.some_or]
        · intro reg
          change Function.update returned.stk 0 (encodeNatBits 2++returned.stk 0) (registerSlot reg)=_
          rw [Function.update_of_ne (register_not_right reg),returnedData]
          exact leftRegs reg
        · change Function.update returned.stk 0 (encodeNatBits 2++returned.stk 0) 0=_
          rw [Function.update_self,returnedData,leftWord]
          simp only [encodeBits,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
        · change Function.update returned.stk 0 (encodeNatBits 2++returned.stk 0) 24=[]
          rw [Function.update_of_ne (by decide : (24 : Stack) ≠ 0),returnedData,leftScratch]
        · simp only [prefixRun,List.length_append,List.length_cons,List.length_nil] at firstTime secondTime ⊢
          omega
        · intro other not0 not24
          change Function.update returned.stk 0 (encodeNatBits 2++returned.stk 0) other=_
          rw [Function.update_of_ne not0,returnedData,leftFrameAll other not0 not24,middleData,
            rightFrameAll other not0 not24]
          change Function.update contents 0 [true] other=contents other
          rw [Function.update_of_ne not0]

theorem supports (left right : Register) : TM2.Supports (program left right) (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label
    all_goals first
    | exact Inline.supports_statement firstLabel 4 Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _)
        (CellRead.program right _) ((CellRead.supports right).2 _ (Finset.mem_univ _))
    | exact Inline.supports_statement secondLabel 7 Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _)
        (CellRead.program left _) ((CellRead.supports left).2 _ (Finset.mem_univ _))
    | simp [program,TM2.SupportsStmt]

end PDROC.BitVM.Kernel.CellPair

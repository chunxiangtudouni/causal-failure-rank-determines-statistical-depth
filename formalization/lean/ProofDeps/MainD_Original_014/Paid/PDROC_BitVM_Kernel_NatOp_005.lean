module

public import Paid.PDROC_BitVM_Kernel_NatOp_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.NatOp

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

def nativeCfg (operation : PaperProofs.Paid.Computation.NatOp) (saved : NatPair.Store)
    (source : TM2.Cfg Numeric.Alphabet Unit (NativeStore operation)) : State operation :=
  StoreIso.cfg (Equiv.prodComm _ _) (Inline.cfg nativeLabels 13 saved source)

/-- An actual old arithmetic transition is the selected caller transition;
the native's unbounded operands remain entirely on physical Bool stacks. -/
theorem native_edge (operation : PaperProofs.Paid.Computation.NatOp) (left right : Register)
    (before after : TM2.Cfg Numeric.Alphabet Unit (NativeStore operation)) (saved : NatPair.Store)
    (edge : TM2.step (primitive operation) before=some after) :
    TM2.step (program operation left right) (nativeCfg operation saved before)=
      some (nativeCfg operation saved after) := by
  rcases before with ⟨label,finiteStore,contents⟩
  cases label with
  | none => cases edge
  | some label =>
    cases label
    have actual : TM2.stepAux (primitive operation ()) finiteStore contents=after := Option.some.inj edge
    change some (TM2.stepAux
      (StoreIso.statement (Equiv.prodComm _ _) (Inline.statement nativeLabels 13 (primitive operation ())))
      (saved,finiteStore) contents)=_
    have reordered : TM2.stepAux
        (StoreIso.statement (Equiv.prodComm _ _) (Inline.statement nativeLabels 13 (primitive operation ())))
        (saved,finiteStore) contents=
        StoreIso.cfg (Equiv.prodComm _ _)
          (TM2.stepAux (Inline.statement nativeLabels 13 (primitive operation ())) (finiteStore,saved) contents) :=
      StoreIso.stepAux_map (Equiv.prodComm _ _) (Inline.statement nativeLabels 13 (primitive operation ()))
        (finiteStore,saved) contents
    rw [reordered,Inline.stepAux_map,actual]
    rfl

theorem native_call (operation : PaperProofs.Paid.Computation.NatOp) (left right : Register)
    (a b : ℕ) (before : TM2.Cfg Numeric.Alphabet Unit (NativeStore operation)) (saved : NatPair.Store)
    (active : (Lift.cfg Numeric.work before).l=some ())
    (represented : BoolOnStacks.representedState (Lift.cfg Numeric.work before)=
      TM0.init (encodeNat a++encodeNat b)) :
    ∃ (run : List (State operation)) (returned : State operation),
      run.head?=some (nativeCfg operation saved before) ∧
      run.IsChain (fun x y=>TM2.step (program operation left right) x=some y) ∧
      run.getLast?=some returned ∧ returned.l=some 13 ∧
      ListBlank.mk (returned.stk 0)=ListBlank.mk (encodeNat (value operation a b)) ∧
      run.length≤32768*(natBits a+natBits b+1)^2+1 ∧
      ∀ other,(∀ index,other≠Numeric.work index) → returned.stk other=before.stk other := by
  obtain ⟨source,sourceLast,head,chain,last,halt,output,bound,frame⟩ :=
    primitive_runs operation a b before active represented
  have lastLabel : sourceLast.l=none := by
    rcases sourceLast with ⟨label,finiteStore,contents⟩
    cases label with
    | none => rfl
    | some label => cases halt
  refine ⟨source.map (nativeCfg operation saved),nativeCfg operation saved sourceLast,
    ?_,?_,?_,?_,?_,?_,frame⟩
  · simp only [List.head?_map,head,Option.map_some]
  · exact List.isChain_map_of_isChain _
      (fun x y edge=>native_edge operation left right x y saved edge) chain
  · simp only [List.getLast?_map,last,Option.map_some]
  · change some (sourceLast.l.map nativeLabels |>.getD 13)=some 13
    rw [lastLabel]
    rfl
  · change (Tape.mk₂ (sourceLast.stk 24) (sourceLast.stk 0)).right₀=_ at output
    change ListBlank.mk (sourceLast.stk 0)=_
    simpa only [Tape.mk₂,Tape.mk'_right₀] using output
  · simpa only [List.length_map] using bound

def before (operation : PaperProofs.Paid.Computation.NatOp)
    (contents : Numeric.Stack → List Bool) (store : Option Bool) : State operation :=
  Inline.cfg pairLabels 11 (default : NativeStore operation) (NatPair.before contents store)

/-- The actual fixed opcode's complete register-read and binary-compute
path, including both call boundaries, control reset and true final HALT.
This phase leaves the result on nativeRight; actual Cell writeback follows. -/
theorem compute_runs (operation : PaperProofs.Paid.Computation.NatOp)
    (logical : PaperProofs.Paid.Computation.State) (left right : Register) (a b : ℕ)
    (contents : Numeric.Stack → List Bool) (store : Option Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (leftNat : logical.register left=.natural a) (rightNat : logical.register right=.natural b)
    (emptyRight : contents 0=[]) (emptyLeft : contents 24=[]) :
    ∃ (run : List (State operation)) (lastState : State operation),
      run.head?=some (before operation contents store) ∧
      run.IsChain (fun x y=>TM2.step (program operation left right) x=some y) ∧
      run.getLast?=some lastState ∧ TM2.step (program operation left right) lastState=none ∧
      RegistersRepresent logical lastState ∧
      ListBlank.mk (lastState.stk 0)=ListBlank.mk (encodeNat (value operation a b)) ∧
      run.length≤2*(encodeNatBits a).length+2*(encodeNatBits b).length+
        32768*(natBits a+natBits b+1)^2+12 ∧
      ∀ other,(∀ index,other≠NatMarshalGlobal.embedding left index)→
        (∀ index,other≠NatMarshalGlobal.embedding right index)→
        (∀ index,other≠Numeric.work index)→lastState.stk other=contents other := by
  obtain ⟨pair,pairEnd,pairHead,pairChain,pairLast,pairHalt,_pairLabel,
    _pairStore,pairRegisters,pairWord,pairScratch,pairLength,pairFrame⟩ :=
    NatPair.pair_runs logical left right a b contents store represented leftNat rightNat emptyRight emptyLeft
  obtain ⟨first,ready,firstHead,firstChain,firstLast,readyLabel,readyStacks,_readyStore,firstLength⟩ :=
    Inline.actual_return_trace pairLabels 11 (NatPair.program left right) (program operation left right)
      (pair_agrees operation left right) pair (NatPair.before contents store) pairEnd
      (default : NativeStore operation) pairHead pairChain pairLast pairHalt
  let reset : State operation := ⟨some 12,(ready.var.1,(0,false)),ready.stk⟩
  have resetEdge : TM2.step (program operation left right) ready=some reset := by
    rcases ready with ⟨label,finiteStore,contentsNow⟩
    change label=some 11 at readyLabel
    subst label
    rfl
  let source : TM2.Cfg Numeric.Alphabet Unit (NativeStore operation) := ⟨some (),(0,false),reset.stk⟩
  have sourceRight : source.stk 0=encodeNat a++encodeNat b := by
    change ready.stk 0=_
    rw [readyStacks,pairWord,PDROC.BitVM.Link.CodecCandidate.encodeNatBits_eq_neutral,
      PDROC.BitVM.Link.CodecCandidate.encodeNatBits_eq_neutral]
  have sourceLeft : source.stk 24=[] := by
    change ready.stk 24=[]
    rw [readyStacks,pairScratch]
  have nativeInitial : BoolOnStacks.representedState (Lift.cfg Numeric.work source)=
      TM0.init (encodeNat a++encodeNat b) := by
    change (⟨0,Tape.mk' (ListBlank.mk (source.stk 24)) (ListBlank.mk (source.stk 0))⟩ :
      TM0.Cfg Bool (Fin (states operation+1)))=_
    rw [sourceLeft,sourceRight]
    rfl
  obtain ⟨second,returned,secondHead,secondChain,secondLast,returnedLabel,result,secondBound,nativeFrame⟩ :=
    native_call operation left right a b source ready.var.1 rfl nativeInitial
  have boundary : nativeCfg operation ready.var.1 source=reset := rfl
  rw [boundary] at secondHead
  have resetPair : [ready,reset].IsChain (fun x y=>TM2.step (program operation left right) x=some y) :=
    List.isChain_cons_cons.mpr ⟨resetEdge,List.isChain_singleton _⟩
  have firstChain' := PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain
    first ready [reset] firstLast firstChain resetPair
  have firstLast' : (first++[reset]).getLast?=some reset := List.getLast?_append_cons first reset []
  have combined := PDROC.BitVM.Log.TwoStack.join_chain (first++[reset]) second reset
    firstChain' secondChain firstLast' secondHead
  let final : State operation := ⟨none,returned.var,returned.stk⟩
  have finalEdge : TM2.step (program operation left right) returned=some final := by
    rcases returned with ⟨label,finiteStore,contentsNow⟩
    change label=some 13 at returnedLabel
    subst label
    rfl
  have finalPair : [returned,final].IsChain (fun x y=>TM2.step (program operation left right) x=some y) :=
    List.isChain_cons_cons.mpr ⟨finalEdge,List.isChain_singleton _⟩
  cases second with
  | nil => simp only [List.head?_nil,reduceCtorEq] at secondHead
  | cons start rest =>
    have initial : start=reset := Option.some.inj secondHead
    subst start
    cases rest with
    | nil =>
      have same : reset=returned := Option.some.inj secondLast
      have wrong := congrArg TM2.Cfg.l same
      rw [returnedLabel] at wrong
      have digits := congrArg (Option.map Fin.val) wrong
      change some 12=some 13 at digits
      cases digits
    | cons next later =>
      let prefixRun := (first++[reset])++next::later
      have prefixLast : prefixRun.getLast?=some returned := by
        rw [List.getLast?_append_cons]
        simpa only [List.getLast?_cons_cons] using secondLast
      have actual := PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain
        prefixRun returned [final] prefixLast combined finalPair
      refine ⟨prefixRun++[final],final,?_,actual,List.getLast?_append_cons prefixRun final [],rfl,?_,result,?_,?_⟩
      · simp only [prefixRun,List.head?_append,firstHead,Option.some_or]
        rfl
      · intro reg
        have outside : ∀ index,registerSlot reg≠Numeric.work index := by
          intro index
          have bounds := registerSlot_bounds reg
          fin_cases index
          · intro same
            have values := congrArg Fin.val same
            change (registerSlot reg).val=0 at values
            omega
          · intro same
            have values := congrArg Fin.val same
            change (registerSlot reg).val=24 at values
            omega
        change returned.stk (registerSlot reg)=_
        rw [nativeFrame _ outside]
        change ready.stk (registerSlot reg)=_
        rw [readyStacks]
        exact pairRegisters reg
      · simp only [prefixRun,List.length_append,List.length_cons,List.length_nil] at secondBound ⊢
        omega
      · intro other outsideLeft outsideRight outsideNative
        change returned.stk other=contents other
        rw [nativeFrame other outsideNative]
        change ready.stk other=_
        rw [readyStacks]
        exact pairFrame other outsideLeft outsideRight

end PDROC.BitVM.Kernel.NatOp

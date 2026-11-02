module

public import Paid.PDROC_BitVM_Kernel_RawNative_033

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawOp

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

/-- One actual two-register read, literal RAW pair construction, finite
native-control reset, frozen finite Bool call and caller return/HALT.
Canonical destination replacement follows in a separate actual writer. -/
theorem compute_runs {states : ℕ} (machine : Machine states) (resultFn : Rat → Rat → Rat) (c d : ℕ)
    (contract : NativeContract machine resultFn c d)
    (logical : PaperProofs.Paid.Computation.State) (left right : Register) (x y : Rat)
    (contents : Stack → List Bool) (store : Option Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (leftRat : logical.register left=.rational x) (rightRat : logical.register right=.rational y)
    (emptyRight : contents 0=[]) (emptyLeft : contents 24=[]) :
    ∃ (run : List (State states)) (final : State states),
      run.head?=some (before contents store) ∧
      run.IsChain (fun a b=>TM2.step (program machine left right) a=some b) ∧
      run.getLast?=some final ∧ TM2.step (program machine left right) final=none ∧
      RegistersRepresent logical final ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (encode [.rational (resultFn x y)]) ∧
      run.length ≤ 2*(encodeCellBits (logical.register left)).length+
        2*(encodeCellBits (logical.register right)).length+
        c*((encode [.rational x,.rational y]).length+1)^d+9 ∧
      ∀ other,other ≠ 0 → other ≠ 24 → final.stk other=contents other := by
  obtain ⟨pair,pairEnd,pairHead,pairChain,pairLast,pairHalt,pairRegisters,pairWord,
    pairScratch,pairLength,pairFrame⟩ :=
    CellPair.runs logical left right contents store represented emptyRight emptyLeft
  obtain ⟨first,ready,firstHead,firstChain,firstLast,readyLabel,readyStacks,_readyStore,firstLength⟩ :=
    Inline.actual_return_trace pairLabels 8 (CellPair.program left right) (program machine left right)
      (pair_agrees machine left right) pair (CellPair.before contents store) pairEnd
      (default : BoolOnStacks.Store states) pairHead pairChain pairLast pairHalt
  let reset : State states := ⟨some 9,(ready.var.1,(0,false)),ready.stk⟩
  have resetEdge : TM2.step (program machine left right) ready=some reset := by
    rcases ready with ⟨label,finiteStore,physical⟩
    change label=some 8 at readyLabel
    subst label
    rfl
  let nativeState : TM2.Cfg Alphabet Unit (BoolOnStacks.Store states) := ⟨some (),(0,false),reset.stk⟩
  have sourceRight : nativeState.stk 0=encode [.rational x,.rational y] := by
    change ready.stk 0=_
    rw [readyStacks,pairWord,leftRat,rightRat]
    rfl
  have sourceLeft : nativeState.stk 24=[] := by
    change ready.stk 24=[]
    rw [readyStacks,pairScratch]
  have nativeInitial : BoolOnStacks.representedState (Lift.cfg Numeric.work nativeState)=
      TM0.init (encode [.rational x,.rational y]) := by
    change (⟨0,Tape.mk' (ListBlank.mk (nativeState.stk 24)) (ListBlank.mk (nativeState.stk 0))⟩ :
      TM0.Cfg Bool (Fin (states+1)))=_
    rw [sourceLeft,sourceRight]
    rfl
  obtain ⟨second,returned,secondHead,secondChain,secondLast,returnedLabel,result,secondBound,nativeFrame⟩ :=
    native_call machine resultFn c d contract left right x y nativeState ready.var.1 rfl nativeInitial
  have boundary : nativeCfg ready.var.1 nativeState=reset := rfl
  rw [boundary] at secondHead
  have resetPair : [ready,reset].IsChain (fun a b=>TM2.step (program machine left right) a=some b) :=
    List.isChain_cons_cons.mpr ⟨resetEdge,List.isChain_singleton _⟩
  have firstChain' := PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain
    first ready [reset] firstLast firstChain resetPair
  have firstLast' : (first++[reset]).getLast?=some reset := List.getLast?_append_cons first reset []
  have combined := PDROC.BitVM.Log.TwoStack.join_chain (first++[reset]) second reset
    firstChain' secondChain firstLast' secondHead
  let final : State states := ⟨none,returned.var,returned.stk⟩
  have finalEdge : TM2.step (program machine left right) returned=some final := by
    rcases returned with ⟨label,finiteStore,physical⟩
    change label=some 10 at returnedLabel
    subst label
    rfl
  have finalPair : [returned,final].IsChain (fun a b=>TM2.step (program machine left right) a=some b) :=
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
      change some 9=some 10 at digits
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
        have outside : ∀ index,registerSlot reg ≠ Numeric.work index := by
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
      · intro other not0 not24
        have outside : ∀ index,other ≠ Numeric.work index := by
          intro index
          fin_cases index
          · exact not0
          · exact not24
        change returned.stk other=contents other
        rw [nativeFrame other outside]
        change ready.stk other=_
        rw [readyStacks]
        exact pairFrame other not0 not24

end PDROC.BitVM.Kernel.RawOp

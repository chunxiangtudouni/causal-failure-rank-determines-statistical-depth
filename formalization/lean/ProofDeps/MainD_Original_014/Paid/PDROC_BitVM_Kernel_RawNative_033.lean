module

public import Paid.PDROC_BitVM_Kernel_RawOp_030

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawOp

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

def nativeCfg {states : ℕ} (saved : CellPair.Store)
    (source : TM2.Cfg Alphabet Unit (BoolOnStacks.Store states)) : State states :=
  StoreIso.cfg (Equiv.prodComm _ _) (Inline.cfg nativeLabels 10 saved source)

theorem native_edge {states : ℕ} (source : Machine states) (left right : Register)
    (before final : TM2.Cfg Alphabet Unit (BoolOnStacks.Store states)) (saved : CellPair.Store)
    (edge : TM2.step (RawMul.program source) before=some final) :
    TM2.step (program source left right) (nativeCfg saved before)=some (nativeCfg saved final) := by
  rcases before with ⟨label,finiteStore,contents⟩
  cases label with
  | none => cases edge
  | some label =>
    cases label
    have actual : TM2.stepAux (RawMul.program source ()) finiteStore contents=final := Option.some.inj edge
    change some (TM2.stepAux
      (StoreIso.statement (Equiv.prodComm _ _) (Inline.statement nativeLabels 10 (RawMul.program source ())))
      (saved,finiteStore) contents)=_
    have reordered : TM2.stepAux
        (StoreIso.statement (Equiv.prodComm _ _) (Inline.statement nativeLabels 10 (RawMul.program source ())))
        (saved,finiteStore) contents=
        StoreIso.cfg (Equiv.prodComm _ _)
          (TM2.stepAux (Inline.statement nativeLabels 10 (RawMul.program source ())) (finiteStore,saved) contents) :=
      StoreIso.stepAux_map (Equiv.prodComm _ _) (Inline.statement nativeLabels 10 (RawMul.program source ()))
        (finiteStore,saved) contents
    rw [reordered,Inline.stepAux_map,actual]
    rfl

/-- The uniform frozen native contract supplies this actual call. All
saved caller fields and every non-work stack are preserved on the very
same path, with a real caller return instead of a free head/state reset. -/
theorem native_call {states : ℕ} (source : Machine states) (result : Rat → Rat → Rat) (c d : ℕ)
    (contract : NativeContract source result c d) (left right : Register) (x y : Rat)
    (before : TM2.Cfg Alphabet Unit (BoolOnStacks.Store states)) (saved : CellPair.Store)
    (active : (Lift.cfg Numeric.work before).l=some ())
    (represented : BoolOnStacks.representedState (Lift.cfg Numeric.work before)=
      TM0.init (encode [.rational x,.rational y])) :
    ∃ (run : List (State states)) (returned : State states),
      run.head?=some (nativeCfg saved before) ∧
      run.IsChain (fun a b=>TM2.step (program source left right) a=some b) ∧
      run.getLast?=some returned ∧ returned.l=some 10 ∧
      ListBlank.mk (returned.stk 0)=ListBlank.mk (encode [.rational (result x y)]) ∧
      run.length ≤ c*((encode [.rational x,.rational y]).length+1)^d+1 ∧
      ∀ other,(∀ index,other ≠ Numeric.work index) → returned.stk other=before.stk other := by
  obtain ⟨old,oldLast,head,chain,last,halt,tape,bound,frame⟩ := contract x y before active represented
  have lastLabel : oldLast.l=none := by
    rcases oldLast with ⟨label,finiteStore,contents⟩
    cases label with
    | none => rfl
    | some label => cases halt
  refine ⟨old.map (nativeCfg saved),nativeCfg saved oldLast,?_,?_,?_,?_,?_,?_,frame⟩
  · simp only [List.head?_map,head,Option.map_some]
  · exact List.isChain_map_of_isChain _
      (fun a b edge=>native_edge source left right a b saved edge) chain
  · simp only [List.getLast?_map,last,Option.map_some]
  · change some (oldLast.l.map nativeLabels |>.getD 10)=some 10
    rw [lastLabel]
    rfl
  · have representedRight := congrArg Tape.right₀ tape
    change (Tape.mk₂ (oldLast.stk 24) (oldLast.stk 0)).right₀=_ at representedRight
    change ListBlank.mk (oldLast.stk 0)=_
    simpa only [Tape.mk₂,Tape.mk₁,Tape.mk'_right₀] using representedRight
  · simpa only [List.length_map] using bound

end PDROC.BitVM.Kernel.RawOp

module

public import Paid.PDROC_BitVM_Kernel_CellPair_028
public import Paid.PDROC_BitVM_Kernel_RawMul_029
public import Paid.PDROC_BitVM_Native_StoreTrace_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawOp

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

abbrev Label := Fin 11
abbrev Store (states : ℕ) := CellPair.Store × BoolOnStacks.Store states
abbrev State (states : ℕ) := TM2.Cfg Alphabet Label (Store states)

def pairLabels (label : CellPair.Label) : Label := ⟨label.val,by omega⟩
def nativeLabels (_ : Unit) : Label := 9

/-- Source and register roles are fixed code. The only finite-control
reset changes the native q/bit store; all unbounded Cell and tape bytes
are transferred by the actual two-register list producer. -/
def program {states : ℕ} (source : Machine states) (left right : Register) (label : Label) :
    TM2.Stmt Alphabet Label (Store states) :=
  if h : label.val<8 then Inline.statement pairLabels 8 (CellPair.program left right ⟨label.val,h⟩)
  else if label=8 then .load (fun store=>(store.1,(0,false))) (.goto (fun _=>9))
  else if label=9 then StoreIso.statement (Equiv.prodComm _ _)
    (Inline.statement nativeLabels 10 (RawMul.program source ()))
  else .halt

def before {states : ℕ} (contents : Stack → List Bool) (store : Option Bool) : State states :=
  Inline.cfg pairLabels 8 (default : BoolOnStacks.Store states) (CellPair.before contents store)

theorem pair_agrees {states : ℕ} (source : Machine states) (left right : Register) : ∀ label,
    program source left right (pairLabels label)=Inline.statement pairLabels 8 (CellPair.program left right label) := by
  intro label
  fin_cases label <;> rfl

theorem supports {states : ℕ} (source : Machine states) (left right : Register) :
    TM2.Supports (program source left right) (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label
    all_goals first
    | exact Inline.supports_statement pairLabels 8 Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _)
        (CellPair.program left right _) ((CellPair.supports left right).2 _ (Finset.mem_univ _))
    | exact StoreIso.supports_statement (Equiv.prodComm _ _) Finset.univ _
        (Inline.supports_statement nativeLabels 10 Finset.univ Finset.univ
          (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _)
          (RawMul.program source ()) ((RawMul.supports source).2 () (Finset.mem_univ _)))
    | simp [program,TM2.SupportsStmt]

/-- A uniform theorem about an existing fixed native machine, not a
per-input run premise. Frozen RAW multiplication supplies this property;
other original rational operations must supply their own frozen machine.
The mathematical result function is never read by program. -/
def NativeContract {states : ℕ} (source : Machine states) (result : Rat → Rat → Rat) (c d : ℕ) : Prop :=
  ∀ (x y : Rat) (before : TM2.Cfg Alphabet Unit (BoolOnStacks.Store states)),
    (Lift.cfg Numeric.work before).l=some () →
    BoolOnStacks.representedState (Lift.cfg Numeric.work before)=TM0.init (encode [.rational x,.rational y]) →
    ∃ (run : List (TM2.Cfg Alphabet Unit (BoolOnStacks.Store states)))
      (final : TM2.Cfg Alphabet Unit (BoolOnStacks.Store states)),
      run.head?=some before ∧ run.IsChain (fun a b=>TM2.step (RawMul.program source) a=some b) ∧
      run.getLast?=some final ∧ TM2.step (RawMul.program source) final=none ∧
      (BoolOnStacks.representedState (Lift.cfg Numeric.work final)).Tape=
        Tape.mk₁ (encode [.rational (result x y)]) ∧
      run.length ≤ c*((encode [.rational x,.rational y]).length+1)^d+1 ∧
      ∀ other,(∀ index,other ≠ Numeric.work index) → final.stk other=before.stk other

theorem actual_mul_contract : ∃ states c d : ℕ,∃ source : Machine states,
    0<c ∧ 0<d ∧ NativeContract source (fun x y=>x*y) c d := RawMul.fixed_machine

end PDROC.BitVM.Kernel.RawOp

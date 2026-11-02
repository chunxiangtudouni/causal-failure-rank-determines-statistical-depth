module

public import Paid.PDROC_BitVM_Kernel_Numeric_002
public import Paid.PDROC_BitVM_Kernel_NatPair_003
public import Paid.PDROC_BitVM_Native_StoreTrace_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.Internal

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

/-- These are two fixed binary SUBROUTINES used inside existing rational
RAM instructions, not additional original RAM opcodes or host oracles. -/
inductive Kind where
  | gcd | lessEqual
  deriving DecidableEq

def states : Kind → ℕ
  | .gcd => 3564
  | .lessEqual => 397

abbrev NativeStore (kind : Kind) := BoolOnStacks.Store (states kind)

def primitive (kind : Kind) : Unit → TM2.Stmt Numeric.Alphabet Unit (NativeStore kind) :=
  match kind with
  | .gcd => Numeric.gcdMachine
  | .lessEqual => Numeric.leMachine

/-- Proof descriptions only; no transition calls this function. -/
def value (kind : Kind) (a b : ℕ) : ℕ :=
  match kind with
  | .gcd => Nat.gcd a b
  | .lessEqual => if decide (a≤b) then 1 else 0

theorem primitive_runs (kind : Kind) (a b : ℕ)
    (before : TM2.Cfg Numeric.Alphabet Unit (NativeStore kind))
    (active : (Lift.cfg Numeric.work before).l=some ())
    (represented : BoolOnStacks.representedState (Lift.cfg Numeric.work before)=
      TM0.init (encodeNat a++encodeNat b)) :
    ∃ (run : List (TM2.Cfg Numeric.Alphabet Unit (NativeStore kind)))
      (lastState : TM2.Cfg Numeric.Alphabet Unit (NativeStore kind)),
      run.head?=some before ∧ run.IsChain (fun x y=>TM2.step (primitive kind) x=some y) ∧
      run.getLast?=some lastState ∧ TM2.step (primitive kind) lastState=none ∧
      (BoolOnStacks.representedState (Lift.cfg Numeric.work lastState)).Tape.right₀=
        ListBlank.mk (encodeNat (value kind a b)) ∧
      run.length ≤ 32768*(natBits a+natBits b+1)^2+1 ∧
      ∀ other,(∀ index,other≠Numeric.work index) → lastState.stk other=before.stk other := by
  cases kind with
  | gcd =>
    obtain ⟨run,lastState,head,chain,last,halt,tape,bound,frame⟩ := Numeric.gcd_runs a b before active represented
    refine ⟨run,lastState,head,chain,last,halt,?_,?_,frame⟩
    · exact (congrArg Tape.right₀ tape).trans (Tape.mk'_right₀ _ _)
    · exact bound.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by decide : 16384≤32768)) 1)
  | lessEqual =>
    obtain ⟨run,lastState,head,chain,last,halt,tape,bound,frame⟩ := Numeric.le_runs a b before active represented
    refine ⟨run,lastState,head,chain,last,halt,?_,?_,frame⟩
    · exact (congrArg Tape.right₀ tape).trans (Tape.mk'_right₀ _ _)
    · exact bound.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by decide : 4096≤32768)) 1)

theorem primitive_supports (kind : Kind) : TM2.Supports (primitive kind) (Finset.univ : Finset Unit) := by
  cases kind
  · exact Numeric.gcd_supports
  · exact Numeric.le_supports

abbrev Label := Fin 14
abbrev Store (kind : Kind) := NatPair.Store × NativeStore kind
abbrev State (kind : Kind) := TM2.Cfg Numeric.Alphabet Label (Store kind)

def pairLabels (label : NatPair.Label) : Label := ⟨label.val,by omega⟩
def nativeLabels (_ : Unit) : Label := 12

/-- Actual source-register marshalling, finite native-control reset and
one frozen GCD/LE call. Kind/source roles are selected before every operand. -/
def program (kind : Kind) (left right : Register) (label : Label) :
    TM2.Stmt Numeric.Alphabet Label (Store kind) :=
  if h : label.val<11 then Inline.statement pairLabels 11 (NatPair.program left right ⟨label.val,h⟩)
  else if label=11 then .load (fun store=>(store.1,(0,false))) (.goto (fun _=>12))
  else if label=12 then StoreIso.statement (Equiv.prodComm _ _)
    (Inline.statement nativeLabels 13 (primitive kind ()))
  else .halt

theorem pair_agrees (kind : Kind) (left right : Register) : ∀ label,
    program kind left right (pairLabels label)=Inline.statement pairLabels 11 (NatPair.program left right label) := by
  intro label
  fin_cases label <;> rfl

theorem supports (kind : Kind) (left right : Register) :
    TM2.Supports (program kind left right) (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label
    all_goals first
    | exact Inline.supports_statement pairLabels 11 Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _)
        (NatPair.program left right _) ((NatPair.supports left right).2 _ (Finset.mem_univ _))
    | exact StoreIso.supports_statement (Equiv.prodComm _ _) Finset.univ _
        (Inline.supports_statement nativeLabels 13 Finset.univ Finset.univ
          (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _)
          (primitive kind ()) ((primitive_supports kind).2 () (Finset.mem_univ _)))
    | simp [program,TM2.SupportsStmt]

end PDROC.BitVM.Kernel.Internal

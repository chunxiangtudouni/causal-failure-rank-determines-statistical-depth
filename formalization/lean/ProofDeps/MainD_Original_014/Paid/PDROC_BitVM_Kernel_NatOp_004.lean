module

public import Paid.PDROC_BitVM_Kernel_Numeric_002
public import Paid.PDROC_BitVM_Kernel_NatPair_003
public import Paid.PDROC_BitVM_Native_StoreTrace_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.NatOp

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

/-- The source program selects the operation before all original inputs. -/
def states : PaperProofs.Paid.Computation.NatOp → ℕ
  | .add => 469 | .subtract => 596 | .multiply => 982 | .divide => 1136 | .modulo => 1113

abbrev NativeStore (operation : PaperProofs.Paid.Computation.NatOp) := BoolOnStacks.Store (states operation)

def primitive (operation : PaperProofs.Paid.Computation.NatOp) : Unit →
    TM2.Stmt Numeric.Alphabet Unit (NativeStore operation) :=
  match operation with
  | .add => Numeric.addMachine
  | .subtract => Numeric.subMachine
  | .multiply => Numeric.mulMachine
  | .divide => Numeric.divMachine
  | .modulo => Numeric.modMachine

/-- A proof-side description of the native result. No transition calls it. -/
def value (operation : PaperProofs.Paid.Computation.NatOp) (a b : ℕ) : ℕ :=
  match operation with
  | .add => a+b | .subtract => a-b | .multiply => a*b | .divide => a/b | .modulo => a%b

theorem value_of_success (operation : PaperProofs.Paid.Computation.NatOp) (a b result : ℕ)
    (success : operation.eval a b=some result) : value operation a b=result := by
  cases operation <;> simp only [PaperProofs.Paid.Computation.NatOp.eval] at success
  · exact Option.some.inj success
  · exact Option.some.inj success
  · exact Option.some.inj success
  · split at success
    · cases success
    · exact Option.some.inj success
  · split at success
    · cases success
    · exact Option.some.inj success

/-- All five original natural opcodes use concrete frozen Bool algorithms.
Only the physical tape/control and ordinary finite store enter transitions. -/
theorem primitive_runs (operation : PaperProofs.Paid.Computation.NatOp) (a b : ℕ)
    (before : TM2.Cfg Numeric.Alphabet Unit (NativeStore operation))
    (active : (Lift.cfg Numeric.work before).l=some ())
    (represented : BoolOnStacks.representedState (Lift.cfg Numeric.work before)=
      TM0.init (encodeNat a++encodeNat b)) :
    ∃ (run : List (TM2.Cfg Numeric.Alphabet Unit (NativeStore operation)))
      (lastState : TM2.Cfg Numeric.Alphabet Unit (NativeStore operation)),
      run.head?=some before ∧ run.IsChain (fun x y=>TM2.step (primitive operation) x=some y) ∧
      run.getLast?=some lastState ∧ TM2.step (primitive operation) lastState=none ∧
      (BoolOnStacks.representedState (Lift.cfg Numeric.work lastState)).Tape.right₀=
        ListBlank.mk (encodeNat (value operation a b)) ∧
      run.length≤32768*(natBits a+natBits b+1)^2+1 ∧
      ∀ other,(∀ index,other≠Numeric.work index)→lastState.stk other=before.stk other := by
  cases operation with
  | add =>
    obtain ⟨run,lastState,head,chain,last,halt,tape,bound,frame⟩ := Numeric.add_runs a b before active represented
    refine ⟨run,lastState,head,chain,last,halt,?_,?_,frame⟩
    · exact (congrArg Tape.right₀ tape).trans (Tape.mk'_right₀ _ _)
    · exact bound.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by decide : 4096≤32768)) 1)
  | subtract =>
    obtain ⟨run,lastState,head,chain,last,halt,tape,bound,frame⟩ := Numeric.sub_runs a b before active represented
    refine ⟨run,lastState,head,chain,last,halt,?_,?_,frame⟩
    · exact (congrArg Tape.right₀ tape).trans (Tape.mk'_right₀ _ _)
    · exact bound.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by decide : 4096≤32768)) 1)
  | multiply =>
    obtain ⟨run,lastState,head,chain,last,halt,tape,bound,frame⟩ := Numeric.mul_runs a b before active represented
    refine ⟨run,lastState,head,chain,last,halt,?_,?_,frame⟩
    · exact (congrArg Tape.right₀ tape).trans (Tape.mk'_right₀ _ _)
    · exact bound.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by decide : 16384≤32768)) 1)
  | divide => exact Numeric.div_runs a b before active represented
  | modulo => exact Numeric.mod_runs a b before active represented

theorem primitive_supports (operation : PaperProofs.Paid.Computation.NatOp) :
    TM2.Supports (primitive operation) (Finset.univ : Finset Unit) := by
  cases operation
  · exact Numeric.add_supports
  · exact Numeric.sub_supports
  · exact Numeric.mul_supports
  · exact Numeric.div_supports
  · exact Numeric.mod_supports

abbrev Label := Fin 14
abbrev Store (operation : PaperProofs.Paid.Computation.NatOp) := NatPair.Store × NativeStore operation
abbrev State (operation : PaperProofs.Paid.Computation.NatOp) := TM2.Cfg Numeric.Alphabet Label (Store operation)

def pairLabels (label : NatPair.Label) : Label := ⟨label.val,by omega⟩
def nativeLabels (_ : Unit) : Label := 12

/-- A fixed original opcode first really marshals both register operands,
then resets only the finite native control and calls its binary machine.
The final right half-tape is canonical modulo physical FALSE padding.
The separate actual Nat writer consumes that physical prefix afterward. -/
def program (operation : PaperProofs.Paid.Computation.NatOp) (left right : Register)
    (label : Label) : TM2.Stmt Numeric.Alphabet Label (Store operation) :=
  if h : label.val<11 then
    Inline.statement pairLabels 11 (NatPair.program left right ⟨label.val,h⟩)
  else if label=11 then .load (fun store=>(store.1,(0,false))) (.goto (fun _=>12))
  else if label=12 then
    StoreIso.statement (Equiv.prodComm _ _)
      (Inline.statement nativeLabels 13 (primitive operation ()))
  else .halt

theorem pair_agrees (operation : PaperProofs.Paid.Computation.NatOp) (left right : Register) :
    ∀ label,program operation left right (pairLabels label)=
      Inline.statement pairLabels 11 (NatPair.program left right label) := by
  intro label
  fin_cases label <;> rfl

theorem finite_reset (operation : PaperProofs.Paid.Computation.NatOp) (left right : Register)
    (contents : Numeric.Stack → List Bool) (saved : Store operation) :
    TM2.step (program operation left right) (⟨some 11,saved,contents⟩ : State operation)=
      some ⟨some 12,(saved.1,(0,false)),contents⟩ := rfl

theorem program_supports (operation : PaperProofs.Paid.Computation.NatOp) (left right : Register) :
    TM2.Supports (program operation left right) (Finset.univ : Finset Label) := by
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
          (primitive operation ()) ((primitive_supports operation).2 () (Finset.mem_univ _)))
    | simp [program,TM2.SupportsStmt]

end PDROC.BitVM.Kernel.NatOp

module
public import RootB236_Controller_DFSDriver_Local020

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing RootB23.GenericRank PaperProofs.Structure
open PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}
variable {q : Nat}
attribute [local irreducible] pushProfile actionProfile nodeProfile

structure StableReply (limit q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (tail archive : List Bool) (context : C) (bound : Nat) (final : State C) : Prop extends Reply limit q stages remaining tail context final where
  fields : FieldsBound final.stk bound
  archive : final.stk 1=archive
  limit_saved : final.stk 2=unary limit
  remaining_saved : final.stk 4=EraseSem.mask remaining
  width_saved : final.stk 11=unary q

/-- A uniform depth/spool budget; global visits do not appear in workspace. -/
def BoundedSpec (finish : Statement C) (limit q bound cap : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) : Prop :=
  ∀ (memory : Store C) (before : Stack → List Bool) (flag : Bool) (tail : List Bool),
    before 0=rows q stages → before 2=unary limit → before 4=EraseSem.mask remaining → before 11=unary q → before 13=flag::tail →
    FieldsBound before bound → limit≤bound → q≤bound → (rows q stages).length≤bound →
    tail.length+stages.length*(28*bound+30)≤cap →
    ∃ steps final,BoundedRun finish (peak C bound cap) (state start memory before) final steps ∧
      StableReply limit q stages remaining tail (before 1) memory.1 bound final ∧
      steps+4*localTime bound cap≤nodeTime bound cap*(evaluate q stages remaining).nodes

theorem evaluate_nodes_pos (q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    1≤(evaluate q stages remaining).nodes := by
  cases stages with
  | nil => exact Nat.le_refl 1
  | cons eligible later => rw [evaluate_nodes_cons];omega

theorem bounded_terminal (finish : Statement C) (limit q bound cap : Nat) (remaining : Finset (Fin q)) :
    BoundedSpec finish limit q bound cap [] remaining := by
  intro memory before flag tail r0 r2 r4 r11 r13 fields limitBound widthBound _rowBound room
  have normal:=node_bank_eq before [] limit (EraseSem.mask remaining) q (flag::tail) r0 r2 r4 r11 r13
  have path:=call_nil_path .halt .halt .halt .halt before memory limit (EraseSem.mask remaining) q (flag::tail)
  rw [normal] at path
  have run:=core_path finish path
  rw [core_state,core_state] at run
  have port : coreMap (if (flag::tail).tail.isEmpty then rootDone else popFrame)=returnPort tail := core_return tail
  rw [port] at run
  have count : clearCost before+2*limit+6≤localTime bound cap := by
    have clean:=clear_cost_bound before bound fields
    dsimp only [localTime,entryCap];omega
  have entry:=complete_bank_bound before bound cap flag tail fields r13 (by simpa only [List.length_nil,Nat.zero_mul,Nat.add_zero] using room)
  have actual:=atom run bound cap entry count
  let output:=Function.update (cleanBank (nodeBank before [] limit (EraseSem.mask remaining) q (false::tail))) 15 (unary limit)
  have outputFields : FieldsBound output bound := by
    apply restore_fields_bound _ bound (unary limit)
    · apply clean_fields_bound
      exact node_fields_bound before bound [] limit (EraseSem.mask remaining) q (false::tail) fields (Nat.zero_le _) limitBound
        (by simpa only [EraseSem.mask_length] using widthBound) widthBound
    · simpa only [unary,RankCompare.unary,List.length_replicate] using limitBound
  refine ⟨_,_,actual,⟨⟨rfl,rfl,rfl,rfl,rfl⟩,outputFields,rfl,rfl,rfl,rfl⟩,?_⟩
  change clearCost before+2*limit+6+4*localTime bound cap≤nodeTime bound cap*1
  dsimp only [nodeTime];omega
end RootB236.Controller.DFSDriver.Machine

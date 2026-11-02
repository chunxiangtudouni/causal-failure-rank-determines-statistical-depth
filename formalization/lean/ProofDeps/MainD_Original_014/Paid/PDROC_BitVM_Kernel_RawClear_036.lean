module

public import Paid.PDROC_BitVM_Kernel_RawWrite_035

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawWrite

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

/-- One actual arbitrary-carry clear in the final result writer, ending
at the next real caller label with the saved finite parser store intact. -/
theorem clear_call (target : Register) (phase : Fin 5) (contents : Stack → List Bool)
    (store : Option Bool) (saved : ResultCell.Store) :
    ∃ (run : List State) (returned : State),
      run.head?=some (⟨some (clearLabel phase),(store,saved),contents⟩ : State) ∧
      run.IsChain (fun a b=>TM2.step (program target) a=some b) ∧
      run.getLast?=some returned ∧ returned.l=some (nextLabel phase) ∧
      returned.var=(none,saved) ∧ returned.stk=Function.update contents (clearRole target phase) [] ∧
      run.length=(contents (clearRole target phase)).length+2 := by
  obtain ⟨old,head,chain,last,halt,time,_frame⟩ := Clear.runs (clearRole target phase) contents store
  obtain ⟨run,returned,actualHead,actualChain,actualLast,label,data,finiteStore,length⟩ :=
    Inline.actual_return_trace (fun _ : Unit=>clearLabel phase) (nextLabel phase)
      (Clear.program (clearRole target phase)) (program target) (clear_agrees target phase)
      old (⟨some (),store,contents⟩ : Clear.State)
      (⟨none,none,Function.update contents (clearRole target phase) []⟩ : Clear.State)
      saved head chain last halt
  refine ⟨run,returned,actualHead,actualChain,actualLast,label,finiteStore,data,?_⟩
  rw [length]
  exact time

def cellCfg (saved : Option Bool) (source : ResultCell.State) : State :=
  StoreIso.cfg (Equiv.prodComm _ _) (Inline.cfg cellLabel (clearLabel 3) saved source)

theorem cell_edge (target : Register) (before final : ResultCell.State) (saved : Option Bool)
    (edge : TM2.step (ResultCell.program target) before=some final) :
    TM2.step (program target) (cellCfg saved before)=some (cellCfg saved final) := by
  rcases before with ⟨label,finiteStore,contents⟩
  cases label with
  | none => cases edge
  | some label =>
    have actual : TM2.stepAux (ResultCell.program target label) finiteStore contents=final := Option.some.inj edge
    change some (TM2.stepAux (StoreIso.statement (Equiv.prodComm _ _)
      (Inline.statement cellLabel (clearLabel 3) (ResultCell.program target label))) (saved,finiteStore) contents)=_
    have reordered : TM2.stepAux (StoreIso.statement (Equiv.prodComm _ _)
        (Inline.statement cellLabel (clearLabel 3) (ResultCell.program target label))) (saved,finiteStore) contents=
        StoreIso.cfg (Equiv.prodComm _ _)
          (TM2.stepAux (Inline.statement cellLabel (clearLabel 3) (ResultCell.program target label)) (finiteStore,saved) contents) :=
      StoreIso.stepAux_map (Equiv.prodComm _ _)
        (Inline.statement cellLabel (clearLabel 3) (ResultCell.program target label)) (finiteStore,saved) contents
    rw [reordered,Inline.stepAux_map,actual]
    rfl

end PDROC.BitVM.Kernel.RawWrite

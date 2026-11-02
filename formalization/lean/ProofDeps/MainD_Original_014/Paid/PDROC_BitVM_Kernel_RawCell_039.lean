module

public import Paid.PDROC_BitVM_Kernel_RawPrepare_037

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawWrite

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

theorem physical_frame (target : Register) (initial final : Stack → List Bool)
    (frame : ∀ role,role ≠ 0 → role ≠ 25 → role ≠ 29 → role ≠ 1 →
      final (ResultCell.embedding target role)=initial (ResultCell.embedding target role)) :
    ∀ role,role ≠ 0 → role ≠ 25 → role ≠ 29 → role ≠ registerSlot target → final role=initial role := by
  intro role not0 not25 not29 notTarget
  let oldRole := (ResultCell.permutation target).symm role
  have image : ResultCell.embedding target oldRole=role := (ResultCell.permutation target).apply_symm_apply role
  have old0 : oldRole ≠ 0 := by
    intro same
    apply not0
    exact image.symm.trans ((congrArg (ResultCell.embedding target) same).trans (ResultCell.fixed0 target))
  have old25 : oldRole ≠ 25 := by
    intro same
    apply not25
    exact image.symm.trans ((congrArg (ResultCell.embedding target) same).trans (ResultCell.fixed25 target))
  have old29 : oldRole ≠ 29 := by
    intro same
    apply not29
    exact image.symm.trans ((congrArg (ResultCell.embedding target) same).trans (ResultCell.fixed29 target))
  have old1 : oldRole ≠ 1 := by
    intro same
    apply notTarget
    exact image.symm.trans ((congrArg (ResultCell.embedding target) same).trans (ResultCell.target_image target))
  have same := frame oldRole old0 old25 old29 old1
  simpa only [image] using same

/-- Actual scanner/drain call inside the fixed writer. The quotient or
rational value is only the postcondition describing the real input Cell.
The original readonly bank1 is preserved by the fixed permutation frame. -/
theorem cell_call (target : Register) (value : Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (store : ResultCell.Store) (saved : Option Bool)
    (input : contents 0=encodeCellBits value++suffix) (ticks : contents 24=[]) (capture : contents 29=[])
    (oldTarget : contents (registerSlot target)=[]) :
    ∃ (run : List State) (returned : State),
      run.head?=some (cellCfg saved (ResultCell.before contents store)) ∧
      run.IsChain (fun a b=>TM2.step (program target) a=some b) ∧
      run.getLast?=some returned ∧ returned.l=some (clearLabel 3) ∧ returned.var=(saved,(none,store.2)) ∧
      returned.stk (registerSlot target)=encodeCellBits value ∧ returned.stk 0=suffix ∧
      returned.stk 24=[] ∧ returned.stk 29=[] ∧ run.length ≤ 2*(encodeCellBits value).length+10 ∧
      (∀ role,role ≠ 0 → role ≠ 25 → role ≠ 29 → role ≠ registerSlot target → returned.stk role=contents role) ∧
      returned.stk 25=(encodeCellBits value).reverse++contents 25 := by
  obtain ⟨old,oldLast,head,chain,last,_halt,label,finiteStore,word,remaining,empty29,time,frame,data⟩ :=
    ResultCell.runs target value suffix contents store input ticks capture oldTarget
  have allFrame := physical_frame target contents oldLast.stk frame
  have targetNot24 : (24 : Stack) ≠ registerSlot target := by cases target <;> decide
  have empty24 : oldLast.stk 24=[] :=
    (allFrame 24 (by decide) (by decide) (by decide) targetNot24).trans ticks
  have archive : oldLast.stk 25=(encodeCellBits value).reverse++contents 25 := by
    have observed := congrFun data (25 : Stack)
    change oldLast.stk (ResultCell.embedding target 25)=_ at observed
    rw [ResultCell.fixed25] at observed
    simpa only [PDROC.BitVM.Log.BankField.result,PDROC.BitVM.Log.BankDrain.drained,
      Function.update_of_ne (by decide : (25 : Stack) ≠ PDROC.BitVM.Log.BankDrain.bankSlot 0),
      Function.update_of_ne (by decide : (25 : Stack) ≠ 29),PDROC.BitVM.Log.BankCell.captured,
      Function.update_self,Lift.slots,ResultCell.fixed25] using observed
  refine ⟨old.map (cellCfg saved),cellCfg saved oldLast,?_,?_,?_,?_,?_,word,remaining,empty24,empty29,?_,allFrame,archive⟩
  · simp only [List.head?_map,head,Option.map_some]
  · exact List.isChain_map_of_isChain _ (fun a b edge=>cell_edge target a b saved edge) chain
  · simp only [List.getLast?_map,last,Option.map_some]
  · change some (oldLast.l.map cellLabel |>.getD (clearLabel 3))=some (clearLabel 3)
    rw [label]
    rfl
  · change (saved,oldLast.var)=(saved,(none,store.2))
    rw [finiteStore]
  · simpa only [List.length_map] using time

end PDROC.BitVM.Kernel.RawWrite

module

public import Paid.PDROC_BitVM_Log_BankField_045
public import Paid.PDROC_BitVM_Kernel_Register_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.ResultCell

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

abbrev Label := PDROC.BitVM.Log.BankField.Label
abbrev Store := PDROC.BitVM.Log.BankField.Store
abbrev State := TM2.Cfg Alphabet Label Store

/-- Compile-time slot renaming reuses the actual bank Cell scanner/drain
for an original destination register. It fixes all four parser work roles. -/
def permutation (target : Register) : Stack ≃ Stack := Equiv.swap 1 (registerSlot target)
def embedding (target : Register) : Stack ↪ Stack := (permutation target).toEmbedding

theorem target_image (target : Register) : embedding target 1=registerSlot target :=
  Equiv.swap_apply_left _ _

theorem fixed0 (target : Register) : embedding target 0=0 := by cases target <;> decide
theorem fixed24 (target : Register) : embedding target 24=24 := by cases target <;> decide
theorem fixed25 (target : Register) : embedding target 25=25 := by cases target <;> decide
theorem fixed29 (target : Register) : embedding target 29=29 := by cases target <;> decide

def program (target : Register) := Lift.machine (embedding target) (PDROC.BitVM.Log.BankField.program 0)
def before (contents : Stack → List Bool) (store : Store) : State :=
  ⟨some PDROC.BitVM.Log.BankField.startLabel,store,contents⟩

/-- The caller must really clear old destination, ticks and capture first.
No q, field width or result enters the machine. The actual parser reads
the Cell prefix after RawResult031's real singleton-header removal. -/
theorem runs (target : Register) (value : Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (store : Store)
    (input : contents 0=encodeCellBits value++suffix) (ticks : contents 24=[]) (capture : contents 29=[])
    (oldTarget : contents (registerSlot target)=[]) :
    ∃ (run : List State) (final : State),
      run.head?=some (before contents store) ∧
      run.IsChain (fun a b=>TM2.step (program target) a=some b) ∧
      run.getLast?=some final ∧ TM2.step (program target) final=none ∧
      final.l=none ∧ final.var=(none,store.2) ∧
      final.stk (registerSlot target)=encodeCellBits value ∧ final.stk 0=suffix ∧ final.stk 29=[] ∧
      run.length ≤ 2*(encodeCellBits value).length+10 ∧
      (∀ role,role ≠ 0 → role ≠ 25 → role ≠ 29 → role ≠ 1 →
        final.stk (embedding target role)=contents (embedding target role)) ∧
      Lift.slots (embedding target) final.stk=
        PDROC.BitVM.Log.BankField.result 0 value suffix (Lift.slots (embedding target) contents) := by
  have viewInput : (Lift.slots (embedding target) contents) 0=encodeCellBits value++suffix := by
    simpa only [Lift.slots,fixed0] using input
  have viewTicks : (Lift.slots (embedding target) contents) 24=[] := by
    simpa only [Lift.slots,fixed24] using ticks
  have viewCapture : (Lift.slots (embedding target) contents) 29=[] := by
    simpa only [Lift.slots,fixed29] using capture
  obtain ⟨old,oldLast,head,chain,last,halt,label,saved,data,time⟩ :=
    PDROC.BitVM.Log.BankField.runs 0 value suffix (Lift.slots (embedding target) contents) store
      viewInput viewTicks viewCapture
  cases old with
  | nil => simp only [List.head?_nil,reduceCtorEq] at head
  | cons start rest =>
    have initial : start=⟨some PDROC.BitVM.Log.BankField.startLabel,store,Lift.slots (embedding target) contents⟩ :=
      Option.some.inj head
    subst start
    obtain ⟨posts,final,length,actual,actualLast,view,_outside⟩ :=
      Lift.path (embedding target) (PDROC.BitVM.Log.BankField.program 0) (before contents store)
        ⟨some PDROC.BitVM.Log.BankField.startLabel,store,Lift.slots (embedding target) contents⟩
        oldLast rest rfl chain last
    refine ⟨before contents store::posts,final,rfl,actual,actualLast,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · apply Lift.halt_project (embedding target) (PDROC.BitVM.Log.BankField.program 0) final
      rw [view]
      exact halt
    · exact (congrArg TM2.Cfg.l view).trans label
    · exact (congrArg TM2.Cfg.var view).trans saved
    · have observed := (congrArg (fun state : PDROC.BitVM.Log.BankField.State=>
        state.stk (PDROC.BitVM.Log.BankDrain.bankSlot 0)) view).trans (congrFun data _)
      rw [PDROC.BitVM.Log.BankField.result_bank] at observed
      change final.stk (embedding target 1)=encodeCellBits value++contents (embedding target 1) at observed
      rw [target_image,oldTarget,List.append_nil] at observed
      exact observed
    · have observed := (congrArg (fun state : PDROC.BitVM.Log.BankField.State=>state.stk 0) view).trans (congrFun data 0)
      rw [PDROC.BitVM.Log.BankField.result_input] at observed
      simpa only [Lift.cfg,Lift.slots,fixed0] using observed
    · have observed := (congrArg (fun state : PDROC.BitVM.Log.BankField.State=>state.stk 29) view).trans (congrFun data 29)
      change final.stk (embedding target 29)=PDROC.BitVM.Log.BankField.result 0 value suffix
        (Lift.slots (embedding target) contents) 29 at observed
      rw [fixed29] at observed
      refine observed.trans ?_
      simp only [PDROC.BitVM.Log.BankField.result,PDROC.BitVM.Log.BankDrain.drained,
        Function.update_of_ne (by decide : (29 : Stack) ≠ PDROC.BitVM.Log.BankDrain.bankSlot 0),
        Function.update_self]
    · simp only [List.length_cons,length] at time ⊢
      exact time
    · intro role not0 not25 not29 not1
      have observed := (congrArg (fun state : PDROC.BitVM.Log.BankField.State=>state.stk role) view).trans (congrFun data role)
      have notBank : role ≠ PDROC.BitVM.Log.BankDrain.bankSlot 0 := not1
      simpa only [Lift.cfg,Lift.slots,PDROC.BitVM.Log.BankField.result,PDROC.BitVM.Log.BankDrain.drained,
        PDROC.BitVM.Log.BankCell.captured,Function.update_of_ne notBank,
        Function.update_of_ne not29,Function.update_of_ne not25,Function.update_of_ne not0] using observed
    · exact (congrArg (fun state : PDROC.BitVM.Log.BankField.State=>state.stk) view).trans data

theorem supports (target : Register) : TM2.Supports (program target) (Finset.univ : Finset Label) :=
  Lift.supports (embedding target) (PDROC.BitVM.Log.BankField.program 0) _
    (PDROC.BitVM.Log.BankField.supports 0)

end PDROC.BitVM.Kernel.ResultCell

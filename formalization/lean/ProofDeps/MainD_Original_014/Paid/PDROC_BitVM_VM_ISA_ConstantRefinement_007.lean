module

public import Paid.PDROC_BitVM_VM_ISA_Frame_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.ISA

open Turing PaperProofs.Paid.Computation

theorem constant_step (backend : RatBackend) (core : Bool) (target : Register) (value : Cell) :
    StepRefinement backend core ⟨.constant target value,rfl⟩ := by
  intro input logical next events contents _size ready success
  have specified : Instruction.execute input (.constant target value) logical =
      some (({logical with pc := logical.pc+1}).set target value) := rfl
  have same : next = ({logical with pc := logical.pc+1}).set target value :=
    Option.some.inj (success.symm.trans specified)
  subst next
  obtain ⟨after,run,final,original,head,chain,last,halt,registers,_spare,_time,frame⟩ :=
    Kernel.RegisterGlobal.constant_instruction_runs input logical
      (⟨some (),none,contents⟩ : TM2.Cfg Alphabet Unit (Option Bool)) target value none rfl rfl
      ready.registers (ready.workspace 31 (Or.inr (by decide)))
  have afterSame : after = ({logical with pc := logical.pc+1}).set target value :=
    Option.some.inj (original.symm.trans specified)
  subst after
  refine ⟨run,final,⟨head,chain,last,halt⟩,?_⟩
  have observed : Source.Observables input (({logical with pc := logical.pc+1}).set target value) events final.stk := by
    apply observables_register_from_frame input logical _ events contents final.stk ready.toObservables registers rfl rfl rfl
    intro role safe
    apply frame
    intro index
    fin_cases index
    · exact protected_not_zero role safe
    · exact protected_not_register role safe target
    · exact protected_not_work role 31 safe (by decide)
  simpa [Log.eventOf] using observed

theorem constant_resources (backend : RatBackend) (core : Bool) (target : Register) (value : Cell) :
    ResourceRefinement backend core ⟨.constant target value,rfl⟩ := by
  refine ⟨3,1,by decide,by decide,?_⟩
  intro input logical next events contents _size ready _success
  obtain ⟨after,run,final,_original,head,chain,last,halt,_registers,_spare,time,_frame⟩ :=
    Kernel.RegisterGlobal.constant_instruction_runs input logical
      (⟨some (),none,contents⟩ : TM2.Cfg Alphabet Unit (Option Bool)) target value none rfl rfl
      ready.registers (ready.workspace 31 (Or.inr (by decide)))
  refine ⟨run,final,⟨head,chain,last,halt⟩,?_⟩
  have width := Kernel.NatInstruction.dataSize_each contents (Kernel.RegisterGlobal.registerSlot target)
  rw [ready.registers target] at width
  have numerical : (encodeCellBits (logical.register target)).length+2 ≤
      3*(Kernel.NatInstruction.dataSize contents+(encodeBits input).length+1)^1 := by
    simp only [pow_one]
    omega
  exact time.le.trans numerical

end PDROC.BitVM.VM.ISA

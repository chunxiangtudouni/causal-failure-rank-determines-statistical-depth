module

public import Paid.PDROC_BitVM_Kernel_Register_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.Nop

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

abbrev State := TM2.Cfg Alphabet Unit Unit

/-- One real no-write callee step, reused for the compile-time
same-register move case. The surrounding original-PC successor is paid
by the actual caller, just as for every other returning source opcode. -/
def program (_ : Unit) : TM2.Stmt Alphabet Unit Unit := .halt

def after (logical : PaperProofs.Paid.Computation.State) := {logical with pc:=logical.pc+1}

theorem move_same_execute (input : List Cell) (logical : PaperProofs.Paid.Computation.State) (reg : Register) :
    Instruction.execute input (.move reg reg) logical=some (after logical) := by
  simp [Instruction.execute,PaperProofs.Paid.Computation.State.set,Function.update_eq_self,after]

theorem move_same_runs (input : List Cell) (logical : PaperProofs.Paid.Computation.State) (reg : Register)
    (contents : Stack → List Bool)
    (represented : ∀ source,contents (registerSlot source)=encodeCellBits (logical.register source)) :
    ∃ (run : List State) (final : State),
      Instruction.execute input (.move reg reg) logical=some (after logical) ∧
      run.head?=some (⟨some (),(),contents⟩ : State) ∧
      run.IsChain (fun a b=>TM2.step program a=some b) ∧
      run.getLast?=some final ∧ TM2.step program final=none ∧
      RegistersRepresent (after logical) final ∧ final.stk=contents ∧ run.length=2 := by
  let start : State := ⟨some (),(),contents⟩
  let final : State := ⟨none,(),contents⟩
  have edge : TM2.step program start=some final := rfl
  refine ⟨[start,final],final,move_same_execute input logical reg,rfl,?_,rfl,rfl,represented,rfl,rfl⟩
  exact List.isChain_cons_cons.mpr ⟨edge,List.isChain_singleton _⟩

theorem supports : TM2.Supports program (Finset.univ : Finset Unit) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    cases label
    trivial

end PDROC.BitVM.Kernel.Nop

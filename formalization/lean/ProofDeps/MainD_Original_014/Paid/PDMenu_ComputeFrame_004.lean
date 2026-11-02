module

public import Paid.PDMenu_ComputeFrame_003
public import Paid.PDLower_CalibrationCompute_Linear_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDMenu.ComputeFrame

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)

def StraightInstruction : Instruction → Prop
  | .branchZero _ _ _ | .jump _ | .jumpIndirect _ | .halt => False
  | _ => True

def StraightCode (code : List Instruction) : Prop := ∀ instruction ∈ code, StraightInstruction instruction

theorem execute_pc_succ (instruction : Instruction) (hstraight : StraightInstruction instruction)
    (input : List Cell) (before after : State) (hrun : instruction.execute input before=some after) :
    after.pc=before.pc+1 := by
  cases instruction <;> simp_all [StraightInstruction,Instruction.execute,State.set,Option.bind_eq_some_iff] <;> grind

theorem linearExecute_pc (input : List Cell) (code : List Instruction) (hstraight : StraightCode code)
    (before after : State) (hrun : linearExecute input code before=some after) :
    after.pc=before.pc+code.length := by
  induction code generalizing before with
  | nil =>
      have he : before=after := by simpa only [linearExecute,Option.some.injEq] using hrun
      subst after
      rfl
  | cons instruction code ih =>
      obtain ⟨middle, hfirst, hlater⟩ := Option.bind_eq_some_iff.mp hrun
      have hp := execute_pc_succ instruction (hstraight instruction (by simp)) input before middle hfirst
      have ht := ih (fun i hm => hstraight i (by simp only [List.mem_cons]; exact Or.inr hm)) middle hlater
      simp only [List.length_cons]
      omega

theorem time_le_length (program : Program) (trace : List State) : time program trace ≤ 15*trace.length := by
  induction trace with
  | nil => simp [time,primitiveTrace]
  | cons state trace ih =>
      calc
        _ = time program [state]+time program trace := time_append _ _ _
        _ ≤ 15+15*trace.length := Nat.add_le_add (time_singleton_le _ _) ih
        _ = 15*(state::trace).length := by simp only [List.length_cons]; ring

end PDMenu.ComputeFrame

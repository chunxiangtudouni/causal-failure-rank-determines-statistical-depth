module

public import Paid.PDLower_CalibrationCompute_Bootstrap_015
public import Paid.PDROC_CalibrationRow_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

@[expose] public section

open PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem all_basicBlock_nonreleasing (label : Label) :
    (basicBlock label).body.all PDROC.CalibrationRow.noRelease=true := by
  cases label <;> rfl

theorem control_nonreleasing (origin : ℕ) (control : Control) :
    PDROC.CalibrationRow.noRelease (controlInstruction origin control)=true := by
  cases control <;> rfl

theorem compiledBlock_nonreleasing (origin : ℕ) (label : Label) :
    ∀ instruction∈compiledBlock origin label,PDROC.CalibrationRow.noRelease instruction=true := by
  intro instruction member
  rw [compiledBlock,List.mem_append,List.mem_singleton] at member
  rcases member with body|equal
  · exact List.all_eq_true.mp (all_basicBlock_nonreleasing label) instruction body
  · subst instruction
    exact control_nonreleasing origin (basicBlock label).control

theorem kernel_nonreleasing (origin : ℕ) :
    ∀ instruction∈(kernel origin).toList,PDROC.CalibrationRow.noRelease instruction=true := by
  intro instruction member
  rw [kernel,List.toList_toArray] at member
  obtain ⟨label,_inside,body⟩ := List.mem_flatMap.mp member
  exact compiledBlock_nonreleasing origin label instruction body

theorem bootstrap_nonreleasing (origin : ℕ) :
    (bootstrap origin).toList.all PDROC.CalibrationRow.noRelease=true := rfl

/-- A syntactic fact about the ONE actual program chosen before every
original paper input. Together with the reusable real-ISA live-mono
lemma this will justify peak space from final footprint. No operand-bit
monotonicity is asserted. The generic live-mono proof stays with Row013. -/
theorem calibrate_toList_nonreleasing :
    calibrate.toList.all (fun instruction => match instruction with
      | .release _ => false
      | _ => true)=true := by
  apply List.all_eq_true.mpr
  intro instruction member
  have singleton : (#[Instruction.jump mainStart] : Program).toList=[.jump mainStart] := rfl
  unfold calibrate at member
  rw [Array.toList_append,Array.toList_append,singleton] at member
  rcases List.mem_append.mp member with earlier|boot
  · rcases List.mem_append.mp earlier with first|body
    · have equal := List.mem_singleton.mp first
      subst instruction
      rfl
    · exact kernel_nonreleasing 1 instruction body
  · exact List.all_eq_true.mp (bootstrap_nonreleasing mainStart) instruction boot

end PDLower.CalibrationCompute

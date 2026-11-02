module

public import Paid.PDLower_CalibrationCompute_NoRelease_065
public import Paid.PDLower_CalibrationCompute_MonotoneSpace_064
public import Paid.PDROC_CalibrationRow_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- The fixed actual standalone calibration program satisfies the real
per-step live monotonicity hypothesis. It is not supplied by a caller. -/
theorem step_live_mono_of_all (program : Program) (input : List Cell) (before after : State)
    (nonreleasing : program.toList.all (fun instruction => match instruction with
      | .release _ => false
      | _ => true)=true)
    (executed : step program input before=some after) : before.live⊆after.live := by
  have predicates : (fun instruction : Instruction => match instruction with
      | .release _ => false | _ => true) = PDROC.CalibrationRow.noRelease := by
    funext instruction
    cases instruction <;> rfl
  have safeProgram : program.toList.all PDROC.CalibrationRow.noRelease=true := by
    rw [←predicates]
    exact nonreleasing
  obtain ⟨instruction,fetched,actual⟩ := Option.bind_eq_some_iff.mp executed
  have inArray : instruction∈program := Array.mem_of_getElem? (xs:=program) (i:=before.pc) fetched
  have member : instruction∈program.toList := (Array.mem_toList_iff (xs:=program)).mpr inArray
  have safe : PDROC.CalibrationRow.noRelease instruction=true :=
    List.all_eq_true.mp safeProgram instruction member
  exact PDROC.CalibrationRow.execute_live_mono instruction input before after safe actual

theorem calibrate_step_live_mono (input : List Cell) (before after : State)
    (executed : step calibrate input before=some after) : before.live⊆after.live :=
  step_live_mono_of_all calibrate input before after calibrate_toList_nonreleasing executed

/-- All genuine prefix record counts are bounded by the actual final
record count, for this original fixed program and every readonly input.
This theorem does not assert termination, final footprint, or bit size. -/
theorem calibrate_peakCells_le_final (input : List Cell) (trace : List State) (final : State)
    (chain : trace.IsChain (fun a b => step calibrate input a=some b)) (last : trace.getLast?=some final) :
    peakCells trace≤workingCells final :=
  chain_peakCells_le_final calibrate input (calibrate_step_live_mono input) trace final chain last

theorem calibrate_standalone_record_bound (input : List Cell) (trace : List State)
    (before final : State) (base M : ℕ) (extra : List Cell)
    (chain : trace.IsChain (fun a b => step calibrate input a=some b)) (last : trace.getLast?=some final)
    (frame : Frame before final base M) (output : final.output=before.output++extra)
    (inputRecords : workingCells before≤registers.length+rowWidth M) (length : extra.length≤rowWidth M) :
    peakCells trace≤38*(M+1) :=
  chain_standalone_record_bound calibrate input (calibrate_step_live_mono input) trace before final base M extra
    chain last frame output inputRecords length

end PDLower.CalibrationCompute

module
public import Structure.B23_5_RawInit_ReverseLoop008

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ReverseLoop
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005

theorem cost_bound (higher output remaining : Nat) :
    cost higher output remaining ≤
      remaining*(4*(higher+remaining)+67*(output+remaining)+120)+3 := by
  induction remaining generalizing higher output with
  | zero => simp [cost]
  | succ remaining ih =>
    have bound := ih (higher+1) (output+1)
    simp only [cost]
    nlinarith

theorem actual_with_resources (remaining higher output : List Bool) (gap inputLength : Nat) :
    ∃ path, RunsFrom machine (state remaining higher gap output) path
        (finish (remaining.reverse++higher) gap (output++remaining)) ∧
      path.length ≤ 200*(remaining.length+higher.length+output.length+gap+1)^2 ∧
      ∀ clock, visitedSpace machine inputLength (path.take clock)≤
        inputLength+400*(remaining.length+higher.length+output.length+gap+1)^2+1 := by
  obtain ⟨path,run,time⟩ := actual remaining higher output gap
  have costBound := cost_bound higher.length output.length remaining.length
  have timeBound : path.length≤200*(remaining.length+higher.length+output.length+gap+1)^2 := by
    rw [time]
    nlinarith [Nat.zero_le (higher.length*output.length),
      Nat.zero_le (higher.length*gap),Nat.zero_le (output.length*gap),
      Nat.zero_le (higher.length^2),Nat.zero_le (output.length^2),Nat.zero_le (gap^2)]
  refine ⟨path,run,timeBound,?_⟩
  intro clock
  have cells := PSTRTMTrace002.visitedSpace_le machine inputLength (path.take clock)
  have take := (List.length_take_le' clock path).trans timeBound
  omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ReverseLoop

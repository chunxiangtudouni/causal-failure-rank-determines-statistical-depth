module
public import PaperProofs.Common.PSTR_TM_Increment_009

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSuffix011
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMIncrement009

/-- One genuine one-digit operand, a SINGLE false separator, and a suffix
beginning true. The separator/suffix form an additional zero digit 01. -/
def unpaddedInput : List Bool := blocks [true] ++ [false, true]

def requiredFramedOutput : List Bool := blocks (bumpDigits [true]) ++ [false, true]

def actualFinal : MachineState 14 := state 14 [false] (blocks (bumpDigits [true, false]))

/-- This is an actual deterministic run of the fixed Bool incrementer. -/
theorem unpadded_actual_run :
    Runs incrementMachine unpaddedInput (computeTrace 0 [true, false]) actualFinal := by
  exact increment_runs [true, false]

theorem unpadded_wrong_output : actualFinal.Tape.right₀ ≠ Turing.ListBlank.mk requiredFramedOutput := by
  intro h
  have hbit := congrArg (fun tape : Turing.ListBlank Bool => tape.nth 5) h
  simp [actualFinal, state, Turing.Tape.mk₂,
    requiredFramedOutput, blocks, bumpDigits] at hbit

/-- No time/space allowance fixes this formatting error. This refutes ONLY
unpadded direct concatenation, not original B23 or a padded/isolated solver. -/
theorem unpadded_no_computes (time space : Nat) :
    ¬ computes incrementMachine unpaddedInput requiredFramedOutput time space := by
  rintro ⟨trace, final, hrun, hout, _, _⟩
  have heq : final = actualFinal := Part.mem_unique hrun.2.2.2.2 unpadded_actual_run.2.2.2.2
  subst final
  exact unpadded_wrong_output hout

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSuffix011


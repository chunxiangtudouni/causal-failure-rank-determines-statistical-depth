module

public import Structure.RootB23_Threshold_OutputArithmetic_Target_001
public import Structure.RootB23_Threshold_Window_CounterCopies_010

/-! One actual tape contains both contiguous original output fields.
The copied B is first backed up by the frozen nearest-field copy; after
the target writer the existing real return/splice tail serializes that B.
The external archive and its actual owned prefix cells remain unchanged. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace RootB23.Threshold.OutputArithmetic.Pair
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

def output (n : Nat) : List Bool := encodeDatum (.natural n) ++ encodeDatum (.rational (Target.value n))

def frontCode : Machine 687 := PSTRTMSeq005.seqMachine counterCopyMachine Target.code

def code : Machine 733 := PSTRTMSeq005.seqMachine frontCode BTarget.tailMachine

theorem tail_bounded (archive : List Bool) (n : Nat) :
    BoundedRun BTarget.tailMachine
      (Tape.mk₂ (false :: PA17TMRatArithmeticCopy006.sourceLeft archive (PSTRTMNatValue017.rawPayload n))
        (encodeDatum (.rational (Target.value n)))) 45
      (Tape.mk₂ (false :: archive) (output n)) (128 * (natBits n + 1) ^ 2) := by
  let digits := PSTRTMNatValue017.rawPayload n
  have entry : Tape.mk₂ (false :: PA17TMRatArithmeticCopy006.sourceLeft archive digits)
      (encodeDatum (.rational (Target.value n))) =
      Tape.mk₂ (false :: false :: PSTRTMThresholdBackupReturn227.sourceLeft archive digits)
        (true :: Target.tail n) := by rw [Target.true_tag]; rfl
  have returned : BoundedRun PSTRTMThresholdBackupReturn227.returnMachine
      (Tape.mk₂ (false :: PA17TMRatArithmeticCopy006.sourceLeft archive digits)
        (encodeDatum (.rational (Target.value n)))) 6
      (Tape.mk₂ (false :: archive)
        (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: Target.tail n))
      (2 * digits.length + 6) := by
    have run := PSTRTMThresholdBackupReturn227.return_runsFrom archive digits (true :: Target.tail n)
    have last : PSTRTMThresholdBackupReturn227.returnFinal archive digits (true :: Target.tail n) =
        ⟨6, Tape.mk₂ (false :: archive)
          (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: Target.tail n)⟩ := rfl
    rw [last] at run
    rw [entry]
    exact ⟨PSTRTMThresholdBackupReturn227.returnTrace archive digits (true :: Target.tail n), run,
      by rw [PSTRTMThresholdBackupReturn227.return_length]⟩
  have spliced := NatSplice.splice_bounded n (false :: archive) (Target.tail n)
  have combined := returned.seq spliced
  have port : PSTRTMSeq005.rightLabel (a := 6) (38 : Fin 39) = (45 : Fin 46) := by decide
  rw [port, ← Target.true_tag] at combined
  have length : digits.length = natBits n := by simp only [digits, PSTRTMNatValue017.rawPayload, List.length_ofFn]
  have fee : (2 * digits.length + 6) + 64 * (natBits n + 1) ^ 2 ≤ 128 * (natBits n + 1) ^ 2 := by
    rw [length]
    nlinarith only [Nat.zero_le (natBits n ^ 2)]
  exact combined.mono fee

private theorem copy_fee (bits : Nat) : 4 * bits ^ 2 + 22 * bits + 21 ≤ 64 * (bits + 1) ^ 2 := by
  nlinarith only [Nat.zero_le (bits ^ 2)]

/-- Complete copied-B DATA -> adjacent Nat B / canonical target Rat.
No caller room, saved B oracle, width, branch bit or source run is given.
Every first/footer/tag write and HALT transfer belongs to this same code. -/
theorem bounded (archive : List Bool) (n : Nat) :
    BoundedRun code
      (Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n))) 733
      (Tape.mk₂ (false :: archive) (output n)) (8192 * (natBits n + 1) ^ 2) := by
  have copied := counterCopy_bounded archive (PSTRTMNatValue017.rawPayload n)
  have copied' : BoundedRun counterCopyMachine
      (Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n))) 50
      (Tape.mk₂ (false :: PA17TMRatArithmeticCopy006.sourceLeft archive (PSTRTMNatValue017.rawPayload n))
        (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n)))
      (64 * (natBits n + 1) ^ 2) := by
    have cost := copied.mono (by
      simp only [PSTRTMNatValue017.rawPayload, List.length_ofFn]
      exact copy_fee (natBits n))
    simpa only [PA17TMRatArithmeticCopy006.workspace, copiedCounterLeft, Target.two_right_blanks] using cost
  have target := Target.bounded (PA17TMRatArithmeticCopy006.sourceLeft archive (PSTRTMNatValue017.rawPayload n)) n
  have final := tail_bounded archive n
  have combined := (copied'.seq target).seq final
  have port : PSTRTMSeq005.rightLabel (a := 687) (45 : Fin 46) = (733 : Fin 734) := by decide
  rw [port] at combined
  exact combined.mono (by omega)

theorem actual_contract (archive : List Bool) (n : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom code
      ⟨0, Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n))⟩ trace
      ⟨733, Tape.mk₂ (false :: archive) (output n)⟩ ∧
      trace.length ≤ 8192 * (natBits n + 1) ^ 2 ∧
      ∀ chargedLength clock, visitedSpace code chargedLength (trace.take clock) ≤
        chargedLength + 16384 * (natBits n + 1) ^ 2 + 1 := by
  obtain ⟨trace, run, time⟩ := bounded archive n
  refine ⟨trace, run, time, ?_⟩
  intro chargedLength clock
  have space := PSTRTMTrace002.visitedSpace_le code chargedLength (trace.take clock)
  have taken : (trace.take clock).length ≤ trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  omega

theorem output_length_le (n : Nat) : (output n).length ≤ 16 * (natBits n + 1) := by
  have width := Target.denominator_width n
  rw [output, Target.bits, PA17TMRatArithmeticPrefix5060.fragment_original_datum]
  simp only [encodeDatum, List.length_append, List.length_cons, List.length_nil,
    PSTRTMLength004.encodeNat_length]
  have unit : natBits 1 = 1 := by decide
  rw [unit]
  omega

end RootB23.Threshold.OutputArithmetic.Pair

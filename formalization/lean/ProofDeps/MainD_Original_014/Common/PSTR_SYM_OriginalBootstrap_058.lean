module

public import Common.PSTR_SYM_RawBootstrapRun_057

/-! SOURCEONLY. Fixed finite Bool original-input adapter for the actual
N/q bootstrap; this is staging, not symbolicOutput or original Full. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawBootstrap

open PaperProofs.Common Turing PSTRTMSeq005 PSTRSymbolicRelabel
open PSTRTMIncrement009 PSTRSymbolicCounter PSTRSymbolicPairedArchive

def bootSupport : Finset BootLabel := Finset.univ

noncomputable def bootstrapMachine : Machine bootSupport.card := finiteMachine bootstrapCode bootSupport

theorem bootstrap_supports : TM0.Supports bootstrapCode (bootSupport : Set BootLabel) := by
  simpa only [bootSupport,Finset.coe_univ] using TM0.univ_supports bootstrapCode

theorem bootstrap_polynomial (count stage tools : Nat) (suffix : List Bool) (room : 2 ≤ count) :
    ∃ (trace : List (MachineState bootSupport.card)) (final : MachineState bootSupport.card),
      Runs bootstrapMachine (bootstrapInput count stage tools suffix) trace final ∧
      final.Tape = bootstrapTape count stage tools suffix ∧
      valueDigits (afterTwo count) + 2 = count ∧
      trace.length ≤ 1024 * ((bootstrapInput count stage tools suffix).length + 1)^2 ∧
      ∀ clock, visitedSpace bootstrapMachine (bootstrapInput count stage tools suffix).length (trace.take clock) ≤
        4096 * ((bootstrapInput count stage tools suffix).length + 1)^2 := by
  obtain ⟨oldTrace,oldFinal,firstHead,chain,lastHead,_,tape,halt,time⟩ := actual_bootstrap count stage tools suffix room
  let bits := bootstrapInput count stage tools suffix
  have first : oldTrace.head? = some (TM0.init bits) := firstHead
  let trace := oldTrace.map (relabelCfg (finiteLabels bootSupport))
  let final := relabelCfg (finiteLabels bootSupport) oldFinal
  have actual := finite_runs bootstrapCode bootSupport bootstrap_supports bits oldTrace oldFinal first chain lastHead halt
  have parts : bits.length = (encodeNat count).length + (encodeDatum (.natural stage)).length +
      (encodeDatum (.natural tools)).length + suffix.length := by
    simp only [bits,bootstrapInput,List.length_append]
  have width : natBits count ≤ bits.length := by
    rw [PSTRTMLength004.encodeNat_length] at parts
    omega
  have stageLength : (encodeDatum (.natural stage)).length ≤ bits.length := by omega
  have toolLength : (encodeDatum (.natural tools)).length ≤ bits.length := by omega
  have countSquare := Nat.pow_le_pow_left (Nat.add_le_add_right width 1) 2
  have stageSquare := Nat.pow_le_pow_left (Nat.add_le_add_right stageLength 1) 2
  have toolSquare := Nat.pow_le_pow_left (Nat.add_le_add_right toolLength 1) 2
  have polynomial : oldTrace.length ≤ 1024 * (bits.length + 1)^2 := by
    nlinarith [Nat.zero_le ((bits.length + 1)^2)]
  have mappedLength : trace.length = oldTrace.length := List.length_map _
  refine ⟨trace,final,actual,tape,(two_count_rounds count room).2.2.1,?_,?_⟩
  · rw [mappedLength]
    exact polynomial
  · intro clock
    change visitedSpace bootstrapMachine bits.length (trace.take clock) ≤ 4096 * (bits.length + 1)^2
    have cells := PSTRTMTrace002.visitedSpace_le bootstrapMachine bits.length (trace.take clock)
    have takeLength : (trace.take clock).length ≤ oldTrace.length := by
      simp only [List.length_take,mappedLength]
      omega
    have inputRoom : bits.length + 1 ≤ (bits.length + 1)^2 := by nlinarith
    omega

def originalRemaining {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) : List Datum :=
  (rawInstance input ++ rawSet available).tail.tail

theorem original_bootstrap_bits {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) :
    CompactPrice.symbolicInput input available = bootstrapInput
      (rawInstance input ++ rawSet available).length I.stageCount I.toolCount
      ((originalRemaining input available).flatMap encodeDatum ++ [true]) := by
  unfold CompactPrice.symbolicInput encode bootstrapInput
  have fields : rawInstance input ++ rawSet available =
      .natural I.stageCount :: .natural I.toolCount :: originalRemaining input available := rfl
  have encoded := congrArg (fun data : List Datum => data.flatMap encodeDatum) fields
  rw [encoded]
  simp only [List.flatMap_cons,List.append_assoc]

theorem original_remaining_count {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) :
    valueDigits (afterTwo (rawInstance input ++ rawSet available).length) =
      (originalRemaining input available).length := by
  have counted := (two_count_rounds (rawInstance input ++ rawSet available).length
    (original_data_count_pos input available)).2.2.1
  have fields : rawInstance input ++ rawSet available =
      .natural I.stageCount :: .natural I.toolCount :: originalRemaining input available := rfl
  have length := congrArg List.length fields
  simp only [List.length_cons] at length
  omega

theorem original_bootstrap {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) :
    ∃ (trace : List (MachineState bootSupport.card)) (final : MachineState bootSupport.card),
      Runs bootstrapMachine (CompactPrice.symbolicInput input available) trace final ∧
      final.Tape = bootstrapTape (rawInstance input ++ rawSet available).length I.stageCount I.toolCount
        ((originalRemaining input available).flatMap encodeDatum ++ [true]) ∧
      valueDigits (afterTwo (rawInstance input ++ rawSet available).length) =
        (originalRemaining input available).length ∧
      trace.length ≤ 1024 * ((CompactPrice.symbolicInput input available).length + 1)^2 ∧
      ∀ clock, visitedSpace bootstrapMachine (CompactPrice.symbolicInput input available).length (trace.take clock) ≤
        4096 * ((CompactPrice.symbolicInput input available).length + 1)^2 := by
  obtain ⟨trace,final,actual,tape,_,time,cells⟩ := bootstrap_polynomial
    (rawInstance input ++ rawSet available).length I.stageCount I.toolCount
      ((originalRemaining input available).flatMap encodeDatum ++ [true]) (original_data_count_pos input available)
  rw [← original_bootstrap_bits input available] at actual time cells
  exact ⟨trace,final,actual,tape,original_remaining_count input available,time,cells⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawBootstrap

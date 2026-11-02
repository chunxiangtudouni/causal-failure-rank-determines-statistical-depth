module
public import Structure.PA17_TM_Division_Full_012a
public import Structure.PA17_TM_Division_FrontLayout_011a
public import Structure.PA17_TM_Division_Loop_002j

/-! Original-input whole-tape composition. The result lists describe the
actual shared kernel output; they are never code or inputs to either machine. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionFull012

open PA17TMDivisionFront007 PA17TMDivisionFrontLayout011
open PA17TMDivisionLoop002
open PSTRTMBinaryAdd024 PSTRTMIncrement009

def loopData (a b : Nat) : List Bool × List (Bool × Bool) :=
  loopValues (initialZeroMode (actualResident a b)) (originalBits a b).reverse [] (actualResident a b)

def resultBits (a b : Nat) : List Bool := (loopData a b).1

def resultResident (a b : Nat) : List (Bool × Bool) := (loopData a b).2

def resultArchive (a b : Nat) : List (Bool × Bool) := archiveFor [] (resultBits a b)

def kernelFinal (a b : Nat) : MachineState 577 :=
  phaseCfg 16 0 (loopTape [] (resultArchive a b) (resultResident a b) [])

def commonFinal (a b : Nat) : MachineState 995 :=
  PSTRTMSeq005.rightCfg (a := 417) (kernelFinal a b)

def commonTrace (a b : Nat) (kernelTrace : List (MachineState 577)) : List (MachineState 995) :=
  (frontTrace a b).map (PSTRTMSeq005.leftCfg (b := 577)) ++
    kernelTrace.map (PSTRTMSeq005.rightCfg (a := 417))

theorem commonTrace_length (a b : Nat) (kernelTrace : List (MachineState 577)) :
    (commonTrace a b kernelTrace).length = (frontTrace a b).length+kernelTrace.length := by
  change ((frontTrace a b).map (PSTRTMSeq005.leftCfg (a := 417) (b := 577)) ++
    kernelTrace.map (PSTRTMSeq005.rightCfg (a := 417) (b := 577))).length = _
  rw [List.length_append]
  exact congrArg₂ Nat.add (List.length_map (PSTRTMSeq005.leftCfg (a := 417) (b := 577)))
    (List.length_map (PSTRTMSeq005.rightCfg (a := 417) (b := 577)))

theorem archiveFor_done_firstValue (bits : List Bool) :
    firstValue (archiveFor [] bits) = valueDigits bits := by
  simp [archiveFor,firstValue,Function.comp_def]

theorem original_kernel (a b : Nat) :
    ∃ trace : List (MachineState 577),
      PSTRTMSeq005.RunsFrom loopMachine ⟨0,(frontFinal a b).Tape⟩ trace (kernelFinal a b) ∧
      valueDigits (resultBits a b) = a/b ∧
      firstValue (resultResident a b) = a%b ∧
      (resultBits a b).length = max (natBits a) (natBits b) ∧
      (resultResident a b).length = max (natBits a) (natBits b)+1 ∧
      trace.length ≤ 128*(max (natBits a) (natBits b)+1)^2 := by
  have width : (actualResident a b).length = (originalBits a b).length+1 := by
    rw [actualResident_length,originalBits_length]
  obtain ⟨trace,run,hq,hr,hql,hrl,_digits,ht,_space⟩ :=
    actual_kernel (originalBits a b) [] (actualResident a b) []
      (actualResident_firstValue a b) width
  have entry : phaseCfg 0 0 (loopTape [] (archiveFor (originalBits a b).reverse []) (actualResident a b) []) =
      (⟨0,(frontFinal a b).Tape⟩ : MachineState 577) := by
    rw [front_loop_tape]
    rfl
  rw [entry] at run
  refine ⟨trace,run,?_,?_,?_,?_,?_⟩
  · simpa only [resultBits,loopData,originalBits_value,actualResident_secondValue] using hq
  · simpa only [resultResident,loopData,originalBits_value,actualResident_secondValue] using hr
  · simpa only [resultBits,loopData,originalBits_length] using hql
  · simpa only [resultResident,loopData,actualResident_length] using hrl
  · simpa only [originalBits_length] using ht

theorem resultArchive_firstValue (a b : Nat) : firstValue (resultArchive a b) = a/b := by
  obtain ⟨_,_,hq,_,_,_,_⟩ := original_kernel a b
  rw [resultArchive,archiveFor_done_firstValue,hq]

theorem resultResident_firstValue (a b : Nat) : firstValue (resultResident a b) = a%b := by
  obtain ⟨_,_,_,hr,_,_,_⟩ := original_kernel a b
  exact hr

theorem common_runs_from_kernel (a b : Nat) (trace : List (MachineState 577))
    (run : PSTRTMSeq005.RunsFrom loopMachine ⟨0,(frontFinal a b).Tape⟩ trace (kernelFinal a b)) :
    Runs commonMachine (encodeNat a ++ encodeNat b) (commonTrace a b trace) (commonFinal a b) :=
  PSTRTMSeq005.seq_runs frontMachine loopMachine (encodeNat a ++ encodeNat b)
    (frontFinal a b) (kernelFinal a b) (frontTrace a b) trace (front_runs a b) run

theorem commonFinal_tape (a b : Nat) :
    (commonFinal a b).Tape =
      PA17TMDivisionCodec003.residentTape (resultArchive a b) (resultResident a b) := by
  change loopTape [] (resultArchive a b) (resultResident a b) [] = _
  exact loopTape_original_layout (resultArchive a b) (resultResident a b)

theorem resultArchive_length (a b : Nat)
    (h : (resultBits a b).length = max (natBits a) (natBits b)) :
    (resultArchive a b).length = max (natBits a) (natBits b) := by
  simpa only [resultArchive,archiveFor_length,List.length_nil,Nat.zero_add] using h

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionFull012

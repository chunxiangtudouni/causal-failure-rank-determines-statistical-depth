module

public import Structure.PA17_TM_Division_Loop_002i
public import Structure.PA17_TM_Division_KernelLift_009b
public import Structure.PA17_TM_Division_Bounds_008a

/-! Complete input-independent long-division kernel. The actual execution
recurses over the remaining source-bit list in the proof; no numeric fuel,
width, quotient, remainder or run witness is supplied to the machine. -/

@[expose] public section
set_option maxRecDepth 28000
set_option maxHeartbeats 2800000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002
open PA17TMDivisionCompose006 PA17TMDivisionKernelLift009
open PSTRTMBinaryAdd024 PSTRTMIncrement009

theorem remaining_segment (zeroMode : Bool) (remaining quotient context : List Bool)
    (resident : List (Bool × Bool)) (suffix : List Bool) :
    let final := loopValues zeroMode remaining quotient resident
    ∃ trace : List (MachineState 577),
      Segment loopMachine
        (phaseCfg (readPhase zeroMode) 0 (loopTape context (archiveFor remaining quotient) resident suffix)) trace
        (phaseCfg 16 0 (loopTape context (archiveFor [] final.1) final.2 suffix)) ∧
      trace.length ≤ remaining.length * (16*(remaining.length+quotient.length)+32*resident.length+42) +
        8*(remaining.length+quotient.length)+10 := by
  induction remaining generalizing quotient resident with
  | nil =>
    obtain ⟨trace,segment,length⟩ := exhausted_segment zeroMode quotient context resident suffix
    refine ⟨trace,segment,?_⟩
    simpa only [List.length_nil,Nat.zero_add,Nat.zero_mul] using length
  | cons bit later ih =>
    obtain ⟨round,hs,hl⟩ := round_segment zeroMode bit later quotient context resident suffix
    obtain ⟨tail,ht,hlt⟩ := ih (residentEmit zeroMode bit resident :: quotient) (residentNext zeroMode bit resident)
    have joined := splice_segment loopMachine _ _ _ round tail hs ht
    refine ⟨splice round tail,joined,?_⟩
    have hsum := splice_length loopMachine _ _ round tail hs
    simp only [List.length_cons,residentNext_length] at hlt ⊢
    nlinarith

/-- The initial equality/nonequality branch is read by actual finite
control. This run theorem needs no numeric correctness or no-overflow input. -/
theorem kernel_runsFrom (source context : List Bool) (resident : List (Bool × Bool)) (suffix : List Bool) :
    let final := loopValues (initialZeroMode resident) source.reverse [] resident
    ∃ trace : List (MachineState 577),
      PSTRTMSeq005.RunsFrom loopMachine
        (phaseCfg 0 0 (loopTape context (archiveFor source.reverse []) resident suffix)) trace
        (phaseCfg 16 0 (loopTape context (archiveFor [] final.1) final.2 suffix)) ∧
      trace.length ≤ PA17TMDivisionBounds008.loopBudget source.length resident.length := by
  obtain ⟨first,hfirst,hlfirst⟩ := initial_segment context (archiveFor source.reverse []) resident suffix
  obtain ⟨tail,htail,hltail⟩ := remaining_segment (initialZeroMode resident) source.reverse [] context resident suffix
  have joined := splice_segment loopMachine _ _ _ first tail hfirst htail
  refine ⟨splice first tail,segment_runsFrom loopMachine _ _ _ joined (done_halt _),?_⟩
  have hsum := splice_length loopMachine _ _ first tail hfirst
  simp only [List.length_reverse,List.length_nil,Nat.add_zero] at hltail
  unfold PA17TMDivisionBounds008.loopBudget
  omega

/-- One and the SAME genuine run certifies both original quotient and
remainder. The hypotheses describe the internal initializer output; final
original-input combination discharges them using actual Front007/Init004. -/
theorem actual_kernel (source context : List Bool) (resident : List (Bool × Bool)) (suffix : List Bool)
    (hr : firstValue resident = 0) (width : resident.length = source.length+1) :
    let final := loopValues (initialZeroMode resident) source.reverse [] resident
    ∃ trace : List (MachineState 577),
      PSTRTMSeq005.RunsFrom loopMachine
        (phaseCfg 0 0 (loopTape context (archiveFor source.reverse []) resident suffix)) trace
        (phaseCfg 16 0 (loopTape context (archiveFor [] final.1) final.2 suffix)) ∧
      valueDigits final.1 = valueDigits source / secondValue resident ∧
      firstValue final.2 = valueDigits source % secondValue resident ∧
      final.1.length = source.length ∧ final.2.length = resident.length ∧
      final.2.map Prod.snd = resident.map Prod.snd ∧
      trace.length ≤ 128*(source.length+1)^2 ∧
      ∀ inputLength : Nat, visitedSpace loopMachine inputLength trace ≤ inputLength+256*(source.length+1)^2+1 := by
  obtain ⟨trace,run,length⟩ := kernel_runsFrom source context resident suffix
  have data := loopValues_original_data source resident hr (by omega)
  have hquad := PA17TMDivisionBounds008.loopBudget_quadratic source.length
  rw [width] at length
  have ht : trace.length ≤ 128*(source.length+1)^2 := length.trans hquad
  refine ⟨trace,run,data.1,data.2.1,data.2.2.1,data.2.2.2.1,data.2.2.2.2,ht,?_⟩
  intro inputLength
  have hv := PSTRTMTrace002.visitedSpace_le loopMachine inputLength trace
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002

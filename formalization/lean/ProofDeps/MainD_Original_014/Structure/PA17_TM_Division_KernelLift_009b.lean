module
public import Structure.PA17_TM_Division_KernelLift_009a
public import Structure.PA17_TM_Division_KernelPort_010c

/-! Genuine one-bit long-division rounds. Numeric correctness is separate:
these traces follow the comparison HALT and work even with modular overflow. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionKernelLift009

open PA17TMDivisionLoop002 PA17TMDivisionCompose006
open PA17TMDivisionKernelPort010

def Span (first last : MachineState 577) (steps : Nat) : Prop :=
  ∃ trace, Segment loopMachine first trace last ∧ trace.length ≤ steps+1

theorem span_trans {first middle last : MachineState 577} {left right : Nat}
    (hx : Span first middle left) (hy : Span middle last right) : Span first last (left+right) := by
  obtain ⟨xs,hxs,hxl⟩ := hx
  obtain ⟨ys,hys,hyl⟩ := hy
  refine ⟨splice xs ys,splice_segment loopMachine first middle last xs ys hxs hys,?_⟩
  have hl := splice_length loopMachine first middle xs ys hxs
  omega

theorem span_mono {first last : MachineState 577} {left right : Nat}
    (h : Span first last left) (bound : left ≤ right) : Span first last right := by
  obtain ⟨trace,segment,length⟩ := h
  exact ⟨trace,segment,by omega⟩

theorem span_of_hop {first last : MachineState 577} {steps : Nat}
    (h : Hop first last (steps+1)) : Span first last steps := by
  obtain ⟨trace,segment,length⟩ := h
  exact ⟨trace,segment,by omega⟩

private theorem source_span (zeroMode bit : Bool) (remaining quotient context : List Bool)
    (resident : List (Bool × Bool)) (suffix : List Bool) :
    Span (phaseCfg (readPhase zeroMode) 0 (loopTape context (archiveFor (bit::remaining) quotient) resident suffix))
      (phaseCfg (shiftPhase zeroMode) (shiftEntry bit) (loopTape context (archiveFor (bit::remaining) quotient) resident suffix))
      (8*(1+remaining.length+quotient.length)+9) := by
  obtain ⟨trace,segment,length⟩ := source_bit_hop zeroMode bit remaining quotient context resident suffix
  exact ⟨trace,segment,by omega⟩

private theorem commit_span (phase nextRead : Fin 17) (emit : Bool)
    (heq : loopMachines phase = padMachine (by decide : 33 ≤ 33) (commitMachine emit))
    (port : loopPorts phase 26 = some (nextRead,0))
    (bit : Bool) (remaining quotient context : List Bool)
    (resident : List (Bool × Bool)) (suffix : List Bool) :
    Span (phaseCfg phase 0 (loopTape context (archiveFor (bit::remaining) quotient) resident suffix))
      (phaseCfg nextRead 0 (loopTape context (archiveFor remaining (emit::quotient)) resident suffix))
      (8*(1+remaining.length+quotient.length)+15) := by
  obtain ⟨trace,segment,length⟩ := commit_hop phase nextRead emit heq port bit remaining quotient context resident suffix
  exact ⟨trace,segment,by omega⟩

theorem initial_segment (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) :
    ∃ trace : List (MachineState 577),
      Segment loopMachine (phaseCfg 0 0 (loopTape context archive resident suffix)) trace
        (phaseCfg (readPhase (decide ((PSTRTMCompareCode054.resultRelation 0 resident).val = 0))) 0
          (loopTape context archive resident suffix)) ∧
      trace.length ≤ 8*resident.length+7 := by
  change Span _ _ (8*resident.length+6)
  by_cases hz : (PSTRTMCompareCode054.resultRelation 0 resident).val = 0
  · have hc := span_of_hop (steps := 4*resident.length+3) (compare0_hop context archive resident suffix)
    simp [compare0Target,hz] at hc
    have hb := span_of_hop (steps := 4*resident.length+3) (rewind1_hop context archive resident suffix)
    have h := span_mono (span_trans hc hb) (by omega : (4*resident.length+3)+(4*resident.length+3) ≤ 8*resident.length+6)
    simpa [readPhase,hz] using h
  · have hc := span_of_hop (steps := 4*resident.length+3) (compare0_hop context archive resident suffix)
    simp [compare0Target,hz] at hc
    have hb := span_of_hop (steps := 4*resident.length+3) (rewind2_hop context archive resident suffix)
    have h := span_mono (span_trans hc hb) (by omega : (4*resident.length+3)+(4*resident.length+3) ≤ 8*resident.length+6)
    simpa [readPhase,hz] using h

/-- Unconditional physical round: the emitted bit is the real compare's
decision. No divisor, arithmetic answer, no-overflow or room premise. -/
theorem round_segment (zeroMode bit : Bool) (remaining quotient context : List Bool)
    (resident : List (Bool × Bool)) (suffix : List Bool) :
    ∃ trace : List (MachineState 577),
      Segment loopMachine
        (phaseCfg (readPhase zeroMode) 0 (loopTape context (archiveFor (bit::remaining) quotient) resident suffix))
        trace
        (phaseCfg (readPhase zeroMode) 0
          (loopTape context (archiveFor remaining (residentEmit zeroMode bit resident::quotient))
            (residentNext zeroMode bit resident) suffix)) ∧
      trace.length ≤ 16*(1+remaining.length+quotient.length)+32*resident.length+43 := by
  change Span _ _ (16*(1+remaining.length+quotient.length)+32*resident.length+42)
  let archive := archiveFor (bit::remaining) quotient
  let shifted := PSTRTMShiftColumnCode065.shiftPairs bit resident
  cases zeroMode with
  | true =>
    have he : residentEmit true bit resident = false := rfl
    have hn : residentNext true bit resident = shifted := rfl
    rw [he,hn]
    have hs := source_span true bit remaining quotient context resident suffix
    have ht := span_of_hop (steps := 7*resident.length+3) (shift5_hop bit context archive resident suffix)
    have hb := span_of_hop (steps := 4*shifted.length+3) (rewind7_hop context archive shifted suffix)
    have hc := commit_span 13 3 false rfl rfl bit remaining quotient context shifted suffix
    apply span_mono (span_trans (span_trans (span_trans hs ht) hb) hc)
    dsimp [shifted]
    simp only [PSTRTMShiftColumnCode065.shiftPairs_length]
    omega
  | false =>
    have hs := source_span false bit remaining quotient context resident suffix
    have ht := span_of_hop (steps := 7*resident.length+3) (shift6_hop bit context archive resident suffix)
    have hb := span_of_hop (steps := 4*shifted.length+3) (rewind8_hop context archive shifted suffix)
    have hc := span_of_hop (steps := 4*shifted.length+3) (compare9_hop context archive shifted suffix)
    by_cases less : (PSTRTMCompareCode054.resultRelation 0 shifted).val = 1
    · have he : residentEmit false bit resident = false := by
        change decide ((PSTRTMCompareCode054.resultRelation 0 shifted).val ≠ 1) = false
        simp [less]
      have hn : residentNext false bit resident = shifted := by simp [residentNext,he,shifted]
      rw [he,hn]
      simp [compare9Target,less] at hc
      have hr := span_of_hop (steps := 4*shifted.length+3) (rewind10_hop context archive shifted suffix)
      have hw := commit_span 14 4 false rfl rfl bit remaining quotient context shifted suffix
      apply span_mono (span_trans (span_trans (span_trans (span_trans (span_trans hs ht) hb) hc) hr) hw)
      dsimp [shifted]
      simp only [PSTRTMShiftColumnCode065.shiftPairs_length]
      omega
    · have he : residentEmit false bit resident = true := by
        change decide ((PSTRTMCompareCode054.resultRelation 0 shifted).val ≠ 1) = true
        simp [less]
      have hn : residentNext false bit resident = PA17TMDivisionSub001.subPairs false shifted := by
        simp [residentNext,he,shifted]
      rw [he,hn]
      simp [compare9Target,less] at hc
      have hr := span_of_hop (steps := 4*shifted.length+3) (rewind11_hop context archive shifted suffix)
      have hu := span_of_hop (steps := 13*shifted.length+6) (sub12_hop context archive shifted suffix)
      have hw := commit_span 15 4 true rfl rfl bit remaining quotient context
        (PA17TMDivisionSub001.subPairs false shifted) suffix
      apply span_mono (span_trans (span_trans (span_trans (span_trans (span_trans (span_trans hs ht) hb) hc) hr) hu) hw)
      dsimp [shifted]
      simp only [PSTRTMShiftColumnCode065.shiftPairs_length]
      omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionKernelLift009

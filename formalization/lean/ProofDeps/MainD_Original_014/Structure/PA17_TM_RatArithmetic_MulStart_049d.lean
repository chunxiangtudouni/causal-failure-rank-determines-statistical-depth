module
public import Structure.PA17_TM_RatArithmetic_MulStart_049c

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulStart049
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticOuter025 PA17TMRatArithmeticSignRead021
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBookmark014
attribute [local implicit_reducible] allocatorCap stageCap mulStartCap

def actualMemory (x y : Rat) : Fin 64 := selectedMemory (mNx x y) (sign x)
def originalFinal (k : Nat) (x y : Rat) : MachineState (mulStartCap k) :=
  homeFinal k (actualMemory x y) (sign x) [false] (bankAt x y (k*(fieldWidth x y)^2))

theorem actualMemory_retains_old (x y : Rat) : (actualMemory x y).val%32=(mNx x y).val :=
  selectedMemory_retains_old _ _
theorem actualMemory_observed_sx (x y : Rat) : (actualMemory x y).val/32=if sign x then 1 else 0 :=
  selectedMemory_observed_sign _ _

theorem originalFinal_tape (k : Nat) (x y : Rat) :
    (originalFinal k x y).Tape=Tape.mk₂ [false]
      (prefixRight (sign x) (bankAt x y (k*(fieldWidth x y)^2))) := rfl
theorem originalFinal_label (k : Nat) (x y : Rat) :
    (originalFinal k x y).q.val=2*(stageCap k+1)+8*(actualMemory x y).val+7 :=
  homeFinal_label _ _ _ _ _

/-- ONE K-dependent code begins at numeric label0 on the exact original
two-rational codec. Both finite-control transfers and all physical head
movement are in this SAME trace. -/
theorem original_mulStart_runs (k : Nat) (x y : Rat) :
    ∃ trace, Runs (mulStartMachine k) (encode [.rational x,.rational y]) trace (originalFinal k x y) ∧
      trace.length≤(16*k+533)*(fieldWidth x y+1)^4 := by
  let body := PA17TMRatArithmeticAllocatePass023.passMachine k
  let bank := bankAt x y (k*(fieldWidth x y)^2)
  obtain ⟨rawTrace,rawRun,rawTime⟩ := raw_allocation_from_body body k (original_body_contract k) x y
  have rawFrom : PSTRTMSeq005.RunsFrom (allocatorMachine k)
      (TM0.init (encode [.rational x,.rational y])) rawTrace
      (rawLoopSavedFinal body (mNx x y) (sign x) bank) :=
    ⟨rawRun.1,rawRun.2.1,rawRun.2.2.1,rawRun.2.2.2.1⟩
  have rawPad := pad_runsFrom (allocator_le_stage k) (allocatorMachine k) _ _ _ rawFrom
  have rawFamily : PSTRTMSeq005.RunsFrom (startFamily k (0 : Fin 3))
      (padCfg (allocator_le_stage k) (TM0.init (encode [.rational x,.rational y])))
      (rawTrace.map (padCfg (allocator_le_stage k)))
      (padCfg (allocator_le_stage k) (rawLoopSavedFinal body (mNx x y) (sign x) bank)) := by
    simpa only [startFamily,Fin.val_zero,ite_true] using rawPad
  have rawSegment := block_segment (startFamily k) (startPorts k) (0 : Fin 3) _ _ _ rawFamily
  obtain ⟨readTrace,readSegment,readStep,readTime⟩ := read_segment k (mNx x y) (sign x) [false] bank
  obtain ⟨homeTrace,homeRun,homeTime⟩ := home_runsFrom k (actualMemory x y) (sign x) [false] bank
  have toRead := allocator_to_read k (mNx x y) (sign x) bank rawFrom.2.2.2
  let rawGlobal : List (MachineState (mulStartCap k)) :=
    (rawTrace.map (padCfg (allocator_le_stage k))).map (blockCfg (s:=stageCap k) (0 : Fin 3))
  have firstSegment : Segment (mulStartMachine k) _ (rawGlobal++readTrace) _ :=
    segment_append (mulStartMachine k) _ _ _ _ _ _ rawSegment readSegment toRead
  have lastSegment : Segment (mulStartMachine k) _ homeTrace _ :=
    ⟨homeRun.1,homeRun.2.1,homeRun.2.2.1⟩
  have fullSegment : Segment (mulStartMachine k) _ ((rawGlobal++readTrace)++homeTrace) _ :=
    segment_append (mulStartMachine k) _ _ _ _ _ _ firstSegment lastSegment readStep
  have initial : blockCfg (0 : Fin 3)
      (padCfg (allocator_le_stage k)
        (TM0.init (encode [.rational x,.rational y]) : MachineState (allocatorCap k)))=
      (TM0.init (encode [.rational x,.rational y]) : MachineState (mulStartCap k)) := by
    change blockCfg (0 : Fin 3)
      (padCfg (allocator_le_stage k)
        (⟨0,Tape.mk₁ (encode [.rational x,.rational y])⟩ : MachineState (allocatorCap k)))=
      (⟨0,Tape.mk₁ (encode [.rational x,.rational y])⟩ : MachineState (mulStartCap k))
    rw [pad_zero,blockCfg_zero]
  have fullRun : Runs (mulStartMachine k) (encode [.rational x,.rational y])
      ((rawGlobal++readTrace)++homeTrace) (originalFinal k x y) := by
    apply PSTRTMTrace002.runs_of_chain
    · exact fullSegment.1.trans (congrArg some initial)
    · exact fullSegment.2.1
    · exact fullSegment.2.2
    · exact homeRun.2.2.2
  have rawLength : rawGlobal.length=rawTrace.length := by
    simp only [rawGlobal,List.length_map]
  have length : ((rawGlobal++readTrace)++homeTrace).length=rawTrace.length+readTrace.length+homeTrace.length := by
    simp only [List.length_append,rawLength]
  refine ⟨(rawGlobal++readTrace)++homeTrace,fullRun,?_⟩
  rw [length]
  have hp : 1≤(fieldWidth x y+1)^4 := by
    have h : 0<(fieldWidth x y+1)^4 := by positivity
    omega
  calc
    _ ≤ (16*k+512)*(fieldWidth x y+1)^4+21 := by omega
    _ ≤ (16*k+512)*(fieldWidth x y+1)^4+21*(fieldWidth x y+1)^4 :=
      Nat.add_le_add_left (by omega) _
    _ = (16*k+533)*(fieldWidth x y+1)^4 := by ring

theorem original_mulStart_contract (k : Nat) (x y : Rat) :
    ∃ trace, Runs (mulStartMachine k) (encode [.rational x,.rational y]) trace (originalFinal k x y) ∧
      trace.length≤(32*k+1068)*((encode [.rational x,.rational y]).length+1)^4 ∧
      ∀ prefixLength, visitedSpace (mulStartMachine k) (encode [.rational x,.rational y]).length
        (trace.take prefixLength)≤(32*k+1068)*((encode [.rational x,.rational y]).length+1)^4 := by
  obtain ⟨trace,hr,ht⟩ := original_mulStart_runs k x y
  let i := (encode [.rational x,.rational y]).length
  have hw := original_width_le_input x y
  have hp : (fieldWidth x y+1)^4≤(i+1)^4 := Nat.pow_le_pow_left (by omega) 4
  have timeBound : trace.length≤(16*k+533)*(i+1)^4 := ht.trans (Nat.mul_le_mul_left _ hp)
  have hi : i+1≤(i+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : (1 : Nat) ≤ i + 1) (by decide : (1 : Nat) ≤ 4)
  refine ⟨trace,hr,timeBound.trans (Nat.mul_le_mul_right _ (by omega)),?_⟩
  intro prefixLength
  have hs := PSTRTMTrace002.visitedSpace_le (mulStartMachine k) i (trace.take prefixLength)
  have hl : (trace.take prefixLength).length≤trace.length := by simp only [List.length_take];omega
  change visitedSpace (mulStartMachine k) i (trace.take prefixLength)≤(32*k+1068)*(i+1)^4
  calc
    _ ≤ (i+1)+2*((16*k+533)*(i+1)^4) := by omega
    _ ≤ (i+1)^4+2*((16*k+533)*(i+1)^4) := Nat.add_le_add_right hi _
    _ = (32*k+1067)*(i+1)^4 := by ring
    _ ≤ (32*k+1068)*(i+1)^4 := Nat.mul_le_mul_right _ (by omega)

/-- Closed original-codec prefix; no observed memory, width, room, sign,
answer, or incoming run qualification is supplied by an original caller. -/
theorem original_mulStart_exists (k : Nat) :
    ∃ states c d : Nat, ∃ program : Machine states, 0<c ∧ 0<d ∧
      ∀ x y : Rat, ∃ trace final, Runs program (encode [.rational x,.rational y]) trace final ∧
        final.Tape=Tape.mk₂ [false] (prefixRight (sign x) (bankAt x y (k*(fieldWidth x y)^2))) ∧
        final.q.val=2*(stageCap k+1)+8*(actualMemory x y).val+7 ∧
        trace.length≤c*((encode [.rational x,.rational y]).length+1)^d ∧
        ∀ prefixLength, visitedSpace program (encode [.rational x,.rational y]).length (trace.take prefixLength)≤
          c*((encode [.rational x,.rational y]).length+1)^d := by
  refine ⟨mulStartCap k,32*k+1068,4,mulStartMachine k,by omega,by decide,?_⟩
  intro x y
  obtain ⟨trace,hr,ht,hs⟩ := original_mulStart_contract k x y
  exact ⟨trace,originalFinal k x y,hr,originalFinal_tape _ _ _,originalFinal_label _ _ _,ht,hs⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulStart049

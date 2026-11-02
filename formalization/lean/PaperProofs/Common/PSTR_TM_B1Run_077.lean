module
public import PaperProofs.Common.PSTR_TM_B1Cleanup_076

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1Run077
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMB1LoopCode071 PSTRTMB1CounterCall073 PSTRTMB1Iteration074 PSTRTMB1Invariant075

def currentPairs (numerator denominator count : Nat) : List (Bool × Bool) :=
  iteratedPairs (initialPairs numerator denominator) count
def width (numerator denominator : Nat) : Nat := (initialPairs numerator denominator).length
def input (numerator denominator : Nat) : List Bool :=
  PSTRTMB1PrepareCode069.preparedWord (PSTRTMPackCode036.digitPairs (PSTRTMNatValue017.rawPayload numerator)
    (PSTRTMNatValue017.rawPayload denominator))

theorem current_length (numerator denominator count : Nat) : (currentPairs numerator denominator count).length = width numerator denominator :=
  iterated_length _ count
theorem current_next (numerator denominator count : Nat) :
    currentPairs numerator denominator (count+1) = PSTRTMShiftColumnCode065.shiftPairs false (currentPairs numerator denominator count) := rfl

def comparisonTrace (pairs : List (Bool × Bool)) (digits : List Bool) : List (MachineState 81) :=
  (PSTRTMCompareTrace055.compareTrace 0 [false] [] pairs (counterSuffix digits)).map liftCompare

theorem comparison_head (pairs : List (Bool × Bool)) (digits : List Bool) :
    (comparisonTrace pairs digits).head? = some (state 0 [false] (PSTRTMBinaryAdd024.operandColumns pairs ++ endRegion digits)) := by
  simp only [comparisonTrace,List.head?_map,PSTRTMCompareTrace055.compare_head,Option.map_some,
    PSTRTMCompareCode054.leftColumns,List.flatMap_nil,List.nil_append]
  rfl

theorem comparison_last (pairs : List (Bool × Bool)) (digits : List Bool) :
    (comparisonTrace pairs digits).getLast? = some (liftCompare (PSTRTMCompareCode054.state
      (PSTRTMCompareCode054.haltLabel (PSTRTMCompareCode054.resultRelation 0 pairs)) (columnsLeft pairs) (endRegion digits))) := by
  simp only [comparisonTrace,List.getLast?_map,PSTRTMCompareTrace055.compare_last,List.append_nil,Option.map_some]
  rfl

theorem comparison_length (pairs : List (Bool × Bool)) (digits : List Bool) :
    (comparisonTrace pairs digits).length = 4*pairs.length+3 := by
  simp only [comparisonTrace,List.length_map,PSTRTMCompareTrace055.compare_length]

theorem comparison_chain (pairs : List (Bool × Bool)) (digits : List Bool) :
    (comparisonTrace pairs digits).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) :=
  PSTRTMB1LoopLift072.compare_chain _ (PSTRTMCompareTrace055.compare_chain 0 [false] [] pairs (counterSuffix digits))

private theorem cleanup_transfer (pairs : List (Bool × Bool)) (digits : List Bool)
    (notLess : PSTRTMCompareCode054.resultRelation 0 pairs ≠ 1) :
    Turing.TM0.step loopMachine (liftCompare (PSTRTMCompareCode054.state
      (PSTRTMCompareCode054.haltLabel (PSTRTMCompareCode054.resultRelation 0 pairs)) (columnsLeft pairs) (endRegion digits))) =
      some (PSTRTMB1Cleanup076.eraseInitial (PSTRTMPackLoop043.pairedDigits pairs).reverse 0 digits) := by
  rw [columnsLeft,PSTRTMCompareRun059.leftColumns_reverse]
  exact PSTRTMB1Cleanup076.terminal_transfer _ notLess _ digits

private theorem iteration_continue (pairs : List (Bool × Bool)) (digits : List Bool) :
    Turing.TM0.step loopMachine (liftRewindAfter (PSTRTMColumnRewind067.state 5 [false]
      (PSTRTMBinaryAdd024.operandColumns (PSTRTMShiftColumnCode065.shiftPairs false pairs) ++ endRegion (nextDigits digits)))) =
      some (state 0 [false] (PSTRTMBinaryAdd024.operandColumns (PSTRTMShiftColumnCode065.shiftPairs false pairs) ++ endRegion (nextDigits digits))) := by
  simpa [liftRewindAfter,rewindAfterLabel,PSTRTMColumnRewind067.state,state] using after_compare_transfer
    (Turing.Tape.mk₂ [false] (PSTRTMBinaryAdd024.operandColumns (PSTRTMShiftColumnCode065.shiftPairs false pairs) ++ endRegion (nextDigits digits)))

private theorem append_link (xs ys : List (MachineState 81)) (last first : MachineState 81)
    (hx : xs.IsChain (fun a b => Turing.TM0.step loopMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step loopMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step loopMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

/-- count/remaining index a proof witness for the SAME fixed82-label code.
The runtime reads neither index, K, a numerical value nor a supplied bound.
All branch conditions are justified below from the actual computed relation. -/
def countTrace (numerator denominator count : Nat) : Nat → List (MachineState 81)
  | 0 => comparisonTrace (currentPairs numerator denominator count) (PSTRTMNatValue017.rawPayload count) ++
      PSTRTMB1Cleanup076.cleanupTrace (currentPairs numerator denominator count) (PSTRTMNatValue017.rawPayload count)
  | remaining+1 => comparisonTrace (currentPairs numerator denominator count) (PSTRTMNatValue017.rawPayload count) ++
      iterationTrace (currentPairs numerator denominator count) (PSTRTMNatValue017.rawPayload count) ++
      countTrace numerator denominator (count+1) remaining

theorem count_head (numerator denominator count remaining : Nat) :
    (countTrace numerator denominator count remaining).head? = some (state 0 [false]
      (PSTRTMBinaryAdd024.operandColumns (currentPairs numerator denominator count) ++ endRegion (PSTRTMNatValue017.rawPayload count))) := by
  cases remaining <;> simp only [countTrace,List.head?_append,comparison_head,Option.some_or]

theorem count_last (numerator denominator count remaining : Nat) :
    (countTrace numerator denominator count remaining).getLast? = some (PSTRTMB1Cleanup076.cleanupFinal
      (currentPairs numerator denominator (count+remaining)) (PSTRTMNatValue017.rawPayload (count+remaining))) := by
  induction remaining generalizing count with
  | zero => simp only [countTrace,List.getLast?_append,PSTRTMB1Cleanup076.cleanup_last,Option.some_or,Nat.add_zero]
  | succ remaining ih =>
    simp only [countTrace,List.getLast?_append,ih,Option.some_or]
    have he : count+1+remaining = count+(remaining+1) := by omega
    rw [he]

theorem count_chain (numerator denominator count remaining : Nat) (hn : 0 < numerator)
    (hcount : count+remaining = PSTRTMB1Value068.exponent numerator denominator) :
    (countTrace numerator denominator count remaining).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  induction remaining generalizing count with
  | zero =>
    have he : count = PSTRTMB1Value068.exponent numerator denominator := by omega
    have hnot : PSTRTMCompareCode054.resultRelation 0 (currentPairs numerator denominator count) ≠ 1 := by
      rw [he]
      exact comparison_not_less_final numerator denominator hn
    rw [countTrace]
    exact append_link _ _ _ _ (comparison_chain _ _)
      (PSTRTMB1Cleanup076.erase_chain _ 0 _) (comparison_last _ _)
      (PSTRTMB1Cleanup076.cleanup_head _ _) (cleanup_transfer _ _ hnot)
  | succ remaining ih =>
    have hlt : count < PSTRTMB1Value068.exponent numerator denominator := by omega
    have hless : PSTRTMCompareCode054.resultRelation 0 (currentPairs numerator denominator count) = 1 :=
      comparison_less_before numerator denominator count hn hlt
    have hno : PSTRTMShiftColumnCode065.finalCarry false (currentPairs numerator denominator count) = false :=
      actual_noOverflow_before numerator denominator count hn hlt
    rw [countTrace]
    refine append_link _ _
      (liftRewindAfter (PSTRTMColumnRewind067.state 5 [false]
        (PSTRTMBinaryAdd024.operandColumns (PSTRTMShiftColumnCode065.shiftPairs false (currentPairs numerator denominator count)) ++
          endRegion (nextDigits (PSTRTMNatValue017.rawPayload count)))))
      (state 0 [false] (PSTRTMBinaryAdd024.operandColumns (currentPairs numerator denominator (count+1)) ++
        endRegion (PSTRTMNatValue017.rawPayload (count+1)))) ?_ (ih (count+1) (by omega)) ?_
      (count_head numerator denominator (count+1) remaining) ?_
    · refine append_link _ _ _ _ (comparison_chain _ _) (iteration_chain _ _ hno)
        (comparison_last _ _) (iteration_head _ _) ?_
      rw [hless]
      exact compare_less_transfer _ _
    · simp only [List.getLast?_append,iteration_last,Option.some_or]
    · simpa only [current_next,nextDigits_rawPayload] using
        iteration_continue (currentPairs numerator denominator count) (PSTRTMNatValue017.rawPayload count)

theorem count_length_le (numerator denominator count remaining : Nat) (hn : 0 < numerator)
    (hcount : count+remaining ≤ PSTRTMB1Value068.exponent numerator denominator) :
    (countTrace numerator denominator count remaining).length ≤
      remaining*(19*width numerator denominator+8*natBits denominator+27)+16*width numerator denominator+10 := by
  induction remaining generalizing count with
  | zero =>
    simp only [countTrace,List.length_append,comparison_length,PSTRTMB1Cleanup076.cleanup_length,current_length]
    omega
  | succ remaining ih =>
    have ht := iteration_length_le (currentPairs numerator denominator count) (PSTRTMNatValue017.rawPayload count)
    rw [current_length] at ht
    have hc := counter_payload_length_le numerator denominator count hn (by omega)
    have hi := ih (count+1) (by omega)
    simp only [countTrace,List.length_append,comparison_length,current_length]
    nlinarith

def loopTrace (numerator denominator : Nat) : List (MachineState 81) :=
  countTrace numerator denominator 0 (PSTRTMB1Value068.exponent numerator denominator)
def loopFinal (numerator denominator : Nat) : MachineState 81 := PSTRTMB1Cleanup076.cleanupFinal
  (currentPairs numerator denominator (PSTRTMB1Value068.exponent numerator denominator))
  (PSTRTMNatValue017.rawPayload (PSTRTMB1Value068.exponent numerator denominator))

theorem initial_state (numerator denominator : Nat) :
    state 0 [false] (PSTRTMBinaryAdd024.operandColumns (currentPairs numerator denominator 0) ++
      endRegion (PSTRTMNatValue017.rawPayload 0)) = Turing.TM0.init (input numerator denominator) := by
  change (⟨0,Turing.Tape.mk₂ [false] (input numerator denominator)⟩ : MachineState 81) = Turing.TM0.init (input numerator denominator)
  simp only [Turing.TM0.init,Turing.Tape.mk₁,Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false]
  simp only [Fin.default_eq_zero]

theorem loop_runs (numerator denominator : Nat) (hn : 0 < numerator) :
    Runs loopMachine (input numerator denominator) (loopTrace numerator denominator) (loopFinal numerator denominator) := by
  apply PSTRTMTrace002.runs_of_chain
  · simpa only [loopTrace,initial_state] using count_head numerator denominator 0 (PSTRTMB1Value068.exponent numerator denominator)
  · exact count_chain numerator denominator 0 _ hn (by omega)
  · simpa only [loopTrace,loopFinal,Nat.zero_add] using count_last numerator denominator 0 (PSTRTMB1Value068.exponent numerator denominator)
  · exact loop_halt _ _

theorem loop_final_tape (numerator denominator : Nat) :
    (loopFinal numerator denominator).Tape = Turing.Tape.mk₁
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (PSTRTMB1Value068.exponent numerator denominator))) :=
  PSTRTMB1Cleanup076.cleanup_final_tape _ _

theorem width_le (numerator denominator : Nat) : width numerator denominator ≤ natBits numerator+natBits denominator+1 := by
  rw [width,initial_length]
  omega

theorem loop_length_le (numerator denominator : Nat) (hn : 0 < numerator) :
    (loopTrace numerator denominator).length ≤ 128*(natBits numerator+natBits denominator+1)^2 := by
  have ht := count_length_le numerator denominator 0 (PSTRTMB1Value068.exponent numerator denominator) hn (by omega)
  have hk := PSTRTMB1Value068.exponent_le_bits numerator denominator hn
  have hw := width_le numerator denominator
  have hm := Nat.mul_le_mul_right (19*width numerator denominator+8*natBits denominator+27) hk
  have hwm := Nat.mul_le_mul_left (natBits denominator) hw
  have hd : natBits denominator ≤ natBits numerator+natBits denominator := by omega
  have hdm := Nat.mul_le_mul_right (natBits numerator+natBits denominator+1) hd
  have hsq := Nat.pow_le_pow_left hd 2
  change (countTrace numerator denominator 0 (PSTRTMB1Value068.exponent numerator denominator)).length ≤ _
  nlinarith

theorem input_length (numerator denominator : Nat) : (input numerator denominator).length = 4*width numerator denominator+6 := by
  simp only [input,PSTRTMB1PrepareCode069.preparedWord,List.length_append,PSTRTMBinaryAdd024.operandColumns_length,
    PSTRTMB1PrepareCode069.suffix,List.length_cons,List.length_nil]
  rfl

theorem loop_visitedSpace_le (numerator denominator : Nat) (hn : 0 < numerator) :
    visitedSpace loopMachine (input numerator denominator).length (loopTrace numerator denominator) ≤
      512*(natBits numerator+natBits denominator+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le loopMachine (input numerator denominator).length (loopTrace numerator denominator)
  have ht := loop_length_le numerator denominator hn
  have hw := width_le numerator denominator
  rw [input_length] at hs ⊢
  nlinarith

/-- Genuine full finite loop, with its actual computed stop/cleanup/HALT
and exact retained canonical counter. Every iteration count bound is from
ORIGINAL bit lengths; no trace, K, fuel or width is supplied to the code. -/
theorem loop_computes (numerator denominator : Nat) (hn : 0 < numerator) :
    computes loopMachine (input numerator denominator)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (PSTRTMB1Value068.exponent numerator denominator)))
      (128*(natBits numerator+natBits denominator+1)^2) (512*(natBits numerator+natBits denominator+1)^2) := by
  refine ⟨loopTrace numerator denominator,loopFinal numerator denominator,loop_runs numerator denominator hn,?_,
    loop_length_le numerator denominator hn,loop_visitedSpace_le numerator denominator hn⟩
  rw [loop_final_tape]
  simp [Turing.Tape.mk₁,Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1Run077

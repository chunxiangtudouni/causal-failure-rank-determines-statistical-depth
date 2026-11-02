module
public import Common.PSTR_TM_B1CleanupFrame_121

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1RunFrame122
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMB1LoopCode071 PSTRTMB1CounterCall073 PSTRTMB1IterationFrame120 PSTRTMB1Invariant075

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

def comparisonTrace (archive : List Bool) (pairs : List (Bool × Bool)) (digits : List Bool) : List (MachineState 81) :=
  (PSTRTMCompareTrace055.compareTrace 0 (false::archive) [] pairs (counterSuffix digits)).map liftCompare

theorem comparison_head (archive : List Bool) (pairs : List (Bool × Bool)) (digits : List Bool) :
    (comparisonTrace archive pairs digits).head? = some (state 0 (false::archive) (PSTRTMBinaryAdd024.operandColumns pairs ++ endRegion digits)) := by
  simp only [comparisonTrace,List.head?_map,PSTRTMCompareTrace055.compare_head,Option.map_some,
    PSTRTMCompareCode054.leftColumns,List.flatMap_nil,List.nil_append]
  rfl

theorem comparison_last (archive : List Bool) (pairs : List (Bool × Bool)) (digits : List Bool) :
    (comparisonTrace archive pairs digits).getLast? = some (liftCompare (PSTRTMCompareCode054.state
      (PSTRTMCompareCode054.haltLabel (PSTRTMCompareCode054.resultRelation 0 pairs)) (columnsLeft archive pairs) (endRegion digits))) := by
  simp only [comparisonTrace,List.getLast?_map,PSTRTMCompareTrace055.compare_last,List.append_nil,Option.map_some]
  rfl

theorem comparison_length (archive : List Bool) (pairs : List (Bool × Bool)) (digits : List Bool) :
    (comparisonTrace archive pairs digits).length = 4*pairs.length+3 := by
  simp only [comparisonTrace,List.length_map,PSTRTMCompareTrace055.compare_length]

theorem comparison_chain (archive : List Bool) (pairs : List (Bool × Bool)) (digits : List Bool) :
    (comparisonTrace archive pairs digits).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) :=
  PSTRTMB1LoopLift072.compare_chain _ (PSTRTMCompareTrace055.compare_chain 0 (false::archive) [] pairs (counterSuffix digits))

private theorem cleanup_transfer (archive : List Bool) (pairs : List (Bool × Bool)) (digits : List Bool)
    (notLess : PSTRTMCompareCode054.resultRelation 0 pairs ≠ 1) :
    Turing.TM0.step loopMachine (liftCompare (PSTRTMCompareCode054.state
      (PSTRTMCompareCode054.haltLabel (PSTRTMCompareCode054.resultRelation 0 pairs)) (columnsLeft archive pairs) (endRegion digits))) =
      some (PSTRTMB1CleanupFrame121.eraseInitial archive (PSTRTMPackLoop043.pairedDigits pairs).reverse 0 digits) := by
  rw [columnsLeft,PSTRTMCompareRun059.leftColumns_reverse]
  exact PSTRTMB1CleanupFrame121.terminal_transfer archive _ notLess _ digits

private theorem iteration_continue (archive : List Bool) (pairs : List (Bool × Bool)) (digits : List Bool) :
    Turing.TM0.step loopMachine (liftRewindAfter (PSTRTMColumnRewind067.state 5 (false::archive)
      (PSTRTMBinaryAdd024.operandColumns (PSTRTMShiftColumnCode065.shiftPairs false pairs) ++ endRegion (nextDigits digits)))) =
      some (state 0 (false::archive) (PSTRTMBinaryAdd024.operandColumns (PSTRTMShiftColumnCode065.shiftPairs false pairs) ++ endRegion (nextDigits digits))) := by
  simpa [liftRewindAfter,rewindAfterLabel,PSTRTMColumnRewind067.state,state] using after_compare_transfer
    (Turing.Tape.mk₂ (false::archive) (PSTRTMBinaryAdd024.operandColumns (PSTRTMShiftColumnCode065.shiftPairs false pairs) ++ endRegion (nextDigits digits)))

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

private theorem framed_nextDigits_rawPayload (count : Nat) :
    PSTRTMB1IterationFrame120.nextDigits (PSTRTMNatValue017.rawPayload count)=PSTRTMNatValue017.rawPayload (count+1) := by
  simpa only [PSTRTMB1IterationFrame120.nextDigits,PSTRTMB1Iteration074.nextDigits] using
    PSTRTMB1Invariant075.nextDigits_rawPayload count

/-- count/remaining index a proof witness for the SAME fixed82-label code.
The runtime reads neither index, K, a numerical value nor a supplied bound.
All branch conditions are justified below from the actual computed relation. -/
def countTrace (archive : List Bool) (numerator denominator count : Nat) : Nat → List (MachineState 81)
  | 0 => comparisonTrace archive (currentPairs numerator denominator count) (PSTRTMNatValue017.rawPayload count) ++
      PSTRTMB1CleanupFrame121.cleanupTrace archive (currentPairs numerator denominator count) (PSTRTMNatValue017.rawPayload count)
  | remaining+1 => comparisonTrace archive (currentPairs numerator denominator count) (PSTRTMNatValue017.rawPayload count) ++
      iterationTrace archive (currentPairs numerator denominator count) (PSTRTMNatValue017.rawPayload count) ++
      countTrace archive numerator denominator (count+1) remaining

theorem count_head (archive : List Bool) (numerator denominator count remaining : Nat) :
    (countTrace archive numerator denominator count remaining).head? = some (state 0 (false::archive)
      (PSTRTMBinaryAdd024.operandColumns (currentPairs numerator denominator count) ++ endRegion (PSTRTMNatValue017.rawPayload count))) := by
  cases remaining <;> simp only [countTrace,List.head?_append,comparison_head,Option.some_or]

theorem count_last (archive : List Bool) (numerator denominator count remaining : Nat) :
    (countTrace archive numerator denominator count remaining).getLast? = some (PSTRTMB1CleanupFrame121.cleanupFinal archive
      (currentPairs numerator denominator (count+remaining)) (PSTRTMNatValue017.rawPayload (count+remaining))) := by
  induction remaining generalizing count with
  | zero => simp only [countTrace,List.getLast?_append,PSTRTMB1CleanupFrame121.cleanup_last,Option.some_or,Nat.add_zero]
  | succ remaining ih =>
    simp only [countTrace,List.getLast?_append,ih,Option.some_or]
    have he : count+1+remaining = count+(remaining+1) := by omega
    rw [he]

theorem count_chain (archive : List Bool) (numerator denominator count remaining : Nat) (hn : 0 < numerator)
    (hcount : count+remaining = PSTRTMB1Value068.exponent numerator denominator) :
    (countTrace archive numerator denominator count remaining).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  induction remaining generalizing count with
  | zero =>
    have he : count = PSTRTMB1Value068.exponent numerator denominator := by omega
    have hnot : PSTRTMCompareCode054.resultRelation 0 (currentPairs numerator denominator count) ≠ 1 := by
      rw [he]
      exact comparison_not_less_final numerator denominator hn
    rw [countTrace]
    exact append_link _ _ _ _ (comparison_chain archive _ _)
      (PSTRTMB1CleanupFrame121.erase_chain archive _ 0 _) (comparison_last archive _ _)
      (PSTRTMB1CleanupFrame121.cleanup_head archive _ _) (cleanup_transfer archive _ _ hnot)
  | succ remaining ih =>
    have hlt : count < PSTRTMB1Value068.exponent numerator denominator := by omega
    have hless : PSTRTMCompareCode054.resultRelation 0 (currentPairs numerator denominator count) = 1 :=
      comparison_less_before numerator denominator count hn hlt
    have hno : PSTRTMShiftColumnCode065.finalCarry false (currentPairs numerator denominator count) = false :=
      actual_noOverflow_before numerator denominator count hn hlt
    rw [countTrace]
    refine append_link _ _
      (liftRewindAfter (PSTRTMColumnRewind067.state 5 (false::archive)
        (PSTRTMBinaryAdd024.operandColumns (PSTRTMShiftColumnCode065.shiftPairs false (currentPairs numerator denominator count)) ++
          endRegion (nextDigits (PSTRTMNatValue017.rawPayload count)))))
      (state 0 (false::archive) (PSTRTMBinaryAdd024.operandColumns (currentPairs numerator denominator (count+1)) ++
        endRegion (PSTRTMNatValue017.rawPayload (count+1)))) ?_ (ih (count+1) (by omega)) ?_
      (count_head archive numerator denominator (count+1) remaining) ?_
    · refine append_link _ _ _ _ (comparison_chain archive _ _) (iteration_chain archive _ _ hno)
        (comparison_last archive _ _) (iteration_head archive _ _) ?_
      rw [hless]
      exact compare_less_transfer _ _
    · simp only [List.getLast?_append,iteration_last,Option.some_or]
    · simpa only [current_next,framed_nextDigits_rawPayload] using
        iteration_continue archive (currentPairs numerator denominator count) (PSTRTMNatValue017.rawPayload count)

theorem count_length_le (archive : List Bool) (numerator denominator count remaining : Nat) (hn : 0 < numerator)
    (hcount : count+remaining ≤ PSTRTMB1Value068.exponent numerator denominator) :
    (countTrace archive numerator denominator count remaining).length ≤
      remaining*(19*width numerator denominator+8*natBits denominator+27)+16*width numerator denominator+10 := by
  induction remaining generalizing count with
  | zero =>
    simp only [countTrace,List.length_append,comparison_length,PSTRTMB1CleanupFrame121.cleanup_length,current_length]
    omega
  | succ remaining ih =>
    have ht := iteration_length_le archive (currentPairs numerator denominator count) (PSTRTMNatValue017.rawPayload count)
    rw [current_length] at ht
    have hc := counter_payload_length_le numerator denominator count hn (by omega)
    have hi := ih (count+1) (by omega)
    simp only [countTrace,List.length_append,comparison_length,current_length]
    nlinarith

def loopTrace (archive : List Bool) (numerator denominator : Nat) : List (MachineState 81) :=
  countTrace archive numerator denominator 0 (PSTRTMB1Value068.exponent numerator denominator)
def loopFinal (archive : List Bool) (numerator denominator : Nat) : MachineState 81 := PSTRTMB1CleanupFrame121.cleanupFinal archive
  (currentPairs numerator denominator (PSTRTMB1Value068.exponent numerator denominator))
  (PSTRTMNatValue017.rawPayload (PSTRTMB1Value068.exponent numerator denominator))

theorem loop_runsFrom (archive : List Bool) (numerator denominator : Nat) (hn : 0 < numerator) :
    PSTRTMSeq005.RunsFrom loopMachine (state 0 (false::archive) (input numerator denominator))
      (loopTrace archive numerator denominator) (loopFinal archive numerator denominator) := by
  refine ⟨?_,count_chain archive numerator denominator 0 _ hn (by omega),?_,loop_halt _ _⟩
  · exact count_head archive numerator denominator 0 (PSTRTMB1Value068.exponent numerator denominator)
  · simpa only [loopTrace,loopFinal,Nat.zero_add] using
      count_last archive numerator denominator 0 (PSTRTMB1Value068.exponent numerator denominator)

theorem loop_final_tape (archive : List Bool) (numerator denominator : Nat) :
    (loopFinal archive numerator denominator).Tape = Turing.Tape.mk₂
      (List.replicate (4*width numerator denominator+5) false ++ archive)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (PSTRTMB1Value068.exponent numerator denominator))) := by
  rw [loopFinal,PSTRTMB1CleanupFrame121.cleanup_final_tape,current_length]

theorem width_le (numerator denominator : Nat) : width numerator denominator ≤ natBits numerator+natBits denominator+1 := by
  rw [width,initial_length]
  omega

theorem loop_length_le (archive : List Bool) (numerator denominator : Nat) (hn : 0 < numerator) :
    (loopTrace archive numerator denominator).length ≤ 128*(natBits numerator+natBits denominator+1)^2 := by
  have ht := count_length_le archive numerator denominator 0 (PSTRTMB1Value068.exponent numerator denominator) hn (by omega)
  have hk := PSTRTMB1Value068.exponent_le_bits numerator denominator hn
  have hw := width_le numerator denominator
  have hm := Nat.mul_le_mul_right (19*width numerator denominator+8*natBits denominator+27) hk
  have hwm := Nat.mul_le_mul_left (natBits denominator) hw
  have hd : natBits denominator ≤ natBits numerator+natBits denominator := by omega
  have hdm := Nat.mul_le_mul_right (natBits numerator+natBits denominator+1) hd
  have hsq := Nat.pow_le_pow_left hd 2
  change (countTrace archive numerator denominator 0 (PSTRTMB1Value068.exponent numerator denominator)).length ≤ _
  nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1RunFrame122

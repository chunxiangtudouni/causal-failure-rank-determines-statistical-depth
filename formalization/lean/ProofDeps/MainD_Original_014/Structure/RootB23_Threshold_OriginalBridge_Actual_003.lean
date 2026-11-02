module

public import Structure.RootB23_Threshold_OriginalBridge_Bounds_002

/-! One actual Bool execution starts on the original risk/depth list,
computes the genuine bare pair, builds and consumes its real window,
dispatches the observed cap branch, and returns to the original B DATA.
The original badRisk/B/risk/depth cells remain on that same whole tape. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace RootB23.Threshold.OriginalBridge
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PSTRTMSeq005 PA17TMDivisionCompose006 PA17TMRatArithmeticParse002
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

attribute [local implicit_reducible] FixedConsumer.cap ProtectedConsumer.cap
  ProtectedConsumer.prefixCap Producer.cap prefixCap rowCap tailCap cap

def branch (risk : Rat) (depth : Nat) : Bool :=
  decide ((1/4 : Rat) ≤ (FactorSource.factorValue risk depth : Rat) * risk)

def spaceCoefficient : Nat := 2 * timeCoefficient + 2

theorem archive_exact (base : List Bool) (x y : Rat) :
    PayloadActual.archive base x y = ReturnBank.archive base x y := rfl

theorem tail_actual (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    ∃ (left right : Nat) (trace : List (MachineState tailCap)),
      RunsFrom tailCode
        ⟨0, Tape.mk₂ (BarePacket.west risk depth)
          (encodeDatum (.rational (FactorSource.factorValue risk depth : Rat)) ++ encodeDatum (.rational risk))⟩
        trace ⟨tailPort (branch risk depth), ReturnActual.finalTape risk depth risk left right⟩ ∧
      32 * width risk depth + 512 ≤ left ∧
      32 * width risk depth + 512 ≤ right + 1 -
        (Spatial.MulCap.output (FactorSource.factorValue risk depth : Rat) risk).length ∧
      left + right = Producer.left FixedConsumer.k (FactorSource.factorValue risk depth : Rat) risk +
        Spatial.MulCap.window (FactorSource.factorValue risk depth : Rat) risk (32 * width risk depth + 512) ∧
      trace.length ≤ FixedConsumer.coefficient * (width risk depth + 1) ^ 8 + ReturnActual.time risk depth risk left := by
  have positive := product_positive risk depth hr
  obtain ⟨left, right, before, windowLast, beforeRun, windowPort, windowTape,
      leftRoom, rightRoom, sum, beforeTime, _⟩ := FixedConsumer.actual (BarePacket.west risk depth)
        (FactorSource.factorValue risk depth : Rat) risk (Nat.cast_nonneg _) (le_of_lt hr) positive
  have room : ReturnCredit.spare (FactorSource.factorValue risk depth : Rat) risk ≤ left := leftRoom
  obtain ⟨after, dispatched, afterRun, afterTime, _⟩ :=
    ReturnActual.actual_contract prefixCap risk depth risk left right positive room
  have observed : ReturnDispatch.dispatch prefixCap windowLast.q =
      some (ReturnDispatch.entry (branch risk depth)) := by
    have realPort : windowLast.q = rightLabel (a := prefixCap)
        (Spatial.MulCap.final (FactorSource.factorValue risk depth : Rat) risk).q := by
      rw [windowPort]
      exact (ProtectedConsumer.lift_final 32 512 _ _ positive).symm
    rw [realPort]
    exact dispatched
  have middle : windowLast.Tape = ReturnActual.postTape risk depth risk left right := by
    simpa only [ReturnActual.postTape, ReturnActual.badRight, archive_exact] using windowTape
  rw [← middle] at afterRun
  have paddedBefore := pad_runsFrom window_le FixedConsumer.code _ _ _ beforeRun
  have atStart : RunsFrom (rows (0 : Fin 2))
      (padCfg window_le ⟨0, Tape.mk₂ (BarePacket.west risk depth)
        (encodeDatum (.rational (FactorSource.factorValue risk depth : Rat)) ++ encodeDatum (.rational risk))⟩)
      (before.map (padCfg window_le)) (padCfg window_le windowLast) := by
    rw [rows_start]
    exact paddedBefore
  have startSegment := block_segment rows ports (0 : Fin 2) _ _ _ atStart
  have transfer := block_transfer rows ports (0 : Fin 2) _
    ((1 : Fin 2), padLabel return_le (ReturnDispatch.entry (branch risk depth)))
    atStart.2.2.2 (ports_observed _ _ observed)
  have paddedAfter := pad_runsFrom return_le ReturnDispatch.code _ _ _ afterRun
  have atReturn : RunsFrom (rows (1 : Fin 2))
      (padCfg return_le ⟨ReturnDispatch.entry (branch risk depth), windowLast.Tape⟩)
      (after.map (padCfg return_le))
      (padCfg return_le ⟨ReturnDispatch.exitPort (branch risk depth), ReturnActual.finalTape risk depth risk left right⟩) := by
    rw [rows_return]
    exact paddedAfter
  have finishRun := block_runsFrom rows ports (1 : Fin 2) _ _ _ atReturn (ports_return _)
  have fullSegment := segment_append tailCode _ _ _ _ _ _ startSegment
    ⟨finishRun.1, finishRun.2.1, finishRun.2.2.1⟩ transfer
  let trace := (before.map (padCfg window_le)).map (blockCfg (p := 1) (0 : Fin 2)) ++
    (after.map (padCfg return_le)).map (blockCfg (p := 1) (1 : Fin 2))
  have run : RunsFrom tailCode
      ⟨0, Tape.mk₂ (BarePacket.west risk depth)
        (encodeDatum (.rational (FactorSource.factorValue risk depth : Rat)) ++ encodeDatum (.rational risk))⟩
      trace ⟨tailPort (branch risk depth), ReturnActual.finalTape risk depth risk left right⟩ := by
    have joined := segment_runsFrom tailCode _ _ _ fullSegment finishRun.2.2.2
    simpa only [trace, padCfg, padLabel, Fin.val_zero, Fin.mk_zero, tailPort, blockCfg,
      label, Nat.zero_mul, Nat.zero_add] using joined
  have length : trace.length = before.length + after.length := by
    dsimp only [trace]
    rw [List.length_append, List.length_map, List.length_map, List.length_map, List.length_map]
  refine ⟨left, right, trace, run, leftRoom, rightRoom, sum, ?_⟩
  rw [length]
  exact Nat.add_le_add beforeTime afterTime

theorem actual_port (risk : Rat) (depth : Nat) :
    finalPort (branch risk depth) =
      if (1/4 : Rat) ≤ (FactorSource.factorValue risk depth : Rat) * risk then truePort else falsePort := by
  by_cases capped : (1/4 : Rat) ≤ (FactorSource.factorValue risk depth : Rat) * risk
  · simp only [branch, capped, decide_true, ite_true]
    rfl
  · simp only [branch, capped, decide_false, ite_false]
    rfl

/-- ONE fixed machine before ALL original inputs. The actual head is at
the original B DATA, with the exact branch-specific markedScratch east
tape and the original archive. Every transfer and every prefix is paid. -/
theorem actual (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    ∃ (left right : Nat) (trace : List (MachineState cap)),
      Runs code (encode [.rational risk, .natural depth]) trace
        ⟨finalPort (branch risk depth), ReturnActual.finalTape risk depth risk left right⟩ ∧
      32 * width risk depth + 512 ≤ left ∧
      32 * width risk depth + 512 ≤ right + 1 -
        (Spatial.MulCap.output (FactorSource.factorValue risk depth : Rat) risk).length ∧
      left + right = Producer.left FixedConsumer.k (FactorSource.factorValue risk depth : Rat) risk +
        Spatial.MulCap.window (FactorSource.factorValue risk depth : Rat) risk (32 * width risk depth + 512) ∧
      trace.length ≤ timeCoefficient * scale risk depth ^ 8 ∧
      (∀ chargedLength clock, visitedSpace code chargedLength (trace.take clock) ≤
        chargedLength + 2 * (timeCoefficient * scale risk depth ^ 8) + 1) ∧
      (∀ clock, visitedSpace code (encode [.rational risk, .natural depth]).length (trace.take clock) ≤
        spaceCoefficient * scale risk depth ^ 8) := by
  obtain ⟨before, bareLast, bareRun, bareTape, beforeTime, _⟩ := BarePacket.original_bare_actual risk depth hr hd
  obtain ⟨left, right, after, afterRun, leftRoom, rightRoom, sum, afterTime⟩ := tail_actual risk depth hr
  have afterRun' : RunsFrom tailCode ⟨0, bareLast.Tape⟩ after
      ⟨tailPort (branch risk depth), ReturnActual.finalTape risk depth risk left right⟩ := by
    rw [bareTape]
    exact afterRun
  let trace := before.map (leftCfg (b := tailCap)) ++ after.map (rightCfg (a := 4405))
  have run : Runs code (encode [.rational risk, .natural depth]) trace
      ⟨finalPort (branch risk depth), ReturnActual.finalTape risk depth risk left right⟩ := by
    exact seq_runs BarePacket.machine tailCode _ bareLast _ before after bareRun afterRun'
  have barePower : scale risk depth ^ 3 ≤ scale risk depth ^ 8 :=
    Nat.pow_le_pow_right (scale_positive risk depth) (by decide : 3 ≤ 8)
  have bareBound : before.length ≤ 268435456 * scale risk depth ^ 8 :=
    beforeTime.trans (Nat.mul_le_mul_left 268435456 barePower)
  have fieldPower := original_power risk depth hr hd
  have windowBound : FixedConsumer.coefficient * (width risk depth + 1) ^ 8 ≤
      (FixedConsumer.coefficient * 16 ^ 8) * scale risk depth ^ 8 := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left FixedConsumer.coefficient fieldPower
  have returnBound := return_time_original risk depth left right hr hd sum
  have later := afterTime.trans (Nat.add_le_add windowBound returnBound)
  have time : trace.length ≤ timeCoefficient * scale risk depth ^ 8 := by
    have length : trace.length = before.length + after.length := by
      dsimp only [trace]
      rw [List.length_append, List.length_map, List.length_map]
    rw [length]
    calc
      _ ≤ 268435456 * scale risk depth ^ 8 +
          ((FixedConsumer.coefficient * 16 ^ 8) * scale risk depth ^ 8 +
            (2 * FixedConsumer.k * 16 ^ 8 + 300) * scale risk depth ^ 8) := Nat.add_le_add bareBound later
      _ = _ := by unfold timeCoefficient; ring
  have prefixes : ∀ chargedLength clock, visitedSpace code chargedLength (trace.take clock) ≤
      chargedLength + 2 * (timeCoefficient * scale risk depth ^ 8) + 1 := by
    intro chargedLength clock
    have space := PSTRTMTrace002.visitedSpace_le code chargedLength (trace.take clock)
    have taken : (trace.take clock).length ≤ trace.length := by
      rw [List.length_take]
      exact Nat.min_le_right _ _
    omega
  refine ⟨left, right, trace, run, leftRoom, rightRoom, sum, time, prefixes, ?_⟩
  intro clock
  have space := prefixes (encode [.rational risk, .natural depth]).length clock
  have inputPower : (encode [.rational risk, .natural depth]).length + 1 ≤ scale risk depth ^ 8 := by
    have input : (encode [.rational risk, .natural depth]).length + 1 ≤ scale risk depth := by unfold scale; omega
    exact input.trans (original_linear_power risk depth)
  unfold spaceCoefficient
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

end RootB23.Threshold.OriginalBridge

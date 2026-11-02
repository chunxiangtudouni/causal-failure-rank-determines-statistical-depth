module

public import Structure.RootB23_Threshold_Window_BarePayload_027
public import Structure.RootB23_Threshold_Window_MarshalSerialize_Actual_004

/-! The complete actual bare-pair window front. Allocation, four real far
copies, observed-bit restoration, prefix clearing, and count2 serialization
are one fixed-code execution. This front does not invoke minquarter. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.Producer
open Turing PSTRTMSeq005 PA17TMDivisionCompose006 PA17TMRatArithmeticParse002

def cap (k : Nat) : Nat := totalStates 32 (BarePayload.rowCap k) + 415 + 1
attribute [local implicit_reducible] cap
def code (k : Nat) : Machine (cap k) := seqMachine (BarePayload.machine k) RootB23.Threshold.Window.MarshalSerialize.code
def exit (k : Nat) : Fin (cap k + 1) := rightLabel (a := totalStates 32 (BarePayload.rowCap k)) (415 : Fin 416)
def left (k : Nat) (x y : Rat) : Nat := k * fieldWidth x y ^ 4 - 3
def coefficient (k : Nat) : Nat := BarePayload.coefficient k + 1024

theorem marshal_width (x y : Rat) : RootB23.Threshold.Window.MarshalSerialize.totalWidth x y = fieldWidth x y := by
  simp only [RootB23.Threshold.Window.MarshalSerialize.totalWidth, fieldWidth, numeratorDigits_length, denominatorDigits_length]

theorem marshal_fields (x y : Rat) : PayloadActual.fields x y = RootB23.Threshold.Window.MarshalSerialize.inputRight x y [] := by
  simp only [PayloadActual.fields, RootB23.Threshold.Window.MarshalSerialize.inputRight, RootB23.Threshold.Uncapped.Serialize.marker,
    List.append_assoc, List.cons_append, List.nil_append]

/-- No source-state, width, room, answer bit, or bodyRun is an original caller
qualification. k is a compile-time constant, chosen before every base/x/y. -/
theorem producer_actual (k : Nat) (positive : 0 < k) (base : List Bool)
    (x y : Rat) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ trace, RunsFrom (code k)
      ⟨0, Tape.mk₂ base (encodeDatum (.rational x) ++ encodeDatum (.rational y))⟩ trace
      ⟨exit k, Tape.mk₂ (List.replicate (left k x y) false ++ PayloadActual.archive base x y)
        (encode [.rational x, .rational y] ++ List.replicate 7 false)⟩ ∧
      trace.length ≤ coefficient k * (fieldWidth x y + 1) ^ 8 ∧
      ∀ inputLength clock, visitedSpace (code k) inputLength (trace.take clock) ≤
        inputLength + 2 * (coefficient k * (fieldWidth x y + 1) ^ 8) + 1 := by
  obtain ⟨before, beforeRun, beforeTime, _⟩ := BarePayload.bare_payload_actual k base x y
  let archive := List.replicate (left k x y) false ++ PayloadActual.archive base x y
  obtain ⟨after, afterRun, afterTime⟩ := RootB23.Threshold.Window.MarshalSerialize.actual_bounded archive [] x y hx hy
  have owned := PayloadActual.owned_seven (PayloadActual.archive base x y) (k * fieldWidth x y ^ 4)
    (PayloadActual.gap_at_least_three k positive x y)
  have middle : (BarePayload.final k base x y).Tape =
      Tape.mk₂ (List.replicate 7 false ++ archive) (RootB23.Threshold.Window.MarshalSerialize.inputRight x y []) := by
    rw [BarePayload.final_tape, owned, marshal_fields]
    rfl
  rw [← middle] at afterRun
  simp only [List.append_nil] at afterRun
  rw [marshal_width] at afterTime
  let trace := before.map (leftCfg (b := 415)) ++
    after.map (rightCfg (a := totalStates 32 (BarePayload.rowCap k)))
  have combined := seq_runsFrom (BarePayload.machine k) RootB23.Threshold.Window.MarshalSerialize.code _ _ _ before after beforeRun afterRun
  have run : RunsFrom (code k)
      ⟨0, Tape.mk₂ base (encodeDatum (.rational x) ++ encodeDatum (.rational y))⟩ trace
      ⟨exit k, Tape.mk₂ archive (encode [.rational x, .rational y] ++ List.replicate 7 false)⟩ := by
    simpa only [code, trace, exit, leftCfg, leftLabel, rightCfg, Fin.val_zero, Fin.mk_zero] using combined
  have time : trace.length ≤ coefficient k * (fieldWidth x y + 1) ^ 8 := by
    have square : (fieldWidth x y + 1) ^ 2 ≤ (fieldWidth x y + 1) ^ 8 :=
      Nat.pow_le_pow_right (by omega : 1 ≤ fieldWidth x y + 1) (by decide)
    simp only [trace, List.length_append, List.length_map]
    unfold coefficient
    nlinarith
  refine ⟨trace, run, time, ?_⟩
  intro inputLength clock
  have space := PSTRTMTrace002.visitedSpace_le (code k) inputLength (trace.take clock)
  have taken : (trace.take clock).length ≤ trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  omega

def fixedCoefficient (callee linear constant : Nat) : Nat := Margin.coefficient callee linear constant
def fixedCode (callee linear constant : Nat) : Machine (cap (fixedCoefficient callee linear constant)) :=
  code (fixedCoefficient callee linear constant)

theorem fixed_positive (callee linear constant : Nat) : 0 < fixedCoefficient callee linear constant := by
  unfold fixedCoefficient Margin.coefficient
  omega

theorem left_room (callee linear constant : Nat) (x y : Rat) :
    callee * ((encode [.rational x, .rational y]).length + 1) ^ 4 +
      2 * (encode [.rational x, .rational y]).length + (linear * fieldWidth x y + constant) + 2 ≤
        left (fixedCoefficient callee linear constant) x y := by
  have length := pair_length x y
  have bound := Margin.exact_window_covered callee linear constant (fieldWidth x y)
    (Margin.rational_width_at_least_four x y)
  simpa only [length, left, fixedCoefficient, fieldWidth, Nat.add_assoc, Nat.reduceAdd] using bound

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.Producer

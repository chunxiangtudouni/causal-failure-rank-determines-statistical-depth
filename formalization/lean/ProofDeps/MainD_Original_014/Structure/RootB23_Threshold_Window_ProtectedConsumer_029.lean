module

public import Structure.RootB23_Threshold_Window_Producer_028
public import Structure.RootB23_Threshold_Spatial_MulCap_001

/-! The complete producer feeds the one frozen compound callee. There is a
single physical frame around RAW64 -> ProductPacket -> actual minquarter.
The TRUE saved-left tape is retained exactly; no WEST return is claimed. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.ProtectedConsumer
open Turing PSTRTMSeq005 PA17TMDivisionCompose006 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticFrame005
open _root_.RootB23.Threshold.Spatial

def k (linear constant : Nat) : Nat := Producer.fixedCoefficient MulCap.timeCoefficient linear constant
def prefixCap (linear constant : Nat) : Nat := Producer.cap (k linear constant)
def cap (linear constant : Nat) : Nat := prefixCap linear constant + MulCap.cap + 1
attribute [local implicit_reducible] prefixCap cap
def code (linear constant : Nat) : Machine (cap linear constant) :=
  seqMachine (Producer.code (k linear constant)) MulCap.code

def truePort (linear constant : Nat) : Fin (cap linear constant + 1) :=
  rightLabel (a := prefixCap linear constant) (rightLabel (a := MulCap.packetCap) (1365 : Fin 1583))
def falsePort (linear constant : Nat) : Fin (cap linear constant + 1) :=
  rightLabel (a := prefixCap linear constant) (rightLabel (a := MulCap.packetCap) (1582 : Fin 1583))
def finalPort (linear constant : Nat) (x y : Rat) : Fin (cap linear constant + 1) :=
  if (1/4 : Rat) ≤ x * y then truePort linear constant else falsePort linear constant

def spare (linear constant : Nat) (x y : Rat) : Nat := linear * fieldWidth x y + constant
def coefficient (linear constant : Nat) : Nat := Producer.coefficient (k linear constant) + k linear constant

theorem tape_right_zeros (left word : List Bool) (n : Nat) :
    Tape.mk₂ left (word ++ List.replicate n false) = Tape.mk₂ left word := by
  apply congrArg (Tape.mk' (ListBlank.mk left))
  apply Quotient.sound
  exact Or.inr ⟨n, by rfl⟩

theorem lift_final (linear constant : Nat) (x y : Rat) (positive : 0 < x * y) :
    rightLabel (a := prefixCap linear constant) (MulCap.final x y).q = finalPort linear constant x y := by
  have old := MulCap.final_control x y positive
  have trueVal : (1365 : Fin 1583).val = 1365 := by decide
  have falseVal : (1582 : Fin 1583).val = 1582 := by decide
  apply Fin.ext
  by_cases branch : (1/4 : Rat) ≤ x * y
  · simp only [finalPort, branch, ite_true, truePort, rightLabel, trueVal]
    rw [old]
    simp only [branch, ite_true]
  · simp only [finalPort, branch, ite_false, falsePort, rightLabel, falseVal]
    rw [old]
    simp only [branch, ite_false]

/-- Fixed before every original bare packet. Both physical credits follow
from the actual producer; room is not an original caller qualification. The
arbitrary WEST archive has the same absolute boundary after the whole call. -/
theorem protected_actual (linear constant : Nat) (base : List Bool)
    (x y : Rat) (hx : 0 ≤ x) (hy : 0 ≤ y) (positive : 0 < x * y) :
    ∃ (finalLeft finalRight : Nat) (trace : List (MachineState (cap linear constant)))
      (last : MachineState (cap linear constant)),
      RunsFrom (code linear constant)
        ⟨0, Tape.mk₂ base (encodeDatum (.rational x) ++ encodeDatum (.rational y))⟩ trace last ∧
      last.q = finalPort linear constant x y ∧
      last.Tape = Tape.mk₂
        (windowPrefix finalLeft (ListBlank.mk (MulCap.oldLeft x y)) ++ PayloadActual.archive base x y)
        (MulCap.output x y ++ List.replicate (finalRight + 1 - (MulCap.output x y).length) false) ∧
      spare linear constant x y ≤ finalLeft ∧
      spare linear constant x y ≤ finalRight + 1 - (MulCap.output x y).length ∧
      finalLeft + finalRight = Producer.left (k linear constant) x y + MulCap.window x y (spare linear constant x y) ∧
      trace.length ≤ coefficient linear constant * (fieldWidth x y + 1) ^ 8 ∧
      ∀ inputLength clock, visitedSpace (code linear constant) inputLength (trace.take clock) ≤
        inputLength + 2 * (coefficient linear constant * (fieldWidth x y + 1) ^ 8) + 1 := by
  have kPositive := Producer.fixed_positive MulCap.timeCoefficient linear constant
  obtain ⟨before, beforeRun, beforeTime, _⟩ := Producer.producer_actual (k linear constant) kPositive base x y hx hy
  have leftRoom : MulCap.window x y (spare linear constant x y) ≤ Producer.left (k linear constant) x y := by
    simpa only [MulCap.window, MulCap.time, MulCap.inputLength, spare, k] using
      Producer.left_room MulCap.timeCoefficient linear constant x y
  obtain ⟨finalLeft, finalRight, after, oldLast, afterRun, afterControl, afterTape,
      leftSpare, rightSpare, sum, afterTime, _⟩ := MulCap.framed_contract x y positive
        (PayloadActual.archive base x y) [] (spare linear constant x y)
        (Producer.left (k linear constant) x y) (MulCap.window x y (spare linear constant x y)) leftRoom (Nat.le_refl _)
  have initialTape : Tape.mk₂ (List.replicate (Producer.left (k linear constant) x y) false ++ PayloadActual.archive base x y)
      (encode [.rational x, .rational y] ++ List.replicate 7 false) =
      Tape.mk₂ (List.replicate (Producer.left (k linear constant) x y) false ++ PayloadActual.archive base x y)
        (encode [.rational x, .rational y] ++
          List.replicate (MulCap.window x y (spare linear constant x y) + 1 - MulCap.inputLength x y) false ++ []) := by
    simp only [List.append_nil, tape_right_zeros]
  rw [← initialTape] at afterRun
  let trace := before.map (leftCfg (b := MulCap.cap)) ++ after.map (rightCfg (a := Producer.cap (k linear constant)))
  let last := rightCfg (a := Producer.cap (k linear constant)) oldLast
  have combined := seq_runsFrom (Producer.code (k linear constant)) MulCap.code _ _ _ before after beforeRun afterRun
  have run : RunsFrom (code linear constant)
      ⟨0, Tape.mk₂ base (encodeDatum (.rational x) ++ encodeDatum (.rational y))⟩ trace last := by
    simpa only [code, trace, last, prefixCap, leftCfg, leftLabel, Fin.val_zero, Fin.mk_zero] using combined
  have port : last.q = finalPort linear constant x y := by
    change rightLabel (a := prefixCap linear constant) oldLast.q = _
    rw [afterControl]
    exact lift_final linear constant x y positive
  have whole : last.Tape = Tape.mk₂
      (windowPrefix finalLeft (ListBlank.mk (MulCap.oldLeft x y)) ++ PayloadActual.archive base x y)
      (MulCap.output x y ++ List.replicate (finalRight + 1 - (MulCap.output x y).length) false) := by
    simpa only [last, rightCfg, List.append_nil] using afterTape
  have calleeBound : MulCap.time x y ≤ k linear constant * fieldWidth x y ^ 4 := by
    unfold MulCap.window Producer.left at leftRoom
    omega
  have fourth : fieldWidth x y ^ 4 ≤ (fieldWidth x y + 1) ^ 8 :=
    (Nat.pow_le_pow_left (Nat.le_succ (fieldWidth x y)) 4).trans
      (Nat.pow_le_pow_right (by omega : 1 ≤ fieldWidth x y + 1) (by decide : 4 ≤ 8))
  have calleePower := calleeBound.trans (Nat.mul_le_mul_left (k linear constant) fourth)
  have time : trace.length ≤ coefficient linear constant * (fieldWidth x y + 1) ^ 8 := by
    simp only [trace, List.length_append, List.length_map]
    calc
      _ ≤ Producer.coefficient (k linear constant) * (fieldWidth x y + 1) ^ 8 +
          k linear constant * (fieldWidth x y + 1) ^ 8 :=
        Nat.add_le_add beforeTime (afterTime.trans calleePower)
      _ = _ := by unfold coefficient; rw [Nat.add_mul]
  refine ⟨finalLeft, finalRight, trace, last, run, port, whole, leftSpare, rightSpare, sum, time, ?_⟩
  intro inputLength clock
  have space := PSTRTMTrace002.visitedSpace_le (code linear constant) inputLength (trace.take clock)
  have taken : (trace.take clock).length ≤ trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  omega

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.ProtectedConsumer

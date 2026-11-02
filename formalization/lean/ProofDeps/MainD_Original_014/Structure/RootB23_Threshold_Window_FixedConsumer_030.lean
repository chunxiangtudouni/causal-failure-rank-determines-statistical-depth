module

public import Structure.RootB23_Threshold_Window_ProtectedConsumer_029

/-! The actual return-B requirement fixes the downstream reserve to 32W+512.
Both constants, the quartic coefficient, every program row and both actual
post-callee ports are fixed before every original bare input. -/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.FixedConsumer
open Turing PSTRTMSeq005 PA17TMRatArithmeticParse002 PA17TMRatArithmeticFrame005
open _root_.RootB23.Threshold.Spatial

def k : Nat := ProtectedConsumer.k 32 512
def cap : Nat := ProtectedConsumer.cap 32 512
attribute [local implicit_reducible] cap
def code : Machine cap := ProtectedConsumer.code 32 512
def truePort : Fin (cap + 1) := ProtectedConsumer.truePort 32 512
def falsePort : Fin (cap + 1) := ProtectedConsumer.falsePort 32 512
def coefficient : Nat := ProtectedConsumer.coefficient 32 512

theorem fixed_coefficient : k = 1296 * MulCap.timeCoefficient + 581 := by
  unfold k ProtectedConsumer.k Producer.fixedCoefficient Margin.coefficient
  omega

theorem actual (base : List Bool) (x y : Rat) (hx : 0 ≤ x) (hy : 0 ≤ y) (positive : 0 < x * y) :
    ∃ (finalLeft finalRight : Nat) (trace : List (MachineState cap)) (last : MachineState cap),
      RunsFrom code ⟨0, Tape.mk₂ base (encodeDatum (.rational x) ++ encodeDatum (.rational y))⟩ trace last ∧
      last.q = (if (1/4 : Rat) ≤ x * y then truePort else falsePort) ∧
      last.Tape = Tape.mk₂
        (windowPrefix finalLeft (ListBlank.mk (MulCap.oldLeft x y)) ++ PayloadActual.archive base x y)
        (MulCap.output x y ++ List.replicate (finalRight + 1 - (MulCap.output x y).length) false) ∧
      32 * fieldWidth x y + 512 ≤ finalLeft ∧
      32 * fieldWidth x y + 512 ≤ finalRight + 1 - (MulCap.output x y).length ∧
      finalLeft + finalRight = Producer.left k x y + MulCap.window x y (32 * fieldWidth x y + 512) ∧
      trace.length ≤ coefficient * (fieldWidth x y + 1) ^ 8 ∧
      ∀ inputLength clock, visitedSpace code inputLength (trace.take clock) ≤
        inputLength + 2 * (coefficient * (fieldWidth x y + 1) ^ 8) + 1 := by
  exact ProtectedConsumer.protected_actual 32 512 base x y hx hy positive

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.FixedConsumer

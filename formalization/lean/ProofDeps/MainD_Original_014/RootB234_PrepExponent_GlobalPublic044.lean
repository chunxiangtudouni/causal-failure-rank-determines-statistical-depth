module

public import RootB234_PrepExponent_GlobalFromState043
public import RootB234_ECost_Public007

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.PrepExponent.Global.Public

open Turing
open PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

/-- One fixed original exponent producer, with all resources on the
same actual execution witness. The cost coefficient and degree precede
every number, rational input, bank and initial finite control state. -/
theorem actual_default (background : Stack → List Bool) (memory : Store C)
    (tail : List Bool) (budget : Rat) (number : Nat) (positive : 0 < budget)
    (input : background 8 = B23_4_RatWordPrep.NatField.packet number []) :
    ∃ (afterMemory : Store C) (part : Segment .halt
      (state default memory (QLoop.bank background tail [] (RatInput.Encoder.packet budget []) []))
      (state .done afterMemory
        (bank background (RatInput.Encoder.packet (qValue number) (RatInput.Encoder.packet budget tail))
          (B23_4_RatWordPrep.NatField.packet (BinaryExperiment.quotaExponent budget number) [])
          (RatInput.Encoder.packet budget []) [] [] []))),
      QLoop.rootContext afterMemory = QLoop.rootContext memory ∧ afterMemory.2 = (false,false) ∧
      PolynomialBounds RootB234.ECost.totalCoefficient 5 (resourceScale background tail budget number) part.trace := by
  obtain ⟨afterMemory,part,context,flags,count⟩ := actual_original .halt background memory tail budget number positive input
  exact ⟨afterMemory,part,context,flags,
    original_resources_of_cap background memory tail budget number _ part _ 5 (by decide)
      (count.trans (RootB234.ECost.total_cost background tail budget number))⟩

/-- Parent composition starts at its actual physical state. Packet and
empty-bank facts are representation invariants which its producer must
discharge; no state reset, supplied exponent or supplied fuel occurs. -/
theorem actual_current (before : State C) (budget : Rat) (number : Nat)
    (positive : 0 < budget) (active : before.l = some default)
    (input : before.stk 8 = B23_4_RatWordPrep.NatField.packet number [])
    (packet : before.stk 15 = RatInput.Encoder.packet budget [])
    (empty : ∀ slot, Owned slot → before.stk slot = []) :
    ∃ (afterMemory : Store C) (part : Segment .halt before
      (state .done afterMemory
        (bank before.stk (RatInput.Encoder.packet (qValue number) (RatInput.Encoder.packet budget (before.stk 7)))
          (B23_4_RatWordPrep.NatField.packet (BinaryExperiment.quotaExponent budget number) [])
          (RatInput.Encoder.packet budget []) [] [] []))),
      QLoop.rootContext afterMemory = QLoop.rootContext before.var ∧ afterMemory.2 = (false,false) ∧
      PolynomialBounds RootB234.ECost.totalCoefficient 5
        (resourceScale before.stk (before.stk 7) budget number) part.trace :=
  from_state_resources before budget number positive active input packet empty
    RootB234.ECost.totalCoefficient 5 (by decide)
    (RootB234.ECost.total_cost before.stk (before.stk 7) budget number)

theorem coefficient_positive : 0 < RootB234.ECost.totalCoefficient := RootB234.ECost.totalCoefficient_pos

end RootB234.PrepExponent.Global.Public

module

public import RootB234_PrepExponent_QLoopResources029

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.QLoop
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource

theorem fullCoefficient_positive : 0 < fullCoefficient := by unfold fullCoefficient;omega

theorem caller_scale (background : Stack → List Bool) (budget : Rat) (number : Nat)
    (input : background 15=RatInput.Encoder.packet budget []) :
    fullScale background (background 7) budget number ≤ 3*(RatInput.occupied background+number+1) := by
  have cache := RatInput.Encoder.point_mass background 7
  have operand := RatInput.Encoder.point_mass background 15
  rw [input,RatInput.Encoder.packet_length] at operand
  unfold fullScale
  simp only [List.length_nil] at operand
  omega

namespace Public

theorem actual {C : Type*} (background : Stack → List Bool) (memory : Store C)
    (tail : List Bool) (budget : Rat) (number : Nat)
    (input : background 8=B23_4_RatWordPrep.NatField.packet number []) :
    ∃ (afterMemory : Store C) (part : Segment .halt
      (state default memory (bank background tail [] (RatInput.Encoder.packet budget []) []))
      (state .done afterMemory
        (bank background (RatInput.Encoder.packet ((12 : Rat)*2^number) (RatInput.Encoder.packet budget tail)) [] [] []))),
      rootContext afterMemory=rootContext memory ∧ afterMemory.2=(false,false) ∧
      UniformBounds background tail budget number part.trace ∧
      (∀ current∈part.trace.dropLast,current.l≠some .done) ∧
      RatInput.occupied
        (bank background (RatInput.Encoder.packet ((12 : Rat)*2^number) (RatInput.Encoder.packet budget tail)) [] [] []) ≤
        512*fullScale background tail budget number := by
  obtain ⟨afterMemory,part,context,flags,count⟩ := full_actual_uniform .halt background memory tail budget number input
  have proper := NativeMulLink.no_early_halt_port (program (C:=C) .halt) .done rfl part.trace _ part.chain part.last rfl
  exact ⟨afterMemory,part,context,flags,segment_resources background memory tail budget number _ part count,
    proper,final_mass background tail budget number⟩

/-- A single finite code and all syntax/resource constants are fixed
before every original numeric value or physical bank. This is a callee:
ACTIVE done has not executed its caller, and is not a whole-prep HALT. -/
theorem fixed_source (C : Type*) [Finite C] :
    ∃ (source : Label → Statement C) (allowed : Finset Label) (time space clock scan charge : Nat),
      source=program .halt ∧ TM2.Supports source allowed ∧ Finite (Store C) ∧
      time=fullCoefficient ∧ space=spaceCoefficient C ∧ clock=clockCoefficient C ∧
      scan=scanCoefficient C ∧ charge=chargeCoefficient C ∧ 0<time ∧
      (∀ point,AuxWorkspace.pushes (source point) ≤ pushAllowance C ∧
        ScannerClock.actions (source point) ≤ actionAllowance C) ∧
      ∀ (background : Stack → List Bool) (memory : Store C) (tail : List Bool) (budget : Rat) (number : Nat),
        background 8=B23_4_RatWordPrep.NatField.packet number [] →
        ∃ (afterMemory : Store C) (part : Segment .halt
          (state default memory (bank background tail [] (RatInput.Encoder.packet budget []) []))
          (state .done afterMemory
            (bank background (RatInput.Encoder.packet ((12 : Rat)*2^number) (RatInput.Encoder.packet budget tail)) [] [] []))),
          rootContext afterMemory=rootContext memory ∧ afterMemory.2=(false,false) ∧
          UniformBounds background tail budget number part.trace ∧
          (∀ current∈part.trace.dropLast,current.l≠some .done) := by
  refine ⟨program .halt,Finset.univ,fullCoefficient,spaceCoefficient C,clockCoefficient C,
    scanCoefficient C,chargeCoefficient C,rfl,supports .halt,finite_store,rfl,rfl,rfl,rfl,rfl,
    fullCoefficient_positive,(fun point => ⟨pushes_le point,actions_le point⟩),?_⟩
  intro background memory tail budget number input
  obtain ⟨afterMemory,part,context,flags,bounds,proper,_finalMass⟩ := actual background memory tail budget number input
  exact ⟨afterMemory,part,context,flags,bounds,proper⟩

end Public
end RootB234.PrepExponent.QLoop

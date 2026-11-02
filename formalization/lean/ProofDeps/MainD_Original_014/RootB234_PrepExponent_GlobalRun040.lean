module

public import RootB234_PrepExponent_GlobalCycle039
public import RootB23_PrepScalarMinimality_001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.Global
open Turing
open PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

def targetExponent (budget : Rat) (number : Nat) : Nat := BinaryExperiment.quotaExponent budget number
def yValue (budget : Rat) (exponent : Nat) : Rat := (2 : Rat)^exponent*budget

theorem q_reference (number : Nat) : qValue number=referenceQuotaConstant number := by
  unfold qValue referenceQuotaConstant
  rw [pow_succ]
  ring

theorem target_test (budget : Rat) (positive : 0<budget) (number exponent : Nat) :
    targetExponent budget number≤exponent ↔ 1≤exponent ∧ rValue number≤yValue budget exponent := by
  simpa only [targetExponent,rValue,q_reference,yValue] using
    RootB23.PrepScalar.exponent_le_iff budget positive number exponent

theorem target_pass (budget : Rat) (positive : 0<budget) (number : Nat) :
    1≤targetExponent budget number ∧ rValue number≤yValue budget (targetExponent budget number) :=
  (target_test budget positive number _).mp le_rfl

theorem target_fail (budget : Rat) (positive : 0<budget) (number exponent : Nat)
    (one : 1≤exponent) (earlier : exponent<targetExponent budget number) :
    ¬rValue number≤yValue budget exponent := by
  intro passes
  have cap := (target_test budget positive number exponent).mpr ⟨one,passes⟩
  omega

theorem y_step (budget : Rat) (exponent : Nat) : 2*yValue budget exponent=yValue budget (exponent+1) := by
  unfold yValue
  rw [pow_succ]
  ring

def loopCost (background : Stack → List Bool) (tail : List Bool) (budget : Rat) (number : Nat) : Nat → Nat → Nat
  | 0,exponent =>
      compareCost background (RatInput.Encoder.packet (qValue number) (RatInput.Encoder.packet budget tail))
        (B23_4_RatWordPrep.NatField.packet exponent []) (rValue number) (yValue budget exponent)+
      stopCost (rValue number) (yValue budget exponent) (qValue number) budget
  | remaining+1,exponent =>
      compareCost background (RatInput.Encoder.packet (qValue number) (RatInput.Encoder.packet budget tail))
        (B23_4_RatWordPrep.NatField.packet exponent []) (rValue number) (yValue budget exponent)+
      repeatCost background (RatInput.Encoder.packet (qValue number) (RatInput.Encoder.packet budget tail))
        (rValue number) (yValue budget exponent) exponent+
      loopCost background tail budget number remaining (exponent+1)

/-- The induction index is a proof of the original least exponent. It
is absent from the executable source and from finite control memory. -/
theorem loop_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (tail : List Bool) (budget : Rat) (number remaining exponent : Nat) (positive : 0<budget)
    (one : 1≤exponent) (finish : exponent+remaining=targetExponent budget number) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state (.packet .compareCopyY 0) memory
        (bank background
          (RatInput.Encoder.packet (yValue budget exponent) (RatInput.Encoder.packet (rValue number)
            (RatInput.Encoder.packet (qValue number) (RatInput.Encoder.packet budget tail))))
          (B23_4_RatWordPrep.NatField.packet exponent []) [] [] [] []))
      (state .done afterMemory
        (bank background (RatInput.Encoder.packet (qValue number) (RatInput.Encoder.packet budget tail))
          (B23_4_RatWordPrep.NatField.packet (targetExponent budget number) [])
          (RatInput.Encoder.packet budget []) [] [] []))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧ afterMemory.2=(false,false) ∧
      part.trace.length ≤ loopCost background tail budget number remaining exponent := by
  let rest := RatInput.Encoder.packet (qValue number) (RatInput.Encoder.packet budget tail)
  induction remaining generalizing memory exponent with
  | zero =>
    have equal : exponent=targetExponent budget number := by omega
    subst exponent
    have passes := (target_pass budget positive number).2
    obtain ⟨cmpMemory,comparison,context,_flags,count⟩ := compare_actual caller background memory rest
      (B23_4_RatWordPrep.NatField.packet (targetExponent budget number) [])
      (rValue number) (yValue budget (targetExponent budget number))
    let compared : Segment caller
        (state (.packet .compareCopyY 0) memory
          (bank background (RatInput.Encoder.packet (yValue budget (targetExponent budget number))
            (RatInput.Encoder.packet (rValue number) rest))
            (B23_4_RatWordPrep.NatField.packet (targetExponent budget number) []) [] [] [] []))
        (state (.packet .stopDropY 0) cmpMemory
          (bank background (RatInput.Encoder.packet (yValue budget (targetExponent budget number))
            (RatInput.Encoder.packet (rValue number) rest))
            (B23_4_RatWordPrep.NatField.packet (targetExponent budget number) []) [] [] [] [])) :=
      ⟨comparison.trace,comparison.first,comparison.chain,comparison.last.trans (congrArg some (by rw [ite_eq_left passes]))⟩
    obtain ⟨stopped,stopCount⟩ := stop_actual caller background cmpMemory tail
      (B23_4_RatWordPrep.NatField.packet (targetExponent budget number) [])
      (rValue number) (yValue budget (targetExponent budget number)) (qValue number) budget
    let whole := compared.append stopped
    refine ⟨(cmpMemory.1,false,false),whole,context,rfl,?_⟩
    have compareCount : compared.trace.length ≤ compareCost background rest
        (B23_4_RatWordPrep.NatField.packet (targetExponent budget number) [])
        (rValue number) (yValue budget (targetExponent budget number)) := count
    have joined : whole.trace.length ≤ compared.trace.length+stopped.trace.length := compared.append_length stopped
    unfold loopCost
    dsimp only [rest] at compareCount
    omega
  | succ remaining ih =>
    have earlier : exponent<targetExponent budget number := by omega
    have fails := target_fail budget positive number exponent one earlier
    obtain ⟨cmpMemory,comparison,cmpContext,_cmpFlags,cmpCount⟩ := compare_actual caller background memory rest
      (B23_4_RatWordPrep.NatField.packet exponent []) (rValue number) (yValue budget exponent)
    let compared : Segment caller
        (state (.packet .compareCopyY 0) memory
          (bank background (RatInput.Encoder.packet (yValue budget exponent) (RatInput.Encoder.packet (rValue number) rest))
            (B23_4_RatWordPrep.NatField.packet exponent []) [] [] [] []))
        (state (.packet .repeatCopyY 0) cmpMemory
          (bank background (RatInput.Encoder.packet (yValue budget exponent) (RatInput.Encoder.packet (rValue number) rest))
            (B23_4_RatWordPrep.NatField.packet exponent []) [] [] [] [])) :=
      ⟨comparison.trace,comparison.first,comparison.chain,comparison.last.trans (congrArg some (by rw [ite_eq_right fails]))⟩
    obtain ⟨nextMemory,repeated,repeatContext,repeatFlags,repeatCount⟩ := repeat_actual caller background cmpMemory rest
      (rValue number) (yValue budget exponent) exponent
    let advanced : Segment caller
        (state (.packet .repeatCopyY 0) cmpMemory
          (bank background (RatInput.Encoder.packet (yValue budget exponent) (RatInput.Encoder.packet (rValue number) rest))
            (B23_4_RatWordPrep.NatField.packet exponent []) [] [] [] []))
        (state (.packet .compareCopyY 0) nextMemory
          (bank background (RatInput.Encoder.packet (yValue budget (exponent+1)) (RatInput.Encoder.packet (rValue number) rest))
            (B23_4_RatWordPrep.NatField.packet (exponent+1) []) [] [] [] [])) :=
      ⟨repeated.trace,repeated.first,repeated.chain,repeated.last.trans (congrArg some (by rw [y_step budget exponent]))⟩
    have nextOne : 1≤exponent+1 := by omega
    have nextFinish : exponent+1+remaining=targetExponent budget number := by omega
    obtain ⟨afterMemory,back,backContext,backFlags,backCount⟩ := ih nextMemory (exponent+1) nextOne nextFinish
    let front := compared.append advanced
    let whole := front.append back
    refine ⟨afterMemory,whole,backContext.trans (repeatContext.trans cmpContext),backFlags,?_⟩
    have compareCount : compared.trace.length ≤ compareCost background rest
        (B23_4_RatWordPrep.NatField.packet exponent []) (rValue number) (yValue budget exponent) := cmpCount
    have advanceCount : advanced.trace.length ≤ repeatCost background rest (rValue number) (yValue budget exponent) exponent := repeatCount
    have frontCount : front.trace.length ≤ compared.trace.length+advanced.trace.length := compared.append_length advanced
    have wholeCount : whole.trace.length ≤ front.trace.length+back.trace.length := front.append_length back
    unfold loopCost
    dsimp only [rest] at compareCount advanceCount
    omega

def totalCost (background : Stack → List Bool) (tail : List Bool) (budget : Rat) (number : Nat) : Nat :=
  initialCost background tail budget number+
    loopCost background tail budget number (targetExponent budget number-1) 1

/-- Full original exponent production in one fixed source: actual N8
and budget15 are the only numeric inputs. The final physical E11 packet
is exactly the paper's quotaExponent; original budget15 is restored. -/
theorem actual_original (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (tail : List Bool) (budget : Rat) (number : Nat) (positive : 0<budget)
    (input : background 8=B23_4_RatWordPrep.NatField.packet number []) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state default memory (QLoop.bank background tail [] (RatInput.Encoder.packet budget []) []))
      (state .done afterMemory
        (bank background (RatInput.Encoder.packet (qValue number) (RatInput.Encoder.packet budget tail))
          (B23_4_RatWordPrep.NatField.packet (BinaryExperiment.quotaExponent budget number) [])
          (RatInput.Encoder.packet budget []) [] [] []))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧ afterMemory.2=(false,false) ∧
      part.trace.length ≤ totalCost background tail budget number := by
  obtain ⟨initialMemory,initial,initialContext,_initialFlags,initialCount⟩ :=
    initial_actual caller background memory tail budget number input
  let ready : Segment caller
      (state default memory (QLoop.bank background tail [] (RatInput.Encoder.packet budget []) []))
      (state (.packet .compareCopyY 0) initialMemory
        (bank background (RatInput.Encoder.packet (yValue budget 1) (RatInput.Encoder.packet (rValue number)
          (RatInput.Encoder.packet (qValue number) (RatInput.Encoder.packet budget tail))))
          (B23_4_RatWordPrep.NatField.packet 1 []) [] [] [] [])) :=
    ⟨initial.trace,initial.first,initial.chain,initial.last.trans (congrArg some (by simp only [yValue,pow_one]))⟩
  have one := (target_pass budget positive number).1
  have finish : 1+(targetExponent budget number-1)=targetExponent budget number := by omega
  obtain ⟨afterMemory,back,backContext,backFlags,backCount⟩ := loop_actual caller background initialMemory tail budget number
    (targetExponent budget number-1) 1 positive (by decide) finish
  let whole := ready.append back
  refine ⟨afterMemory,whole,backContext.trans initialContext,backFlags,?_⟩
  have readyCount : ready.trace.length ≤ initialCost background tail budget number := initialCount
  have joined : whole.trace.length ≤ ready.trace.length+back.trace.length := ready.append_length back
  unfold totalCost
  omega

end RootB234.PrepExponent.Global

module
public import Structure.PA17_TM_RatArithmetic_RatDivController_070a

/-! The actual original all-input division run. The proof splits on y=0
only after proving the fixed machine's observed finite-control branch is
that same branch. All physical prefix and terminal traces are retained. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRatDivController070

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticWideCache045
open PA17TMRatArithmeticMulController057 (narrow64 widen64)
open PA17TMRatArithmeticDivPrefix067 (prefixCap prefixMemory prefixFinal observed
  prefixFinal_decode prefixFinal_old_memory observed_yzero mRecord dRecord prefixTimeCoefficient)
open PA17TMRatArithmeticRatDivFields066
attribute [local implicit_reducible] component zeroComponent normalComponent normalStates controllerCap
  PA17TMRatArithmeticDivPrefix067.prefixComponent

def originalPower (x y : Rat) : Nat := ((encode [.rational x,.rational y]).length+1)^4
def finishCoefficient : Nat := PA17TMRatArithmeticDivZero068.coefficient+
  PA17TMRatArithmeticRatDivSuffix069.normalTimeCoefficient
def divTimeCoefficient : Nat := prefixTimeCoefficient+finishCoefficient
def divResourceCoefficient : Nat := 2*divTimeCoefficient+2
theorem divResourceCoefficient_pos : 0<divResourceCoefficient := by unfold divResourceCoefficient;omega
private theorem zero_budget : PA17TMRatArithmeticDivZero068.coefficient≤finishCoefficient := by
  unfold finishCoefficient;omega
private theorem normal_budget : PA17TMRatArithmeticRatDivSuffix069.normalTimeCoefficient≤finishCoefficient := by
  unfold finishCoefficient;omega
private theorem time_le_resource : divTimeCoefficient≤divResourceCoefficient := by
  unfold divResourceCoefficient;omega
private theorem cells_le_resource : 2*divTimeCoefficient+1≤divResourceCoefficient := by
  unfold divResourceCoefficient;omega

private theorem zero_widths (x y : Rat) (gm gd : Nat) :
    ∀ r∈[mRecord x y gm,dRecord x y gd],r.digits.length≤fieldWidth x y := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · simpa only [mRecord,PA17TMRatArithmeticNativeTail055.resultRecord,
      PSTRTMNatValue017.rawPayload,List.length_ofFn] using divMagnitude_bits x y
  · simpa only [dRecord,PA17TMRatArithmeticNativeTail055.resultRecord,
      PSTRTMNatValue017.rawPayload,List.length_ofFn] using divDenominator_bits x y

private theorem old_memory (x y : Rat) (gm gd : Nat) :
    narrow64 (observed x y)=PA17TMRatArithmeticMulStart049.actualMemory x y := by
  have h := prefixFinal_old_memory x y gm gd
  rw [prefixFinal_decode] at h
  apply Fin.ext
  exact h

private theorem combined_length (x y : Rat) (tp : List (MachineState prefixCap)) (phase : Fin 3)
    (tt : List (MachineState (component phase).states))
    (hp : tp.length≤prefixTimeCoefficient*originalPower x y)
    (ht : tt.length≤finishCoefficient*originalPower x y) :
    (liftTrace (0 : Fin 3) tp++liftTrace phase tt).length≤divTimeCoefficient*originalPower x y := by
  have lp : (liftTrace (0 : Fin 3) tp).length=tp.length := liftTrace_length _ _
  have lt : (liftTrace phase tt).length=tt.length := liftTrace_length _ _
  rw [List.length_append,lp,lt]
  calc
    _ ≤ prefixTimeCoefficient*originalPower x y+finishCoefficient*originalPower x y := Nat.add_le_add hp ht
    _ = _ := by unfold divTimeCoefficient;ring

/-- No D-nonzero qualification on original inputs. x/0 and 0/0 take the
actual observed zero branch; all other inputs enter frozen057 at phase4. -/
theorem original_div_runs (x y : Rat) :
    ∃ trace final, Runs divMachine (encode [.rational x,.rational y]) trace final ∧
      final.Tape=Tape.mk₁ (encode [.rational (x/y)]) ∧
      trace.length≤divTimeCoefficient*originalPower x y := by
  obtain ⟨gm,gd,tp,_lm,um,_ld,ud,rp,lenP⟩ := PA17TMRatArithmeticDivPrefix067.original_prefix_runs x y
  have prefixRun : PSTRTMSeq005.RunsFrom PA17TMRatArithmeticDivPrefix067.prefixMachine
      (TM0.init (encode [.rational x,.rational y])) tp (prefixFinal x y gm gd) :=
    ⟨rp.1,rp.2.1,rp.2.2.1,rp.2.2.2.1⟩
  change tp.length≤prefixTimeCoefficient*originalPower x y at lenP
  have paid := paid_prefix_transfer (prefixFinal x y gm gd) prefixRun.2.2.2
  rw [prefixFinal_decode] at paid
  by_cases hy : y=0
  · have flag : (observed x y).val/64=1 := by rw [observed_yzero];simp [hy]
    have branch : branchPhase (observed x y)=(1 : Fin 3) := ite_eq_left flag
    have hg : ∀ r∈[mRecord x y gm,dRecord x y gd],r.gap≤2*allocationK*(fieldWidth x y)^2 := by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact um
      · exact ud
    obtain ⟨tz,rz,timeZ,_spaceZ⟩ := PA17TMRatArithmeticDivZero068.original_zero_contract
      (mRecord x y gm) (dRecord x y gd) x y hg (zero_widths x y gm gd)
    let localLast : MachineState PA17TMRatArithmeticDivZero068.zeroCap :=
      ⟨PA17TMRatArithmeticDivZero068.zeroPort,Tape.mk₁ (encode [.rational (0 : Rat)])⟩
    have zeroRun : PSTRTMSeq005.RunsFrom (component (1 : Fin 3)).code
        ⟨0,(prefixFinal x y gm gd).Tape⟩ tz localLast := rz
    have lifted := terminal_runs (1 : Fin 3) (by decide) _ _ _ zeroRun
    rw [branch,entry_zero] at paid
    have actual := join_prefix _ tp _ prefixRun _ _ _ lifted paid
    have whole : (liftCfg (1 : Fin 3) localLast).Tape=Tape.mk₁ (encode [.rational (x/y)]) := by
      rw [lift_tape]
      change Tape.mk₁ (encode [.rational (0 : Rat)])=Tape.mk₁ (encode [.rational (x/y)])
      simp only [hy,div_zero]
    have tailTime : tz.length≤finishCoefficient*originalPower x y :=
      timeZ.trans (Nat.mul_le_mul_right _ zero_budget)
    exact ⟨liftTrace (0 : Fin 3) tp++liftTrace (1 : Fin 3) tz,liftCfg (1 : Fin 3) localLast,
      actual,whole,combined_length x y tp (1 : Fin 3) tz lenP tailTime⟩
  · have flag : (observed x y).val/64=0 := by rw [observed_yzero];simp [hy]
    have notOne : (observed x y).val/64≠1 := by rw [flag];decide
    have branch : branchPhase (observed x y)=(2 : Fin 3) := ite_eq_right notOne
    have hd : divDenominator x y≠0 := fun h => hy ((divDenominator_zero_iff x y).mp h)
    obtain ⟨tn,lastN,rn,wholeN,timeN⟩ := PA17TMRatArithmeticRatDivSuffix069.normal_runs x y hd gm gd um ud
    have normalRun : PSTRTMSeq005.RunsFrom (component (2 : Fin 3)).code
        (PA17TMRatArithmeticMulController057.entryCfg (4 : Fin 17)
          (widen64 (PA17TMRatArithmeticMulStart049.actualMemory x y)) (prefixFinal x y gm gd).Tape)
        tn lastN := rn
    have lifted := terminal_runs (2 : Fin 3) (by decide) _ _ _ normalRun
    rw [branch,entry_normal,old_memory x y gm gd] at paid
    have actual := join_prefix _ tp _ prefixRun _ _ _ lifted paid
    have whole : (liftCfg (2 : Fin 3) lastN).Tape=Tape.mk₁ (encode [.rational (x/y)]) := by
      rw [lift_tape]
      exact wholeN
    have tailTime : tn.length≤finishCoefficient*originalPower x y := timeN.trans (Nat.mul_le_mul_right _ normal_budget)
    exact ⟨liftTrace (0 : Fin 3) tp++liftTrace (2 : Fin 3) tn,liftCfg (2 : Fin 3) lastN,
      actual,whole,combined_length x y tp (2 : Fin 3) tn lenP tailTime⟩

theorem original_div_contract (x y : Rat) :
    ∃ trace final, Runs divMachine (encode [.rational x,.rational y]) trace final ∧
      final.Tape=Tape.mk₁ (encode [.rational (x/y)]) ∧
      trace.length≤divResourceCoefficient*originalPower x y ∧
      ∀ prefixLength, visitedSpace divMachine (encode [.rational x,.rational y]).length
        (trace.take prefixLength)≤divResourceCoefficient*originalPower x y := by
  obtain ⟨trace,final,actual,whole,time⟩ := original_div_runs x y
  let i := (encode [.rational x,.rational y]).length
  have input : i+1≤(i+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (Nat.succ_le_succ (Nat.zero_le i)) (by decide : (1 : Nat)≤4)
  refine ⟨trace,final,actual,whole,time.trans (Nat.mul_le_mul_right _ time_le_resource),?_⟩
  intro prefixLength
  have space := PSTRTMTrace002.visitedSpace_le divMachine i (trace.take prefixLength)
  have taken : (trace.take prefixLength).length≤trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  change trace.length≤divTimeCoefficient*(i+1)^4 at time
  change visitedSpace divMachine i (trace.take prefixLength)≤divResourceCoefficient*(i+1)^4
  calc
    _ ≤ i+2*(trace.take prefixLength).length+1 := space
    _ ≤ i+2*(divTimeCoefficient*(i+1)^4)+1 :=
      Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (taken.trans time)) i) 1
    _ = (i+1)+2*(divTimeCoefficient*(i+1)^4) := by ac_rfl
    _ ≤ (i+1)^4+2*(divTimeCoefficient*(i+1)^4) := Nat.add_le_add_right input _
    _ = (2*divTimeCoefficient+1)*(i+1)^4 := by ring
    _ ≤ divResourceCoefficient*(i+1)^4 := Nat.mul_le_mul_right _ cells_le_resource

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRatDivController070

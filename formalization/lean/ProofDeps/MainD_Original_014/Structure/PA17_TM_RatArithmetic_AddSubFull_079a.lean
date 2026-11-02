module
public import Structure.PA17_TM_RatArithmetic_AddSubPrefix_074b
public import Structure.PA17_TM_RatArithmetic_AddSubChoice_076b
public import Structure.PA17_TM_RatArithmetic_AddSubNormalize_077a
public import Structure.PA17_TM_RatArithmetic_AddSubFinish_078b
public import Structure.PA17_TM_RatArithmetic_MulSuffix_063c
public import Structure.PA17_TM_RatArithmetic_RatDivController_070c

/-! Whole original-codec addition and subtraction. The fixed mode and
program precede ALL operands; all physical producer, branch, native,
zero-sensor, return, output and cleanup traces are joined unchanged. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubFull079

open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticAddSubController075
open PA17TMRatArithmeticMulController057 (widen64)
open PA17TMRatArithmeticSignedSumFields072 (target)
attribute [local implicit_reducible] component controllerCap totalStates
  PA17TMRatArithmeticAddSubPrefix074.prefixComponent

def addSubTimeCoefficient : Nat := PA17TMRatArithmeticAddSubPrefix074.prefixTimeCoefficient+
  PA17TMRatArithmeticAddSubChoice076.choiceCoefficient+
  2*PA17TMRatArithmeticAddSubNormalize077.roundCoefficient+
  PA17TMRatArithmeticAddSubFinish078.vCoefficient+
  PA17TMRatArithmeticAddSubFinish078.finishCoefficient

def addSubResourceCoefficient : Nat := 2*addSubTimeCoefficient+2

theorem addSubResourceCoefficient_pos : 0<addSubResourceCoefficient := by
  unfold addSubResourceCoefficient
  omega

/-- Two closed finite Bool programs, with no mode field on the input tape. -/
def addMachine : Machine controllerCap := addSubMachine false
def subMachine : Machine controllerCap := addSubMachine true

/-- All component runs below are the physically constructed runs. The
only case selection is the actual controller's observed finite row. -/
theorem original_add_sub_runs (subtract : Bool) (x y : Rat) :
    ∃ trace final, Runs (addSubMachine subtract) (encode [.rational x,.rational y]) trace final ∧
      final.Tape=Tape.mk₁ (encode [.rational (target subtract x y)]) ∧
      trace.length≤addSubTimeCoefficient*originalPower x y := by
  obtain ⟨gm,gn,ge,gp,gq,tp,_lm,um,_ln,un,_le,ue,_lp,up,_lq,uq,rp,lenP⟩ :=
    PA17TMRatArithmeticAddSubPrefix074.original_prefix_runs x y
  have prefixRun : PSTRTMSeq005.RunsFrom PA17TMRatArithmeticAddSubPrefix074.prefixMachine
      (TM0.init (encode [.rational x,.rational y])) tp
      (PA17TMRatArithmeticAddSubPrefix074.prefixFinal x y gm gn ge gp gq) :=
    ⟨rp.1,rp.2.1,rp.2.2.1,rp.2.2.2.1⟩
  have liftedP := component_segment subtract (0 : Fin 19) _ _ _ prefixRun
  have firstSegment : Segment (addSubMachine subtract) (TM0.init (encode [.rational x,.rational y]))
      (liftTrace (0 : Fin 19) tp)
      (liftCfg (0 : Fin 19) (PA17TMRatArithmeticAddSubPrefix074.prefixFinal x y gm gn ge gp gq)) :=
    ⟨liftedP.1.trans (congrArg some (initial_mapped _)),liftedP.2.1,liftedP.2.2⟩
  have stepP := transfer_to subtract (0 : Fin 19) (1 : Fin 19) (by decide)
    (PA17TMRatArithmeticAddSubPrefix074.prefixFinal x y gm gn ge gp gq)
    (widen64 (PA17TMRatArithmeticMulStart049.actualMemory x y))
    (widen64 (PA17TMRatArithmeticMulStart049.actualMemory x y))
    (PA17TMRatArithmeticAddSubPrefix074.postTape x y gm gn ge gp gq)
    prefixRun.2.2.2 (PA17TMRatArithmeticAddSubPrefix074.prefixFinal_decode x y gm gn ge gp gq) rfl rfl rfl
  obtain ⟨gr,tr,lastR,_lr,ur,segR,stepR,lenR⟩ :=
    PA17TMRatArithmeticAddSubChoice076.choice_segment subtract x y gm gn ge gp gq um un ue up uq
  obtain ⟨gg,tg,lastG,_lg,ug,segG,stepG,lenG⟩ :=
    PA17TMRatArithmeticAddSubNormalize077.g_segment subtract x y gm gn ge gp gq gr um un ue up uq ur
  obtain ⟨gu,tu,lastU,_lu,uu,segU,stepU,lenU⟩ :=
    PA17TMRatArithmeticAddSubNormalize077.u_segment subtract x y gm gn ge gp gq gr gg um un ue up uq ur ug
  obtain ⟨gv,tv,lastV,_lv,uv,segV,stepV,lenV⟩ :=
    PA17TMRatArithmeticAddSubFinish078.v_segment subtract x y gm gn ge gp gq gr gg gu um un ue up uq ur ug uu
  obtain ⟨tf,final,runF,whole,lenF⟩ :=
    PA17TMRatArithmeticAddSubFinish078.finish_segment subtract x y gm gn ge gp gq gr gg gu gv
      um un ue up uq ur ug uu uv
  have joinedPR := segment_append (addSubMachine subtract) _ _ _ lastR _ tr firstSegment segR stepP
  have joinedPRG := segment_append (addSubMachine subtract) _ lastR _ lastG _ tg joinedPR segG stepR
  have joinedPRGU := segment_append (addSubMachine subtract) _ lastG _ lastU _ tu joinedPRG segU stepG
  have joinedPRGUV := segment_append (addSubMachine subtract) _ lastU _ lastV _ tv joinedPRGU segV stepU
  have segmentF : Segment (addSubMachine subtract) _ tf final := ⟨runF.1,runF.2.1,runF.2.2.1⟩
  have joined := segment_append (addSubMachine subtract) _ lastV _ final _ tf joinedPRGUV segmentF stepV
  let trace := (((((liftTrace (0 : Fin 19) tp++tr)++tg)++tu)++tv)++tf)
  have actual : Runs (addSubMachine subtract) (encode [.rational x,.rational y]) trace final :=
    PSTRTMTrace002.runs_of_chain (addSubMachine subtract) _ _ _
      joined.1 joined.2.1 joined.2.2 runF.2.2.2
  have length : trace.length≤addSubTimeCoefficient*originalPower x y := by
    simp only [trace,List.length_append]
    rw [liftTrace_length (0 : Fin 19) tp]
    change tp.length≤PA17TMRatArithmeticAddSubPrefix074.prefixTimeCoefficient*originalPower x y at lenP
    calc
      _ ≤ ((((PA17TMRatArithmeticAddSubPrefix074.prefixTimeCoefficient*originalPower x y+
              PA17TMRatArithmeticAddSubChoice076.choiceCoefficient*originalPower x y)+
              PA17TMRatArithmeticAddSubNormalize077.roundCoefficient*originalPower x y)+
              PA17TMRatArithmeticAddSubNormalize077.roundCoefficient*originalPower x y)+
              PA17TMRatArithmeticAddSubFinish078.vCoefficient*originalPower x y)+
              PA17TMRatArithmeticAddSubFinish078.finishCoefficient*originalPower x y :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add lenP lenR) lenG) lenU) lenV) lenF
      _ = addSubTimeCoefficient*originalPower x y := by unfold addSubTimeCoefficient;ring
  exact ⟨trace,final,actual,whole,length⟩

/-- Time and EVERY visited-space prefix concern exactly this actual trace
and the ORIGINAL two-Rat input length. No record invariant is an input. -/
theorem original_add_sub_contract (subtract : Bool) (x y : Rat) :
    ∃ trace final, Runs (addSubMachine subtract) (encode [.rational x,.rational y]) trace final ∧
      final.Tape=Tape.mk₁ (encode [.rational (target subtract x y)]) ∧
      trace.length≤addSubResourceCoefficient*originalPower x y ∧
      ∀ prefixLength, visitedSpace (addSubMachine subtract) (encode [.rational x,.rational y]).length
        (trace.take prefixLength)≤addSubResourceCoefficient*originalPower x y := by
  obtain ⟨trace,final,actual,whole,time⟩ := original_add_sub_runs subtract x y
  let i := (encode [.rational x,.rational y]).length
  have input : i+1≤(i+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (Nat.succ_le_succ (Nat.zero_le i)) (by decide : (1 : Nat)≤4)
  have hc : addSubTimeCoefficient≤addSubResourceCoefficient := by unfold addSubResourceCoefficient;omega
  refine ⟨trace,final,actual,whole,time.trans (Nat.mul_le_mul_right _ hc),?_⟩
  intro prefixLength
  have space := PSTRTMTrace002.visitedSpace_le (addSubMachine subtract) i (trace.take prefixLength)
  have taken : (trace.take prefixLength).length≤trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  change trace.length≤addSubTimeCoefficient*(i+1)^4 at time
  change visitedSpace (addSubMachine subtract) i (trace.take prefixLength)≤addSubResourceCoefficient*(i+1)^4
  calc
    _ ≤ i+2*(trace.take prefixLength).length+1 := space
    _ ≤ i+2*(addSubTimeCoefficient*(i+1)^4)+1 :=
      Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (taken.trans time)) i) 1
    _ = (i+1)+2*(addSubTimeCoefficient*(i+1)^4) := by ac_rfl
    _ ≤ (i+1)^4+2*(addSubTimeCoefficient*(i+1)^4) := Nat.add_le_add_right input _
    _ = (2*addSubTimeCoefficient+1)*(i+1)^4 := by ring
    _ ≤ addSubResourceCoefficient*(i+1)^4 :=
      Nat.mul_le_mul_right _ (by unfold addSubResourceCoefficient;omega)

theorem original_add_sub_computes (subtract : Bool) (x y : Rat) :
    computes (addSubMachine subtract) (encode [.rational x,.rational y])
      (encode [.rational (target subtract x y)])
      (addSubResourceCoefficient*originalPower x y) (addSubResourceCoefficient*originalPower x y) := by
  obtain ⟨trace,final,actual,whole,time,space⟩ := original_add_sub_contract subtract x y
  refine ⟨trace,final,actual,?_,time,?_⟩
  · rw [whole]
    exact Turing.Tape.mk'_right₀ _ _
  · have h := space trace.length
    simpa only [List.take_length] using h

theorem original_add_sub_exists (subtract : Bool) :
    ∃ states c d : Nat, ∃ program : Machine states, 0<c ∧ 0<d ∧
      ∀ x y : Rat, ∃ trace final,
        Runs program (encode [.rational x,.rational y]) trace final ∧
        final.Tape=Tape.mk₁ (encode [.rational (target subtract x y)]) ∧
        trace.length≤c*((encode [.rational x,.rational y]).length+1)^d ∧
        ∀ prefixLength, visitedSpace program (encode [.rational x,.rational y]).length
          (trace.take prefixLength)≤c*((encode [.rational x,.rational y]).length+1)^d := by
  refine ⟨controllerCap,addSubResourceCoefficient,4,addSubMachine subtract,addSubResourceCoefficient_pos,by decide,?_⟩
  intro x y
  exact original_add_sub_contract subtract x y

theorem original_add_computes (x y : Rat) :
    computes (addSubMachine false) (encode [.rational x,.rational y]) (encode [.rational (x+y)])
      (addSubResourceCoefficient*originalPower x y) (addSubResourceCoefficient*originalPower x y) :=
  original_add_sub_computes false x y

theorem original_sub_computes (x y : Rat) :
    computes (addSubMachine true) (encode [.rational x,.rational y]) (encode [.rational (x-y)])
      (addSubResourceCoefficient*originalPower x y) (addSubResourceCoefficient*originalPower x y) :=
  original_add_sub_computes true x y

theorem original_add_exists :
    ∃ states c d : Nat, ∃ program : Machine states, 0<c ∧ 0<d ∧
      ∀ x y : Rat, ∃ trace final,
        Runs program (encode [.rational x,.rational y]) trace final ∧
        final.Tape=Tape.mk₁ (encode [.rational (x+y)]) ∧
        trace.length≤c*((encode [.rational x,.rational y]).length+1)^d ∧
        ∀ prefixLength, visitedSpace program (encode [.rational x,.rational y]).length
          (trace.take prefixLength)≤c*((encode [.rational x,.rational y]).length+1)^d :=
  original_add_sub_exists false

theorem original_sub_exists :
    ∃ states c d : Nat, ∃ program : Machine states, 0<c ∧ 0<d ∧
      ∀ x y : Rat, ∃ trace final,
        Runs program (encode [.rational x,.rational y]) trace final ∧
        final.Tape=Tape.mk₁ (encode [.rational (x-y)]) ∧
        trace.length≤c*((encode [.rational x,.rational y]).length+1)^d ∧
        ∀ prefixLength, visitedSpace program (encode [.rational x,.rational y]).length
          (trace.take prefixLength)≤c*((encode [.rational x,.rational y]).length+1)^d :=
  original_add_sub_exists true

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubFull079

module
public import RootPaper_TableCost_Widths007
public import RootPaper_TableCost_Candidate006

/-! Closed primitive fees. All coefficients and the WORD code are selected
from frozen concrete binary implementations before any instance, sample,
history or clock. No implementation/cost certificate is a caller premise. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RootPaper.TableCost
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open RationalControllerComputation PSTRWordBool
variable {I : Instance}

def scalarFee : RootPaper.Reference.ScalarCall I→Nat
  | .budgetVisit kind _ risk => 16+4*RatInput.Encoder.fieldSize risk+4*RootB236.RiskFold.caseDepth kind
  | .half risk => (RootPaper.BudgetCost.half risk).cost
  | .target risk depth => (RootB23.Threshold.ReturnOriginalPacket.timeCoefficient+283)*
      RootB23.Threshold.OriginalBridge.scale risk depth^10
  | .badRisk risk target => (RootPaper.BudgetCost.badRisk risk target).cost
  | .word _ _ _ => 0

def scalarRate : Nat := RootPaper.BudgetCost.coefficient+
  RootB23.Threshold.ReturnOriginalPacket.timeCoefficient+284

theorem scalarRate_pos : 0<scalarRate := by unfold scalarRate;omega

private theorem power_cap (c rate n cap d : Nat) (coefficient : c≤rate)
    (size : n≤cap) (positive : 1≤cap) (degree : d≤10) : c*n^d≤rate*cap^10 :=
  Nat.mul_le_mul coefficient ((Nat.pow_le_pow_left size d).trans (Nat.pow_le_pow_right positive degree))

theorem scalarFee_bound (S D : Nat) (call : RootPaper.Reference.ScalarCall I) (bounded : CallBound S D call) :
    scalarFee call≤scalarRate*(4096*(S+D+1))^10 := by
  have positive : 1≤4096*(S+D+1) := by omega
  cases call with
  | budgetVisit kind error risk =>
      rcases bounded with ⟨width,depth⟩
      have small : scalarFee (.budgetVisit (I:=I) kind error risk)≤4096*(S+D+1) := by
        simp only [scalarFee];omega
      have power : 4096*(S+D+1)≤(4096*(S+D+1))^10 := by
        simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤10)
      exact small.trans (power.trans (by have rate:=scalarRate_pos;nlinarith))
  | half risk =>
      exact (RootPaper.BudgetCost.half_cost risk).trans
        (power_cap _ _ _ _ 8 (by unfold scalarRate;omega)
          (by change RatInput.Encoder.fieldSize risk+1≤_;change RatInput.Encoder.fieldSize risk≤S at bounded;omega)
          positive (by decide))
  | target risk depth =>
      have size:=RootB236.RiskFold.threshold_scale risk depth
      exact power_cap _ _ _ _ 10 (by unfold scalarRate;omega)
        (by have width:=bounded.2.2.1;have d:=bounded.2.2.2;omega) positive (by decide)
  | badRisk risk target =>
      exact (RootPaper.BudgetCost.badRisk_cost risk target).trans
        (power_cap _ _ _ _ 8 (by unfold scalarRate;omega)
          (by change RatInput.Encoder.fieldSize risk+RatInput.Encoder.fieldSize target+1≤_
              rcases bounded with ⟨width,targetWidth⟩;omega) positive (by decide))
  | word stage target length => exact bounded.elim

def ScalarRealized : RootPaper.Reference.ScalarCall I→Prop
  | .budgetVisit _ _ _ => True
  | .half risk => ∀ op∈(RootPaper.BudgetCost.half risk).operations,op.Realized
  | .badRisk risk target => ∀ op∈(RootPaper.BudgetCost.badRisk risk target).operations,op.Realized
  | .target risk depth =>
      computes RootB23.Threshold.ReturnOriginalPacket.code (encode [.rational risk,.natural depth])
        (thresholdOutput risk depth)
        (RootB23.Threshold.ReturnOriginalPacket.timeCoefficient*RootB23.Threshold.OriginalBridge.scale risk depth^10)
        (RootB23.Threshold.ReturnOriginalPacket.spaceCoefficient*RootB23.Threshold.OriginalBridge.scale risk depth^10) ∧
      RootB23.Threshold.ReturnOriginalPacket.timeCoefficient*RootB23.Threshold.OriginalBridge.scale risk depth^10+
        (encode [.rational risk,.natural depth]).length+(thresholdOutput risk depth).length≤scalarFee (.target (I:=I) risk depth)
  | .word _ _ _ => False

theorem scalar_realized (S D : Nat) (call : RootPaper.Reference.ScalarCall I) (bounded : CallBound S D call) :
    ScalarRealized call := by
  cases call with
  | budgetVisit kind error risk => trivial
  | half risk => exact RootPaper.BudgetCost.half_realized risk
  | badRisk risk target => exact RootPaper.BudgetCost.badRisk_realized risk target
  | target risk depth =>
      have closed:=RootPaper.Scalar.threshold_closed risk depth bounded.1 bounded.2.1
      exact ⟨closed.1,closed.2.2⟩
  | word stage target length => exact bounded.elim

def rationalFee (pair : Rat×Rat) : Nat :=
  (RootPaper.Prep.Operation.rational .le pair.1 pair.2).nativeFee

theorem rationalFee_bound (pair : Rat×Rat) (S : Nat)
    (width : RatInput.Encoder.fieldSize pair.1+RatInput.Encoder.fieldSize pair.2≤S) :
    rationalFee pair≤RootPaper.Prep.nativeRate*(S+2)^8 :=
  (RootPaper.Prep.nativeFee_bound (.rational .le pair.1 pair.2)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (by change RatInput.Encoder.fieldSize pair.1+RatInput.Encoder.fieldSize pair.2+1+1≤S+2;omega) 8))

theorem rational_realized (pair : Rat×Rat) :
    (RootPaper.Prep.Operation.rational .le pair.1 pair.2).Realized :=
  RootPaper.Prep.operation_realized _

/-- Up to eight comparisons, reversal for equality/strict guards, and
linear binary input/result traversal. Boolean negation is in localTicks. -/
def naturalFee (pair : Nat×Nat) : Nat :=
  8*4101*(natBits pair.1+natBits pair.2+1)^2+32*(natBits pair.1+natBits pair.2+1)

theorem natural_realized (a b : Nat) :
    (PSTRTMNativeLe060.nativeTrace a b).length+(encodeNat a++encodeNat b).length+
      (encodeNat (if decide (a≤b) then 1 else 0)).length≤naturalFee (a,b) := by
  have closed:=(RootPaper.Scalar.nat_le_closed a b).2
  have positive : 1≤natBits a+natBits b+1 := by omega
  have square : natBits a+natBits b+1≤(natBits a+natBits b+1)^2 := by nlinarith
  unfold naturalFee
  nlinarith

structure WordCode where
  states : Nat
  code : Machine states
  coefficient : Nat
  degree : Nat
  positive : 0<coefficient ∧ 0<degree
  actual : ∀ (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord),
    ∃ trace final,Runs code (wordInput E target word) trace final ∧
      final.Tape.right₀=Turing.ListBlank.mk (wordOutput E target word) ∧
      trace.length+(wordInput E target word).length+(wordOutput E target word).length≤
        coefficient*((wordInput E target word).length+word.1+1)^degree

theorem wordCode_exists : Nonempty WordCode := by
  obtain ⟨states,code,port,c,d,hc,hd,actual⟩:=RootPaper.Scalar.word_closed
  refine ⟨⟨states,code,c,d,⟨hc,hd⟩,?_⟩⟩
  intro E target word
  obtain ⟨trace,final,run,atPort,halted,output,time,space⟩:=actual E target word
  exact ⟨trace,final,run,output,time⟩

noncomputable def wordCode : WordCode := Classical.choice wordCode_exists

noncomputable def wordFee {input : StatisticalInput I} (call : WordCall input) : Nat :=
  wordCode.coefficient*((wordInput (input.experiment call.stage) call.target call.word).length+call.word.1+1)^wordCode.degree

theorem word_realized {input : StatisticalInput I} (call : WordCall input) :
    ∃ trace final,Runs wordCode.code (wordInput (input.experiment call.stage) call.target call.word) trace final ∧
      final.Tape.right₀=Turing.ListBlank.mk (wordOutput (input.experiment call.stage) call.target call.word) ∧
      trace.length+(wordInput (input.experiment call.stage) call.target call.word).length+
        (wordOutput (input.experiment call.stage) call.target call.word).length≤wordFee call :=
  wordCode.actual _ _ _

end RootPaper.TableCost

module
public import RootPaper_Reference_WordBounds019
public import RootPaper_Reference_QueryCost008
public import RootPaper_TableCost_Helper016

/-! Closed prices for the actual primitive calls and measured helper work.
The WORD code, port and bounds are selected together before every input.
Data debits depend on the actual leaf inputs, not on a desired F polynomial.
All fee annotations are erased; the controller receives no fee/width oracle. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open Turing PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RootPaper.Reference RationalControllerComputation PSTRWordBool
variable {I : Instance}

structure WordRuntime where
  states : Nat
  code : Machine states
  port : Fin (states+1)
  coefficient : Nat
  degree : Nat
  positive : 0<coefficient ∧ 0<degree
  actual : ∀ (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord),
    ∃ trace final,Runs code (wordInput E target word) trace final ∧ final.q=port ∧
      TM0.step code final=none ∧ final.Tape.right₀=ListBlank.mk (wordOutput E target word) ∧
      trace.length+(wordInput E target word).length+(wordOutput E target word).length≤
        coefficient*((wordInput E target word).length+word.1+1)^degree ∧
      ∀ clock,visitedSpace code (wordInput E target word).length (trace.take clock)≤
        coefficient*((wordInput E target word).length+word.1+1)^degree

theorem wordRuntime_exists : Nonempty WordRuntime := by
  obtain ⟨states,code,port,c,d,hc,hd,actual⟩:=RootPaper.Scalar.word_closed
  exact ⟨⟨states,code,port,c,d,⟨hc,hd⟩,actual⟩⟩

def wordFeeFor (runtime : WordRuntime) {input : StatisticalInput I} (call : WordCall input) : Nat :=
  runtime.coefficient*((wordInput (input.experiment call.stage) call.target call.word).length+call.word.1+1)^runtime.degree

theorem word_realized (runtime : WordRuntime) {input : StatisticalInput I} (call : WordCall input) :
    ∃ trace final,Runs runtime.code (wordInput (input.experiment call.stage) call.target call.word) trace final ∧
      final.q=runtime.port ∧ TM0.step runtime.code final=none ∧
      final.Tape.right₀=ListBlank.mk (wordOutput (input.experiment call.stage) call.target call.word) ∧
      trace.length+(wordInput (input.experiment call.stage) call.target call.word).length+
        (wordOutput (input.experiment call.stage) call.target call.word).length≤wordFeeFor runtime call ∧
      ∀ clock,visitedSpace runtime.code (wordInput (input.experiment call.stage) call.target call.word).length
        (trace.take clock)≤wordFeeFor runtime call := runtime.actual _ _ _

structure QueryExecution (I : Instance) (stage : Nat) (remaining : Finset I.Tool) where
  trace : List (RootB236.Controller.DFSDriver.Machine.State Unit)
  final : RootB236.Controller.DFSDriver.Machine.State Unit
  actual : RootB236.Controller.DFSDriver.Machine.Facts (C:=Unit) .halt I.stageCount I.toolCount
    (I.compatibility.drop stage) remaining default (queryBank I stage remaining) [] trace final
  rank : RootB23.GenericRank.decodeRank I.stageCount (final.stk 15).length=(query I stage remaining).rank
  flag : final.stk 13=[(query I stage remaining).pick.isSome]
  pick : final.stk 14=RootB236.Controller.DFSDriver.Machine.pickBits (query I stage remaining).pick
  charged : trace.length+RootB236.Controller.DFSDriver.Machine.clockSum .halt trace≤
    queryCoefficient*(I.stageCount+I.toolCount+2)^8*generalStructureFactor I

theorem queryExecution_exists (I : Instance) (stage : Nat) (remaining : Finset I.Tool) :
    Nonempty (QueryExecution I stage remaining) := by
  obtain ⟨trace,final,actual,rank,flag,pick,charged⟩:=query_cost I stage remaining
  exact ⟨⟨trace,final,actual,rank,flag,pick,charged⟩⟩

/-- An erased actual-run witness of one fixed deterministic DFS program.
The operational controller is query; no witness is passed to that query. -/
noncomputable def queryExecution (I : Instance) (stage : Nat) (remaining : Finset I.Tool) :
    QueryExecution I stage remaining := Classical.choice (queryExecution_exists I stage remaining)

noncomputable def queryFee (I : Instance) (call : RankCall I) : Nat :=
  (queryExecution I call.stage call.remaining).trace.length+
    RootB236.Controller.DFSDriver.Machine.clockSum .halt (queryExecution I call.stage call.remaining).trace

theorem queryFee_bound (I : Instance) (call : RankCall I) :
    queryFee I call≤queryCoefficient*(I.stageCount+I.toolCount+2)^8*generalStructureFactor I :=
  (queryExecution I call.stage call.remaining).charged

/-- Construction/indexing/copy allowances use the actual encoded inputs.
Squared material covers repeated linked-field access and the StoppedWord's
finite-list indexing; primitive input/output copies are also paid in fees. -/
def queryDataUnits (I : Instance) (call : RankCall I) : Nat :=
  (RootB236.Controller.DFSDriver.Machine.mass (queryBank I call.stage call.remaining)+1)^2+
    I.stageCount+I.toolCount+4

def wordDataUnits {input : StatisticalInput I} (call : WordCall input) : Nat :=
  ((wordInput (input.experiment call.stage) call.target call.word).length+call.word.1+1)^2

def dataUnits {input : StatisticalInput I} (calculation : ControllerCalculation input) : Nat :=
  calculation.administration+(calculation.ranks.map (queryDataUnits I)).sum+
    (calculation.words.map wordDataUnits).sum+1

def unitRate : Nat := (RootPaper.Prep.nativeRate+65536)*2^160
def unitFee (B : Nat) : Nat := unitRate*(B+1)^8

theorem unitRate_positive : 0<unitRate := by
  unfold unitRate
  exact Nat.mul_pos (by omega) (by decide)

/-- Actual binary comparison fees, including input/result copies. -/
theorem natural_guard_paid (B : Nat) (pair : Nat×Nat) (width : RootPaper.TableCost.NatPairBound B pair) :
    RootPaper.TableCost.naturalFee pair≤unitFee B := by
  have actual:=RootPaper.TableCost.helper_binary_guard B pair width
  have coefficient : 32840*9+4096≤unitRate := by unfold unitRate;omega
  exact actual.trans (Nat.mul_le_mul coefficient (Nat.pow_le_pow_right (by omega) (by decide : 2≤8)))

theorem rational_guard_paid (B : Nat) (pair : Rat×Rat)
    (width : RatInput.Encoder.fieldSize pair.1+RatInput.Encoder.fieldSize pair.2≤65536*(B+1)) :
    RootPaper.TableCost.rationalFee pair≤unitFee B := by
  have actual:=RootPaper.TableCost.rationalFee_bound pair (65536*(B+1)) width
  have size : 65536*(B+1)+2≤131072*(B+1) := by omega
  have coefficient : RootPaper.Prep.nativeRate*131072^8≤unitRate := by unfold unitRate;omega
  have power:=Nat.pow_le_pow_left size 8
  calc
    _≤RootPaper.Prep.nativeRate*(131072*(B+1))^8:=actual.trans (Nat.mul_le_mul_left _ power)
    _=(RootPaper.Prep.nativeRate*131072^8)*(B+1)^8:=by rw [mul_pow];ring
    _≤unitFee B:=Nat.mul_le_mul_right _ coefficient

def counterOperations (n : Nat) : List RootPaper.Prep.Operation :=
  [.natural n,.rational .add (n : Rat) 1,.rational .sub ((n+1 : Nat) : Rat) 1]

theorem counter_values (n : Nat) :
    (n : Rat)+1=((n+1 : Nat) : Rat) ∧ ((n+1 : Nat) : Rat)-1=(n : Rat) := by
  constructor <;> push_cast <;> ring

theorem counter_realized (n : Nat) : ∀ op∈counterOperations n,op.Realized := by
  intro op _
  exact RootPaper.Prep.operation_realized op

theorem counter_paid (B n : Nat) (bounded : n≤B) :
    RootPaper.Prep.arithmeticCost (counterOperations n)≤unitFee B := by
  have first : RootPaper.Prep.field (n : Rat)≤B+2 := by
    rw [RootPaper.Prep.nat_field_eq]
    have bits:=RootPaper.TableCost.natBits_le_value n
    omega
  have next : RootPaper.Prep.field ((n+1 : Nat) : Rat)≤B+3 := by
    rw [RootPaper.Prep.nat_field_eq]
    have bits:=RootPaper.TableCost.natBits_le_value (n+1)
    omega
  have operations : RootPaper.Prep.Bounded (counterOperations n) 3 (B+6) := by
    refine ⟨by change (3 : Nat)≤3;omega,?_⟩
    intro op member
    simp only [counterOperations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    all_goals simp only [RootPaper.Prep.Operation.width,RootPaper.Prep.field_one]
    all_goals omega
  have actual:=RootPaper.Prep.bounded_arithmeticCost operations
  have size : B+7≤7*(B+1) := by omega
  have coefficient : 3*RootPaper.Prep.nativeRate*7^8≤unitRate := by unfold unitRate;omega
  calc
    _≤3*RootPaper.Prep.nativeRate*(7*(B+1))^8:=actual.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left size 8))
    _=(3*RootPaper.Prep.nativeRate*7^8)*(B+1)^8:=by rw [mul_pow];ring
    _≤unitFee B:=Nat.mul_le_mul_right _ coefficient

noncomputable def runningCost (runtime : WordRuntime) (B : Nat) {input : StatisticalInput I}
    (calculation : ControllerCalculation input) : Nat :=
  (calculation.ranks.map (queryFee I)).sum+
    (calculation.scalar.map RootPaper.TableCost.scalarFee).sum+
    (calculation.words.map (wordFeeFor runtime)).sum+unitFee B*dataUnits calculation

end RootPaper.Reference.Charged

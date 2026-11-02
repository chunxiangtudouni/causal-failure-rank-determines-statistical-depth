module

public import RootL01_PHCompat_Public007
public import Structure.PSTR_CurrentRecordSlice_147
public import Common.PSTR_ST_TablePolicyBridge_045
public import Common.PSTR_ST_InfiniteRankClaims_010
import Lean.Util.CollectAxioms

/-! Paper-required composition only. The fixed original P/Live/H programs
and all costs are concrete conclusions. No Bool machine, parser, supplied
callback records, correctness oracle or unknown cost premise is introduced.
H and Live start from the SAME chosen P output heap, with their original
packingInitial register resets; this does not assert a new H-then-Live
in-place trajectory. Scalar preparation and Expr copying/output costs are
separate paper obligations, not silently discharged by this theorem. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open MeasureTheory
open scoped ENNReal

namespace RootPaper.Table

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open PaperProofs.Structure PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims PA17A19RuntimeEntry020
open PSTRQueryRecords PA17L01HistoryPrefixCommands001 PA17L01HistoryPrefixStrategy002

/-- Three fixed original Word programs, all selected before the instance. -/
def preprocessor : List PackingOp:=RootL01.PHCompat.Preparation.program
def live : List PackingOp:=PSTRLiveControllerCode.program
def heads : List PackingOp:=PSTRUniformHeads.program
def preprocessingConstant : Nat:=RootL01.PHCompat.Preparation.constant

abbrev preparedHeap:=@RootL01.PHCompat.Assembly.preparedHeap

def PreparedRun {q : Nat} (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (prepSteps headSteps : Nat) : Prop :=
  DynamicRunCorrect (allocatedWords full) (controllerInput q full used) preprocessor prepSteps
    (fun _ => BitVec.ofNat (wordBits full) 0) ∧
  totalCost (allocatedWords full) (controllerInput q full used) preprocessor prepSteps
    (fun _ => BitVec.ofNat (wordBits full) 0) ≤ preprocessingConstant * preprocessingWork full.length q (treeSize q full) ∧
  HeapRepresents q full (capacity full) ⟨0,used,false⟩ (preparedHeap full used prepSteps) ∧
  headSteps ≤ (full.length+1)*(PSTRUniformQuery.budget full+101) ∧
  DynamicRunCorrect (allocatedWords full) (callInput q full .query) heads headSteps (preparedHeap full used prepSteps) ∧
  callCost q full heads .query headSteps (preparedHeap full used prepSteps) ≤ 30000 * CompactPrice.headWork q full ∧
  (let after:=packingRun (callInput q full .query) heads headSteps (packingInitial (preparedHeap full used prepSteps));
    HeapRepresents q full (capacity full) ⟨full.length,used,false⟩ after.heap ∧
    (after.register .index).toNat+(CompactPrice.headWords q full used).length ≤ allocatedWords full ∧
    heapWordsAt after.heap (after.register .index).toNat (CompactPrice.headWords q full used).length=CompactPrice.headWords q full used)

/-- One actual P witness is retained for both the heads and live consumers. -/
theorem prepared_run {q : Nat} (full : List (Finset (Fin q)))
    (laminar : LaminarSchedule full) (used : Finset (Fin q)) :
    ∃ prepSteps headSteps, PreparedRun full used prepSteps headSteps := by
  obtain ⟨prepSteps,dynamic,cost,represented⟩:=RootL01.PHCompat.Preparation.actual q full laminar used
  have rep:HeapRepresents q full (capacity full) ⟨0,used,false⟩ (preparedHeap full used prepSteps):=represented
  obtain ⟨headSteps,time,headDynamic,headCost,output⟩:=
    PSTRUniformHeads.actual_heads full laminar used (preparedHeap full used prepSteps) rep
  exact ⟨prepSteps,headSteps,dynamic,cost,rep,time,headDynamic,headCost,output⟩

variable {I : Instance}

/-- Original Prefix semantics suffice also in the infinite-rank branch;
no artificial RiskChoice or exponent qualification is added for records. -/
theorem actual_records (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (positive : 0<budget) (small : budget≤1/2) (quota : I.Stage → Nat)
    (policy : Policy input C .native accounting Unit)
    (sameRule : policy.rule=CompactPrice.tableRule input available budget (some quota))
    (sample : Unit × input.World) (clock : Nat) (counts : List Nat)
    (heap : BitVec (wordBits I.compatibility) → BitVec (wordBits I.compatibility))
    (execution : CommandsRunClaims 65536 I.toolCount I.compatibility (capacity I.compatibility)
      (allocatedWords I.compatibility) live ⟨0,Finset.univ\available,false⟩
      (CompactPrice.commandsAt I (run input C .native accounting policy.rule sample clock).history) counts heap) :
    CompactPrice.queryRecords I.toolCount I.compatibility live
      (CompactPrice.commandsAt I (run input C .native accounting policy.rule sample clock).history) counts heap =
      nativeRecords available (run input C .native accounting policy.rule sample clock).history := by
  have transitions :
      let history:=(run input C .native accounting policy.rule sample clock).history
      StageTransitions I.compatibility (declarationAt history) (stageUsed available history)
        (min (historyCursor history) I.stageCount) := by
    rw [PA17L01HistoryPrefixActual004.native_table_run_eq input C accounting available budget (some quota)
      policy sameRule sample clock]
    have legal:LegalRule input C .uncapped accounting (CompactPrice.tableRule input available budget (some quota)):=by
      rw [←sameRule]
      exact legalRule_uncapped_of_native input C accounting policy.rule policy.legal
    obtain ⟨_,_,prefixRun⟩:=run_has_prefix input C .uncapped accounting _ legal sample clock
    exact prefix_stageTransitions input C laminar current accounting available budget positive small
      (some quota) sample.1 _ _ prefixRun
  exact (records_of_run I.compatibility live _ _ counts heap execution).trans
    (history_semantic_records available _ transitions _)

def NativeWordRun (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (quota : I.Stage → Nat) (policy : Policy input C .native accounting Unit)
    (heap : BitVec (wordBits I.compatibility) → BitVec (wordBits I.compatibility)) : Prop :=
  ∀ sample : Unit × input.World,
    let horizon:=quotaActionBound I quota+1
    let final:=run input C .native accounting policy.rule sample horizon
    let commands:=CompactPrice.commandsAt I final.history
    final.halted=true ∧ ∃ counts : List Nat,
      counts.length=commands.length ∧ commands.length≤2*I.stageCount+1 ∧
      CommandsRunClaims 65536 I.toolCount I.compatibility (capacity I.compatibility)
        (allocatedWords I.compatibility) live ⟨0,Finset.univ\available,false⟩ commands counts heap ∧
      commandsCost I.toolCount I.compatibility live commands counts heap ≤
        65536*(I.stageCount+1)*liveWork I.toolCount (treeSize I.toolCount I.compatibility) ∧
      CompactPrice.queryRecords I.toolCount I.compatibility live commands counts heap=nativeRecords available final.history ∧
      ∀ clock : Fin horizon,
        let history:=(run input C .native accounting policy.rule sample clock.val).history
        let current:=CompactPrice.commandsAt I history
        let records:=CompactPrice.queryRecords I.toolCount I.compatibility live current (counts.take current.length) heap
        current.IsPrefix commands ∧
        CommandsRunClaims 65536 I.toolCount I.compatibility (capacity I.compatibility)
          (allocatedWords I.compatibility) live ⟨0,Finset.univ\available,false⟩ current (counts.take current.length) heap ∧
        records=nativeRecords available history ∧ records.length≤4*(2*I.stageCount+1) ∧
        ∀ word∈records,word<2^wordBits I.compatibility

theorem native_word_run (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (positive : 0<budget) (small : budget≤1/2) (quota : I.Stage → Nat)
    (policy : Policy input C .native accounting Unit)
    (sameRule : policy.rule=CompactPrice.tableRule input available budget (some quota))
    (heap : BitVec (wordBits I.compatibility) → BitVec (wordBits I.compatibility))
    (rep : HeapRepresents I.toolCount I.compatibility (capacity I.compatibility) ⟨0,Finset.univ\available,false⟩ heap) :
    NativeWordRun input C accounting available quota policy heap := by
  intro sample
  let horizon:=quotaActionBound I quota+1
  let history:=(run input C .native accounting policy.rule sample horizon).history
  let commands:=CompactPrice.commandsAt I history
  have actual:=PA17L01HistoryPrefixActual004.native_table_history_data input C laminar current accounting
    available budget positive small (some quota) policy sameRule
  have length:commands.length≤2*I.stageCount+1:=PSTRStatistics.CompactABI.commandsAt_length_le _
  obtain ⟨counts,countsLength,execution,cost,prefixes⟩:=PSTRLiveController.actual_bounded_prefixes
    I.compatibility laminar ⟨0,Finset.univ\available,false⟩ commands (actual.allowed sample horizon) length heap rep
  refine ⟨PSTRStatistics.CompactABI.tablePolicy_halted input C current.1 accounting available budget quota
      policy sameRule sample,counts,countsLength,length,execution,cost,?_,?_⟩
  · exact actual_records input C laminar current accounting available budget positive small quota policy sameRule
      sample horizon counts heap execution
  · intro clock
    have isPrefix:=actual.commands_prefix sample (Nat.le_of_lt clock.isLt)
    have prefixExecution:=prefixes _ isPrefix
    refine ⟨isPrefix,prefixExecution,?_,PSTRStatistics.CompactABI.actualQueryRecords_length_le _ _ _ _,
      PSTRStatistics.CompactABI.queryRecords_wordBound I.compatibility _ _ _ _⟩
    exact actual_records input C laminar current accounting available budget positive small quota policy sameRule
      sample clock.val _ heap prefixExecution

def WordRun (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (quota : I.Stage → Nat) (policy : Policy input C .native accounting Unit) : Prop :=
  ∃ prepSteps headSteps,
    PreparedRun I.compatibility (Finset.univ\available) prepSteps headSteps ∧
    NativeWordRun input C accounting available quota policy (preparedHeap I.compatibility (Finset.univ\available) prepSteps)

theorem word_run (input : StatisticalInput I) (C : Contract I) (laminar : LaminarSchedule I.compatibility)
    (current : C.IsCurrentAllocation) (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (positive : 0<budget) (small : budget≤1/2) (quota : I.Stage → Nat)
    (policy : Policy input C .native accounting Unit)
    (sameRule : policy.rule=CompactPrice.tableRule input available budget (some quota)) :
    WordRun input C accounting available quota policy := by
  obtain ⟨prepSteps,headSteps,prepared⟩:=prepared_run I.compatibility laminar (Finset.univ\available)
  exact ⟨prepSteps,headSteps,prepared,native_word_run input C laminar current accounting available budget positive small
    quota policy sameRule _ prepared.2.2.1⟩

/-- Original H0/caps and whole-execution bills, including failed and
finite-paid nonreturning ideal paths. There is no success conditioning. -/
structure Core (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (exponent : Nat) (policy : Policy input C .native accounting Unit) : Prop where
  same_rule : policy.rule=CompactPrice.tableRule input available budget (some (referenceQuota input exponent))
  same_run : ∀ sample clock,run input C .native accounting policy.rule sample clock=
    run input C .uncapped accounting (CompactPrice.tableRule input available budget (some (referenceQuota input exponent))) sample clock
  caps : ∀ sample clock,(run input C .native accounting policy.rule sample clock).ledger.obeysCaps C ∧
    (run input C .native accounting policy.rule sample clock).ledger.normalCalls≤(C.normalCallBound:ℕ∞)
  sample_bill : ∀ sample,runActualBill input C .native accounting policy.rule sample≤
    runActualBill input C .uncapped accounting (CompactPrice.tableRule input available budget none) sample
  full_bill : expectedBill input C .native accounting policy.rule (Measure.dirac ())≤
    expectedBill input C .uncapped accounting (CompactPrice.tableRule input available budget none) (Measure.dirac ())

theorem core_of_rule (input : StatisticalInput I) (C : Contract I) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (exponent : Nat)
    (qualification : CompactPrice.OriginalQualification input C accounting available budget exponent)
    (policy : Policy input C .native accounting Unit)
    (sameRule : policy.rule=CompactPrice.tableRule input available budget (some (referenceQuota input exponent))) :
    Core input C accounting available budget exponent policy := by
  obtain ⟨canonical,canonicalRule,canonicalRun,canonicalCaps⟩:=PSTRStatistics.tableNativeImplementation
    input C current.1 accounting available budget exponent qualification
  have samePolicy:=PSTRStatistics.CompactABI.policy_eq_of_rule_eq input C .native accounting policy canonical
    (sameRule.trans canonicalRule.symm)
  have sameRun:=samePolicy.symm ▸ canonicalRun
  have caps:=samePolicy.symm ▸ canonicalCaps
  have bills : ∀ sample,runActualBill input C .native accounting policy.rule sample≤
      runActualBill input C .uncapped accounting (CompactPrice.tableRule input available budget none) sample := by
    intro sample
    have equality : runActualBill input C .native accounting policy.rule sample=
        runActualBill input C .uncapped accounting
          (CompactPrice.tableRule input available budget (some (referenceQuota input exponent))) sample := by
      unfold runActualBill
      simp_rw [sameRun]
    rw [equality]
    exact PSTRStatistics.TableTruncation.tableRunActualBill_le_ideal input C current.1 accounting available budget
      (referenceQuota input exponent) sample
  exact ⟨sameRule,sameRun,caps,bills,lintegral_mono bills⟩

def NativeClaims : Prop :=
  ∀ (I : Instance),LaminarSchedule I.compatibility → ∀ (input : StatisticalInput I) (C : Contract I),C.IsCurrentAllocation →
  ∀ (accounting : NormalAccounting I) (available : Finset I.Tool) (delta : ℝ),0<delta → delta≤1/2 →
  ∀ (budget : ℚ) (exponent : Nat),ReferenceRiskChoice I.stageCount delta exponent budget →
    CompactPrice.OriginalQualification input C accounting available budget exponent →
    ∃ policy : Policy input C .native accounting Unit,
      Core input C accounting available budget exponent policy ∧
      WordRun input C accounting available (referenceQuota input exponent) policy ∧
      risk input C .native accounting policy.rule (Measure.dirac ())≤ENNReal.ofReal delta

theorem native_claims : NativeClaims := by
  intro I laminar input C current accounting available delta positive small budget exponent choice qualification
  obtain ⟨policy,sameRule,_sameRun,_caps,riskBound,_bill⟩:=
    PSTRStatistics.TableNativeRisk.tableNativeStatisticalClaims input laminar C current accounting available
      delta positive small budget exponent choice qualification
  exact ⟨policy,core_of_rule input C current accounting available budget exponent qualification policy sameRule,
    word_run input C laminar current accounting available budget choice.positive choice.small
      (referenceQuota input exponent) policy sameRule,riskBound⟩

def SharpClaims : Prop :=
  ∀ (I : Instance),LaminarSchedule I.compatibility → ∀ (input : StatisticalInput I) (available : Finset I.Tool)
    (depth : Nat),errorRank I.compatibility available=(depth:ℕ∞) →
    ∀ epsilon : ℝ,0<epsilon → ∃ cutoff : ℝ,0<cutoff ∧ ∀ delta : ℝ,0<delta → delta<cutoff → delta≤1/2 →
    ∀ (budget : ℚ) (exponent : Nat),ReferenceRiskChoice I.stageCount delta exponent budget →
    ∀ (C : Contract I),C.IsCurrentAllocation → ∀ accounting : NormalAccounting I,
      CompactPrice.OriginalQualification input C accounting available budget exponent →
      ∃ policy : Policy input C .native accounting Unit,
        Core input C accounting available budget exponent policy ∧
        WordRun input C accounting available (referenceQuota input exponent) policy ∧
        risk input C .native accounting policy.rule (Measure.dirac ())≤ENNReal.ofReal delta ∧
        expectedBill input C .native accounting policy.rule (Measure.dirac ())≤
          ENNReal.ofReal ((1+epsilon)*(PaperProofs.Common.SymbolicPrice.inputExpression input available).eval*
            iteratedLog depth delta⁻¹)

theorem sharp_claims : SharpClaims := by
  intro I laminar input available depth rank epsilon positive
  obtain ⟨cutoff,cutoffPositive,upper⟩:=PSTRStatistics.sharpUpperClaims I laminar input available depth rank epsilon positive
  refine ⟨cutoff,cutoffPositive,?_⟩
  intro delta deltaPositive below small budget exponent choice C current accounting qualification
  obtain ⟨policy,sameRule,riskBound,billBound⟩:=
    upper delta deltaPositive below small budget exponent choice C current accounting qualification
  exact ⟨policy,core_of_rule input C current accounting available budget exponent qualification policy sameRule,
    word_run input C laminar current accounting available budget choice.positive choice.small
      (referenceQuota input exponent) policy sameRule,riskBound,billBound⟩

def InfiniteClaims : Prop :=
  ∀ (I : Instance),LaminarSchedule I.compatibility → ∀ (input : StatisticalInput I) (available : Finset I.Tool),
    errorRank I.compatibility available=⊤ → ∀ (C : Contract I),C.IsCurrentAllocation →
    ∀ (accounting : NormalAccounting I) (budget : ℚ) (exponent : Nat),0<budget → budget≤1/2 →
      CompactPrice.OriginalQualification input C accounting available budget exponent →
      ∃ policy : Policy input C .native accounting Unit,
        Core input C accounting available budget exponent policy ∧
        WordRun input C accounting available (referenceQuota input exponent) policy ∧
        risk input C .native accounting policy.rule (Measure.dirac ())=0 ∧
        expectedObservationBill input C .native accounting policy.rule (Measure.dirac ())=0 ∧
        expectedBill input C .native accounting policy.rule (Measure.dirac ())≤
          (min I.stageCount I.toolCount:Nat)*input.fees.maxCorrection

theorem infinite_claims : InfiniteClaims := by
  intro I laminar input available rank C current accounting budget exponent positive small qualification
  obtain ⟨policy,sameRule,riskZero,observationsZero,billBound⟩:=
    PSTRStatistics.TableInfinite.infiniteRankClaims I laminar input available rank C current accounting budget exponent
      positive small qualification
  exact ⟨policy,core_of_rule input C current accounting available budget exponent qualification policy sameRule,
    word_run input C laminar current accounting available budget positive small
      (referenceQuota input exponent) policy sameRule,riskZero,observationsZero,billBound⟩

/-- This closes the paper's fixed Word/same-TABLE structural-statistical
composition. Actual Expr construction/output bits and scalar qualification
algorithm costs are the separately assigned remaining paper endpoints. -/
theorem paper_table :
    0<preprocessingConstant ∧
    (∀ (q : Nat) (full : List (Finset (Fin q))),LaminarSchedule full → ∀ used : Finset (Fin q),
      ∃ prepSteps headSteps,PreparedRun full used prepSteps headSteps) ∧
    NativeClaims ∧ SharpClaims ∧ InfiniteClaims :=
  ⟨RootL01.PHCompat.Public.constant_positive,fun _ _ laminar used => prepared_run _ laminar used,
    native_claims,sharp_claims,infinite_claims⟩

end RootPaper.Table

#print axioms RootPaper.Table.paper_table

open Lean Elab Command
run_cmd do
  let env:=(← getEnv).setExporting false
  let declarations:=env.constants.toList.filter (fun (name,_) =>
    name.toString.startsWith "RootPaper.Table.")
  unless declarations.length>0 do throwError "ROOT_PAPER_TABLE_STD3_FAIL no own declarations"
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let mut theorems : Nat:=0
  for (name,info) in declarations do
    match info with
    | .axiomInfo _ => throwError m!"ROOT_PAPER_TABLE_STD3_FAIL new_axiom={name}"
    | .opaqueInfo _ => throwError m!"ROOT_PAPER_TABLE_STD3_FAIL opaque={name}"
    | .thmInfo _ => theorems:=theorems+1
    | _ => pure ()
    for ax in ← collectAxioms name do
      unless allowed.contains ax do throwError m!"ROOT_PAPER_TABLE_STD3_FAIL forbidden={ax} declaration={name}"
  logInfo m!"ROOT_PAPER_TABLE_STD3_PASS declarations={declarations.length} theorems={theorems} new_axioms=0 forbidden=0"

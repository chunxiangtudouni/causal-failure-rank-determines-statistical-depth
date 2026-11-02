module

public import PaperProofs.Paid.PenaltyProgram
public import PaperProofs.Common.ReferenceController
public import PaperProofs.Common.NativeRepairCount
public import Mathlib.Data.List.MinMax

/-!
The concrete finite-menu penalty table and native endpoint-policy script
from paid-proofs.tex:476--482. The table is rational executable data, distinct
from the independently defined full-history paidPenaltyValue. A solve fixes
all actions before running the native policy; no value or strategy oracle is
called by the history script. An unbounded endpoint script is NOT the later
calibrated Q-bounded implementation from D23--D26.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Paid

open Common Common.Native

inductive MenuBadAction where
  | abandon
  | repair
  deriving DecidableEq, Repr

inductive MenuAction where
  | finish
  | abandon
  | test (level : ℕ) (bad : MenuBadAction)
  deriving DecidableEq, Repr

/-- Data only: all three means are rational. No correctness, feasibility,
sign, risk bound or optimality assertion is stored in a table entry. -/
structure MenuEntry where
  action : MenuAction
  observation : ℚ
  repairs : ℚ
  failure : ℚ
  deriving DecidableEq, Repr

def MenuEntry.objective (entry : MenuEntry) (fee penalty : ℚ) : ℚ :=
  entry.observation + fee * entry.repairs + penalty * entry.failure

def finishEntry : MenuEntry := ⟨.finish, 0, 0, 0⟩
def abandonEntry : MenuEntry := ⟨.abandon, 0, 0, 1⟩

/-- A paid bad branch adds one REAL execution to the stored mean. The
controller will allocate and execute it using its genuine mismatch handle. -/
def repairEntry (child : MenuEntry) : MenuEntry :=
  { child with repairs := 1 + child.repairs }

abbrev MenuRow := Array MenuEntry
abbrev MenuTable := Array MenuRow

def baseMenuRow (tools : ℕ) : MenuRow := Array.replicate (tools + 1) finishEntry

/-- One original independent fair-guess bit for each physical stage. The
finite product is fixed before the run and is independent of its World. -/
abbrev MenuSeed (N K : ℕ) := (freshInstance N K).Stage → Bool

noncomputable def menuSeedLaw (N K : ℕ) : Measure (MenuSeed N K) :=
  Measure.pi (fun _ : (freshInstance N K).Stage => Statistics.BinarySymmetric.Parameters.fairGuessLaw)

instance menuSeedLaw_probability (N K : ℕ) : IsProbabilityMeasure (menuSeedLaw N K) := by
  unfold menuSeedLaw
  infer_instance

theorem menuSeedLaw_eval (N K : ℕ) (stage : (freshInstance N K).Stage) :
    (menuSeedLaw N K).map (Function.eval stage) = Statistics.BinarySymmetric.Parameters.fairGuessLaw :=
  (measurePreserving_eval
    (fun _ : (freshInstance N K).Stage => Statistics.BinarySymmetric.Parameters.fairGuessLaw) stage).map_eq

theorem menuSeedLaw_independent (N K : ℕ) :
    ProbabilityTheory.iIndepFun (fun stage (seed : MenuSeed N K) => seed stage) (menuSeedLaw N K) := by
  exact ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : (freshInstance N K).Stage => Statistics.BinarySymmetric.Parameters.fairGuessLaw)
    (X := fun _ bit => bit) (fun _ => aemeasurable_id)

theorem menuSeedLaw_conditionalError (N K : ℕ) (stage : (freshInstance N K).Stage) (truth : Bool) :
    menuSeedLaw N K {seed | seed stage ≠ truth} = ENNReal.ofReal (1 / 2 : ℝ) := by
  change menuSeedLaw N K ((Function.eval stage) ⁻¹' {bit : Bool | bit ≠ truth}) = _
  rw [← Measure.map_apply (measurable_pi_apply stage) (by measurability), menuSeedLaw_eval]
  cases truth <;> norm_num [Statistics.BinarySymmetric.Parameters.fairGuessLaw,
    Statistics.BinarySymmetric.Parameters.rocCoinLaw]

namespace Parameters

def menuBadBranch (_P : PaperProofs.Paid.Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) : MenuBadAction × MenuEntry :=
  match tools with
  | 0 => (.abandon, abandonEntry)
  | next + 1 =>
      let corrected := repairEntry (previous.getD next abandonEntry)
      if corrected.objective fee penalty < penalty then (.repair, corrected)
      else (.abandon, abandonEntry)

def menuTestingEntry (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (tools level : ℕ) : MenuEntry :=
  let good := previous.getD tools abandonEntry
  let bad := P.menuBadBranch fee penalty previous tools
  let p := P.binarySymmetric.endpointError level
  {
    action := .test level bad.1
    observation := P.binarySymmetric.endpointCharge level + (1 - p) * good.observation + p * bad.2.observation
    repairs := (1 - p) * good.repairs + p * bad.2.repairs
    failure := (1 - p) * good.failure + p * bad.2.failure
  }

theorem menuTestingEntry_objective (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (tools level : ℕ) :
    (P.menuTestingEntry fee penalty previous tools level).objective fee penalty =
      P.binarySymmetric.endpointCharge level +
        (1 - P.binarySymmetric.endpointError level) * (previous.getD tools abandonEntry).objective fee penalty +
        P.binarySymmetric.endpointError level * (P.menuBadBranch fee penalty previous tools).2.objective fee penalty := by
  dsimp only [menuTestingEntry, MenuEntry.objective]
  ring

theorem menuBadBranch_zero (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ) (previous : MenuRow) :
    (P.menuBadBranch fee penalty previous 0).2.objective fee penalty = penalty := by
  simp [menuBadBranch, abandonEntry, MenuEntry.objective]

theorem menuBadBranch_succ (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) :
    (P.menuBadBranch fee penalty previous (tools + 1)).2.objective fee penalty =
      min penalty (fee + (previous.getD tools abandonEntry).objective fee penalty) := by
  have hrepair : (repairEntry (previous.getD tools abandonEntry)).objective fee penalty =
      fee + (previous.getD tools abandonEntry).objective fee penalty := by
    dsimp only [repairEntry, MenuEntry.objective]
    ring
  dsimp only [menuBadBranch]
  rw [hrepair]
  split_ifs with hlt
  · dsimp only
    rw [hrepair, min_eq_right hlt.le]
  · simp only [abandonEntry, MenuEntry.objective, mul_zero, mul_one, add_zero, zero_add]
    exact (min_eq_left (le_of_not_gt hlt)).symm

/-- Ascending indices and Mathlib's first-occurrence argmin fix the ORIGINAL
least minimizing testing index. This minimization precedes the separate
outer abandonment comparison. The menu always includes level zero. -/
def leastTestingLevel (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) : ℕ :=
  ((List.range (P.certificate.M + 1)).argmin
    (fun level => (P.menuTestingEntry fee penalty previous tools level).objective fee penalty)).getD 0

private theorem index_in_range (m n : ℕ) (hm : m < n) : (List.range n).idxOf m = m := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ]
    by_cases hlt : m < n
    · rw [List.idxOf_append_of_mem (List.mem_range.mpr hlt)]
      exact ih hlt
    · have heq : m = n := by omega
      subst m
      rw [List.idxOf_append_of_notMem (by simp)]
      simp

/-- The computed testing index is minimal over the original complete menu
and is the LEAST natural index among all ties; no value oracle is assumed. -/
theorem leastTestingLevel_spec (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) :
    let chosen := P.leastTestingLevel fee penalty previous tools
    chosen ≤ P.certificate.M ∧
      (∀ m : ℕ, m ≤ P.certificate.M →
        (P.menuTestingEntry fee penalty previous tools chosen).objective fee penalty ≤
          (P.menuTestingEntry fee penalty previous tools m).objective fee penalty) ∧
      ∀ m : ℕ, m ≤ P.certificate.M →
        (P.menuTestingEntry fee penalty previous tools chosen).objective fee penalty =
          (P.menuTestingEntry fee penalty previous tools m).objective fee penalty → chosen ≤ m := by
  dsimp only
  cases hchoice : (List.range (P.certificate.M + 1)).argmin
      (fun level => (P.menuTestingEntry fee penalty previous tools level).objective fee penalty) with
  | none =>
    have hnil := List.argmin_eq_none.mp hchoice
    have hlen := congrArg List.length hnil
    simp at hlen
  | some chosen =>
    have hs := List.argmin_eq_some_iff.mp hchoice
    have hc : chosen < P.certificate.M + 1 := List.mem_range.mp hs.1
    have heq : P.leastTestingLevel fee penalty previous tools = chosen := by
      simp only [leastTestingLevel, hchoice, Option.getD_some]
    rw [heq]
    refine ⟨by omega, ?_, ?_⟩
    · intro m hm
      exact hs.2.1 m (List.mem_range.mpr (by omega))
    · intro m hm he
      have hi := hs.2.2 m (List.mem_range.mpr (by omega)) he.symm.le
      rw [index_in_range chosen (P.certificate.M + 1) hc,
        index_in_range m (P.certificate.M + 1) (by omega)] at hi
      exact hi

def nextMenuEntry (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) : MenuEntry :=
  if penalty = 0 then abandonEntry else
    let best := P.menuTestingEntry fee penalty previous tools (P.leastTestingLevel fee penalty previous tools)
    if penalty ≤ best.objective fee penalty then abandonEntry else best

def nextMenuRow (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) : MenuRow :=
  Array.ofFn (fun k : Fin (tools + 1) => P.nextMenuEntry fee penalty previous k.val)

theorem baseMenuRow_size (tools : ℕ) : (baseMenuRow tools).size = tools + 1 := by
  simp [baseMenuRow]

theorem nextMenuRow_size (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) : (P.nextMenuRow fee penalty previous tools).size = tools + 1 := by
  simp [nextMenuRow]

/-- The actual complete table is stored row by row. Each new row reads
ONLY the preceding row, with both k and k-1 inside the original width.
Runtime/word-RAM complexity is not inferred from this definition alone. -/
def solveMenuTable (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ) (tools : ℕ) : ℕ → MenuTable
  | 0 => #[baseMenuRow tools]
  | stages + 1 =>
      let rows := P.solveMenuTable fee penalty tools stages
      rows.push (P.nextMenuRow fee penalty (rows.getD stages (baseMenuRow tools)) tools)

theorem solveMenuTable_size (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ) (tools stages : ℕ) :
    (P.solveMenuTable fee penalty tools stages).size = stages + 1 := by
  induction stages with
  | zero => rfl
  | succ stages ih => simp only [solveMenuTable, Array.size_push, ih]

theorem solveMenuTable_row_size (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ) (tools stages : ℕ) :
    ∀ row ∈ P.solveMenuTable fee penalty tools stages, row.size = tools + 1 := by
  induction stages with
  | zero =>
    intro row hrow
    have heq : row = baseMenuRow tools := by simpa only [solveMenuTable, Array.mem_singleton] using hrow
    subst row
    exact baseMenuRow_size tools
  | succ stages ih =>
    intro row hrow
    change row ∈ (P.solveMenuTable fee penalty tools stages).push
      (P.nextMenuRow fee penalty ((P.solveMenuTable fee penalty tools stages).getD stages (baseMenuRow tools)) tools) at hrow
    rcases Array.mem_push.mp hrow with hold | heq
    · exact ih row hold
    · subst row
      exact P.nextMenuRow_size fee penalty _ tools

def menuEntryAt (table : MenuTable) (stages tools : ℕ) : MenuEntry :=
  (table.getD stages #[]).getD tools abandonEntry

/-- The actual finite observed BSC walk. An invalid public symbol is not
silently interpreted as a letter of the original alphabet. -/
def menuWordScore (observations : List ℕ) : ℤ :=
  observations.foldl (fun score symbol => if symbol = 1 then score + 1 else score - 1) 0

def endpointTestingAction (_P : PaperProofs.Paid.Parameters) (N K : ℕ) (level : ℕ)
    (seed : MenuSeed N K)
    (history : List (VisibleEvent (freshInstance N K))) (stage : (freshInstance N K).Stage) :
    Action (freshInstance N K) :=
  if level = 0 then .write stage (seed stage) else
  let observations := historyObservations history stage
  if observations.all (fun symbol => symbol < 2) then
    let score := menuWordScore observations
    if level ≤ score.natAbs then .write stage (decide (0 ≤ score)) else .review stage
  else .abandon

@[simp] theorem endpointTestingAction_zero (P : PaperProofs.Paid.Parameters) (N K : ℕ)
    (seed : MenuSeed N K) (history : List (VisibleEvent (freshInstance N K))) (stage : (freshInstance N K).Stage) :
    P.endpointTestingAction N K 0 seed history stage = .write stage (seed stage) := by
  simp only [endpointTestingAction, ite_true]

/-- At a stage entry, only earlier PHYSICAL executions reduce k. During
its allocate/execute pair this snapshot stays unchanged; after advance the
completed correction enters the next row. Pending rights are still excluded
from the separate genuine unused-tool selection below. -/
def menuEntryTools (_P : PaperProofs.Paid.Parameters) (N K : ℕ)
    (history : List (VisibleEvent (freshInstance N K))) (stage : (freshInstance N K).Stage) : ℕ :=
  K - ((historyExecutions history).filter (fun execution => execution.1.stage.val < stage.val)).length

def menuUnusedTool (_P : PaperProofs.Paid.Parameters) (N K : ℕ)
    (history : List (VisibleEvent (freshInstance N K))) : Option (freshInstance N K).Tool :=
  (List.finRange K).find? (fun tool => tool ∉ historyUsed history)

def menuRepairAction (P : PaperProofs.Paid.Parameters) (N K : ℕ)
    (history : List (VisibleEvent (freshInstance N K))) (stage : (freshInstance N K).Stage) :
    Action (freshInstance N K) :=
  if (historyExecutions history).any (fun execution => execution.1.stage == stage) then .advance stage
  else match (historyCommitments history).find? (fun commitment => commitment.1.stage == stage) with
  | some commitment => .execute commitment.1 commitment.2
  | none => match referenceVisibleHandle history stage, P.menuUnusedTool N K history with
    | some handle, some tool => .allocate handle tool
    | _, _ => .abandon

def menuCandidateAction (P : PaperProofs.Paid.Parameters) (N K : ℕ) (table : MenuTable)
    (seed : MenuSeed N K)
    (history : List (VisibleEvent (freshInstance N K))) : Action (freshInstance N K) :=
  if historyHalted history then .stop else
  if hstage : historyCursor history < N then
    let stage : (freshInstance N K).Stage := ⟨historyCursor history, by simpa [freshInstance] using hstage⟩
    let entry := menuEntryAt table (N - stage.val) (P.menuEntryTools N K history stage)
    match historyWrite history stage with
    | none => match entry.action with
      | .finish | .abandon => .abandon
      | .test level _ => P.endpointTestingAction N K level seed history stage
    | some (bit, serial) => match historyReport history stage with
      | none => .abandon
      | some (truth, reportedSerial) =>
          if serial != reportedSerial then .abandon else
          if bit == truth then .advance stage else
          match entry.action with
          | .test _ .repair => P.menuRepairAction N K history stage
          | _ => .abandon
  else if historyCursor history = N then .stop else .abandon

/-- A fixed visible permission wrapper. Its legality is proved independently;
its NONBINDING behavior on the selected script remains a correctness target.
The wrapper has no world, truth, fee-budget or statistical-value oracle. -/
def compiledMenuRule (P : PaperProofs.Paid.Parameters) (N K : ℕ) (table : MenuTable)
    : PolicyRule (freshInstance N K) (MenuSeed N K) :=
  fun seed history =>
    let action := P.menuCandidateAction N K table seed history
    if historyAllowsAction history action then action else .abandon

/-- This creates the entire rational table before the returned history
closure is run. It is the original ideal endpoint controller, not a new
native implementation obtained by naively truncating its endpoint tests. -/
def paidEndpointRule (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ) :
    PolicyRule P.sharedInstance (MenuSeed P.certificate.stages P.tools) :=
  let table := P.solveMenuTable fee penalty P.tools P.certificate.stages
  P.compiledMenuRule P.certificate.stages P.tools table

theorem measurable_compiledMenuRule (P : PaperProofs.Paid.Parameters) (N K : ℕ) (table : MenuTable)
    : MeasurableRule (P.compiledMenuRule N K table) :=
  measurable_of_countable _

theorem compiledMenuRule_uncapped_legal (P : PaperProofs.Paid.Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K)) :
    LegalRule (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) := by
  intro seed truth tapes n state hp hactive
  let action := P.menuCandidateAction N K table seed state.history
  by_cases allowed : historyAllowsAction state.history action
  · obtain ⟨next, step⟩ := historyAllowsAction_sound (P.freshInput N K fee hfee) C hearly accounting
      (P.compiledMenuRule N K table) seed truth tapes hp hactive action allowed
    exact ⟨next, by simpa only [compiledMenuRule, action, ite_eq_left allowed] using step⟩
  · exact ⟨stopState state true, by
      simpa only [compiledMenuRule, action, ite_eq_right allowed] using
        (Step.abandon (input := P.freshInput N K fee hfee) (C := C) (mode := ResourceMode.uncapped)
          (accounting := accounting) (tapes := tapes) state hactive)⟩

def compiledMenuPolicy (P : PaperProofs.Paid.Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K)) :
    Policy (P.freshInput N K fee hfee) C .uncapped accounting (MenuSeed N K) where
  rule := P.compiledMenuRule N K table
  measurable_rule := P.measurable_compiledMenuRule N K table
  legal := P.compiledMenuRule_uncapped_legal N K table fee hfee C hearly accounting

/-- The fixed endpoint compiler on EXACTLY the original shared input and
actual fee. Its legal-policy package contains no performance or value claim. -/
def paidEndpointPolicy (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (penalty : ℚ)
    (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (accounting : NormalAccounting P.sharedInstance) :
    Policy (P.input fee hfee) C .uncapped accounting (MenuSeed P.certificate.stages P.tools) :=
  P.compiledMenuPolicy P.certificate.stages P.tools
    (P.solveMenuTable fee penalty P.tools P.certificate.stages) fee hfee C hearly accounting

@[simp] theorem paidEndpointPolicy_rule (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (penalty : ℚ)
    (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (accounting : NormalAccounting P.sharedInstance) :
    (P.paidEndpointPolicy fee hfee penalty C hearly accounting).rule = P.paidEndpointRule fee penalty := rfl

/-- Structural and least-tie checks for actual computed entries. The
mathematical full-policy value is not a premise or field of the table. -/
def MenuTableDataCorrect (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee penalty : ℚ), 0 ≤ fee → 0 ≤ penalty → ∀ N K : ℕ,
    (P.solveMenuTable fee penalty K N).size = N + 1 ∧
    (∀ row ∈ P.solveMenuTable fee penalty K N, row.size = K + 1) ∧
    ∀ (previous : MenuRow) (k : ℕ),
      let chosen := P.leastTestingLevel fee penalty previous k
      chosen ≤ P.certificate.M ∧
      (∀ m : ℕ, m ≤ P.certificate.M →
        (P.menuTestingEntry fee penalty previous k chosen).objective fee penalty ≤
          (P.menuTestingEntry fee penalty previous k m).objective fee penalty) ∧
      ∀ m : ℕ, m ≤ P.certificate.M →
        (P.menuTestingEntry fee penalty previous k chosen).objective fee penalty =
          (P.menuTestingEntry fee penalty previous k m).objective fee penalty → chosen ≤ m

theorem menuTableDataCorrect (P : PaperProofs.Paid.Parameters) : P.MenuTableDataCorrect := by
  intro fee penalty _hfee _hpenalty N K
  exact ⟨P.solveMenuTable_size fee penalty K N, P.solveMenuTable_row_size fee penalty K N,
    fun previous k => P.leastTestingLevel_spec fee penalty previous k⟩

/-- The pending D18 full-history optimality identity of the computed table.
F was already independently defined over ALL legal randomized policies. -/
def MenuTableValueCorrect (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee penalty : ℚ) (hfee : 0 ≤ fee), 0 ≤ penalty → penalty ≤ P.Lambda →
    ∀ (N K n k : ℕ), n ≤ N → k ≤ K →
      P.freshPaidPenalty fee hfee n k (ENNReal.ofReal (penalty : ℝ)) =
        ENNReal.ofReal ((menuEntryAt (P.solveMenuTable fee penalty K N) n k).objective fee penalty : ℝ)

/-- Explicit signs/ranges prevent ofReal from concealing an invalid negative
record. These properties are pending, not fields assumed by the compiler. -/
def MenuTableStatsBounds (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee penalty : ℚ), 0 ≤ fee → 0 ≤ penalty → ∀ (N K n k : ℕ), n ≤ N → k ≤ K →
    let entry := menuEntryAt (P.solveMenuTable fee penalty K N) n k
    0 ≤ entry.observation ∧ 0 ≤ entry.repairs ∧ entry.repairs ≤ (min n k : ℕ) ∧
      0 ≤ entry.failure ∧ entry.failure ≤ 1

/-- True expected records of the actual compiler, including failure paths.
No finite-ET, MAP or optimality assumption is inserted into a Policy. -/
def MenuCompilerMeans (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee penalty : ℚ) (hfee : 0 ≤ fee), 0 ≤ penalty → penalty ≤ P.Lambda →
    ∀ (N K : ℕ) (C : Contract (freshInstance N K)), C.IsCurrentPayment →
      ∀ accounting : NormalAccounting (freshInstance N K),
        let table := P.solveMenuTable fee penalty K N
        let rule := P.compiledMenuRule N K table
        let entry := menuEntryAt table N K
        expectedObservationBill (P.freshInput N K fee hfee) C .uncapped accounting rule (menuSeedLaw N K) =
          ENNReal.ofReal (entry.observation : ℝ) ∧
        expectedRepairCount (P.freshInput N K fee hfee) C .uncapped accounting rule (menuSeedLaw N K) =
          ENNReal.ofReal (entry.repairs : ℝ) ∧
        expectedBill (P.freshInput N K fee hfee) C .uncapped accounting rule (menuSeedLaw N K) =
          ENNReal.ofReal ((entry.observation + fee * entry.repairs : ℚ) : ℝ) ∧
        risk (P.freshInput N K fee hfee) C .uncapped accounting rule (menuSeedLaw N K) =
          ENNReal.ofReal (entry.failure : ℝ)

/-- The visible fallback must not introduce additional abandonment on a
reached valid compiler path. This is a target about real Prefixes. -/
def MenuCompilerGuardNonbinding (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee penalty : ℚ) (hfee : 0 ≤ fee), 0 ≤ penalty → penalty ≤ P.Lambda →
    ∀ (N K : ℕ) (C : Contract (freshInstance N K)), C.IsCurrentPayment →
      ∀ (accounting : NormalAccounting (freshInstance N K)) (sample : MenuSeed N K × (P.freshInput N K fee hfee).World) n,
        let table := P.solveMenuTable fee penalty K N
        let rule := P.compiledMenuRule N K table
        let state := run (P.freshInput N K fee hfee) C .uncapped accounting rule sample n
        state.halted = false → rule sample.1 state.history = P.menuCandidateAction N K table sample.1 state.history

def MenuCompilerClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  P.MenuTableDataCorrect ∧ P.MenuTableStatsBounds ∧ P.MenuTableValueCorrect ∧
    P.MenuCompilerMeans ∧ P.MenuCompilerGuardNonbinding

end Parameters
end PaperProofs.Paid


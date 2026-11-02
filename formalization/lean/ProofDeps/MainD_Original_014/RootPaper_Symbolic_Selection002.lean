module
public import RootPaper_Symbolic_Construct001

/-! Paper-scope original-index lookup and finite expression assembly.
Input navigation is explicit: skipped experiment records are scanned, bit by
bit, rather than accessed by an uncharged statistical oracle. The nested
lists and rational bitstrings are the supplied input representation. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootPaper.Symbolic
open PaperProofs.Common PaperProofs.Common.SymbolicPrice PaperProofs.Statistics
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.RationalControllerComputation.PSTRTMLength004
open PSTRSymbolicBits

def skipBits : List Bool → Nat
  | [] => 0
  | _ :: later => 1 + skipBits later

theorem skipBits_exact (bits : List Bool) : skipBits bits = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit later ih => simp only [skipBits, List.length_cons, ih]; omega

/-- One record/link navigation plus every input bit read, including the
final end-of-list test. No rational arithmetic or comparisons are used. -/
def skipData : List Datum → Nat
  | [] => 1
  | datum :: later => 1 + skipBits (encodeDatum datum) + skipData later

theorem skipData_exact (data : List Datum) :
    skipData data = 1 + data.length + datumMass data := by
  induction data with
  | nil => rfl
  | cons datum later ih =>
    simp only [skipData, skipBits_exact, encodeDatum_length, datumMass_cons, List.length_cons, ih]
    omega

def experimentMass (items : List BinaryExperiment) : Nat :=
  (items.map (fun E => datumMass (rawExperiment E))).sum

/-- Original channel input consists of the false row followed by the true
row. Pair their supplied leaf descriptors by an actual simultaneous scan;
do not assume an interleaved channel view was supplied for free. -/
def zipGiven : List GivenRat → List GivenRat → List Row × Nat
  | first :: later, second :: rest =>
      let tail := zipGiven later rest
      ((first, second) :: tail.1, 4 + tail.2)
  | _, _ => ([], 1)

theorem zipGiven_ofFn {n : Nat} (first second : Fin n → GivenRat) :
    (zipGiven (List.ofFn first) (List.ofFn second)).1 = List.ofFn (fun y => (first y, second y)) ∧
      (zipGiven (List.ofFn first) (List.ofFn second)).2 = 4 * n + 1 := by
  induction n with
  | zero => simp [zipGiven]
  | succ n ih =>
    have tail := ih (fun y => first y.succ) (fun y => second y.succ)
    simp only [List.ofFn_succ, zipGiven, tail.1, tail.2]
    constructor
    · exact True.intro
    · omega

def sourceStage (E : BinaryExperiment) (paired : List Row) : Built :=
  navigate 3 (multiply (copyRat (given E.observationFee))
    (add (divide (add (constant 1) (multiply (constant (-1)) (copyRat (given E.priorOne))))
        (divergence paired false))
      (divide (copyRat (given E.priorOne)) (divergence paired true))))

def preparedLocal (E : BinaryExperiment) : Built :=
  let prepared := zipGiven (List.ofFn (fun y => given (E.channel false y)))
    (List.ofFn (fun y => given (E.channel true y)))
  navigate prepared.2 (sourceStage E prepared.1)

theorem preparedLocal_eq (E : BinaryExperiment) :
    preparedLocal E = navigate (4 * E.alphabetSize + 1) (stageBuild E) := by
  have paired := zipGiven_ofFn (fun y => given (E.channel false y)) (fun y => given (E.channel true y))
  simp only [preparedLocal, paired.1, paired.2]
  rfl

theorem preparedLocal_work_le (E : BinaryExperiment) :
    (preparedLocal E).work ≤ 48 * datumMass (rawExperiment E) := by
  have built := local_work_le E
  have channels := channelMass_ge E
  have mass := rawExperiment_mass E
  have header : 4 ≤ datumBits (.natural E.alphabetSize) := by
    simp only [datumBits, natBits]
    omega
  rw [preparedLocal_eq]
  simp only [navigate, Built.work] at built ⊢
  omega

/-- A total recursion on the actual natural stage index. The invalid-index
branch is only a totalization; original table indices are proved valid below. -/
def lookup : List BinaryExperiment → Nat → Built
  | [], _ => navigate 1 (constant 0)
  | E :: _, 0 => navigate 1 (preparedLocal E)
  | E :: later, index + 1 => navigate (1 + skipData (rawExperiment E)) (lookup later index)

theorem lookup_expression {items : List BinaryExperiment} {index : Nat} {E : BinaryExperiment}
    (found : items[index]? = some E) : (lookup items index).expression = (stageBuild E).expression := by
  induction items generalizing index with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at found
  | cons first later ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst first
      rw [lookup, preparedLocal_eq]
      rfl
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      exact ih found

theorem lookup_work_le (items : List BinaryExperiment) (index : Nat) :
    (lookup items index).work ≤ 48 * experimentMass items + 2 * items.length + 18 := by
  induction items generalizing index with
  | nil =>
    simp only [lookup, navigate, Built.work, experimentMass, List.map_nil, List.sum_nil,
      List.length_nil, Nat.mul_zero, Nat.zero_add]
    have c := constant_zero
    omega
  | cons E later ih =>
    have localBound := preparedLocal_work_le E
    have lengthBound := length_le_datumMass (rawExperiment E)
    cases index with
    | zero =>
      simp only [lookup, navigate, Built.work] at ⊢
      simp only [Built.work] at localBound
      simp only [experimentMass, List.map_cons, List.sum_cons, List.length_cons]
      omega
    | succ index =>
      have tailBound := ih index
      simp only [lookup, navigate, Built.work, skipData_exact]
      simp only [Built.work] at tailBound
      simp only [experimentMass, List.map_cons, List.sum_cons, List.length_cons] at ⊢ tailBound
      omega

/-- Read each actual index once, emit its outer sum node once, and build
the stage by the explicit lookup above. The terminating zero is also copied. -/
def assemble (items : List BinaryExperiment) : List Nat → Built
  | [] => navigate 1 (constant 0)
  | index :: later => navigate 1 (add (lookup items index) (assemble items later))

theorem assemble_expression (items : List BinaryExperiment) (indices : List Nat) :
    (assemble items indices).expression =
      sumExpr (indices.map (fun index => (lookup items index).expression)) := by
  induction indices with
  | nil => rfl
  | cons index later ih =>
    simp only [assemble, navigate, add, List.map_cons, sumExpr, ih]

theorem assemble_work_le (items : List BinaryExperiment) (indices : List Nat) :
    (assemble items indices).work ≤
      18 + indices.length * (48 * experimentMass items + 2 * items.length + 20) := by
  induction indices with
  | nil =>
    simp only [assemble, navigate, Built.work, List.length_nil, Nat.zero_mul, Nat.add_zero]
    have c := constant_zero
    omega
  | cons index later ih =>
    have current := lookup_work_le items index
    simp only [assemble, navigate, add, Built.work, List.length_cons]
    simp only [Built.work] at current ih
    nlinarith

theorem heads_payload {Tool : Type*} [DecidableEq Tool]
    (stages : ExperimentSchedule Tool) (remaining : Finset Tool) (target : ℕ∞) (offset : Nat)
    {entry : Nat × BinaryExperiment} (member : entry ∈ heads stages remaining target offset) :
    ∃ position : Nat, entry.1 = offset + position ∧
      (stages.map Prod.snd)[position]? = some entry.2 := by
  induction stages generalizing offset with
  | nil => simp only [heads, List.not_mem_nil] at member
  | cons stage later ih =>
    rcases stage with ⟨eligible, E⟩
    simp only [heads] at member
    split at member
    · rcases List.mem_cons.mp member with rfl | tailMember
      · exact ⟨0, by omega, rfl⟩
      · obtain ⟨position, indexEq, found⟩ := ih (offset + 1) tailMember
        exact ⟨position + 1, by omega, by simpa only [List.map_cons, List.getElem?_cons_succ] using found⟩
    · obtain ⟨position, indexEq, found⟩ := ih (offset + 1) member
      exact ⟨position + 1, by omega, by simpa only [List.map_cons, List.getElem?_cons_succ] using found⟩

variable {I : Instance}

def experiments (input : StatisticalInput I) : List BinaryExperiment :=
  List.ofFn input.experiment

theorem inputHead_lookup (input : StatisticalInput I) (available : Finset I.Tool)
    {entry : Nat × BinaryExperiment} (member : entry ∈ inputHeads input available) :
    (experiments input)[entry.1]? = some entry.2 := by
  unfold inputHeads at member
  split at member
  · simp only [List.not_mem_nil] at member
  · obtain ⟨position, indexEq, found⟩ := heads_payload (inputSchedule input) available _ 0 member
    have posEq : position = entry.1 := by omega
    subst position
    simpa only [inputSchedule, List.map_ofFn, experiments, Function.comp_def] using found

theorem experiments_mass (input : StatisticalInput I) :
    experimentMass (experiments input) = originalExperimentMass input := by
  simp only [experimentMass, experiments, originalExperimentMass,
    List.ofFn_eq_map, List.map_map, Function.comp_def]

def fromIndices (input : StatisticalInput I) (indices : List Nat) : Built :=
  assemble (experiments input) indices

theorem from_original_heads_expression (input : StatisticalInput I) (available : Finset I.Tool) :
    (fromIndices input ((inputHeads input available).map Prod.fst)).expression =
      sumExpr ((inputHeads input available).map (fun entry => (stageBuild entry.2).expression)) := by
  rw [fromIndices, assemble_expression, List.map_map]
  apply congrArg sumExpr
  apply List.map_congr_left
  intro entry member
  exact lookup_expression (inputHead_lookup input available member)

theorem from_original_heads_eval (input : StatisticalInput I) (available : Finset I.Tool) :
    (fromIndices input ((inputHeads input available).map Prod.fst)).expression.eval =
      input.orderedCoefficient available := by
  rw [from_original_heads_expression, eval_sumExpr, List.map_map]
  have old := inputExpression_eval input available
  rw [inputExpression_eq_head_sum, eval_sumExpr, List.map_map] at old
  simpa only [Function.comp_def, local_eval, localCoefficientExpr_eval] using old

theorem from_original_heads_nodes (input : StatisticalInput I) (available : Finset I.Tool) :
    (fromIndices input ((inputHeads input available).map Prod.fst)).expression.nodes =
      1 + ((inputHeads input available).map (fun entry => 14 * entry.2.alphabetSize + 14)).sum := by
  rw [from_original_heads_expression, sumExpr_nodes, List.map_map]
  have point :
      (fun entry : Nat × BinaryExperiment => (stageBuild entry.2).expression.nodes + 1) =
        (fun entry => 14 * entry.2.alphabetSize + 14) := by
    funext entry
    rw [← (stageBuild entry.2).emitted_exact, local_emitted]
  simp only [Function.comp_def]
  rw [point]
  omega

/-- Uniform polynomial bound for the concrete recursive construction. This
is a work theorem, not an inference of running time from output size. Even
repeated valid indices satisfy it; no precomputed coefficient is an input. -/
theorem fromIndices_work_le (input : StatisticalInput I) (available : Finset I.Tool)
    (indices : List Nat) (count : indices.length ≤ I.stageCount) :
    (fromIndices input indices).work ≤ 88 * ((symbolicInput input available).length + 1) ^ 2 := by
  have bound := assemble_work_le (experiments input) indices
  have mass := (originalExperimentMass_le input available).trans (originalInputMass_le_length input available)
  have stages := stageCount_le_input_length input available
  rw [experiments_mass] at bound
  have length : (experiments input).length = I.stageCount := by
    simp only [experiments, List.length_ofFn, PaperProofs.Common.Instance.stageCount]
  rw [length] at bound
  unfold fromIndices
  have monotone :
      indices.length * (48 * originalExperimentMass input + 2 * I.stageCount + 20) ≤
        (symbolicInput input available).length * (50 * (symbolicInput input available).length + 20) := by
    apply Nat.mul_le_mul (count.trans stages)
    omega
  nlinarith

end RootPaper.Symbolic

module

public import RootPaper_Prep_Closed006

/-! Dedicated charged preparation recursion. Numerical results and the
arithmetic schedule are returned by the SAME recursion. This is not an
instruction language or interpreter and has no bind/VM/caller certificate.
The log is an erased cost annotation. administration counts the separate
finite traversals, Boolean/control steps, input accesses and result fields. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

open scoped BigOperators
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.PSTRWordBool

namespace RootPaper.Prep

structure Calculation (α : Type*) where
  value : α
  operations : List Operation
  administration : Nat

def powerCalculation : Nat → Calculation Rat
  | 0 => ⟨1,[],1⟩
  | n+1 =>
      let before := powerCalculation n
      ⟨before.value*2,before.operations++[.rational .mul before.value 2],before.administration+3⟩

theorem powerCalculation_spec (n : Nat) :
    (powerCalculation n).value = (2 : Rat)^n ∧
    (powerCalculation n).operations = powerOps n ∧
    (powerCalculation n).administration ≤ 4*((powerCalculation n).operations.length+1) := by
  induction n with
  | zero => simp [powerCalculation, powerOps]
  | succ n ih =>
    simp only [powerCalculation]
    refine ⟨by rw [ih.1, pow_succ], ?_, ?_⟩
    · simp only [ih.1, ih.2.1, powerOps, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    · have control := ih.2.2
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

def ratioTestCalculation (r : Rat) (n : Nat) : Calculation Bool :=
  let power := powerCalculation n
  let inverse := 1/r
  let first := decide (r ≤ power.value)
  let second := decide (inverse ≤ power.value)
  ⟨first && second, power.operations++[.rational .div 1 r,
    .rational .le r power.value,.rational .le inverse power.value,.branch],power.administration+8⟩

theorem ratioTestCalculation_spec (r : Rat) (n : Nat) :
    (ratioTestCalculation r n).value = ratioTest r n ∧
    (ratioTestCalculation r n).operations = ratioTestOps r n ∧
    (ratioTestCalculation r n).administration ≤ 8*((ratioTestCalculation r n).operations.length+1) := by
  have power := powerCalculation_spec n
  refine ⟨?_,?_,?_⟩
  · simp only [ratioTestCalculation, power.1, ratioTest]
  · simp only [ratioTestCalculation, power.1, power.2.1, ratioTestOps]
  · have control := power.2.2
    simp only [ratioTestCalculation, List.length_append, List.length_cons, List.length_nil]
    omega

def exponentTestCalculation (budget : Rat) (N n : Nat) : Calculation Bool :=
  let numberPower := powerCalculation (N+1)
  let dyadicPower := powerCalculation n
  let constant := 6*numberPower.value
  let twiceN := 2*(N : Rat)
  let target := twiceN*constant
  let dyadic := dyadicPower.value*budget
  ⟨decide (1 ≤ n) && decide (target ≤ dyadic),
    numberPower.operations++dyadicPower.operations++naturalLE 1 n++
      [.natural N,.rational .mul 6 numberPower.value,.rational .mul 2 (N : Rat),
        .rational .mul twiceN constant,.rational .mul dyadicPower.value budget,
        .rational .le target dyadic,.branch],
    numberPower.administration+dyadicPower.administration+15⟩

theorem exponentTestCalculation_spec (budget : Rat) (N n : Nat) :
    (exponentTestCalculation budget N n).value = exponentTest budget N n ∧
    (exponentTestCalculation budget N n).operations = exponentTestOps budget N n ∧
    (exponentTestCalculation budget N n).administration ≤
      8*((exponentTestCalculation budget N n).operations.length+1) := by
  have first := powerCalculation_spec (N+1)
  have second := powerCalculation_spec n
  refine ⟨?_,?_,?_⟩
  · simp only [exponentTestCalculation, first.1, second.1, exponentTest, referenceQuotaConstant]
    rfl
  · simp only [exponentTestCalculation, first.1, second.1, first.2.1, second.2.1, exponentTestOps]
  · have a := first.2.2
    have b := second.2.2
    simp only [exponentTestCalculation, naturalLE, List.length_append, List.length_cons, List.length_nil]
    omega

def quotaTestCalculation (e b m : Nat) (d : Rat) (n : Nat) : Calculation Bool :=
  let sum := (e : Rat)+b
  let first := 2*sum
  let current := d*(n : Rat)
  let squareM := (m : Rat)*m
  let eightM := 8*squareM
  let second := (e : Rat)*eightM
  let squareD := d*d
  let currentSquare := squareD*(n : Rat)
  ⟨decide (first ≤ current) && decide (second ≤ currentSquare),
    [.natural e,.natural b,.natural m,.natural n,
      .rational .add (e : Rat) (b : Rat),.rational .mul 2 sum,.rational .mul d (n : Rat),
      .rational .le first current,.rational .mul (m : Rat) (m : Rat),.rational .mul 8 squareM,
      .rational .mul (e : Rat) eightM,.rational .mul d d,.rational .mul squareD (n : Rat),
      .rational .le second currentSquare,.branch],30⟩

theorem quotaTestCalculation_spec (e b m : Nat) (d : Rat) (n : Nat) :
    (quotaTestCalculation e b m d n).value = quotaTest e b m d n ∧
    (quotaTestCalculation e b m d n).operations = quotaTestOps e b m d n ∧
    (quotaTestCalculation e b m d n).administration ≤
      8*((quotaTestCalculation e b m d n).operations.length+1) := by
  exact ⟨rfl,rfl,by change 30 ≤ 8*(15+1); decide⟩

def ratioCalculation (r : Rat) (n : Nat) : Calculation Nat :=
  if (ratioTestCalculation r n).value then
    ⟨n,(ratioTestCalculation r n).operations,(ratioTestCalculation r n).administration+3⟩
  else
    let next := ratioCalculation r (n+1)
    ⟨next.value,(ratioTestCalculation r n).operations++naturalAdd n 1++next.operations,
      (ratioTestCalculation r n).administration+next.administration+9⟩
termination_by BinaryExperiment.ratioIntegerBound r-n
decreasing_by
  have failed : ¬ratioTest r n = true := by
    rw [←(ratioTestCalculation_spec r n).1]
    assumption
  have before : n < BinaryExperiment.ratioIntegerBound r := by
    have : ¬BinaryExperiment.ratioIntegerBound r ≤ n := fun h => failed ((ratioTest_iff r n).2 h)
    omega
  omega

theorem ratioCalculation_spec (r : Rat) (n : Nat) :
    (ratioCalculation r n).value = ratioSearch r n ∧
    (ratioCalculation r n).operations = ratioOps r n ∧
    (ratioCalculation r n).administration ≤ 32*((ratioCalculation r n).operations.length+1) := by
  fun_induction ratioCalculation r n with
  | case1 n passed =>
    have test := ratioTestCalculation_spec r n
    have pass : ratioTest r n = true := by rw [←test.1]; exact passed
    refine ⟨?_,?_,?_⟩
    · rw [ratioSearch_eq, max_eq_left ((ratioTest_iff r n).1 pass)]
    · rw [ratioOps, ite_eq_left pass]
      exact test.2.1
    · have control := test.2.2
      dsimp only
      omega
  | case2 n failed next ih =>
    have test := ratioTestCalculation_spec r n
    have fail : ¬ratioTest r n = true := by rw [←test.1]; exact failed
    have before : n < BinaryExperiment.ratioIntegerBound r := by
      have : ¬BinaryExperiment.ratioIntegerBound r ≤ n := fun h => fail ((ratioTest_iff r n).2 h)
      omega
    refine ⟨?_,?_,?_⟩
    · rw [ih.1, ratioSearch_eq, ratioSearch_eq, max_eq_right (by omega), max_eq_right (by omega)]
    · rw [ratioOps, ite_eq_right fail, test.2.1, ih.2.1]
    · have control := test.2.2
      have rest := ih.2.2
      dsimp only [next]
      simp only [List.length_append, naturalAdd, List.length_cons, List.length_nil]
      omega

def exponentCalculation (budget : Rat) (positive : 0 < budget) (N n : Nat) : Calculation Nat :=
  if (exponentTestCalculation budget N n).value then
    ⟨n,(exponentTestCalculation budget N n).operations,(exponentTestCalculation budget N n).administration+3⟩
  else
    let next := exponentCalculation budget positive N (n+1)
    ⟨next.value,(exponentTestCalculation budget N n).operations++naturalAdd n 1++next.operations,
      (exponentTestCalculation budget N n).administration+next.administration+9⟩
termination_by BinaryExperiment.quotaExponent budget N-n
decreasing_by
  have failed : ¬exponentTest budget N n = true := by
    rw [←(exponentTestCalculation_spec budget N n).1]
    assumption
  have before : n < BinaryExperiment.quotaExponent budget N := by
    have : ¬BinaryExperiment.quotaExponent budget N ≤ n := fun h =>
      failed ((exponentTest_iff budget positive N n).2 h)
    omega
  omega

theorem exponentCalculation_spec (budget : Rat) (positive : 0 < budget) (N n : Nat) :
    (exponentCalculation budget positive N n).value = exponentSearch budget positive N n ∧
    (exponentCalculation budget positive N n).operations = exponentOps budget positive N n ∧
    (exponentCalculation budget positive N n).administration ≤
      32*((exponentCalculation budget positive N n).operations.length+1) := by
  fun_induction exponentCalculation budget positive N n with
  | case1 n passed =>
    have test := exponentTestCalculation_spec budget N n
    have pass : exponentTest budget N n = true := by rw [←test.1]; exact passed
    refine ⟨?_,?_,?_⟩
    · rw [exponentSearch_eq, max_eq_left ((exponentTest_iff budget positive N n).1 pass)]
    · rw [exponentOps, ite_eq_left pass]
      exact test.2.1
    · have control := test.2.2
      dsimp only
      omega
  | case2 n failed next ih =>
    have test := exponentTestCalculation_spec budget N n
    have fail : ¬exponentTest budget N n = true := by rw [←test.1]; exact failed
    have before : n < BinaryExperiment.quotaExponent budget N := by
      have : ¬BinaryExperiment.quotaExponent budget N ≤ n := fun h =>
        fail ((exponentTest_iff budget positive N n).2 h)
      omega
    refine ⟨?_,?_,?_⟩
    · rw [ih.1, exponentSearch_eq, exponentSearch_eq, max_eq_right (by omega), max_eq_right (by omega)]
    · rw [exponentOps, ite_eq_right fail, test.2.1, ih.2.1]
    · have control := test.2.2
      have rest := ih.2.2
      dsimp only [next]
      simp only [List.length_append, naturalAdd, List.length_cons, List.length_nil]
      omega

def quotaCalculation (e b m : Nat) (d : Rat) (positive : 0 < d) (n : Nat) : Calculation Nat :=
  if (quotaTestCalculation e b m d n).value then
    ⟨n,(quotaTestCalculation e b m d n).operations,(quotaTestCalculation e b m d n).administration+3⟩
  else
    let next := quotaCalculation e b m d positive (n+1)
    ⟨next.value,(quotaTestCalculation e b m d n).operations++naturalAdd n 1++next.operations,
      (quotaTestCalculation e b m d n).administration+next.administration+9⟩
termination_by RootB234.Quota.quota e b m d-n
decreasing_by
  have failed : ¬quotaTest e b m d n = true := by
    rw [←(quotaTestCalculation_spec e b m d n).1]
    assumption
  have before : n < RootB234.Quota.quota e b m d := by
    have : ¬RootB234.Quota.quota e b m d ≤ n := fun h =>
      failed ((quotaTest_iff e b m d positive n).2 h)
    omega
  omega

theorem quotaCalculation_spec (e b m : Nat) (d : Rat) (positive : 0 < d) (n : Nat) :
    (quotaCalculation e b m d positive n).value = quotaSearch e b m d positive n ∧
    (quotaCalculation e b m d positive n).operations = quotaOps e b m d positive n ∧
    (quotaCalculation e b m d positive n).administration ≤
      32*((quotaCalculation e b m d positive n).operations.length+1) := by
  fun_induction quotaCalculation e b m d positive n with
  | case1 n passed =>
    have test := quotaTestCalculation_spec e b m d n
    have pass : quotaTest e b m d n = true := by rw [←test.1]; exact passed
    refine ⟨?_,?_,?_⟩
    · rw [quotaSearch_eq, max_eq_left ((quotaTest_iff e b m d positive n).1 pass)]
    · rw [quotaOps, ite_eq_left pass]
      exact test.2.1
    · have control := test.2.2
      dsimp only
      omega
  | case2 n failed next ih =>
    have test := quotaTestCalculation_spec e b m d n
    have fail : ¬quotaTest e b m d n = true := by rw [←test.1]; exact failed
    have before : n < RootB234.Quota.quota e b m d := by
      have : ¬RootB234.Quota.quota e b m d ≤ n := fun h =>
        fail ((quotaTest_iff e b m d positive n).2 h)
      omega
    refine ⟨?_,?_,?_⟩
    · rw [ih.1, quotaSearch_eq, quotaSearch_eq, max_eq_right (by omega), max_eq_right (by omega)]
    · rw [quotaOps, ite_eq_right fail, test.2.1, ih.2.1]
    · have control := test.2.2
      have rest := ih.2.2
      dsimp only [next]
      simp only [List.length_append, naturalAdd, List.length_cons, List.length_nil]
      omega

def channelCalculation (E : BinaryExperiment) (ys : List (Fin E.alphabetSize)) (current : Nat) : Calculation Nat :=
  match ys with
  | [] => ⟨current,[],1⟩
  | y::ys =>
      let ratio := E.channel true y/E.channel false y
      let bound := ratioCalculation ratio 0
      let chosen := if decide (current ≤ bound.value) then bound.value else current
      let next := channelCalculation E ys chosen
      ⟨next.value,[.rational .div (E.channel true y) (E.channel false y)]++
        bound.operations++naturalLE current bound.value++next.operations,
        bound.administration+next.administration+12⟩

theorem channelCalculation_spec (E : BinaryExperiment) (ys : List (Fin E.alphabetSize)) (current : Nat) :
    (channelCalculation E ys current).value =
      (ys.map (fun y => ratioSearch (E.channel true y/E.channel false y) 0)).foldl max current ∧
    (channelCalculation E ys current).operations = channelOpsAux E ys current ∧
    (channelCalculation E ys current).administration ≤
      64*((channelCalculation E ys current).operations.length+1) := by
  induction ys generalizing current with
  | nil => exact ⟨rfl,rfl,by change 1 ≤ 64*(0+1); decide⟩
  | cons y ys ih =>
    have bound := ratioCalculation_spec (E.channel true y/E.channel false y) 0
    have later := ih (max current (ratioCalculation (E.channel true y/E.channel false y) 0).value)
    simp only [channelCalculation, maximum_selection]
    refine ⟨?_,?_,?_⟩
    · rw [later.1, bound.1]
      rfl
    · rw [bound.2.1, later.2.1, bound.1]
      rfl
    · have a := bound.2.2
      have b := later.2.2
      simp only [List.length_append, naturalLE, List.length_cons, List.length_nil]
      omega

def absoluteOperations (E : BinaryExperiment) (y : Fin E.alphabetSize) (current : Rat) : List Operation :=
  let difference := E.channel true y-E.channel false y
  let magnitude := if decide (0 ≤ difference) then difference else 0-difference
  [.rational .sub (E.channel true y) (E.channel false y),.rational .le 0 difference,
    .rational .sub 0 difference,.branch,.rational .add current magnitude]

def sumCalculation (E : BinaryExperiment) (ys : List (Fin E.alphabetSize)) (current : Rat) : Calculation Rat :=
  match ys with
  | [] => ⟨current,[],1⟩
  | y::ys =>
      let difference := E.channel true y-E.channel false y
      let magnitude := if decide (0 ≤ difference) then difference else 0-difference
      let next := sumCalculation E ys (current+magnitude)
      ⟨next.value,absoluteOperations E y current++next.operations,next.administration+10⟩

theorem sumCalculation_spec (E : BinaryExperiment) (ys : List (Fin E.alphabetSize)) (current : Rat) :
    (sumCalculation E ys current).value =
      ys.foldl (fun total y => total+|E.channel true y-E.channel false y|) current ∧
    (sumCalculation E ys current).administration ≤ 64*((sumCalculation E ys current).operations.length+1) := by
  induction ys generalizing current with
  | nil => exact ⟨rfl,by change 1 ≤ 64*(0+1); decide⟩
  | cons y ys ih =>
    have later := ih (current+|E.channel true y-E.channel false y|)
    simp only [sumCalculation, absolute_selection]
    refine ⟨later.1,?_⟩
    have control := later.2
    simp only [List.length_append, absoluteOperations, List.length_cons, List.length_nil]
    omega

/-- Each operand in the accumulation log is the actual fold state reached
by its earlier steps, rather than a supplied prefix-sum value. -/
theorem sumCalculation_operations (E : BinaryExperiment) (ys : List (Fin E.alphabetSize)) (current : Rat) :
    (sumCalculation E ys current).operations = ys.zipIdx.flatMap (fun pair =>
      absoluteOperations E pair.1
        ((ys.take pair.2).foldl (fun total y => total+|E.channel true y-E.channel false y|) current)) := by
  induction ys generalizing current with
  | nil => rfl
  | cons y ys ih =>
    simp only [sumCalculation, absolute_selection, List.zipIdx_cons', List.flatMap_cons,
      List.flatMap_map, List.take_zero, List.foldl_nil]
    rw [ih]
    simp only [Prod.map_fst, Prod.map_snd, id_eq, List.take_succ_cons, List.foldl_cons]

theorem original_sumCalculation (E : BinaryExperiment) :
    (sumCalculation E (List.finRange E.alphabetSize).reverse 0).value = sumAbs E ∧
    (sumCalculation E (List.finRange E.alphabetSize).reverse 0).operations = sumAbsOps E ∧
    (sumCalculation E (List.finRange E.alphabetSize).reverse 0).administration ≤
      64*((sumCalculation E (List.finRange E.alphabetSize).reverse 0).operations.length+1) := by
  have values := sumCalculation_spec E (List.finRange E.alphabetSize).reverse 0
  refine ⟨values.1,?_,values.2⟩
  rw [sumCalculation_operations]
  simp only [sumAbsOps]
  apply List.flatMap_congr
  intro pair _
  rw [sumAbs_prefix_state]
  simp only [absoluteOperations, absolute_selection, sumStepOps]

def reviewCalculation {I : Instance} (C : Contract I) : List (I.Stage × StageResult) → Calculation Bool
  | [] => ⟨true,[],1⟩
  | row::rows =>
      let before := decide (row.2.quota ≤ C.reviewQuota row.1)
      let next := reviewCalculation C rows
      ⟨before && next.value,naturalLE row.2.quota (C.reviewQuota row.1)++next.operations,
        next.administration+6⟩

theorem reviewCalculation_spec (I : Instance) (C : Contract I) (rows : List (I.Stage × StageResult)) :
    (reviewCalculation C rows).value = rows.all (fun row => decide (row.2.quota ≤ C.reviewQuota row.1)) ∧
    (reviewCalculation C rows).operations = rows.flatMap (fun row => naturalLE row.2.quota (C.reviewQuota row.1)) ∧
    (reviewCalculation C rows).administration ≤ 32*((reviewCalculation C rows).operations.length+1) := by
  induction rows with
  | nil => exact ⟨rfl,rfl,by change 1 ≤ 32*(0+1); decide⟩
  | cons row rows ih =>
    simp only [reviewCalculation]
    refine ⟨?_,?_,?_⟩
    · simp only [ih.1, List.all_cons]
    · rw [ih.2.1]
      rfl
    · have control := ih.2.2
      simp only [List.length_append, naturalLE, List.length_cons, List.length_nil]
      omega

def quotaSumCalculation {α : Type*} (rows : List (α × StageResult)) (current : Nat) : Calculation Nat :=
  match rows with
  | [] => ⟨current,[],1⟩
  | row::rows =>
      let sum := current+row.2.quota
      let next := quotaSumCalculation rows sum
      ⟨next.value,naturalAdd current row.2.quota++next.operations,next.administration+6⟩

theorem quotaSumCalculation_spec {α : Type*} (rows : List (α × StageResult)) (current : Nat) :
    (quotaSumCalculation rows current).value = current+(rows.map (fun row => row.2.quota)).sum ∧
    (quotaSumCalculation rows current).operations = quotaSumOps rows current ∧
    (quotaSumCalculation rows current).administration ≤ 32*((quotaSumCalculation rows current).operations.length+1) := by
  induction rows generalizing current with
  | nil => exact ⟨by simp only [quotaSumCalculation, List.map_nil, List.sum_nil, Nat.add_zero], rfl, by change 1 ≤ 32*(0+1); decide⟩
  | cons row rows ih =>
    have later := ih (current+row.2.quota)
    simp only [quotaSumCalculation]
    refine ⟨?_,?_,?_⟩
    · simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using later.1
    · rw [later.2.1]
      rfl
    · have control := later.2.2
      simp only [List.length_append, naturalAdd, List.length_cons, List.length_nil]
      omega

def qualificationCalculation {I : Instance} (C : Contract I) (rows : List (I.Stage × StageResult)) : Calculation Bool :=
  let reviews := reviewCalculation C rows
  let sum := quotaSumCalculation rows 0
  let minimum := if decide (I.stageCount ≤ I.toolCount) then I.stageCount else I.toolCount
  let first := C.normalCallBound+sum.value
  let final := first+minimum
  ⟨reviews.value && decide (final ≤ C.totalCallCap),
    reviews.operations++sum.operations++naturalLE I.stageCount I.toolCount++
      naturalAdd C.normalCallBound sum.value++naturalAdd first minimum++naturalLE final C.totalCallCap,
    reviews.administration+sum.administration+20⟩

theorem qualificationCalculation_spec (I : Instance) (C : Contract I) (rows : List (I.Stage × StageResult)) :
    (qualificationCalculation C rows).value = qualify C rows ∧
    (qualificationCalculation C rows).operations = qualificationOps C rows ∧
    (qualificationCalculation C rows).administration ≤ 128*((qualificationCalculation C rows).operations.length+1) := by
  have reviews := reviewCalculation_spec I C rows
  have sum := quotaSumCalculation_spec rows 0
  simp only [qualificationCalculation, minimum_selection]
  refine ⟨?_,?_,?_⟩
  · rw [reviews.1, sum.1]
    simp only [qualify, Nat.zero_add]
  · rw [reviews.2.1, sum.2.1, sum.1]
    simp only [qualificationOps, Nat.zero_add]
  · have a := reviews.2.2
    have b := sum.2.2
    simp only [List.length_append, naturalLE, naturalAdd, List.length_cons, List.length_nil]
    omega

def stageCalculation (E : BinaryExperiment) (e : Nat) : Calculation StageResult :=
  let prior := ratioCalculation (E.priorOne/(1-E.priorOne)) 0
  let channels := channelCalculation E (List.finRange E.alphabetSize) 0
  let sum := sumCalculation E (List.finRange E.alphabetSize).reverse 0
  let d := sum.value*sum.value/2
  let positive : 0 < d := by
    have same : d = drift E := by
      dsimp only [d,sum]
      rw [(original_sumCalculation E).1]
      rfl
    rw [same, drift_eq]
    exact E.channelDriftLower_pos
  let quota := quotaCalculation e prior.value channels.value d positive 0
  ⟨⟨d,channels.value,prior.value,quota.value⟩,
    [.rational .sub 1 E.priorOne,.rational .div E.priorOne (1-E.priorOne)]++
      prior.operations++channels.operations++sum.operations++
      [.rational .mul sum.value sum.value,.rational .div (sum.value*sum.value) 2]++quota.operations,
    prior.administration+channels.administration+sum.administration+quota.administration+14⟩

theorem stageCalculation_spec (E : BinaryExperiment) (e : Nat) :
    (stageCalculation E e).value = prepareStage E e ∧
    (stageCalculation E e).operations = stageOps E e ∧
    (stageCalculation E e).administration ≤ 128*((stageCalculation E e).operations.length+1) ∧
    4 ≤ (stageCalculation E e).operations.length := by
  have prior := ratioCalculation_spec (E.priorOne/(1-E.priorOne)) 0
  have channel := channelCalculation_spec E (List.finRange E.alphabetSize) 0
  have sum := original_sumCalculation E
  have dpos : 0 < (sumCalculation E (List.finRange E.alphabetSize).reverse 0).value*
      (sumCalculation E (List.finRange E.alphabetSize).reverse 0).value/2 := by
    rw [sum.1]
    change 0 < drift E
    rw [drift_eq]
    exact E.channelDriftLower_pos
  have quota := quotaCalculation_spec e (ratioCalculation (E.priorOne/(1-E.priorOne)) 0).value
    (channelCalculation E (List.finRange E.alphabetSize) 0).value
    ((sumCalculation E (List.finRange E.alphabetSize).reverse 0).value*
      (sumCalculation E (List.finRange E.alphabetSize).reverse 0).value/2) dpos 0
  simp only [stageCalculation]
  refine ⟨?_,?_,?_,?_⟩
  · rw [quota.1]
    simp only [prior.1, channel.1, sum.1, prepareStage, channelMax, drift]
  · rw [quota.2.1]
    simp only [prior.2.1, channel.2.1, sum.2.1, prior.1, channel.1, sum.1,
      stageOps, channelOps, channelMax, drift, driftEndOps]
  · have a := prior.2.2
    have b := channel.2.2
    have c := sum.2.2
    have d := quota.2.2
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def stagesCalculation {I : Instance} (input : StatisticalInput I) (e : Nat) :
    List I.Stage → Calculation (List (I.Stage × StageResult))
  | [] => ⟨[],[],1⟩
  | stage::stages =>
      let first := stageCalculation (input.experiment stage) e
      let next := stagesCalculation input e stages
      ⟨(stage,first.value)::next.value,first.operations++next.operations,
        first.administration+next.administration+5⟩

theorem stagesCalculation_spec (I : Instance) (input : StatisticalInput I) (e : Nat) (stages : List I.Stage) :
    (stagesCalculation input e stages).value = stages.map (fun stage => (stage,prepareStage (input.experiment stage) e)) ∧
    (stagesCalculation input e stages).operations = stages.flatMap (fun stage => stageOps (input.experiment stage) e) ∧
    (stagesCalculation input e stages).administration ≤ 256*((stagesCalculation input e stages).operations.length+1) := by
  induction stages with
  | nil => exact ⟨rfl,rfl,by change 1 ≤ 256*(0+1); decide⟩
  | cons stage stages ih =>
    have first := stageCalculation_spec (input.experiment stage) e
    simp only [stagesCalculation]
    refine ⟨?_,?_,?_⟩
    · rw [first.1, ih.1]
      rfl
    · rw [first.2.1, ih.2.1]
      rfl
    · have a := first.2.2.1
      have minimum := first.2.2.2
      have b := ih.2.2
      simp only [List.length_append]
      omega

def inputCalculation : List Datum → Calculation (List Datum)
  | [] => ⟨[],[],1⟩
  | datum::data =>
      let next := inputCalculation data
      let copied := match datum with | .natural n => Datum.natural n | .rational q => .rational (q+0)
      let op := match datum with | .natural n => Operation.natural n | .rational q => .rational .add q 0
      ⟨copied::next.value,op::next.operations,next.administration+5⟩

theorem inputCalculation_spec (data : List Datum) :
    (inputCalculation data).value = data ∧
    (inputCalculation data).operations = data.map (fun datum => match datum with
      | .natural n => Operation.natural n | .rational q => .rational .add q 0) ∧
    (inputCalculation data).administration ≤ 8*((inputCalculation data).operations.length+1) := by
  induction data with
  | nil => exact ⟨rfl,rfl,by decide⟩
  | cons datum data ih =>
    simp only [inputCalculation]
    refine ⟨?_,?_,?_⟩
    · cases datum <;> simp only [add_zero, ih.1]
    · rw [ih.2.1]
      rfl
    · have control := ih.2.2
      simp only [List.length_cons]
      omega

def preparationCalculation {I : Instance} (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (positive : 0 < budget) : Calculation (NumericalPreparation I) :=
  let copied := inputCalculation (originalData input C budget)
  let exponent := exponentCalculation budget positive I.stageCount 1
  let rows := stagesCalculation input exponent.value (List.finRange I.stageCount)
  let qualified := qualificationCalculation C rows.value
  ⟨⟨exponent.value,rows.value,qualified.value⟩,
    copied.operations++exponent.operations++rows.operations++qualified.operations,
    copied.administration+exponent.administration+rows.administration+qualified.administration+20⟩

/-- The requested accounting connection: erasure, arithmetic sequence, and
all additional work follow from the same executable charged recursion. -/
theorem preparationCalculation_spec (I : Instance) (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (positive : 0 < budget) :
    (preparationCalculation input C budget positive).value = numericalPreparation input C budget positive ∧
    (preparationCalculation input C budget positive).operations = preparationOps input C budget positive ∧
    (preparationCalculation input C budget positive).administration ≤
      512*((preparationCalculation input C budget positive).operations.length+1) := by
  have copied := inputCalculation_spec (originalData input C budget)
  have exponent := exponentCalculation_spec budget positive I.stageCount 1
  have rows := stagesCalculation_spec I input (exponentCalculation budget positive I.stageCount 1).value
    (List.finRange I.stageCount)
  have qualification := qualificationCalculation_spec I C
    (stagesCalculation input (exponentCalculation budget positive I.stageCount 1).value (List.finRange I.stageCount)).value
  simp only [preparationCalculation]
  refine ⟨?_,?_,?_⟩
  · rw [qualification.1, rows.1, exponent.1]
    rfl
  · rw [copied.2.1, exponent.2.1, rows.2.1, qualification.2.1, rows.1, exponent.1]
    rfl
  · have a := copied.2.2
    have b := exponent.2.2
    have c := rows.2.2
    have d := qualification.2.2
    simp only [List.length_append]
    omega

/-- The largest actual operand/result field and the original input scan.
The cost annotation is erased: its lists need not be materialized at runtime.
A control unit can copy a fixed number of numerical fields, visit a list node,
combine Boolean flags, or scan the original typed input for the next field.
The fixed factor 32 pays each such action in binary bits. Counter arithmetic
itself is performed by the charged arithmetic primitives, not by this unit. -/
def frameWidth (base : Nat) (operations : List Operation) : Nat :=
  (operations.map (fun op => op.width+op.resultWidth+1)).foldl max (base+1)

def runningCost {α : Type*} (base : Nat) (calculation : Calculation α) : Nat :=
  arithmeticCost calculation.operations+32*calculation.administration*frameWidth base calculation.operations

theorem foldMaximum_bound (xs : List Nat) (initial bound : Nat) (start : initial ≤ bound)
    (each : ∀ n ∈ xs,n ≤ bound) : xs.foldl max initial ≤ bound := by
  induction xs generalizing initial with
  | nil => exact start
  | cons n ns ih =>
    exact ih (max initial n) (max_le start (each n List.mem_cons_self))
      (fun m member => each m (List.mem_cons_of_mem n member))

def administrativeCoefficient : Nat := 32*512*1000001*20485

theorem preparationCalculation_cost (I : Instance) (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (positive : 0 < budget) :
    runningCost (inputSize input C budget) (preparationCalculation input C budget positive) ≤
      (1000000*nativeRate*4097^8+administrativeCoefficient)*(arithmeticScale input C budget)^12 := by
  let P := arithmeticScale input C budget
  let calculation := preparationCalculation input C budget positive
  have one : 1 ≤ P := Nat.succ_le_succ (Nat.zero_le _)
  have spec := preparationCalculation_spec I input C budget positive
  have bounds := original_preparationOps_bounded I input C budget positive
  rw [←spec.2.1] at bounds
  have base : inputSize input C budget ≤ P := by unfold P arithmeticScale; omega
  have frame : frameWidth (inputSize input C budget) calculation.operations ≤ 20485*P := by
    apply foldMaximum_bound
    · omega
    · intro width member
      obtain ⟨op,present,rfl⟩ := List.mem_map.mp member
      have operand := bounds.2 op present
      have result := resultWidth_bound op
      change op.width ≤ 4096*P at operand
      omega
  have one4 : 1 ≤ P^4 := one_le_pow₀ one
  have count : calculation.operations.length+1 ≤ 1000001*P^4 :=
    (Nat.add_le_add bounds.1 one4).trans_eq (by ring)
  have admin : calculation.administration ≤ (512*1000001)*P^4 :=
    spec.2.2.trans ((Nat.mul_le_mul_left 512 count).trans_eq (by ring))
  have overhead : 32*calculation.administration*frameWidth (inputSize input C budget) calculation.operations ≤
      administrativeCoefficient*P^5 := by
    have bound := Nat.mul_le_mul (Nat.mul_le_mul_left 32 admin) frame
    exact bound.trans_eq (by unfold administrativeCoefficient; ring)
  have power5 : P^5 ≤ P^12 := Nat.pow_le_pow_right one (by decide)
  have overhead12 := overhead.trans (Nat.mul_le_mul_left administrativeCoefficient power5)
  have arithmetic := paper_preparation_arithmetic I input C budget positive
  rw [←spec.2.1] at arithmetic
  exact (Nat.add_le_add arithmetic overhead12).trans_eq (by
    dsimp only [runningCost, calculation, P]
    ring)

/-- Complete paper preparation endpoint, including whole-run accounting.
No complexity/rate/width/output/fuel premise occurs. -/
theorem paper_preparation_accounted :
    ∃ coefficient degree : Nat, 0 < coefficient ∧ 0 < degree ∧
      ∀ (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget : Rat) (positive : 0 < budget),
        let calculation := preparationCalculation input C budget positive
        calculation.value =
          ⟨computedExponent (I:=I) budget,originalRows input budget,numericQualification input C budget⟩ ∧
        calculation.operations = preparationOps input C budget positive ∧
        (∀ op ∈ calculation.operations,op.Realized) ∧
        runningCost (inputSize input C budget) calculation ≤ coefficient*(arithmeticScale input C budget)^degree := by
  refine ⟨1000000*nativeRate*4097^8+administrativeCoefficient,12,?_,by decide,?_⟩
  · have pos : 0 < administrativeCoefficient := by unfold administrativeCoefficient; decide
    exact lt_of_lt_of_le pos (Nat.le_add_left _ _)
  · intro I input C budget positive
    have spec := preparationCalculation_spec I input C budget positive
    exact ⟨spec.1.trans (numericalPreparation_eq I input C budget positive),spec.2.1,
      fun op _ => operation_realized op,preparationCalculation_cost I input C budget positive⟩

end RootPaper.Prep

#print axioms RootPaper.Prep.preparationCalculation_spec
#print axioms RootPaper.Prep.paper_preparation_accounted

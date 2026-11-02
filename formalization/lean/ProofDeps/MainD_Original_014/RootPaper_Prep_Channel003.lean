module

public import RootPaper_Prep_Arithmetic002

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

def originalData {I : Instance} (input : StatisticalInput I) (C : Contract I) (budget : Rat) : List Datum :=
  rawInstance input ++ rawContract C ++ [.rational budget]

theorem original_bits_le_scale (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    (preparationInput input C budget).length ≤ arithmeticScale input C budget := by
  unfold arithmeticScale inputSize
  omega

theorem input_rat_field (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget q : Rat)
    (present : Datum.rational q ∈ originalData input C budget) :
    field q ≤ arithmeticScale input C budget := by
  rw [field, RootB23.WordOddsBits.ratInput_fieldSize_eq]
  exact (RootB23.WordOddsBits.datum_width_le_encode _ q present).trans
    (original_bits_le_scale I input C budget)

theorem nat_field_eq (n : Nat) : field (n : Rat) = natBits n+1 := by
  change RootB234.ECost.field (n : Rat) = natBits n+1
  rw [RootB234.ECost.nat_field_exact]
  simp only [RootB234.ECost.raw, PSTRTMNatValue017.rawPayload, List.length_ofFn]

theorem input_nat_field (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget : Rat) (n : Nat)
    (present : Datum.natural n ∈ originalData input C budget) :
    field (n : Rat) ≤ arithmeticScale input C budget := by
  have localSize : field (n : Rat) ≤ (encodeDatum (.natural n)).length := by
    simp only [nat_field_eq, encodeDatum, encodeNat, List.length_cons, List.length_append,
      List.length_replicate, List.length_ofFn, List.length_nil]
    omega
  have one : (encodeDatum (.natural n)).length ≤
      (((originalData input C budget).map (fun d => (encodeDatum d).length))).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨.natural n, present, rfl⟩)
  have sumLength (data : List Datum) :
      (data.map (fun d => (encodeDatum d).length)).sum = (data.flatMap encodeDatum).length := by
    induction data with
    | nil => rfl
    | cons d ds ih => simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, ih]
  rw [sumLength] at one
  have room : ((originalData input C budget).flatMap encodeDatum).length ≤
      (preparationInput input C budget).length := by
    simp only [preparationInput, originalData, encode, List.length_append, List.length_cons, List.length_nil]
    omega
  exact localSize.trans (one.trans (room.trans (original_bits_le_scale I input C budget)))

theorem experiment_material_le_input (I : Instance) (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (stage : I.Stage) :
    ((rawExperiment (input.experiment stage)).flatMap encodeDatum).length ≤
      (preparationInput input C budget).length := by
  let f := fun stage : I.Stage => ((rawExperiment (input.experiment stage)).flatMap encodeDatum).length
  have member : f stage ∈ (List.finRange I.stageCount).map f :=
    List.mem_map.mpr ⟨stage, List.mem_finRange stage, rfl⟩
  have localBound := List.le_sum_of_mem member
  have concat (stages : List I.Stage) :
      (stages.map f).sum =
        ((stages.flatMap (fun s => rawExperiment (input.experiment s))).flatMap encodeDatum).length := by
    induction stages with
    | nil => rfl
    | cons s stages ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.flatMap_append,
        List.length_append, ←ih]
      rfl
  change f stage ≤ ((List.finRange I.compatibility.length).map f).sum at localBound
  rw [concat] at localBound
  have room :
      (((List.finRange I.stageCount).flatMap (fun s => rawExperiment (input.experiment s))).flatMap encodeDatum).length ≤
        (preparationInput input C budget).length := by
    simp only [preparationInput, rawInstance, encode, List.flatMap_append, List.length_append,
      List.length_cons, List.length_nil]
    omega
  exact localBound.trans room

theorem input_prior_field (I : Instance) (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (stage : I.Stage) :
    field (input.experiment stage).priorOne ≤ arithmeticScale input C budget := by
  apply input_rat_field I input C budget
  unfold originalData
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  unfold rawInstance
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  right
  exact List.mem_flatMap.mpr ⟨stage, List.mem_finRange stage, by simp [rawExperiment]⟩

theorem input_channel_field (I : Instance) (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (stage : I.Stage) (truth : Bool) (y : Fin (input.experiment stage).alphabetSize) :
    field ((input.experiment stage).channel truth y) ≤ arithmeticScale input C budget := by
  apply input_rat_field I input C budget
  unfold originalData
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  unfold rawInstance
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨stage, List.mem_finRange stage, ?_⟩
  unfold rawExperiment
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨truth, by cases truth <;> simp, List.mem_map.mpr ⟨y, List.mem_finRange y, rfl⟩⟩

theorem original_prefix_field (I : Instance) (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (stage : I.Stage) (k : Nat) :
    field (RootB234.ChannelWidth.reversePrefixAbs (input.experiment stage) k) ≤
      8*arithmeticScale input C budget := by
  have bound := RootB234.ChannelWidth.Public.reverse_prefix_fieldSize_le (input.experiment stage) k
  have material := experiment_material_le_input I input C budget stage
  have raw := original_bits_le_scale I input C budget
  have positive : 1 ≤ arithmeticScale input C budget := by unfold arithmeticScale; omega
  exact bound.trans (by omega)

theorem original_drift_field (I : Instance) (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (stage : I.Stage) :
    field (input.experiment stage).channelDriftLower ≤ 32*arithmeticScale input C budget := by
  have bound := RootB234.ChannelWidth.Public.channel_drift_fieldSize_le (input.experiment stage)
  have material := experiment_material_le_input I input C budget stage
  have raw := original_bits_le_scale I input C budget
  have positive : 1 ≤ arithmeticScale input C budget := by unfold arithmeticScale; omega
  exact bound.trans (by omega)

def channelOpsAux (E : BinaryExperiment) (ys : List (Fin E.alphabetSize)) (current : Nat) : List Operation :=
  match ys with
  | [] => []
  | y::ys =>
    let r := E.channel true y/E.channel false y
    let b := ratioSearch r 0
    [.rational .div (E.channel true y) (E.channel false y)] ++
      ratioOps r 0 ++ naturalLE current b ++ channelOpsAux E ys (max current b)

def channelOps (E : BinaryExperiment) : List Operation := channelOpsAux E (List.finRange E.alphabetSize) 0

theorem channelOpsAux_bounded (E : BinaryExperiment) (S : Nat) (positive : 1 ≤ S)
    (fields : ∀ truth y, field (E.channel truth y) ≤ S)
    (ratios : ∀ y, field (E.channel true y/E.channel false y) ≤ S)
    (limits : ∀ y, BinaryExperiment.ratioIntegerBound (E.channel true y/E.channel false y) ≤ S)
    (ys : List (Fin E.alphabetSize)) (current : Nat) (initial : current ≤ S) :
    Bounded (channelOpsAux E ys current) (ys.length*(32*S^2)) (64*S) := by
  induction ys generalizing current with
  | nil => exact bounded_nil _ _
  | cons y ys ih =>
    let r := E.channel true y/E.channel false y
    let b := ratioSearch r 0
    have beq : b = BinaryExperiment.ratioIntegerBound r := by simp [b, ratioSearch_eq]
    have bb : b ≤ S := by rw [beq]; exact limits y
    have currentField := field_nat current
    have bField := field_nat b
    have division : Bounded [.rational .div (E.channel true y) (E.channel false y)] 1 (64*S) := by
      constructor
      · rfl
      · intro op member
        have same : op = .rational .div (E.channel true y) (E.channel false y) := List.mem_singleton.mp member
        rw [same]
        simp only [Operation.width]
        have a := fields true y
        have b := fields false y
        omega
    have scan := ratioOps_bounded r 0 S positive (ratios y) (limits y) (Nat.zero_le _)
    have compare := naturalLE_bounded current b (4*S) (by omega) (by omega) (by omega)
    have head := bounded_append (bounded_append division scan)
      (bounded_mono compare (Nat.le_refl _) (by omega))
    have tail := ih (max current b) (max_le initial bb)
    unfold channelOpsAux
    change Bounded (_++_++_++channelOpsAux E ys (max current b)) _ _
    exact bounded_mono (bounded_append head tail) (by
      have product := Nat.mul_le_mul_right (S+8) (Nat.add_le_add_right (limits y) 1)
      simp only [Nat.sub_zero] at head ⊢
      simp only [List.length_cons]
      have lower : S ≤ S^2 := by nlinarith
      nlinarith) (Nat.le_refl _)

def sumStepOps (E : BinaryExperiment) (y : Fin E.alphabetSize) (k : Nat) : List Operation :=
  let difference := E.channel true y-E.channel false y
  [.rational .sub (E.channel true y) (E.channel false y), .rational .le 0 difference,
    .rational .sub 0 difference, .branch,
    .rational .add (RootB234.ChannelWidth.reversePrefixAbs E k) |difference|]

def sumAbsOps (E : BinaryExperiment) : List Operation :=
  (((List.finRange E.alphabetSize).reverse).zipIdx).flatMap (fun pair => sumStepOps E pair.1 pair.2)

theorem abs_field (q : Rat) : field |q| = field q := by
  by_cases positive : 0 ≤ q
  · rw [abs_of_nonneg positive]
  · rw [abs_of_neg (lt_of_not_ge positive)]
    simp only [field, RootB23.WordOddsBits.ratInput_fieldSize_eq, RootB23.WordOddsBits.width,
      Rat.neg_num, Int.natAbs_neg, Rat.neg_den]

theorem sumStepOps_bounded (E : BinaryExperiment) (S : Nat) (positive : 1 ≤ S)
    (fields : ∀ truth y, field (E.channel truth y) ≤ S)
    (prefixes : ∀ k, field (RootB234.ChannelWidth.reversePrefixAbs E k) ≤ S)
    (y : Fin E.alphabetSize) (k : Nat) : Bounded (sumStepOps E y k) 5 (64*S) := by
  have difference := field_sub (E.channel true y) (E.channel false y)
  have left := fields true y
  have right := fields false y
  have prefixBound := prefixes k
  have zero : field (0 : Rat) = 2 := rfl
  constructor
  · rfl
  · intro op member
    simp only [sumStepOps, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp only [Operation.width, zero, abs_field] <;> omega

theorem sumAbsOps_bounded (E : BinaryExperiment) (S : Nat) (positive : 1 ≤ S)
    (fields : ∀ truth y, field (E.channel truth y) ≤ S)
    (prefixes : ∀ k, field (RootB234.ChannelWidth.reversePrefixAbs E k) ≤ S) :
    Bounded (sumAbsOps E) (E.alphabetSize*5) (64*S) := by
  have all := bounded_flatMap (((List.finRange E.alphabetSize).reverse).zipIdx)
    (fun pair => sumStepOps E pair.1 pair.2) 5 (64*S)
      (fun pair _ => sumStepOps_bounded E S positive fields prefixes pair.1 pair.2)
  simpa only [sumAbsOps, List.length_zipIdx, List.length_reverse, List.length_finRange] using all

/-- The running state used in the cost annotations is the actual prefix
accumulator of the executable fold, not an additional input. -/
theorem sumAbs_prefix_state (E : BinaryExperiment) (k : Nat) :
    (((List.finRange E.alphabetSize).reverse).take k).foldl
      (fun total y => total+|E.channel true y-E.channel false y|) 0 =
        RootB234.ChannelWidth.reversePrefixAbs E k := by
  have fold (ys : List (Fin E.alphabetSize)) (total : Rat) :
      ys.foldl (fun a y => a+|E.channel true y-E.channel false y|) total =
        total+(ys.map (fun y => |E.channel true y-E.channel false y|)).sum := by
    induction ys generalizing total with
    | nil => simp
    | cons y ys ih => simp [ih, add_assoc]
  simp only [fold, zero_add, RootB234.ChannelWidth.reversePrefixAbs]

end RootPaper.Prep

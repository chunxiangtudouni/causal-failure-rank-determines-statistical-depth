module

public import Common.PSTR_SYM_OutputBits_001

/-! Source-only candidate: charge every occurrence in the ORIGINAL Expr tree
to the original encoded experiment. No DAG sharing or numerical KL/log
evaluation is used, and no Bool machine correctness is claimed. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.CompactPrice.PSTRSymbolicBits

open PaperProofs.Common.SymbolicPrice PaperProofs.Statistics
open RationalControllerComputation RationalControllerComputation.PSTRTMLength004
open RationalControllerComputation.PSTRTMArithmetic008

private theorem sum_affine {α : Type} (items : List α) (first second : α → Nat) :
    (items.map (fun x => 36 + 2 * first x + second x)).sum =
      36 * items.length + 2 * (items.map first).sum + (items.map second).sum := by
  induction items with
  | nil => simp
  | cons head later ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

theorem sum_map_ge_const {α : Type} (items : List α) (value : α → Nat) (bound : Nat)
    (hbound : ∀ x ∈ items, bound ≤ value x) :
    bound * items.length ≤ (items.map value).sum := by
  revert hbound
  induction items with
  | nil => intro _; simp
  | cons head later ih =>
    intro hbound
    have headBound := hbound head List.mem_cons_self
    have tailBound := ih (by intro x hx; exact hbound x (List.mem_cons_of_mem _ hx))
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.mul_add, Nat.mul_one]
    omega

def channelMass (experiment : BinaryExperiment) : Nat :=
  ((List.finRange experiment.alphabetSize).map (fun y => ratBits (experiment.channel false y))).sum +
    ((List.finRange experiment.alphabetSize).map (fun y => ratBits (experiment.channel true y))).sum

theorem channelMass_ge (experiment : BinaryExperiment) :
    16 * experiment.alphabetSize ≤ channelMass experiment := by
  have each (truth : Bool) := sum_map_ge_const (List.finRange experiment.alphabetSize)
    (fun y => ratBits (experiment.channel truth y)) 8 (by intro y _; exact ratBits_ge_eight _)
  have first := each false
  have second := each true
  simp only [List.length_finRange] at first second
  unfold channelMass
  omega

theorem rawExperiment_mass (experiment : BinaryExperiment) :
    datumMass (rawExperiment experiment) =
      datumBits (.natural experiment.alphabetSize) + ratBits experiment.priorOne +
        ratBits experiment.observationFee + channelMass experiment := by
  simp only [rawExperiment, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [datumMass_append, datumMass_cons]
  simp only [datumMass, List.map_map, Function.comp_def, List.map_nil,
    List.sum_nil, ratBits, channelMass]
  omega

theorem rawExperiment_mass_ge_four (experiment : BinaryExperiment) :
    4 ≤ datumMass (rawExperiment experiment) := by
  have header : 4 ≤ datumBits (.natural experiment.alphabetSize) := by
    simp only [datumBits, natBits]
    omega
  rw [rawExperiment_mass]
  omega

/-- The three rational leaves in EACH real channel term are all counted. -/
theorem divergence_bits (experiment : BinaryExperiment) (truth : Bool) :
    exprBits (divergenceExpr experiment truth) =
      12 + 36 * experiment.alphabetSize +
        2 * ((List.finRange experiment.alphabetSize).map (fun y => ratBits (experiment.channel truth y))).sum +
        ((List.finRange experiment.alphabetSize).map (fun y => ratBits (experiment.channel (!truth) y))).sum := by
  rw [divergenceExpr, exprBits_sumExpr, List.ofFn_eq_map, List.map_map]
  have pointwise :
      (fun y : Fin experiment.alphabetSize =>
        4 + exprBits (.multiply (.rational (experiment.channel truth y))
          (.log (.divide (.rational (experiment.channel truth y)) (.rational (experiment.channel (!truth) y)))))) =
      (fun y : Fin experiment.alphabetSize =>
        36 + 2 * ratBits (experiment.channel truth y) + ratBits (experiment.channel (!truth) y)) := by
    funext y
    simp only [exprBits_multiply, exprBits_rational, exprBits_log, exprBits_divide]
    omega
  simp only [Function.comp_def]
  rw [pointwise, sum_affine, List.length_finRange]
  omega

theorem localCoefficient_bits (experiment : BinaryExperiment) :
    exprBits (localCoefficientExpr experiment) =
      58 + 72 * experiment.alphabetSize + ratBits experiment.observationFee +
        ratBits (experiment.prior false) + ratBits (experiment.prior true) + 3 * channelMass experiment := by
  simp only [localCoefficientExpr, exprBits_multiply, exprBits_add, exprBits_divide,
    exprBits_rational, divergence_bits, Bool.not_false, Bool.not_true]
  unfold channelMass
  omega

/-- One serialized selected-stage summand costs at most sixteen times its
ORIGINAL raw experiment bits. The extra four bits are the real outer add. -/
theorem localCoefficient_bits_le_raw (experiment : BinaryExperiment) :
    4 + exprBits (localCoefficientExpr experiment) ≤ 16 * datumMass (rawExperiment experiment) := by
  have channels := channelMass_ge experiment
  have header : 4 ≤ datumBits (.natural experiment.alphabetSize) := by
    simp only [datumBits, natBits]
    omega
  have complement : ratBits (experiment.prior false) ≤ 2 * ratBits experiment.priorOne := by
    simpa [ratBits, BinaryExperiment.prior] using one_sub_datumBits_le experiment.priorOne
  have positivePrior : ratBits (experiment.prior true) = ratBits experiment.priorOne := by
    simp [BinaryExperiment.prior]
  rw [localCoefficient_bits, rawExperiment_mass, positivePrior]
  omega

end PaperProofs.Common.Native.CompactPrice.PSTRSymbolicBits

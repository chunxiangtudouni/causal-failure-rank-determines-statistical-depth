module

public import PaperProofs.Paid.MultiplierSearch
public import PaperProofs.Common.NativeBellmanExpectation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- The original independent initial coin chooses one whole original
policy. This is a genuine product-law identity for arbitrary nonnegative
charges, including infinity and failed/nonreturn paths. -/
theorem searchCoin_integral (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (state : MultiplierState)
    (f : P.SearchSeed × (P.input fee hfee).World → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ sample, f sample ∂(P.input fee hfee).seededWorldLaw (P.searchSeedLaw state)) =
      ENNReal.ofReal (P.stateWeight state).val *
        (∫⁻ sample, f ((true, sample.1), sample.2) ∂(P.input fee hfee).seededWorldLaw (menuSeedLaw P.certificate.stages P.tools)) +
      ENNReal.ofReal (1 - (P.stateWeight state).val) *
        (∫⁻ sample, f ((false, sample.1), sample.2) ∂(P.input fee hfee).seededWorldLaw (menuSeedLaw P.certificate.stages P.tools)) := by
  let input := P.input fee hfee
  let ν := menuSeedLaw P.certificate.stages P.tools
  let μ := input.worldLaw
  let coin := PaperProofs.Statistics.BinarySymmetric.Parameters.rocCoinLaw (P.stateWeight state)
  let g : P.SearchSeed → ℝ≥0∞ := fun seed => ∫⁻ world, f (seed, world) ∂μ
  have hg : Measurable g := hf.lintegral_prod_right'
  have ht : Measurable (fun sample : MenuSeed P.certificate.stages P.tools × input.World => f ((true, sample.1), sample.2)) :=
    hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hfalse : Measurable (fun sample : MenuSeed P.certificate.stages P.tools × input.World => f ((false, sample.1), sample.2)) :=
    hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hfirst : (∫⁻ sample, f sample ∂input.seededWorldLaw (P.searchSeedLaw state)) = ∫⁻ seed, g seed ∂coin.prod ν :=
    lintegral_prod f hf.aemeasurable
  rw [hfirst, lintegral_prod g hg.aemeasurable]
  have hchoice : Measurable (fun choice : Bool => ∫⁻ seed, g (choice, seed) ∂ν) :=
    measurable_of_countable _
  rw [show coin = ENNReal.ofReal (P.stateWeight state).val • Measure.dirac true +
      ENNReal.ofReal (1 - (P.stateWeight state).val) • Measure.dirac false from rfl,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac' _ hchoice, lintegral_dirac' _ hchoice]
  congr 1
  · exact congrArg (fun charge => ENNReal.ofReal (P.stateWeight state).val * charge) (lintegral_prod _ ht.aemeasurable).symm
  · exact congrArg (fun charge => ENNReal.ofReal (1 - (P.stateWeight state).val) * charge) (lintegral_prod _ hfalse.aemeasurable).symm

end PDMenu

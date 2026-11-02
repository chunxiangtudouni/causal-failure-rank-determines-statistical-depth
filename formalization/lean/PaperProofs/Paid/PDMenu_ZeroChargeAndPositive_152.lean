module

public import PaperProofs.Paid.PDMenu_ZeroChargeNative_148
public import PaperProofs.Paid.PDMenu_FirstPositivePathFloor_151

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

universe u

theorem zeroChargeOptimum (P : Parameters) : P.ZeroChargeOptimum.{u} := by
  intro fee hfee C accounting
  exact ⟨zeroCharge_runActualBill P fee hfee C accounting,
    zeroCharge_risk P fee hfee C accounting,
    PDROC.ZeroChargeLower.originalZeroChargePolicyLower P fee hfee C accounting,
    zeroCharge_native P fee hfee C accounting⟩

theorem positiveChargeLower (P : Parameters) : P.PositiveChargeLower.{u} := by
  intro fee hfee hgap
  refine ⟨PDROC.ZeroChargeLower.Transport.positiveValueFloor_pos P fee hfee hgap, ?_⟩
  intro C accounting mode Seed m
  let : MeasurableSpace Seed := m
  intro ν hν
  let : IsProbabilityMeasure ν := hν
  intro policy hrisk
  exact ⟨positiveChargeEvent_mass_lower P fee hfee C mode accounting ν policy hrisk,
    fun sample hsample => positiveChargeEvent_pathfloor P fee hfee C mode accounting policy sample hsample,
    PDROC.ZeroChargeLower.originalPositiveCostFloor P fee hfee hgap C accounting mode Seed m ν hν policy hrisk⟩

end PDMenu

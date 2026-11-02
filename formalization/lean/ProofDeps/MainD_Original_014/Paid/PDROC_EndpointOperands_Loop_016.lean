module

public import Paid.PDROC_EndpointOperands_Loop_012
public import Paid.PDROC_EndpointOperands_Loop_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

/-- All literal prefixes of the original115 row instructions preserve
the real header-plus-two-cache-cells region. Existing source values and
old destination/live cells are carried exactly; no future cache suffix
value, future liveness, or numerical cell bound is assumed. -/
theorem rowStraight_prefix_memory (P : Parameters) (m : ℕ) (input : List Cell)
    (before : State) (base E returnPC : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (invariant : EndpointValues P E returnPC m values) (separated : base + 48 ≤ E) :
    ∀ count ≤ rowStraightCode.length, ∀ state,
      linearExecute input (rowStraightCode.take count) before = some state →
        RegionMemory before state (endpointRowRegion base E m) := by
  let casted := Function.update values 18 (.rational (m : ℚ))
  let castState := castRowResult before base m
  let scalarValues := rowValues casted P.certificate.gamma P.reviewFee (powerRecurrence P.certificate.odds m) m
  let region := endpointRowRegion base E m
  have castRun := castRow_execute input before base m fresh (header.live 8 (by decide))
    ((header.value 8 (by decide)).trans invariant.counter)
  have castHeader : Header castState base casted := castRow_header before base m values header
  have castFresh : castState.register .fresh = .natural base := (castRow_fresh before base m).trans fresh
  have evaluated : headerEval rowCommands casted = some scalarValues :=
    row_eval P.certificate.gamma P.reviewFee (powerRecurrence P.certificate.odds m) m casted
      (by simp [casted, invariant.one]) (by simp [casted, invariant.two])
      (by simp [casted, invariant.power]) (by simp [casted, invariant.fee])
      (by simp [casted]) (by simp [casted, invariant.denominator])
      (error_den_ne_zero P m) (mean_den_ne_zero P)
  obtain ⟨scalar, scalarRun, scalarHeader, scalarFresh, _scalarPC, _frame, _output⟩ :=
    headerCode_realize rowCommands input castState base 0 0 casted scalarValues
      rowCommands_valid castHeader castFresh evaluated
  have castMemory : RegionMemory before castState region :=
    (HeaderMemory.write header 18 (by decide) (.rational (m : ℚ))
      (castRow_heap before base m) (castRow_live before base m) (castRow_output before base m)).region _ Finset.subset_union_left
  have scalarMemory : RegionMemory before scalar region := castMemory.trans
    ((headerCode_memory rowCommands input castState scalar base casted scalarValues rowCommands_valid
      castHeader castFresh evaluated scalarRun).region _ Finset.subset_union_left)
  have scalarE : scalarValues 0 = .natural E := by simp [scalarValues, rowValues, casted, invariant.cache]
  have scalarRow : scalarValues 8 = .natural m := by simp [scalarValues, rowValues, casted, invariant.counter]
  have scalarError : scalarValues 9 = .rational (P.endpointConstant m).error := by
    dsimp only [scalarValues]
    rw [rowValues_error, endpointFromPower_original]
  have scalarCharge : scalarValues 11 = .rational (P.endpointConstant m).charge := by
    dsimp only [scalarValues]
    rw [rowValues_charge, endpointFromPower_original]
  let pair := pairStoreResult scalar base E m (P.endpointConstant m).error (P.endpointConstant m).charge
  have zeroLive : base ∈ scalar.live := by simpa only [Nat.add_zero] using scalarHeader.live 0 (by decide)
  have zeroCell : scalar.heap base = .natural E := by
    simpa only [Nat.add_zero] using (scalarHeader.value 0 (by decide)).trans scalarE
  have pairRun := pairStore_execute input scalar base E m (P.endpointConstant m).error (P.endpointConstant m).charge
    scalarFresh zeroLive (scalarHeader.live 8 (by decide)) (scalarHeader.live 9 (by decide))
    (scalarHeader.live 11 (by decide)) zeroCell ((scalarHeader.value 8 (by decide)).trans scalarRow)
    ((scalarHeader.value 9 (by decide)).trans scalarError) ((scalarHeader.value 11 (by decide)).trans scalarCharge)
  have pairHeader : Header pair base scalarValues :=
    pairStore_header scalar base E m (P.endpointConstant m).error (P.endpointConstant m).charge scalarValues scalarHeader separated
  have pairFresh : pair.register .fresh = .natural base :=
    (pairStore_fresh scalar base E m (P.endpointConstant m).error (P.endpointConstant m).charge).trans scalarFresh
  have pairMemory : RegionMemory before pair region := scalarMemory.trans
    ((pairStore_prefix_region input scalar pair base E m (P.endpointConstant m).error (P.endpointConstant m).charge
      scalarValues scalarHeader scalarFresh scalarE scalarRow scalarError scalarCharge 20 (Nat.le_refl _) (by
        have full : pairStoreCode.take 20 = pairStoreCode := by rw [←pairStoreCode_length, List.take_length]
        simpa only [full] using pairRun)).enlarge Finset.subset_union_right)
  have castPrefixes : ∀ count ≤ castRowCode.length, ∀ state,
      linearExecute input (castRowCode.take count) before = some state → RegionMemory before state region := by
    intro count bound state actual
    exact (castRow_prefix_region input before state base m values header fresh invariant.counter count
      (by simpa only [castRowCode_length] using bound) actual).enlarge Finset.subset_union_left
  have scalarPrefixes : ∀ count ≤ (headerCode rowCommands).length, ∀ state,
      linearExecute input ((headerCode rowCommands).take count) castState = some state → RegionMemory before state region := by
    intro count bound state actual
    exact castMemory.trans ((headerCode_prefix_memory rowCommands input castState state base casted scalarValues
      rowCommands_valid castHeader castFresh evaluated count bound actual).region _ Finset.subset_union_left)
  have pairPrefixes : ∀ count ≤ pairStoreCode.length, ∀ state,
      linearExecute input (pairStoreCode.take count) scalar = some state → RegionMemory before state region := by
    intro count bound state actual
    exact scalarMemory.trans ((pairStore_prefix_region input scalar state base E m (P.endpointConstant m).error
      (P.endpointConstant m).charge scalarValues scalarHeader scalarFresh scalarE scalarRow scalarError scalarCharge
      count (by simpa only [pairStoreCode_length] using bound) actual).enlarge Finset.subset_union_right)
  have advancePrefixes : ∀ count ≤ advanceCode.length, ∀ state,
      linearExecute input (advanceCode.take count) pair = some state → RegionMemory before state region := by
    intro count bound state actual
    exact pairMemory.trans ((advance_prefix_memory P m input pair base scalarValues pairHeader pairFresh
      (by simp [scalarValues, rowValues, casted, invariant.power])
      (by simp [scalarValues, rowValues, casted, invariant.odds]) scalarRow count bound state actual).region _ Finset.subset_union_left)
  have tail := PDCompute.Pack.invariant_prefix_append input pairStoreCode advanceCode scalar pair pairRun
    (fun state => RegionMemory before state region) pairPrefixes advancePrefixes
  have suffix := PDCompute.Pack.invariant_prefix_append input (headerCode rowCommands) (pairStoreCode ++ advanceCode)
    castState scalar scalarRun (fun state => RegionMemory before state region) scalarPrefixes tail
  change ∀ count ≤ (castRowCode ++ (headerCode rowCommands ++ (pairStoreCode ++ advanceCode))).length, ∀ state,
    linearExecute input ((castRowCode ++ (headerCode rowCommands ++ (pairStoreCode ++ advanceCode))).take count)
      before = some state → RegionMemory before state region
  exact PDCompute.Pack.invariant_prefix_append input castRowCode (headerCode rowCommands ++ (pairStoreCode ++ advanceCode))
    before castState castRun (fun state => RegionMemory before state region) castPrefixes suffix

end PDROC.EndpointOperands.Loop

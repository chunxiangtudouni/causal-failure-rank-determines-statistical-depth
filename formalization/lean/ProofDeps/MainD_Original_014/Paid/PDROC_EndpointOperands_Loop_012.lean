module

public import Paid.PDROC_EndpointOperands_Loop_009
public import Paid.PDROC_EndpointOperands_Loop_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute linearExecute_append)

/-- Pure execution/semantic adapter for the original115 straight row
instructions. Existing cast/scalar/pair/advance results and original
endpoint identities are reused. No trace, cached answer, or alternative
functional endpoint implementation is selected or defined here. -/
theorem rowStraight_execute_spec (P : Parameters) (m : ℕ) (input : List Cell)
    (before : State) (base E returnPC : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (invariant : EndpointValues P E returnPC m values) (separated : base + 48 ≤ E) :
    ∃ after, linearExecute input rowStraightCode before = some after ∧
      after.pc = before.pc + 115 ∧ after.register .fresh = .natural base ∧
      Header after base (bodyValues P values m) ∧
      E + 1 + 2 * m ∈ after.live ∧ E + 2 + 2 * m ∈ after.live ∧
      after.heap (E + 1 + 2 * m) = .rational (P.endpointConstant m).error ∧
      after.heap (E + 2 + 2 * m) = .rational (P.endpointConstant m).charge ∧
      (∀ address, address < base ∨ base + 48 ≤ address →
        address ≠ E + 1 + 2 * m → address ≠ E + 2 + 2 * m → after.heap address = before.heap address) ∧
      after.live = insert (E + 2 + 2 * m) (insert (E + 1 + 2 * m) before.live) ∧
      after.output = before.output := by
  let casted := Function.update values 18 (.rational (m : ℚ))
  let castState := castRowResult before base m
  let scalarValues := rowValues casted P.certificate.gamma P.reviewFee (powerRecurrence P.certificate.odds m) m
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
  obtain ⟨scalar, scalarRun, scalarHeader, scalarFresh, scalarPC, _scalarFrame, _scalarOutput⟩ :=
    headerCode_realize rowCommands input castState base 0 0 casted scalarValues
      rowCommands_valid castHeader castFresh evaluated
  have castMemory : HeaderMemory before castState base :=
    HeaderMemory.write header 18 (by decide) (.rational (m : ℚ))
      (castRow_heap before base m) (castRow_live before base m) (castRow_output before base m)
  have scalarMemory := headerCode_memory rowCommands input castState scalar base casted scalarValues
    rowCommands_valid castHeader castFresh evaluated scalarRun
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
  have scalarPower : scalarValues 7 = .rational (powerRecurrence P.certificate.odds m) := by
    simp [scalarValues, rowValues, casted, invariant.power]
  have scalarOdds : scalarValues 6 = .rational P.certificate.odds := by
    simp [scalarValues, rowValues, casted, invariant.odds]
  obtain ⟨after, advanceRun, afterHeader, afterFresh, afterPC, advanceMemory⟩ :=
    advance_execute_spec P m input pair base scalarValues pairHeader pairFresh scalarPower scalarOdds scalarRow
  have cells := pairStore_cells scalar base E m (P.endpointConstant m).error (P.endpointConstant m).charge
  refine ⟨after, ?_, ?_, afterFresh, afterHeader, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change linearExecute input (castRowCode ++ (headerCode rowCommands ++ (pairStoreCode ++ advanceCode))) before = some after
    rw [linearExecute_append, castRun, Option.bind_some]
    change linearExecute input (headerCode rowCommands ++ (pairStoreCode ++ advanceCode)) castState = some after
    rw [linearExecute_append, scalarRun, Option.bind_some]
    rw [linearExecute_append, pairRun, Option.bind_some]
    exact advanceRun
  · rw [afterPC, pairStore_pc, scalarPC, castRow_pc]
    rfl
  · rw [advanceMemory.2.1]
    exact cells.1
  · rw [advanceMemory.2.1]
    exact cells.2.1
  · rw [advanceMemory.1 _ (Or.inr (by omega : base + 48 ≤ E + 1 + 2 * m))]
    exact cells.2.2.1
  · rw [advanceMemory.1 _ (Or.inr (by omega : base + 48 ≤ E + 2 + 2 * m))]
    exact cells.2.2.2
  · intro address outside notFirst notSecond
    rw [advanceMemory.1 address outside, pairStore_heap,
      Function.update_of_ne (by omega : address ≠ E + (m * 2 + 1) + 1),
      Function.update_of_ne (by omega : address ≠ E + (m * 2 + 1))]
    exact (scalarMemory.1 address outside).trans (castMemory.1 address outside)
  · rw [advanceMemory.2.1, pairStore_live, scalarMemory.2.1, castMemory.2.1]
    congr 1
    · omega
    · congr 1
      omega
  · exact advanceMemory.2.2.trans ((pairStore_output scalar base E m (P.endpointConstant m).error
      (P.endpointConstant m).charge).trans (scalarMemory.2.2.trans castMemory.2.2))

end PDROC.EndpointOperands.Loop

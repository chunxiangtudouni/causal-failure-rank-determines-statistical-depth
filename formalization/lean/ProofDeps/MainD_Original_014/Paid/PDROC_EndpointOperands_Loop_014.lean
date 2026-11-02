module

public import Paid.PDROC_EndpointOperands_Loop_002
public import Paid.PDROC_EndpointOperands_Loop_012
public import Paid.PDROC_EndpointOperands_Loop_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver RootD27.Bits
open PDROC.CalibrationRow.Operand

/-- Every prefix of the ORIGINAL115 straight row instructions has SAME
caller B. The original endpoint identities and finite evaluated rational
DAG are proved by the frozen semantic and concrete Scalar/Math modules;
there is no external row-trace or whole-loop numerical oracle. -/
theorem rowStraight_prefix_safe (input : List Cell) (P : Parameters)
    (origin base E returnPC m budget : ℕ) (before : State) (values : ℕ → Cell)
    (rowBound : m ≤ P.certificate.M) (header : Header before base values)
    (fresh : before.register .fresh = .natural base)
    (invariant : EndpointValues P E returnPC m values) (separated : base + 48 ≤ E)
    (safe : SafeBits before budget) (control : ControlBudget P origin base E returnPC budget)
    (rational : rationalBudget P ≤ budget) (position : before.pc + 115 ≤ pcCap origin returnPC) :
    PrefixSafe input rowStraightCode before budget := by
  let casted := Function.update values 18 (.rational (m : ℚ))
  let castState := castRowResult before base m
  let scalarValues := rowValues casted P.certificate.gamma P.reviewFee (powerRecurrence P.certificate.odds m) m
  have castRun := castRow_execute input before base m fresh (header.live 8 (by decide))
    ((header.value 8 (by decide)).trans invariant.counter)
  have castHeader : Header castState base casted := castRow_header before base m values header
  have castFresh : castState.register .fresh = .natural base := (castRow_fresh before base m).trans fresh
  have castSafe := castRow_prefix_safe input before base m budget values header fresh invariant.counter safe
    ((rationalBounds P m (by omega)).rowCast.trans rational)
    (ControlBudget.headerAddress P origin base E returnPC budget control)
    (ControlBudget.pc P origin base E returnPC budget (before.pc + 7) control (by omega))
  have evaluated : headerEval rowCommands casted = some scalarValues :=
    row_eval P.certificate.gamma P.reviewFee (powerRecurrence P.certificate.odds m) m casted
      (by simp [casted, invariant.one]) (by simp [casted, invariant.two])
      (by simp [casted, invariant.power]) (by simp [casted, invariant.fee])
      (by simp [casted]) (by simp [casted, invariant.denominator])
      (error_den_ne_zero P m) (mean_den_ne_zero P)
  obtain ⟨scalar, scalarRun, scalarHeader, scalarFresh, scalarPC, _frame, _output⟩ :=
    headerCode_realize rowCommands input castState base 0 0 casted scalarValues
      rowCommands_valid castHeader castFresh evaluated
  have scalarPC' : scalar.pc = before.pc + 77 := by
    rw [scalarPC, castRow_pc, rowScalarCode_length]
  have scalarSafe := row_scalar_prefix_safe input P origin base E returnPC m budget castState casted
    (by omega) castHeader castFresh (by simp [casted, invariant.one]) (by simp [casted, invariant.two])
    (by simp [casted, invariant.power]) (by simp [casted, invariant.fee]) (by simp [casted])
    (by simp [casted, invariant.denominator]) (castSafe.final castRun) control rational
    (by change (castRowResult before base m).pc + 70 ≤ pcCap origin returnPC; rw [castRow_pc]; omega)
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
  have pairSafe := pairStore_prefix_safe input scalar base E m budget scalarValues scalarHeader scalarFresh scalarE scalarRow
    (scalarSafe.final scalarRun)
    (fun n inside => ControlBudget.nat P origin base E returnPC budget n control (by unfold naturalCap; omega))
    (ControlBudget.headerAddress P origin base E returnPC budget control)
    (ControlBudget.pc P origin base E returnPC budget (scalar.pc + 20) control (by rw [scalarPC']; omega))
  have pairPC : pair.pc = before.pc + 97 := by
    rw [pairStore_pc, scalarPC']
  have advanceSafe := advance_prefix_safe input P origin base E returnPC m budget pair scalarValues (by omega)
    pairHeader pairFresh (by simp [scalarValues, rowValues, casted, invariant.power])
    (by simp [scalarValues, rowValues, casted, invariant.odds]) scalarRow (pairSafe.final pairRun) control rational
    (by rw [pairPC]; omega)
  have tail := PrefixSafe.append input pairStoreCode advanceCode scalar pair budget pairRun pairSafe advanceSafe
  have suffix := PrefixSafe.append input (headerCode rowCommands) (pairStoreCode ++ advanceCode)
    castState scalar budget scalarRun scalarSafe tail
  change PrefixSafe input (castRowCode ++ (headerCode rowCommands ++ (pairStoreCode ++ advanceCode))) before budget
  exact PrefixSafe.append input castRowCode (headerCode rowCommands ++ (pairStoreCode ++ advanceCode))
    before castState budget castRun castSafe suffix

end PDROC.EndpointOperands.Loop

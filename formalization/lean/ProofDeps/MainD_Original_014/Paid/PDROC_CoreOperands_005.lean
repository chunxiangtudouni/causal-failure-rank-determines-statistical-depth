module

public import Paid.PDROC_CoreOperands_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.CoreOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits PDROC.CalibrationRow.Operand

theorem solver_return_prefix_safe (input : List Cell) (before : State) (returnPC budget : ℕ)
    (safe : SafeBits before budget) (cacheBits : (Cell.natural 96).bits≤budget)
    (returnBits : (Cell.natural returnPC).bits≤budget) (pcBits : natBits (before.pc+2)≤budget) :
    PrefixSafe input [.constant .address (.natural 96),.constant .old (.natural returnPC)] before budget := by
  let first := ({before with pc:=before.pc+1}).set .address (.natural 96)
  let final := ({first with pc:=first.pc+1}).set .old (.natural returnPC)
  have firstSafe : SafeBits first budget :=
    (safe.withPC _ ((PDROC.DataBits.natBits_mono (by omega : before.pc+1≤before.pc+2)).trans pcBits)).set _ _ cacheBits
  have finalSafe : SafeBits final budget :=
    (firstSafe.withPC _ (by simpa only [first,State.set,Nat.add_assoc] using pcBits)).set _ _ returnBits
  apply PrefixSafe.cons input _ _ before first budget rfl safe
  apply PrefixSafe.cons input _ [] first final budget rfl firstSafe
  exact PrefixSafe.nil input final budget finalSafe

theorem solver_tail_prefix_safe (input : List Cell) (before : State) (useLambda : Bool)
    (returnPC budget : ℕ) (safe : SafeBits before budget) (live : 11∈before.live)
    (small : 4≤budget) (lambdaAddressBits : (Cell.natural 11).bits≤budget)
    (cacheBits : (Cell.natural 96).bits≤budget) (returnBits : (Cell.natural returnPC).bits≤budget)
    (pcBits : natBits (before.pc+4)≤budget) :
    PrefixSafe input (RootD27.Core.initialHeapPenaltyCode useLambda++
      [.constant .address (.natural 96),.constant .old (.natural returnPC)]) before budget := by
  cases useLambda with
  | false =>
      let first := ({before with pc:=before.pc+1}).set .total (.rational 0)
      have firstSafe : SafeBits first budget :=
        (safe.withPC _ ((PDROC.DataBits.natBits_mono (by omega : before.pc+1≤before.pc+4)).trans pcBits)).set _ _
          ((show (Cell.rational 0).bits≤4 by decide).trans small)
      have laterSafe := solver_return_prefix_safe input first returnPC budget firstSafe cacheBits returnBits
        (by simpa only [first,State.set,Nat.add_assoc] using
          ((PDROC.DataBits.natBits_mono (by omega : before.pc+3≤before.pc+4)).trans pcBits))
      exact PrefixSafe.cons input _ _ before first budget rfl safe laterSafe
  | true =>
      let first := directReadResult before 11 .total
      have firstRun := directRead_execute input before 11 .total live
      have firstSafe := directRead_prefix_safe input before 11 budget .total safe live lambdaAddressBits
        ((PDROC.DataBits.natBits_mono (by omega : before.pc+2≤before.pc+4)).trans pcBits)
      have laterSafe := solver_return_prefix_safe input first returnPC budget (firstSafe.final firstRun) cacheBits returnBits
        (by simpa only [first,directReadResult,State.set,Nat.add_assoc] using pcBits)
      exact PrefixSafe.append input (directReadCode 11 .total)
        [.constant .address (.natural 96),.constant .old (.natural returnPC)] before first budget firstRun firstSafe laterSafe

/-- All ORIGINAL fifteen/sixteen solver argument instructions have SAME
caller B at every literal prefix. N/K/fee/Lambda are live-heap reads;
99+2M is genuinely computed, and the original readonly input is arbitrary. -/
theorem solver_heap_arguments_prefix_safe (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (useLambda : Bool) (returnPC budget : ℕ)
    (safe : SafeBits before budget) (prepared : PDCompute.Solver.HeapList before 0 (preparedInput P fee))
    (small : 4≤budget) (baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤budget)
    (returnBits : (Cell.natural returnPC).bits≤budget) (pcBits : natBits (before.pc+16)≤budget) :
    PrefixSafe input (RootD27.Core.solverHeapArgumentsCode useLambda returnPC) before budget := by
  have live (slot : ℕ) (inside : slot<13) : slot∈before.live :=
    by simpa only [Nat.zero_add] using prepared.1 slot (by change slot<13; exact inside)
  have valueM := PDLower.CalibrationCompute.HeapList.value prepared 7 (by change 7<13; decide)
  change before.heap 7=.natural P.certificate.M at valueM
  let first := solverBaseResult before P.certificate.M
  let second := solverReadResult first
  have firstRun := solverBase_execute input before P.certificate.M (live 7 (by decide)) valueM
  have firstSafe := solver_base_prefix_safe input before P.certificate.M budget safe (live 7 (by decide)) valueM baseBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+6≤before.pc+16)).trans pcBits)
  have secondRun := solverReads_execute input first live
  have secondSafe := solverReads_prefix_safe input first budget (firstSafe.final firstRun) live small
    (by simpa only [first,solverBaseResult,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+12≤before.pc+16)).trans pcBits))
  have natural (n : ℕ) (bounded : n≤99+2*P.certificate.M) : (Cell.natural n).bits≤budget :=
    (Nat.add_le_add_left (PDROC.DataBits.natBits_mono bounded) 1).trans baseBits
  have tailSafe := solver_tail_prefix_safe input second useLambda returnPC budget (secondSafe.final secondRun)
    (live 11 (by decide)) small (natural 11 (by omega)) (natural 96 (by omega)) returnBits
    (by simpa only [second,first,solverReadResult,directReadResult,solverBaseResult,State.set,Nat.add_assoc] using pcBits)
  have suffix := PrefixSafe.append input (RootD27.Core.solverHeapArgumentPrefix.drop 6)
    (RootD27.Core.initialHeapPenaltyCode useLambda++[.constant .address (.natural 96),.constant .old (.natural returnPC)])
    first second budget secondRun secondSafe tailSafe
  change PrefixSafe input ((RootD27.Core.solverHeapArgumentPrefix.take 6)++
    ((RootD27.Core.solverHeapArgumentPrefix.drop 6)++
      (RootD27.Core.initialHeapPenaltyCode useLambda++[.constant .address (.natural 96),.constant .old (.natural returnPC)]))) before budget
  exact PrefixSafe.append input (RootD27.Core.solverHeapArgumentPrefix.take 6)
    ((RootD27.Core.solverHeapArgumentPrefix.drop 6)++
      (RootD27.Core.initialHeapPenaltyCode useLambda++[.constant .address (.natural 96),.constant .old (.natural returnPC)]))
    before first budget firstRun firstSafe suffix

end PDROC.CoreOperands

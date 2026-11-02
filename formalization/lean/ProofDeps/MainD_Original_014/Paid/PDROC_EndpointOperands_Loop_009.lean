module

public import Paid.PDROC_EndpointOperands_Loop_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver RootD27.Bits
open PDROC.CalibrationRow.Operand

/- Draft only until strict validation. These are exactly the original
twenty instructions; no new endpoint formula or functional state is used. -/

theorem pairStore_prefix_safe (input : List Cell) (before : State)
    (base E m budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (cache : values 0 = .natural E) (row : values 8 = .natural m)
    (safe : SafeBits before budget)
    (natural : ∀ n, n ≤ E + 2 * m + 2 → (Cell.natural n).bits ≤ budget)
    (addressBits : 1 + natBits (base + headerWords) ≤ budget)
    (pcBits : natBits (before.pc + 20) ≤ budget) :
    PrefixSafe input pairStoreCode before budget := by
  obtain ⟨loaded, run, firstSafe, _header, _fresh, index, total, position⟩ :=
    pairLoads_safe input before base E m budget values header fresh cache row safe addressBits
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 12 ≤ before.pc + 20)).trans pcBits)
  have tailSafe := pairTail_prefix_safe input loaded E m budget (firstSafe.final run) index total natural
    (by rw [position]; simpa only [Nat.add_assoc] using pcBits)
  change PrefixSafe input (pairLoadCode ++ pairTailCode) before budget
  exact PrefixSafe.append input pairLoadCode pairTailCode before loaded budget run firstSafe tailSafe

end PDROC.EndpointOperands.Loop

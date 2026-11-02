module

public import Paid.PDROC_EndpointOperands_Loop_009
public import Paid.PDROC_EndpointOperands_Base_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver RootD27.Bits

/- Draft numeric instantiations. The fixed Base budget only governs new
assigned naturals/addresses/PC; old registers and cells keep caller B. -/

theorem test_phase_safe (program : Program) (input : List Cell) (P : Parameters)
    (origin base E returnPC m budget : ℕ) (values : ℕ → Cell) (before state : State)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (row : values 8 = .natural m) (stop : values 3 = .natural P.certificate.M)
    (position : before.pc = origin + 105) (safe : SafeBits before budget)
    (bounds : ControlBudget P origin base E returnPC budget)
    (actual : ControlledPrefix program input rowCompareCode before
      (if m ≤ P.certificate.M then origin + 113 else origin + 229) state) :
    SafeBits state budget := by
  have zero := ControlBudget.nat P origin base E returnPC budget 0 bounds (by unfold naturalCap; omega)
  have one := ControlBudget.nat P origin base E returnPC budget 1 bounds (by unfold naturalCap; omega)
  have pc := ControlBudget.pc P origin base E returnPC budget (before.pc + 7) bounds
    (by rw [position]; unfold pcCap; omega)
  have literal := rowCompare_prefix_safe input before base m P.certificate.M budget values
    header fresh row stop safe zero one (ControlBudget.headerAddress P origin base E returnPC budget bounds) pc
  apply ControlledPrefix.safe program input rowCompareCode before state _ budget literal _ actual
  apply ControlBudget.pc P origin base E returnPC budget _ bounds
  unfold pcCap
  split_ifs <;> omega

theorem restore_phase_safe (program : Program) (input : List Cell) (P : Parameters)
    (origin base E returnPC budget : ℕ) (values : ℕ → Cell) (before state : State)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (stop : values 3 = .natural P.certificate.M) (position : before.pc = origin + 229)
    (safe : SafeBits before budget) (bounds : ControlBudget P origin base E returnPC budget)
    (actual : ControlledPrefix program input returnPrefixCode before returnPC state) :
    SafeBits state budget := by
  have natural (n : ℕ) (inside : n ≤ 2 * P.certificate.M + 3) : (Cell.natural n).bits ≤ budget :=
    ControlBudget.nat P origin base E returnPC budget n bounds (by unfold naturalCap; omega)
  have pc := ControlBudget.pc P origin base E returnPC budget (before.pc + 13) bounds
    (by rw [position]; unfold pcCap; omega)
  have literal := returnPrefix_prefix_safe input before base P.certificate.M budget values header fresh stop safe natural
    (ControlBudget.headerAddress P origin base E returnPC budget bounds) pc
  exact ControlledPrefix.safe program input returnPrefixCode before state returnPC budget literal
    (ControlBudget.pc P origin base E returnPC budget returnPC bounds (by unfold pcCap; omega)) actual

end PDROC.EndpointOperands.Loop

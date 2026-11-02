module

public import Paid.PDROC_CalibrationRow_ScatterOperands_006
public import Paid.PDROC_CalibrationRow_ScatterOperands_013
public import Paid.PDROC_CalibrationRow_ScatterOperands_016
public import Paid.PDROC_CalibrationRow_ScatterOperands_017
public import Paid.PDROC_CalibrationRow_ScatterOperands_018
public import Paid.PDROC_CalibrationRow_OperandPrefix_003
public import Paid.PDROC_CalibrationRow_OperandPrefix_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame RootD27.Bits

/-- Every original scatter label preserves one caller budget. The
catalogue covers only actual new assignments; arbitrary old scratch
cells enter solely through the actual caller's SafeBits invariant. -/
theorem entry_prefix_safe (input : List Cell) (P : Parameters)
    (origin base level clock cursor read write budget : ℕ) (label : Label) (before : State)
    (entry : ScatterEntry P base level clock cursor read write before label)
    (position : before.pc = labelAddress origin label) (levelBound : level ≤ P.certificate.M + 1)
    (caller : SafeBits before budget)
    (assigned : ∀ value, Catalog P base level clock value → value.bits ≤ budget)
    (pc : ∀ next, natBits (labelAddress origin next + 32) ≤ budget) :
    Operand.PrefixSafe input (basicBlock label).body before budget := by
  have counter (length : ℕ) (bound : length ≤ 32) : natBits (before.pc + length) ≤ budget := by
    apply (PDROC.DataBits.natBits_mono ?_).trans (pc label)
    rw [position]
    omega
  have address (offset : ℕ) (inside : offset ≤ 16) : (Cell.natural (base + offset)).bits ≤ budget :=
    assigned _ (header_address_catalog P base level clock offset inside)
  have zero : (Cell.natural 0).bits ≤ budget := assigned _ (offset_catalog P base level clock 0 (by decide))
  have one : (Cell.natural 1).bits ≤ budget := assigned _ (offset_catalog P base level clock 1 (by decide))
  cases entry with
  | gate data bound =>
      rw [scatterGate_body]
      exact Operand.gate_prefix_safe input before base 7 8 cursor (2 * level + 1) budget caller
        data.control.header.fresh (data.control.header.live 7 (by decide)) (data.control.header.live 8 (by decide))
        data.control.cursorValue data.control.width (address 7 (by decide)) (address 8 (by decide))
        zero one (counter 7 (by decide))
  | leftRead data inside index =>
      apply prefixSafe_of_sources input (basicBlock .leftRead).body before (Catalog P base level clock) budget
        (basicBlock_straight _) ?_ caller assigned (counter _ (by decide))
      intro n bound after run
      exact leftRead_prefix_catalog input P base level clock cursor read write n before after data inside levelBound index bound run
  | leftInterior data inside _ index _ =>
      apply prefixSafe_of_sources input (basicBlock .leftInterior).body before (Catalog P base level clock) budget
        (basicBlock_straight _) ?_ caller assigned (counter _ (by decide))
      intro n bound after run
      exact interior_prefix_catalog input P base level clock cursor n false before after index inside levelBound bound run
  | leftStore data inside index value =>
      apply prefixSafe_of_sources input (basicBlock .leftStore).body before (Catalog P base level clock) budget
        (basicBlock_straight _) ?_ caller assigned (counter _ (by decide))
      intro n bound after run
      exact leftStore_prefix_catalog input P base level clock cursor read write n before after data inside levelBound index value bound run
  | rightRead inside data =>
      apply prefixSafe_of_sources input (basicBlock .rightRead).body before (Catalog P base level clock) budget
        (basicBlock_straight _) ?_ caller assigned (counter _ (by decide))
      intro n bound after run
      exact rightRead_prefix_catalog input P base level clock cursor read write n inside before after data levelBound bound run
  | rightInterior inside data _ index _ =>
      apply prefixSafe_of_sources input (basicBlock .rightInterior).body before (Catalog P base level clock) budget
        (basicBlock_straight _) ?_ caller assigned (counter _ (by decide))
      intro n bound after run
      exact interior_prefix_catalog input P base level clock cursor n true before after index inside levelBound bound run
  | rightStore inside data index value =>
      apply prefixSafe_of_sources input (basicBlock .rightStore).body before (Catalog P base level clock) budget
        (basicBlock_straight _) ?_ caller assigned (counter _ (by decide))
      intro n bound after run
      exact rightStore_prefix_catalog input P base level clock cursor read write n inside before after data levelBound index value bound run
  | next data inside =>
      have successor : Catalog P base level clock (.natural (cursor + 1)) := by
        apply small_natural_catalog
        have width := activeWidth_le P.certificate.M level levelBound
        omega
      rw [scatterNext_body]
      exact Operand.increment_prefix_safe input before base 7 cursor budget caller data.control.header.fresh
        (data.control.header.live 7 (by decide)) data.control.cursorValue (address 7 (by decide)) one
        (assigned _ successor) (counter 8 (by decide))

end PDROC.CalibrationRow.ScatterOperands

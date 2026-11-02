module

public import Paid.PDROC_CalibrationRow_053
public import Paid.PDROC_CalibrationRow_029
public import Paid.PDROC_CalibrationRow_OperandPrefix_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- A fixed NEW natural-value envelope for the original row controls.
It is additive in M and Q; its bit length introduces no M*Q factor.
Arbitrary old caller cells remain governed by the caller's same B. -/
def controlNaturalCap (P : Parameters) (base : ℕ) : ℕ :=
  firstRow base+2*rowWidth P.certificate.M+P.certificate.Q+1

structure ControlBudget (P : Parameters) (origin base budget : ℕ) : Prop where
  small : 4≤budget
  naturalBits : 1+natBits (controlNaturalCap P base)≤budget
  pcBits : ∀ target,natBits (labelAddress origin target+32)≤budget

theorem controlNaturalCap_lower (P : Parameters) (base : ℕ) :
    base+16≤controlNaturalCap P base ∧ rowWidth P.certificate.M≤controlNaturalCap P base ∧
      P.certificate.Q+1≤controlNaturalCap P base := by
  unfold controlNaturalCap firstRow rowWidth
  omega

theorem ControlBudget.address (P : Parameters) (origin base budget address : ℕ)
    (bounds : ControlBudget P origin base budget) (inside : address≤controlNaturalCap P base) :
    1+natBits address≤budget :=
  (Nat.add_le_add_left (PDROC.DataBits.natBits_mono inside) 1).trans bounds.naturalBits

theorem ControlBudget.nat (P : Parameters) (origin base budget value : ℕ)
    (bounds : ControlBudget P origin base budget) (inside : value≤controlNaturalCap P base) :
    (Cell.natural value).bits≤budget := by
  change 1+natBits value≤budget
  exact ControlBudget.address P origin base budget value bounds inside

theorem ControlBudget.literal (P : Parameters) (origin base budget value : ℕ)
    (bounds : ControlBudget P origin base budget) (inside : value≤16) :
    (Cell.natural value).bits≤budget :=
  ControlBudget.nat P origin base budget value bounds (by have lower := (controlNaturalCap_lower P base).1; omega)

theorem ControlBudget.slot (P : Parameters) (origin base budget offset : ℕ)
    (bounds : ControlBudget P origin base budget) (inside : offset≤16) :
    1+natBits (base+offset)≤budget :=
  ControlBudget.address P origin base budget (base+offset) bounds
    ((Nat.add_le_add_left inside base).trans (controlNaturalCap_lower P base).1)

theorem ControlBudget.counter (P : Parameters) (origin base budget counter : ℕ)
    (bounds : ControlBudget P origin base budget) (inside : counter≤P.certificate.Q+1) :
    (Cell.natural counter).bits≤budget :=
  ControlBudget.nat P origin base budget counter bounds (inside.trans (controlNaturalCap_lower P base).2.2)

theorem ControlBudget.rowAddress (P : Parameters) (origin base budget read write cursor : ℕ)
    (bounds : ControlBudget P origin base budget) (buffers : Buffers base P.certificate.M read write)
    (inside : cursor≤rowWidth P.certificate.M) :
    1+natBits (read+cursor)≤budget ∧ 1+natBits (write+cursor)≤budget := by
  have lowerRead : read+cursor≤controlNaturalCap P base := by
    rcases buffers with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp only [controlNaturalCap,firstRow,secondRow,rowWidth] at * <;> omega
  have lowerWrite : write+cursor≤controlNaturalCap P base := by
    rcases buffers with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp only [controlNaturalCap,firstRow,secondRow,rowWidth] at * <;> omega
  exact ⟨ControlBudget.address P origin base budget _ bounds lowerRead,ControlBudget.address P origin base budget _ bounds lowerWrite⟩

theorem ControlBudget.pc_prefix (P : Parameters) (origin base budget : ℕ)
    (bounds : ControlBudget P origin base budget) (before : State) (label : Label) (count : ℕ)
    (position : before.pc=labelAddress origin label) (inside : count≤32) :
    natBits (before.pc+count)≤budget := by
  rw [position]
  exact (PDROC.DataBits.natBits_mono (Nat.add_le_add_left inside _)).trans (bounds.pcBits label)

theorem ControlBudget.pc_target (P : Parameters) (origin base budget : ℕ)
    (bounds : ControlBudget P origin base budget) (label : Label) :
    natBits (labelAddress origin label)≤budget :=
  (PDROC.DataBits.natBits_mono (by omega : labelAddress origin label≤labelAddress origin label+32)).trans
    (bounds.pcBits label)

end PDROC.CalibrationRow.Operand

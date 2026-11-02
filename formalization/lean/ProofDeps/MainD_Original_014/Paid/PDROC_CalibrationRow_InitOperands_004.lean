module

public import Paid.PDROC_CalibrationRow_InitOperands_001
public import Paid.PDROC_CalibrationRow_InitOperands_003
public import Paid.PDROC_CalibrationRow_OperandPrefix_003
public import Paid.PDROC_CalibrationRow_Init_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

theorem init_slot_bits (base M slot budget : ℕ) (inside : slot < 16)
    (addressBits : 1+natBits (firstRow base+rowWidth M) ≤ budget) :
    1+natBits (base+slot) ≤ budget := by
  apply (Nat.add_le_add_left (PDROC.DataBits.natBits_mono ?_) 1).trans addressBits
  unfold firstRow rowWidth
  omega

theorem init_target_bits (P : Parameters) (base level cursor budget : ℕ)
    (inside : cursor < 2*level+1) (levelBound : level ≤ P.certificate.M+1)
    (addressBits : 1+natBits (firstRow base+rowWidth P.certificate.M) ≤ budget) :
    (Cell.natural (firstRow base+cursor)).bits ≤ budget := by
  change 1+natBits (firstRow base+cursor) ≤ budget
  apply (Nat.add_le_add_left (PDROC.DataBits.natBits_mono ?_) 1).trans addressBits
  have width := activeWidth_le P.certificate.M level levelBound
  omega

theorem init_pc_bits (origin : ℕ) (before : State) (label : Label) (count budget : ℕ)
    (position : before.pc=labelAddress origin label) (bound : count ≤ 15)
    (pcBits : ∀ target,natBits (labelAddress origin target+15) ≤ budget) :
    natBits (before.pc+count) ≤ budget := by
  rw [position]
  exact (PDROC.DataBits.natBits_mono (by omega : labelAddress origin label+count ≤ labelAddress origin label+15)).trans (pcBits label)

/-- The genuine live header8 width bounds the successor in the SAME caller
budget; there is no budget multiplication by the number of loop rounds. -/
theorem init_successor_bits (P : Parameters) (base level cursor budget : ℕ) (before : State)
    (data : InitData P base level cursor before) (safe : SafeBits before budget)
    (inside : cursor < 2*level+1) : (Cell.natural (cursor+1)).bits ≤ budget := by
  have widthBits := safe.heap (base+8) (data.header.live 8 (by decide))
  rw [data.width] at widthBits
  change 1+natBits (2*level+1) ≤ budget at widthBits
  change 1+natBits (cursor+1) ≤ budget
  exact (Nat.add_le_add_left (PDROC.DataBits.natBits_mono (by omega : cursor+1 ≤ 2*level+1)) 1).trans widthBits

/-- Every real init block prefix retains its actual caller B. Only fixed
new constants, concrete addresses and actual PCs use the supplied bounds;
all untouched registers, live values and Header6 retain caller provenance. -/
theorem init_body_prefix_safe (input : List Cell) (P : Parameters) (origin base level cursor budget : ℕ)
    (label : Label) (before : State) (data : InitData P base level cursor before)
    (entry : InitLabelEntry level cursor label before) (position : before.pc=labelAddress origin label)
    (safe : SafeBits before budget) (small : 4 ≤ budget)
    (addressBits : 1+natBits (firstRow base+rowWidth P.certificate.M) ≤ budget)
    (pcBits : ∀ target,natBits (labelAddress origin target+15) ≤ budget)
    (levelBound : level ≤ P.certificate.M+1) :
    PrefixSafe input (basicBlock label).body before budget := by
  have zeroNat : (Cell.natural 0).bits ≤ budget := (show (Cell.natural 0).bits ≤ 4 by decide).trans small
  have oneNat : (Cell.natural 1).bits ≤ budget := (show (Cell.natural 1).bits ≤ 4 by decide).trans small
  have zeroRat : (Cell.rational 0).bits ≤ budget := (show (Cell.rational 0).bits ≤ 4 by decide).trans small
  have oneRat : (Cell.rational 1).bits ≤ budget := (show (Cell.rational 1).bits ≤ 4 by decide).trans small
  rcases entry with gate | ⟨inside,index,cell | ⟨center,_⟩ | ⟨store,_⟩⟩
  · subst label
    simpa only [initGate_body] using
      gate_prefix_safe input before base 7 8 cursor (2*level+1) budget safe data.header.fresh
        (data.header.live 7 (by decide)) (data.header.live 8 (by decide)) data.cursorValue data.width
        (init_slot_bits base P.certificate.M 7 budget (by decide) addressBits)
        (init_slot_bits base P.certificate.M 8 budget (by decide) addressBits) zeroNat oneNat
        (init_pc_bits origin before .initGate 7 budget position (by decide) pcBits)
  · subst label
    exact initCell_prefix_safe input before base level cursor budget safe data.header.fresh
      (data.header.live 5 (by decide)) data.header.level index
      (init_slot_bits base P.certificate.M 5 budget (by decide) addressBits) zeroNat oneNat zeroRat
      (init_pc_bits origin before .initCell 5 budget position (by decide) pcBits)
  · subst label
    exact initCenter_prefix_safe input before budget safe oneRat
      (init_pc_bits origin before .initCenter 1 budget position (by decide) pcBits)
  · subst label
    exact initStore_prefix_safe input before base cursor budget safe data.header.fresh
      (data.header.live 9 (by decide)) data.read (data.header.live 7 (by decide)) data.cursorValue index
      (init_slot_bits base P.certificate.M 9 budget (by decide) addressBits)
      (init_slot_bits base P.certificate.M 7 budget (by decide) addressBits)
      (init_target_bits P base level cursor budget inside levelBound addressBits) oneNat
      (init_successor_bits P base level cursor budget before data safe inside)
      (init_pc_bits origin before .initStore 13 budget position (by decide) pcBits)

end PDROC.CalibrationRow.Operand

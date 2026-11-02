module

public import Paid.PDROC_CalibrationRow_InitOperands_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits PDMenu.ComputeFrame

theorem init_safeBits_closed (input : List Cell) (P : Parameters) (origin base level budget : ℕ)
    (small : 4 ≤ budget)
    (addressBits : 1+natBits (firstRow base+rowWidth P.certificate.M) ≤ budget)
    (pcBits : ∀ target,natBits (labelAddress origin target+15) ≤ budget)
    (levelBound : level ≤ P.certificate.M+1) :
    InitClosed P origin base level input (fun state => SafeBits state budget) := by
  intro cursor label before middle after data _bound entry safe position body control state location
  have prefixes := init_body_prefix_safe input P origin base level cursor budget label before data entry
    position safe small addressBits pcBits levelBound
  rcases location with ⟨count,_,run⟩ | equal
  · exact prefixes count state run
  · subst state
    exact control_safe origin (basicBlock label).control input middle after budget (prefixes.final body)
      (fun target => (PDROC.DataBits.natBits_mono (by omega : labelAddress origin target ≤ labelAddress origin target+15)).trans (pcBits target)) control

/-- Converts EACH state on an already existing canonical initialization
trace, using its own constructor's real data/body/control/literal prefix.
No new existential execution trace needs to be aligned with the caller. -/
theorem initProvenance_safe (input : List Cell) (P : Parameters) (origin base level budget : ℕ)
    (caller state : State) (callerSafe : SafeBits caller budget) (small : 4 ≤ budget)
    (addressBits : 1+natBits (firstRow base+rowWidth P.certificate.M) ≤ budget)
    (pcBits : ∀ target,natBits (labelAddress origin target+15) ≤ budget)
    (levelBound : level ≤ P.certificate.M+1)
    (provenance : InitProvenance P origin base level input caller state) : SafeBits state budget := by
  induction provenance with
  | initial => exact callerSafe
  | block cursor label before middle after state previous data bound entry position body control prefixRun ih =>
    exact init_safeBits_closed input P origin base level budget small addressBits pcBits levelBound
      cursor label before middle after data bound entry ih position body control state prefixRun

/-- Both facts are discharged for the SAME actual body/control/prefix
state. The original loop builder therefore produces one trace carrying
canonical provenance AND the unchanged numerical caller budget. -/
theorem init_joint_closed (input : List Cell) (P : Parameters) (origin base level budget : ℕ)
    (caller : State) (small : 4 ≤ budget)
    (addressBits : 1+natBits (firstRow base+rowWidth P.certificate.M) ≤ budget)
    (pcBits : ∀ target,natBits (labelAddress origin target+15) ≤ budget)
    (levelBound : level ≤ P.certificate.M+1) :
    InitClosed P origin base level input
      (fun state => InitProvenance P origin base level input caller state ∧ SafeBits state budget) := by
  intro cursor label before middle after data bound entry good position body control state location
  exact ⟨initProvenance_closed P origin base level input caller cursor label before middle after
      data bound entry good.1 position body control state location,
    init_safeBits_closed input P origin base level budget small addressBits pcBits levelBound
      cursor label before middle after data bound entry good.2 position body control state location⟩

/-- One genuine fetched trace, canonical InitProvenance and all ORIGINAL
stateCellBits at most the caller's SAME B. No supplied Good/closure, no
second existential trace, no incoming clock type or P-only scratch bound. -/
theorem init_complete_provenance_safeBits (P : Parameters) (origin base level : ℕ)
    (input : List Cell) (before : State) (header : PDROC.CalibrationRow.Header P base level before)
    (position : before.pc=labelAddress origin .initGate)
    (cursor : before.heap (base+7)=.natural 0)
    (width : before.heap (base+8)=.natural (2*level+1))
    (read : before.heap (base+9)=.natural (firstRow base))
    (write : before.heap (base+10)=.natural (secondRow base P.certificate.M))
    (levelBound : level ≤ P.certificate.M+1) (budget : ℕ) (safe : SafeBits before budget)
    (small : 4 ≤ budget)
    (addressBits : 1+natBits (firstRow base+rowWidth P.certificate.M) ≤ budget)
    (pcBits : ∀ target,natBits (labelAddress origin target+15) ≤ budget) :
    ∃ after : State,SafeSegment origin base (region base P.certificate.M) input
      (fun state => InitProvenance P origin base level input before state ∧ SafeBits state budget)
      before after (1600*(level+1)) ∧ after.pc=labelAddress origin .stepStart ∧
      PDROC.CalibrationRow.Header P base level after ∧
      after.heap (base+7)=.natural (2*level+1) ∧ after.heap (base+8)=.natural (2*level+1) ∧
      after.heap (base+9)=.natural (firstRow base) ∧
      after.heap (base+10)=.natural (secondRow base P.certificate.M) ∧
      RowAt after (firstRow base) (P.walkRow level true 0) :=
  init_complete_safe P origin base level input
    (fun state => InitProvenance P origin base level input before state ∧ SafeBits state budget)
    (init_joint_closed input P origin base level budget before small addressBits pcBits levelBound)
    before header ⟨.initial,safe⟩ position cursor width read write levelBound

end PDROC.CalibrationRow.Operand

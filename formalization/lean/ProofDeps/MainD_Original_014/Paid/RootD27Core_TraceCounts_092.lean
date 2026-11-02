module

public import Paid.RootD27Core_OriginalLoop_089

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame

/-- Arbitrary physical phase labels, including endpoint/calibration;
the original counter is not replaced by a different log convention. -/
theorem entryCount_append_pc (entry : ℕ) (first later : List State) :
    entryCount entry (first++later)=entryCount entry first+entryCount entry later := by
  simp only [entryCount,List.filter_append,List.length_append]

theorem entryCount_zero_of_excluded (entry : ℕ) (trace : List State)
    (excluded : ∀ state∈trace,state.pc≠entry) : entryCount entry trace=0 := by
  have empty : trace.filter (fun state=>state.pc==entry)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro state member
    simpa only [beq_iff_eq] using excluded state member
  simp only [entryCount,empty,List.length_nil]

theorem entryCount_zero_of_lower (entry floor : ℕ) (trace : List State)
    (earlier : entry<floor) (lower : ∀ state∈trace,floor≤state.pc) : entryCount entry trace=0 := by
  apply entryCount_zero_of_excluded
  intro state member
  have bound:=lower state member
  omega

/-- Joining removes the first trace's boundary exactly once. It changes
no phase counter when that SAME actual boundary is not the phase entry. -/
theorem entryCount_dropLast_ne (entry : ℕ) (trace : List State) (middle : State)
    (last : trace.getLast?=some middle) (outside : middle.pc≠entry) :
    entryCount entry trace.dropLast=entryCount entry trace := by
  have split:=List.dropLast_append_getLast? middle (by rw [last];simp)
  have whole : entryCount entry trace=entryCount entry trace.dropLast+entryCount entry [middle] := by
    conv_lhs=>rw [←split]
    exact entryCount_append_pc entry _ _
  have single : entryCount entry [middle]=0 :=
    entryCount_zero_of_excluded entry [middle] (by
      intro state member
      have same:=List.mem_singleton.mp member
      subst state
      exact outside)
  rw [single,Nat.add_zero] at whole
  exact whole.symm

theorem entryCount_join_ne (entry : ℕ) (first later : List State) (middle : State)
    (last : first.getLast?=some middle) (outside : middle.pc≠entry) :
    entryCount entry (joinTrace first later)=entryCount entry first+entryCount entry later := by
  change entryCount entry (first.dropLast++later)=_
  rw [entryCount_append_pc,entryCount_dropLast_ne entry first middle last outside]

/-- A once-only original phase remains once-only after the later real
main run, whose every PC is provably above that earlier phase label. -/
theorem entryCount_one_join_lower (entry floor : ℕ) (first later : List State) (middle : State)
    (last : first.getLast?=some middle) (middleLower : floor≤middle.pc)
    (earlier : entry<floor) (firstCount : entryCount entry first=1)
    (laterLower : ∀ state∈later,floor≤state.pc) :
    entryCount entry (joinTrace first later)=1 := by
  rw [entryCount_join_ne entry first later middle last (by omega),firstCount,
    entryCount_zero_of_lower entry floor later earlier laterLower,Nat.add_zero]

end RootD27.Core

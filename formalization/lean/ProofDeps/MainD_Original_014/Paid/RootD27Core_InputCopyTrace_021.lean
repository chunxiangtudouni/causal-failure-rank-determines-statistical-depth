module

public import Paid.RootD27Core_InputCopyResult_020

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

theorem inputCopy_budget_succ (count : ℕ) : 60*count+15+60=60*(count+1)+15 := by omega

/-- Genuine ROM-to-live-heap copying from arbitrary caller memory.
No preallocated Header or successful-copy premise is assumed. Every
physical prefix has only the actual count-cell write region. -/
theorem inputCopy_actual (program : Program) (input : List Cell) (before : State) :
    ∀ count : ℕ, count ≤ input.length →
      FetchesCode program before.pc (inputCopyCode count) →
      ∃ trace : List State,
        trace.head?=some before ∧ trace.getLast?=some (inputCopyResult input before count) ∧
        trace.IsChain (fun first later => step program input first=some later) ∧
        time program trace≤60*count+15 ∧
        ∀ state∈trace,RegionMemory before state (Finset.range count) := by
  intro count
  induction count with
  | zero =>
    intro _ _
    refine ⟨[before],rfl,rfl,.singleton before,time_singleton_le program before,?_⟩
    intro state member
    have same : state=before:=List.mem_singleton.mp member
    subst state
    exact RegionMemory.refl before (Finset.range 0)
  | succ count ih =>
    intro bounded fetched
    have firstFetch : FetchesCode program before.pc (inputCopyCode count) := fetched.append_left
    obtain ⟨first,fh,fl,fc,ft,firstMemory⟩:=ih (by omega) firstFetch
    let middle:=inputCopyResult input before count
    have nextFetch : FetchesCode program middle.pc (inputSlotCode count) := by
      simpa only [middle,inputCopy_pc,inputCopy_length] using fetched.append_right
    have inside : count < input.length := by omega
    have payload : input[count]?=some ((input[count]?).getD (.natural 0)) := by
      simp only [List.getElem?_eq_getElem inside,Option.getD_some]
    obtain ⟨later,lh,ll,lc,lt,laterMemory⟩:=
      inputSlot_actual_region program input middle count ((input[count]?).getD (.natural 0)) payload nextFetch
    have joined:=joinTrace_spec program input first later before middle
      (inputCopyResult input before (count+1)) (60*count+15) 60 fh fl lh ll fc lc ft lt
    refine ⟨joinTrace first later,joined.1,joined.2.1,joined.2.2.1,
      joined.2.2.2.trans_eq (inputCopy_budget_succ count),?_⟩
    have oldRegion : Finset.range count⊆Finset.range (count+1) := by
      intro address member
      exact Finset.mem_range.mpr (by have prior:=Finset.mem_range.mp member;omega)
    have newRegion : ({count} : Finset ℕ)⊆Finset.range (count+1) := by
      intro address member
      have same : address=count:=Finset.mem_singleton.mp member
      subst address
      simp
    exact RegionMemory.join_trace first later before middle _ fl
      (fun state member => (firstMemory state member).enlarge oldRegion)
      (fun state member => (laterMemory state member).enlarge newRegion)

theorem inputCopy_workingCells (before after : State) (count : ℕ)
    (memory : RegionMemory before after (Finset.range count)) :
    workingCells after≤workingCells before+count := by
  simpa only [Finset.card_range] using memory.workingCells_le

end RootD27.Core

module

public import Paid.RootD27Core_SelectedPost_074

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch

/-- One real fetched control instruction, not a free PC relabelling.
The old heap/live/output and fixed bit budget survive on the SAME two
states. Both actual labels are before the real solver entry. -/
theorem actual_control_step (program : Program) (labels : RoutineLabels) (input : List Cell)
    (before : State) (instruction : Instruction) (target budget : ℕ)
    (fetched : program[before.pc]?=some instruction)
    (executed : instruction.execute input before=some {before with pc:=target})
    (safe : RootD27.Bits.SafeBits before budget) (pcBits : natBits target≤budget)
    (beforeBelow : before.pc<labels.solveEntry) (targetBelow : target<labels.solveEntry) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some {before with pc:=target} ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤30 ∧
      (∀ state∈trace,RegionMemory before state ∅ ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,state.pc=before.pc ∨ state.pc=target) ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 := by
  let after : State:={before with pc:=target}
  have actual : step program input before=some after:=by unfold step;rw [fetched];exact executed
  have noCalls:=no_solve_entry labels [before,after] (by
    intro state member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same
    · subst state
      exact Nat.ne_of_lt beforeBelow
    · subst state
      exact Nat.ne_of_lt targetBelow)
  refine ⟨[before,after],rfl,rfl,?_,?_,?_,?_,noCalls.1,noCalls.2⟩
  · simpa only [List.isChain_cons_cons,List.isChain_singleton,and_true] using actual
  · exact (time_le_length program [before,after]).trans (by simp only [List.length_cons,List.length_nil];omega)
  · intro state member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same
    · subst state
      exact ⟨RegionMemory.refl before ∅,safe⟩
    · subst state
      exact ⟨RegionMemory.refl before ∅,safe.withPC target pcBits⟩
  · intro state member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same
    · subst state
      exact Or.inl rfl
    · subst state
      exact Or.inr rfl

/-- Real equality/less-risk comparison using physical scalar fields.
Only40 is written, preserving BOTH original solves, the saved returned
descriptor, the true midpoint statistics and the remaining counter. -/
theorem represented_comparison_actual (P : Parameters) (fee : ℚ) (source : MultiplierState)
    (comparison : Comparison) (left right : ℕ) (x y : ℚ)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State) (budget : ℕ)
    (header : Header before 0 (fun slot=>before.heap slot)) (fresh : before.register .fresh=.natural 0)
    (represented : SearchStateRep P fee before source) (leftInside : left<headerWords) (rightInside : right<headerWords)
    (leftValue : before.heap left=.rational x) (rightValue : before.heap right=.rational y)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (before.pc+10)≤budget)
    (belowEntry : before.pc+10<labels.solveEntry)
    (fetched : FetchesCode program before.pc (comparisonStoredCode comparison left right)) :
    ∃ trace : List State,
      trace.head?=some before ∧
      trace.getLast?=some (comparisonStoredResult before left right (comparison.rat x y)) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤165 ∧
      SearchStateRep P fee (comparisonStoredResult before left right (comparison.rat x y)) source ∧
      Header (comparisonStoredResult before left right (comparison.rat x y)) 0
        (fun slot=>(comparisonStoredResult before left right (comparison.rat x y)).heap slot) ∧
      (comparisonStoredResult before left right (comparison.rat x y)).register .fresh=.natural 0 ∧
      (comparisonStoredResult before left right (comparison.rat x y)).register .flag=
        .natural (if comparison.rat x y then 1 else 0) ∧
      RegionMemory before (comparisonStoredResult before left right (comparison.rat x y)) {40} ∧
      (∀ state∈trace,RegionMemory before state scalarRegion ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+10) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+10) ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 := by
  let after:=comparisonStoredResult before left right (comparison.rat x y)
  obtain ⟨actual,afterHeader⟩:=PDLower.CoreSearch.Located.comparisonStored_segment_bits comparison left right x y
    program input before (fun slot=>before.heap slot) budget header leftInside rightInside leftValue rightValue fresh
    safe small addressBits pcBits fetched before.pc (before.pc+10) (le_refl _) (le_refl _)
  have finalProperties:=actual.final
  have precise : RegionMemory before after {40} := by
    apply header_final_values_region _ header afterHeader finalProperties.1
    intro slot _inside outside
    have different : slot≠40:=by simpa only [Finset.mem_singleton] using outside
    exact Function.update_of_ne different _ _
  have contained : ({40} : Finset ℕ)⊆Finset.Icc 24 47 := by
    intro slot member
    have same : slot=40:=Finset.mem_singleton.mp member
    subst slot
    decide
  have afterRep:=represented.preserve_small_temporary precise contained
  have fields:=comparisonStored_fields before left right (comparison.rat x y)
  have liveHeader : Header after 0 (fun slot=>after.heap slot) := by
    intro slot inside
    exact ⟨afterHeader.live slot inside,by simp only [Nat.zero_add]⟩
  obtain ⟨trace,head,last,chain,cost,properties,proper⟩:=actual
  have noCalls:=no_solve_entry labels trace (by
    intro state member
    have bound:=(properties state member).2
    omega)
  exact ⟨trace,head,last,chain,cost,afterRep,liveHeader,fields.2.2.1.trans fresh,fields.2.2.2.1,precise,
    (fun state member=>⟨scalar_region_memory (properties state member).1.1,(properties state member).1.2⟩),
    (fun state member=>(properties state member).2),proper,noCalls.1,noCalls.2⟩

end RootD27.Core

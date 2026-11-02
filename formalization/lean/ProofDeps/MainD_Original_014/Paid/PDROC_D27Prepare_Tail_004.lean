module

public import Paid.PDROC_D27Prepare_Q_008
public import Paid.PDROC_D27Prepare_Search_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDROC.D27Prepare.Program PDROC.D27Prepare.Resources PDMenu.ComputeFrame
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.Tail

/-- The actual rational comparison page preserves all memory at each
physical prefix. The selected branch is its real Boolean result. -/
theorem rat_compare_segment (R : Finset ℕ) (input : List Cell) (page : ℕ)
    (inside : page<pageCount) (before : State) (location : before.pc=pc page)
    (comparison : Comparison) (left right whenZero whenNonzero : ℕ) (x y : ℚ)
    (layout : pageCode page=ratCompareSlots comparison left right++branch whenZero whenNonzero)
    (fresh : before.register .fresh=.natural 0)
    (leftValue : Search.SlotHas before left (.rational x))
    (rightValue : Search.SlotHas before right (.rational y)) (B : ℕ)
    (bounded : StateBounds 64 B before) (addressBits : 1+natBits 64≤B)
    (leftInside : left<64) (rightInside : right<64) (enough : 2≤B) :
    ∃ after : State,
      after.pc=(if comparison.rat x y then pc whenNonzero else pc whenZero) ∧
      after.heap=before.heap ∧ after.live=before.live ∧
      Segment R input before after 64 B 9 := by
  let terminal := comparisonResult before 0 left right (comparison.rat x y)
  let destination := if comparison.rat x y then pc whenNonzero else pc whenZero
  let after : State := {terminal with pc:=destination}
  obtain ⟨trace,head,last,length,chain,heap,live,afterFresh,output,members⟩ :=
    Search.rat_compare_page_trace input page inside before location comparison left right
      whenZero whenNonzero x y layout fresh leftValue rightValue
  have executed : linearExecute input (ratCompareSlots comparison left right) before=some terminal :=
    ratCompareSlots_execute input before 0 left right x y comparison fresh
      (by simpa only [Nat.zero_add] using leftValue.1)
      (by simpa only [Nat.zero_add] using rightValue.1)
      (by simpa only [Nat.zero_add] using leftValue.2)
      (by simpa only [Nat.zero_add] using rightValue.2)
  have bits := ratCompareSlots_prefix_bounds input before left right 64 B comparison x y bounded fresh
    leftValue.1 rightValue.1 leftValue.2 rightValue.2 leftInside rightInside addressBits enough
  have clean : ∀ instruction∈ratCompareSlots comparison left right,NoMemoryWrite instruction := by
    intro instruction member
    simp only [ratCompareSlots,PDLower.CalibrationCompute.loadSlot,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with ((rfl|rfl|rfl)|(rfl|rfl|rfl))|rfl <;> trivial
  have frames : LinearPrefixMemory R input (ratCompareSlots comparison left right) before := by
    intro count state actual
    exact linearExecute_no_memory_write R input _ before state
      (fun instruction member => clean instruction (List.mem_of_mem_take member)) actual
  refine ⟨after,rfl,heap,live,⟨⟨trace,head,last,chain,length.le,?_,?_⟩,output,afterFresh⟩⟩
  · intro state member
    rcases members state member with same|⟨count,_,actual⟩
    · simpa only [same] using (bits.final executed).with_pc destination
    · exact bits count state actual
  · intro state member
    rcases members state member with same|⟨count,_,actual⟩
    · simpa only [same] using (frames.final executed).with_pc destination
    · exact frames count state actual

end PDROC.D27Prepare.Tail

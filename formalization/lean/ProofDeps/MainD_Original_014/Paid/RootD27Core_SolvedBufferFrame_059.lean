module

public import Paid.RootD27Core_SolvedBufferCall_058

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- The call writes its three statistics, its real copy scratch and its
selected buffer/length. In particular it does not modify either lambda,
the source state tag or the remaining source iteration count. -/
theorem solvedCall_small_outside (P : Parameters) (fee penalty : ℚ) (upper : Bool)
    (address : ℕ) (small : address<46)
    (notStatistics : address≠statisticsSlot upper ∧ address≠statisticsSlot upper+1 ∧
      address≠statisticsSlot upper+2)
    (notLength : address≠tableLengthSlot upper) :
    address∉solvedBufferCallRegion P fee penalty upper := by
  let base:=99+2*P.certificate.M
  have lower : 48≤retainedTableBase base P.certificate.stages P.tools upper := by
    have bound:=retained_base_above_workspace base P.certificate.stages P.tools upper
    unfold workspaceSize headerWords at bound
    omega
  intro member
  rcases Finset.mem_union.mp member with solverRegion|copyRegion
  · rcases Finset.mem_union.mp solverRegion with work|statistics
    · obtain ⟨offset,_inside,equal⟩:=Finset.mem_image.mp work
      change 99+2*P.certificate.M+offset=address at equal
      omega
    · simp only [Finset.mem_insert,Finset.mem_singleton] at statistics
      omega
  · rcases Finset.mem_union.mp copyRegion with copy|lengthSlot
    · rcases Finset.mem_union.mp copy with scratch|destination
      · simp only [Finset.mem_insert,Finset.mem_singleton] at scratch
        omega
      · have bounds:=(mem_cellRegion_iff _ _ _).mp destination
        change retainedTableBase base P.certificate.stages P.tools upper≤address ∧
          address<retainedTableBase base P.certificate.stages P.tools upper+
            (originalSolveEncoding P fee penalty).length at bounds
        omega
    · exact notLength (Finset.mem_singleton.mp lengthSlot)

theorem solvedCall_tag_outside (P : Parameters) (fee penalty : ℚ) (upper : Bool) :
    13∉solvedBufferCallRegion P fee penalty upper := by
  apply solvedCall_small_outside P fee penalty upper 13 (by decide)
  · cases upper <;> decide
  · cases upper <;> decide

theorem solvedCall_counter_outside (P : Parameters) (fee penalty : ℚ) (upper : Bool) :
    28∉solvedBufferCallRegion P fee penalty upper := by
  apply solvedCall_small_outside P fee penalty upper 28 (by decide)
  · cases upper <;> decide
  · cases upper <;> decide

/-- All four physical pieces of the opposite solved buffer survive the
same actual full solver/copy/commit call. Both tables are the original
encodings, so their capacity bounds are proved here, not caller inputs. -/
theorem SolvedBuffer.preserve_other_call {P : Parameters} {fee keptPenalty writtenPenalty : ℚ}
    {kept written : Bool} {before after : State}
    (represented : SolvedBuffer P fee keptPenalty kept before) (different : written≠kept)
    (memory : RegionMemory before after (solvedBufferCallRegion P fee writtenPenalty written)) :
    SolvedBuffer P fee keptPenalty kept after := by
  let base:=99+2*P.certificate.M
  let n:=P.certificate.stages
  let k:=P.tools
  have keptCapacity : (originalSolveEncoding P fee keptPenalty).length≤retainedTableCapacity n k :=
    (original_table_capacity P fee keptPenalty n k).trans (retained_capacity_enough n k)
  have writtenCapacity : (originalSolveEncoding P fee writtenPenalty).length≤retainedTableCapacity n k :=
    (original_table_capacity P fee writtenPenalty n k).trans (retained_capacity_enough n k)
  have keptLower : 48≤retainedTableBase base n k kept := by
    have bound:=retained_base_above_workspace base n k kept
    unfold workspaceSize headerWords at bound
    omega
  apply represented.preserve _ memory
  · intro offset inside
    have zero : offset=0:=by omega
    subst offset
    simp only [Nat.add_zero]
    apply solvedCall_small_outside
    · cases kept <;> decide
    · cases written <;> cases kept <;> simp_all [multiplierSlot,statisticsSlot]
    · cases written <;> cases kept <;> simp_all [multiplierSlot,tableLengthSlot]
  · intro offset inside
    apply solvedCall_small_outside
    · cases kept <;> simp only [statisticsSlot,Bool.false_eq_true,ite_false,ite_true] <;> omega
    · cases written <;> cases kept <;>
        simp_all [statisticsSlot] <;> omega
    · cases written <;> cases kept <;>
        simp_all [statisticsSlot,tableLengthSlot] <;> omega
  · intro offset inside
    have zero : offset=0:=by omega
    subst offset
    simp only [Nat.add_zero]
    apply solvedCall_small_outside
    · cases kept <;> decide
    · cases written <;> cases kept <;> simp_all [tableLengthSlot,statisticsSlot]
    · cases written <;> cases kept <;> simp_all [tableLengthSlot]
  · intro offset inside member
    change retainedTableBase base n k kept+offset∈
      ((workspace base n k∪{statisticsSlot written,statisticsSlot written+1,statisticsSlot written+2})∪
        (({46,47}∪cellRegion (retainedTableBase base n k written)
          (originalSolveEncoding P fee writtenPenalty).length)∪{tableLengthSlot written})) at member
    rcases Finset.mem_union.mp member with solverRegion|copyRegion
    · rcases Finset.mem_union.mp solverRegion with work|statistics
      · exact retained_outside_workspace base n k offset kept work
      · cases written <;> simp only [statisticsSlot,Bool.false_eq_true,ite_false,ite_true,
          Finset.mem_insert,Finset.mem_singleton] at statistics <;> omega
    · rcases Finset.mem_union.mp copyRegion with copy|lengthSlot
      · rcases Finset.mem_union.mp copy with scratch|destination
        · simp only [Finset.mem_insert,Finset.mem_singleton] at scratch
          omega
        · have bounds:=(mem_cellRegion_iff _ _ _).mp destination
          cases written <;> cases kept <;>
            simp_all only [Bool.false_eq_true,not_false_eq_true,not_true_eq_false,ne_eq,
              not_true_eq_false,retainedTableBase,retainedTableCapacity,ite_false,ite_true] <;>
            omega
      · have equal:=Finset.mem_singleton.mp lengthSlot
        have bound:=(tableLengthSlot_bounds written).2
        omega

end RootD27.Core

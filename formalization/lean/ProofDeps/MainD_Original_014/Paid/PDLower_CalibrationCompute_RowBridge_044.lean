module

public import Paid.PDLower_CalibrationCompute_Rows_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- The two ORIGINAL commands for each of the preceding physical
source cells, in their original state/letter order. -/
def rowPrefixCommands (P : Parameters) (level : ℕ) (previous : Array ℚ) (cursor : ℕ) :
    List (WalkCell level × ℚ) :=
  ((List.finRange (2*level+1)).take cursor).flatMap (fun state =>
    (List.finRange 2).map (fun letter =>
      (walkMove level state letter,previous.getD state.val 0*P.experiment.channel true letter)))

def rowScatterPrefix (P : Parameters) (level : ℕ) (previous : Array ℚ) (cursor : ℕ) : Array ℚ :=
  PDROC.endpointArrayScatter (rowPrefixCommands P level previous cursor) (Array.replicate (2*level+1) 0)

theorem rowScatterPrefix_size (P : Parameters) (level : ℕ) (previous : Array ℚ) (cursor : ℕ) :
    (rowScatterPrefix P level previous cursor).size=2*level+1 := by
  simp only [rowScatterPrefix,PDROC.endpointArrayScatter_size,Array.size_replicate]

theorem rowScatterPrefix_zero (P : Parameters) (level : ℕ) (previous : Array ℚ) :
    rowScatterPrefix P level previous 0=Array.replicate (2*level+1) 0 := rfl

theorem rowPrefixCommands_succ (P : Parameters) (level : ℕ) (previous : Array ℚ) (cursor : ℕ)
    (inside : cursor<2*level+1) :
    rowPrefixCommands P level previous (cursor+1)=rowPrefixCommands P level previous cursor ++
      (List.finRange 2).map (fun letter =>
        (walkMove level ⟨cursor,inside⟩ letter,previous.getD cursor 0*P.experiment.channel true letter)) := by
  have bound : cursor<(List.finRange (2*level+1)).length := by simpa only [List.length_finRange] using inside
  have lookup : (List.finRange (2*level+1))[cursor]=⟨cursor,inside⟩ := by simp
  simp only [rowPrefixCommands,List.take_succ_eq_append_getElem bound,List.flatMap_append,
    List.flatMap_singleton,lookup]

/-- This is an exact prefix identity of the original frozen walkUpdate.
Both commands remain, including when absorption gives equal targets. -/
theorem rowScatterPrefix_succ (P : Parameters) (level : ℕ) (previous : Array ℚ) (cursor : ℕ)
    (inside : cursor<2*level+1) :
    rowScatterPrefix P level previous (cursor+1)=
      PDROC.endpointArrayBump
        (PDROC.endpointArrayBump (rowScatterPrefix P level previous cursor)
          (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val
          (previous.getD cursor 0*(1/2-P.certificate.gamma)))
        (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).val
        (previous.getD cursor 0*(1/2+P.certificate.gamma)) := by
  have letters : List.finRange 2=([0,1] : List (Fin 2)) := rfl
  rw [rowScatterPrefix,rowPrefixCommands_succ P level previous cursor inside]
  simp only [PDROC.endpointArrayScatter,List.foldl_append,letters,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil]
  rfl

theorem rowScatterPrefix_complete (P : Parameters) (level : ℕ) (previous : Array ℚ) :
    rowScatterPrefix P level previous (2*level+1)=P.walkUpdate level true previous := by
  have taken : (List.finRange (2*level+1)).take (2*level+1)=List.finRange (2*level+1) := by
    simpa only [List.length_finRange] using (List.take_length (l:=List.finRange (2*level+1)))
  rw [PDROC.walkUpdate_eq_endpointScatter]
  simp only [rowScatterPrefix,rowPrefixCommands,PDROC.endpointWalkCommands,taken]

end PDLower.CalibrationCompute

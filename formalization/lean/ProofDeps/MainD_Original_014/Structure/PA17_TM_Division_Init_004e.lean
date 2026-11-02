module
public import Structure.PA17_TM_Division_Init_004d

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionInit004
open PSTRTMBinaryAdd024
open PSTRTMCompareCode054 (leftColumns)

def residentWord (remainingReverse done : List (Bool × Bool)) : List Bool :=
  operandColumns remainingReverse.reverse ++ (markedColumns done ++ [false,false])
def copyState (remainingReverse done : List (Bool × Bool)) : MachineState 66 :=
  state 0 (sep (archiveLeft done)) (residentWord remainingReverse done)

def iterationTrace (a b : Bool) (previous done : List (Bool × Bool)) : List (MachineState 66) :=
  splice (splice (splice (splice
    (seekTrace (sep (archiveLeft done)) (previous.reverse ++ [(a,b)]) (markerTail done))
    (extractTrace a b (leftColumns previous ++ sep (archiveLeft done)) (markedColumns done ++ [false,false])))
    (fullBackTrace a (archiveLeft done) previous (markedColumns ((a,b)::done) ++ [false,false])))
    (fullArchiveTrace a (archivePairs done).reverse (sep (residentWord previous ((a,b)::done)))))
    (returnTrace true [] (archivePairs ((a,b)::done)) (residentWord previous ((a,b)::done)))

theorem iteration_segment (a b : Bool) (previous done : List (Bool × Bool)) :
    Segment (copyState ((a,b)::previous) done) (iterationTrace a b previous done) (copyState previous ((a,b)::done)) := by
  have hs : Segment (copyState ((a,b)::previous) done)
      (seekTrace (sep (archiveLeft done)) (previous.reverse ++ [(a,b)]) (markerTail done))
      (state 5 (true::b::true::a::(leftColumns previous ++ sep (archiveLeft done))) (markedColumns done ++ [false,false])) := by
    have h := seek_segment (sep (archiveLeft done)) (previous.reverse ++ [(a,b)]) (markerTail done)
    rw [← marked_decompose done] at h
    simpa [copyState,residentWord,List.reverse_cons,List.reverse_append,leftColumns,List.flatMap_append,List.append_assoc] using h
  have he := extract_segment a b (leftColumns previous ++ sep (archiveLeft done)) (markedColumns done ++ [false,false])
  have hb : Segment
      (state (keep 3 a) (leftColumns previous ++ sep (archiveLeft done)) (false::false::b::true::(markedColumns done ++ [false,false])))
      (fullBackTrace a (archiveLeft done) previous (markedColumns ((a,b)::done) ++ [false,false]))
      (state (keep 9 a) (archiveLeft done) (sep (residentWord previous ((a,b)::done)))) := by
    exact fullBack_segment a (archiveLeft done) previous (markedColumns ((a,b)::done) ++ [false,false])
  have ha : Segment (state (keep 9 a) (archiveLeft done) (sep (residentWord previous ((a,b)::done))))
      (fullArchiveTrace a (archivePairs done).reverse (sep (residentWord previous ((a,b)::done))))
      (state 50 [] (operandColumns (archivePairs ((a,b)::done)) ++ sep (residentWord previous ((a,b)::done)))) := by
    simpa only [archiveLeft,archivePairs,List.map_cons,List.reverse_reverse] using
      fullArchive_segment a (archivePairs done).reverse (sep (residentWord previous ((a,b)::done)))
  have hr : Segment
      (state 50 [] (operandColumns (archivePairs ((a,b)::done)) ++ sep (residentWord previous ((a,b)::done))))
      (returnTrace true [] (archivePairs ((a,b)::done)) (residentWord previous ((a,b)::done)))
      (copyState previous ((a,b)::done)) := by
    simpa only [returnLabel,ite_true,copyState,archiveLeft,List.append_nil] using
      return_segment true [] (archivePairs ((a,b)::done)) (residentWord previous ((a,b)::done))
  exact segment_splice (segment_splice (segment_splice (segment_splice hs he) hb) ha) hr

theorem splice_length_le (xs ys : List (MachineState 66)) : (splice xs ys).length ≤ xs.length + ys.length := by
  simp only [splice,List.length_append,List.length_dropLast]
  omega

theorem splice5_length_le (xs ys zs us vs : List (MachineState 66)) :
    (splice (splice (splice (splice xs ys) zs) us) vs).length ≤ xs.length+ys.length+zs.length+us.length+vs.length := by
  have h1 := splice_length_le xs ys
  have h2 := splice_length_le (splice xs ys) zs
  have h3 := splice_length_le (splice (splice xs ys) zs) us
  have h4 := splice_length_le (splice (splice (splice xs ys) zs) us) vs
  omega

theorem iteration_length_le (a b : Bool) (previous done : List (Bool × Bool)) :
    (iterationTrace a b previous done).length ≤ 8*(previous.length+done.length)+37 := by
  have h := splice5_length_le
    (seekTrace (sep (archiveLeft done)) (previous.reverse ++ [(a,b)]) (markerTail done))
    (extractTrace a b (leftColumns previous ++ sep (archiveLeft done)) (markedColumns done ++ [false,false]))
    (fullBackTrace a (archiveLeft done) previous (markedColumns ((a,b)::done) ++ [false,false]))
    (fullArchiveTrace a (archivePairs done).reverse (sep (residentWord previous ((a,b)::done))))
    (returnTrace true [] (archivePairs ((a,b)::done)) (residentWord previous ((a,b)::done)))
  simp only [seek_length,extract_length,fullBack_length,fullArchive_length,return_length,
    List.length_reverse,List.length_append,List.length_cons,List.length_nil,archivePairs,List.length_map] at h
  change (iterationTrace a b previous done).length ≤ _ at h
  omega

def copyLoopTrace : List (Bool × Bool) → List (Bool × Bool) → List (MachineState 66)
  | [], done => [copyState [] done]
  | (a,b)::previous, done => splice (iterationTrace a b previous done) (copyLoopTrace previous ((a,b)::done))

theorem copyLoop_segment (remainingReverse done : List (Bool × Bool)) :
    Segment (copyState remainingReverse done) (copyLoopTrace remainingReverse done) (copyState [] (remainingReverse.reverse ++ done)) := by
  induction remainingReverse generalizing done with
  | nil => exact segment_single _
  | cons pair previous ih =>
    obtain ⟨a,b⟩ := pair
    simpa only [copyLoopTrace,List.reverse_cons,List.append_assoc,List.singleton_append] using
      segment_splice (iteration_segment a b previous done) (ih ((a,b)::done))

theorem copyLoop_length_le (remainingReverse done : List (Bool × Bool)) :
    (copyLoopTrace remainingReverse done).length ≤
      remainingReverse.length * (8*(remainingReverse.length+done.length)+37)+1 := by
  induction remainingReverse generalizing done with
  | nil => simp only [copyLoopTrace,List.length_singleton,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | cons pair previous ih =>
    obtain ⟨a,b⟩ := pair
    have hs := splice_length_le (iterationTrace a b previous done) (copyLoopTrace previous ((a,b)::done))
    have hi := iteration_length_le a b previous done
    have ht := ih ((a,b)::done)
    simp only [List.length_cons] at ht ⊢
    change (splice (iterationTrace a b previous done) (copyLoopTrace previous ((a,b)::done))).length ≤ _
    nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionInit004

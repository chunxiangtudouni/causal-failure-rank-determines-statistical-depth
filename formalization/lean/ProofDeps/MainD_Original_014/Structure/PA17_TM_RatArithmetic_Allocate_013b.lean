module
public import Structure.PA17_TM_RatArithmetic_Allocate_013a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocate013

open Turing

/-- k is compiled into finite code before all tape inputs. It is not a
caller-supplied runtime width or fuel. This is a constant allocation chunk. -/
def gapMachine (k : Nat) : Machine (3*k) := fun q _symbol =>
  if live : q.val < 3*k then
    some (⟨q.val+1,by omega⟩,
      if q.val%3=0 then .write false else if q.val%3=1 then .move .right else .write true)
  else none

def gapState (k q : Nat) (bound : q ≤ 3*k) (left right : List Bool) : MachineState (3*k) :=
  ⟨⟨q,by omega⟩,Tape.mk₂ left right⟩

def gapTrace (k done remaining : Nat) (count : done+remaining=k)
    (left suffix : List Bool) : List (MachineState (3*k)) :=
  match remaining with
  | 0 => [gapState k (3*done) (by omega) left (true::suffix)]
  | n+1 =>
    [gapState k (3*done) (by omega) left (true::false::(List.replicate n false++suffix)),
      gapState k (3*done+1) (by omega) left (false::false::(List.replicate n false++suffix)),
      gapState k (3*done+2) (by omega) (false::left) (false::(List.replicate n false++suffix))] ++
    gapTrace k (done+1) n (by omega) (false::left) suffix
termination_by remaining

theorem gap_head (k done remaining : Nat) (count : done+remaining=k) (left suffix : List Bool) :
    (gapTrace k done remaining count left suffix).head? =
      some (gapState k (3*done) (by omega) left (true::(List.replicate remaining false++suffix))) := by
  cases remaining <;> simp [gapTrace,List.replicate_succ]

theorem gap_last (k done remaining : Nat) (count : done+remaining=k) (left suffix : List Bool) :
    (gapTrace k done remaining count left suffix).getLast? =
      some (gapState k (3*k) (by omega) (List.replicate remaining false++left) (true::suffix)) := by
  induction remaining generalizing done left with
  | zero =>
    have hd : done=k := by omega
    subst done
    simp [gapTrace]
  | succ n ih =>
    rw [gapTrace,List.getLast?_append,ih]
    have hrep : List.replicate n false ++ false::left = List.replicate (n+1) false ++ left := by
      rw [List.replicate_succ']
      simp only [List.append_assoc,List.singleton_append]
    simp only [hrep,Option.some_or]

theorem gap_length (k done remaining : Nat) (count : done+remaining=k) (left suffix : List Bool) :
    (gapTrace k done remaining count left suffix).length = 3*remaining+1 := by
  induction remaining generalizing done left with
  | zero => simp [gapTrace]
  | succ n ih => simp [gapTrace,ih]; omega

theorem gap_chain (k done remaining : Nat) (count : done+remaining=k) (left suffix : List Bool) :
    (gapTrace k done remaining count left suffix).IsChain
      (fun before after => TM0.step (gapMachine k) before = some after) := by
  induction remaining generalizing done left with
  | zero => simp [gapTrace]
  | succ n ih =>
    have h0 : 3*done < 3*k := by omega
    have h1 : 3*done+1 < 3*k := by omega
    have h2 : 3*done+2 < 3*k := by omega
    have hm0 : (3*done)%3=0 := by omega
    have hm1 : (3*done+1)%3=1 := by omega
    have hm2 : (3*done+2)%3=2 := by omega
    rw [gapTrace]
    simp only [List.cons_append,List.nil_append,List.isChain_cons_cons]
    refine ⟨?_,?_,?_⟩
    · simp [TM0.step,gapMachine,gapState,h0,hm0,Tape.mk₂]
    · simp [TM0.step,gapMachine,gapState,h1,hm1,Tape.mk₂]
    · apply List.IsChain.cons (ih (done+1) (by omega) (false::left))
      intro next hn
      rw [gap_head] at hn
      simp only [Option.mem_some_iff] at hn
      subst next
      have hq : 3*done+2+1=3*(done+1) := by omega
      simp [TM0.step,gapMachine,gapState,h2,hm2,hq,Tape.mk₂]

/-- Fully actual allocation of a fixed chunk: the old owned TRUE marker is
moved k cells right, leaving k real false cells. External left/suffix survive
unchanged; exactly k OWNfalse cells on entry are consumed, never invented. -/
theorem gap_runsFrom (k : Nat) (left suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (gapMachine k)
      ⟨0,Tape.mk₂ left (true::(List.replicate k false++suffix))⟩
      (gapTrace k 0 k (by omega) left suffix)
      (gapState k (3*k) (by omega) (List.replicate k false++left) (true::suffix)) := by
  refine ⟨?_,gap_chain k 0 k (by omega) left suffix,gap_last k 0 k (by omega) left suffix,?_⟩
  · simpa only [gapState,Nat.mul_zero,Fin.mk_zero] using gap_head k 0 k (by omega) left suffix
  · simp [TM0.step,gapMachine,gapState]

theorem gap_prefix_space (k : Nat) (left suffix : List Bool) (prefixLength inputLength : Nat) :
    visitedSpace (gapMachine k) inputLength ((gapTrace k 0 k (by omega) left suffix).take prefixLength) ≤
      inputLength+6*k+3 := by
  have hs := PSTRTMTrace002.visitedSpace_le (gapMachine k) inputLength
    ((gapTrace k 0 k (by omega) left suffix).take prefixLength)
  have ht := gap_length k 0 k (by omega) left suffix
  have hp : ((gapTrace k 0 k (by omega) left suffix).take prefixLength).length ≤
      (gapTrace k 0 k (by omega) left suffix).length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocate013

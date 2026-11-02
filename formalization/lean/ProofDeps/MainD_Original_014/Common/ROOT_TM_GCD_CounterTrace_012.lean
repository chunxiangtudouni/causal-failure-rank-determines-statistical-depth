module
public import Common.ROOT_TM_GCD_CounterCode_011

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDCounter011
open PaperProofs.Common.Native.RationalControllerComputation

private theorem append_link (xs ys : List (MachineState 5)) (last first : MachineState 5)
    (hx : xs.IsChain (fun a b => Turing.TM0.step counterMachine a=some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step counterMachine a=some b))
    (hl : xs.getLast?=some last) (hh : ys.head?=some first)
    (hs : Turing.TM0.step counterMachine last=some first) :
    (xs++ys).IsChain (fun a b => Turing.TM0.step counterMachine a=some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he:=Option.mem_some_iff.mp ha
  have hf:=Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def prefixTrace (n : Nat) (tail : List Bool) : List (MachineState 5) :=
  [state 0 (false::ones n) tail,state 1 (ones n) (false::tail)]
def fullTrace (n : Nat) (tail : List Bool) : List (MachineState 5) :=
  prefixTrace n tail++searchTrace n (false::tail)++
    [state 3 [] (true::(ones n++false::tail))]++returnTrace n [true] tail

theorem prefix_chain (n : Nat) (tail : List Bool) :
    (prefixTrace n tail).IsChain (fun a b => Turing.TM0.step counterMachine a=some b) := by
  simp [prefixTrace,List.isChain_cons_cons,Turing.TM0.step,counterMachine,state,Turing.Tape.mk₂]
theorem prefix_search (n : Nat) (tail : List Bool) :
    Turing.TM0.step counterMachine (state 1 (ones n) (false::tail))=some (searchInitial n (false::tail)) := by
  cases n <;> simp [searchInitial,Turing.TM0.step,counterMachine,state,Turing.Tape.mk₂,ones,List.replicate_succ]
theorem search_write (n : Nat) (tail : List Bool) :
    Turing.TM0.step counterMachine (state 2 [] (false::(ones n++false::tail)))=
      some (state 3 [] (true::(ones n++false::tail))) := by
  simp [Turing.TM0.step,counterMachine,state,Turing.Tape.mk₂]
theorem write_return (n : Nat) (tail : List Bool) :
    Turing.TM0.step counterMachine (state 3 [] (true::(ones n++false::tail)))=
      some (state 4 [true] (ones n++false::tail)) := by
  simp [Turing.TM0.step,counterMachine,state,Turing.Tape.mk₂]

theorem full_head (n : Nat) (tail : List Bool) :
    (fullTrace n tail).head?=some (state 0 (false::ones n) tail) := rfl
theorem full_last (n : Nat) (tail : List Bool) :
    (fullTrace n tail).getLast?=some (state 5 (false::ones (n+1)) tail) := by
  have h : ones n++[true]=ones (n+1) := by simp only [ones,List.replicate_succ']
  simp only [fullTrace,List.getLast?_append,return_last,h,Option.some_or]
theorem full_length (n : Nat) (tail : List Bool) : (fullTrace n tail).length=2*n+6 := by
  simp only [fullTrace,prefixTrace,List.length_append,List.length_cons,List.length_nil,search_length,return_length]
  omega
theorem full_chain (n : Nat) (tail : List Bool) :
    (fullTrace n tail).IsChain (fun a b => Turing.TM0.step counterMachine a=some b) := by
  have hprefix : (prefixTrace n tail).getLast?=some (state 1 (ones n) (false::tail)) := rfl
  have hfirst := append_link _ _ _ _ (prefix_chain n tail) (search_chain n (false::tail))
    hprefix (search_head n (false::tail)) (prefix_search n tail)
  have hlast : (prefixTrace n tail++searchTrace n (false::tail)).getLast?=
      some (state 2 [] (false::(ones n++false::tail))) := by
    simp only [List.getLast?_append,search_last,Option.some_or]
  have hsecond := append_link _ [state 3 [] (true::(ones n++false::tail))] _ _ hfirst
    (by simp only [List.isChain_singleton]) hlast rfl (search_write n tail)
  have hlast' : ((prefixTrace n tail++searchTrace n (false::tail))++
      [state 3 [] (true::(ones n++false::tail))]).getLast?=
      some (state 3 [] (true::(ones n++false::tail))) := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  exact append_link _ _ _ _ hsecond (return_chain n [true] tail) hlast' (return_head n [true] tail) (write_return n tail)

/-- Genuine finite-control increment of the common-two exponent. The tape
right of the operand guard is literally identical, with no parameter oracle. -/
theorem counter_runsFrom (n : Nat) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom counterMachine (state 0 (false::ones n) tail) (fullTrace n tail)
      (state 5 (false::ones (n+1)) tail) := by
  refine ⟨full_head n tail,full_chain n tail,full_last n tail,?_⟩
  simp [Turing.TM0.step,counterMachine,state]

theorem counter_visitedSpace_le (n : Nat) (tail : List Bool) (inputLength : Nat) :
    visitedSpace counterMachine inputLength (fullTrace n tail) ≤ inputLength+4*n+13 := by
  have h:=PSTRTMTrace002.visitedSpace_le counterMachine inputLength (fullTrace n tail)
  rw [full_length] at h
  omega

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDCounter011

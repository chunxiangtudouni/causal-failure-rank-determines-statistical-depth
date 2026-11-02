module
public import Common.ROOT_TM_GCD_PopCode_016

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDPop016
open PaperProofs.Common.Native.RationalControllerComputation

private theorem append_link (xs ys : List (MachineState 7)) (last first : MachineState 7)
    (hx : xs.IsChain (fun a b => Turing.TM0.step popMachine a=some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step popMachine a=some b))
    (hl : xs.getLast?=some last) (hh : ys.head?=some first)
    (hs : Turing.TM0.step popMachine last=some first) :
    (xs++ys).IsChain (fun a b => Turing.TM0.step popMachine a=some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he:=Option.mem_some_iff.mp ha
  have hf:=Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def prefixTrace (n : Nat) (tail : List Bool) : List (MachineState 7) :=
  [state 0 (false::ones n) tail,state 1 (ones n) (false::tail)]
def eraseTrace (n : Nat) (tail : List Bool) : List (MachineState 7) :=
  [state 3 [] (ones (n+1)++false::tail),state 4 [] (false::(ones n++false::tail))]
def succTrace (n : Nat) (tail : List Bool) : List (MachineState 7) :=
  prefixTrace (n+1) tail++searchTrace (n+1) (false::tail)++eraseTrace n tail++returnTrace n [false] tail
def zeroTrace (tail : List Bool) : List (MachineState 7) :=
  [state 0 [false] tail,state 1 [] (false::tail),state 2 [] (false::false::tail),
    state 3 [] (false::tail),state 7 [false] tail]

theorem prefix_chain (n : Nat) (tail : List Bool) :
    (prefixTrace n tail).IsChain (fun a b => Turing.TM0.step popMachine a=some b) := by
  simp [prefixTrace,List.isChain_cons_cons,Turing.TM0.step,popMachine,state,Turing.Tape.mk₂]
theorem prefix_search (n : Nat) (tail : List Bool) :
    Turing.TM0.step popMachine (state 1 (ones n) (false::tail))=some (searchInitial n (false::tail)) := by
  cases n <;> simp [searchInitial,Turing.TM0.step,popMachine,state,Turing.Tape.mk₂,ones,List.replicate_succ]
theorem search_erase (n : Nat) (tail : List Bool) :
    Turing.TM0.step popMachine (state 2 [] (false::(ones (n+1)++false::tail)))=
      some (state 3 [] (ones (n+1)++false::tail)) := by
  simp [Turing.TM0.step,popMachine,state,Turing.Tape.mk₂,PSTRTMRawNat010.blank_single_false]
theorem erase_chain (n : Nat) (tail : List Bool) :
    (eraseTrace n tail).IsChain (fun a b => Turing.TM0.step popMachine a=some b) := by
  simp [eraseTrace,List.isChain_cons_cons,Turing.TM0.step,popMachine,state,Turing.Tape.mk₂,ones,List.replicate_succ]
theorem erase_return (n : Nat) (tail : List Bool) :
    Turing.TM0.step popMachine (state 4 [] (false::(ones n++false::tail)))=
      some (state 5 [false] (ones n++false::tail)) := by
  simp [Turing.TM0.step,popMachine,state,Turing.Tape.mk₂]

theorem succ_head (n : Nat) (tail : List Bool) :
    (succTrace n tail).head?=some (state 0 (false::ones (n+1)) tail) := rfl
theorem state_left_append_false (q : Fin 8) (left right : List Bool) :
    state q (left++[false]) right=state q left right := by
  simp only [state,Turing.Tape.mk₂,PSTRTMRawNat010.blank_append_false]
theorem succ_last (n : Nat) (tail : List Bool) :
    (succTrace n tail).getLast?=some (state 6 (false::ones n) tail) := by
  have hstate : state 6 (false::(ones n++[false])) tail=state 6 (false::ones n) tail := by
    simpa only [List.cons_append] using state_left_append_false 6 (false::ones n) tail
  simp only [succTrace,List.getLast?_append,return_last,hstate,Option.some_or]
theorem succ_length (n : Nat) (tail : List Bool) : (succTrace n tail).length=2*n+8 := by
  simp only [succTrace,prefixTrace,eraseTrace,List.length_append,List.length_cons,List.length_nil,search_length,return_length]
  omega
theorem succ_chain (n : Nat) (tail : List Bool) :
    (succTrace n tail).IsChain (fun a b => Turing.TM0.step popMachine a=some b) := by
  have hp : (prefixTrace (n+1) tail).getLast?=some (state 1 (ones (n+1)) (false::tail)) := rfl
  have hfirst:=append_link _ _ _ _ (prefix_chain (n+1) tail) (search_chain (n+1) (false::tail))
    hp (search_head (n+1) (false::tail)) (prefix_search (n+1) tail)
  have hl : (prefixTrace (n+1) tail++searchTrace (n+1) (false::tail)).getLast?=
      some (state 2 [] (false::(ones (n+1)++false::tail))) := by
    simp only [List.getLast?_append,search_last,Option.some_or]
  have hsecond:=append_link _ (eraseTrace n tail) _ _ hfirst (erase_chain n tail) hl rfl (search_erase n tail)
  have hl' : ((prefixTrace (n+1) tail++searchTrace (n+1) (false::tail))++eraseTrace n tail).getLast?=
      some (state 4 [] (false::(ones n++false::tail))) := by
    simp only [List.getLast?_append,eraseTrace,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  exact append_link _ _ _ _ hsecond (return_chain n [false] tail) hl' (return_head n [false] tail) (erase_return n tail)

theorem zero_chain (tail : List Bool) :
    (zeroTrace tail).IsChain (fun a b => Turing.TM0.step popMachine a=some b) := by
  simp [zeroTrace,List.isChain_cons_cons,Turing.TM0.step,popMachine,state,Turing.Tape.mk₂,
    PSTRTMRawNat010.blank_single_false]
theorem pop_succ_runsFrom (n : Nat) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom popMachine (state 0 (false::ones (n+1)) tail) (succTrace n tail)
      (state 6 (false::ones n) tail) := by
  refine ⟨succ_head n tail,succ_chain n tail,succ_last n tail,?_⟩
  simp [Turing.TM0.step,popMachine,state]
theorem pop_zero_runsFrom (tail : List Bool) :
    PSTRTMSeq005.RunsFrom popMachine (state 0 [false] tail) (zeroTrace tail)
      (state 7 [false] tail) := by
  refine ⟨rfl,zero_chain tail,rfl,?_⟩
  simp [Turing.TM0.step,popMachine,state]

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDPop016

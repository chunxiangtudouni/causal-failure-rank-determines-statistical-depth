module
public import Common.ROOT_TM_GCD_CounterTrace_012

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDPop016
open PaperProofs.Common.Native.RationalControllerComputation

/-- Eight fixed labels really remove one unary common-two mark at the far
left end. The HALT label6 means a mark was found,7 means the counter was
actually empty. No count or branch certificate is runtime input. -/
def popMachine : Machine 7 := fun q bit =>
  match q.val with
  | 0 => some (1,.move .left)
  | 1 => some (2,.move .left)
  | 2 => if bit then some (2,.move .left) else some (3,.move .right)
  | 3 => if bit then some (4,.write false) else some (7,.move .right)
  | 4 => some (5,.move .right)
  | 5 => if bit then some (5,.move .right) else some (6,.move .right)
  | _ => none
def state (q : Fin 8) (left right : List Bool) : MachineState 7 := ⟨q,Turing.Tape.mk₂ left right⟩
abbrev ones (n : Nat) := List.replicate n true
def searchTrace : Nat → List Bool → List (MachineState 7)
  | 0,tail => [state 2 [] (false::tail)]
  | n+1,tail => state 2 (ones n) (true::tail)::searchTrace n (true::tail)
def searchInitial : Nat → List Bool → MachineState 7
  | 0,tail => state 2 [] (false::tail)
  | n+1,tail => state 2 (ones n) (true::tail)
theorem search_head (n : Nat) (tail : List Bool) :
    (searchTrace n tail).head?=some (searchInitial n tail) := by cases n <;> rfl
theorem search_last (n : Nat) (tail : List Bool) :
    (searchTrace n tail).getLast?=some (state 2 [] (false::(ones n++tail))) := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih =>
    have hne : searchTrace n (true::tail)≠[] := by
      intro h
      have hh:=search_head n (true::tail)
      simp [h] at hh
    rw [searchTrace,List.getLast?_cons_of_ne_nil hne,ih]
    have h : ones n++true::tail=ones (n+1)++tail := by simp [ones,List.replicate_succ',List.append_assoc]
    rw [h]
theorem search_length (n : Nat) (tail : List Bool) : (searchTrace n tail).length=n+1 := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih => simp only [searchTrace,List.length_cons,ih]
theorem search_chain (n : Nat) (tail : List Bool) :
    (searchTrace n tail).IsChain (fun before after => Turing.TM0.step popMachine before=some after) := by
  induction n generalizing tail with
  | zero => simp only [searchTrace,List.isChain_singleton]
  | succ n ih =>
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [search_head] at ha
      have he:=Option.mem_some_iff.mp ha
      subst after
      cases n <;> simp [searchInitial,Turing.TM0.step,popMachine,state,Turing.Tape.mk₂,ones,List.replicate_succ]
    · exact ih _
def returnTrace : Nat → List Bool → List Bool → List (MachineState 7)
  | 0,left,tail => [state 5 left (false::tail),state 6 (false::left) tail]
  | n+1,left,tail => state 5 left (ones (n+1)++false::tail)::returnTrace n (true::left) tail
theorem return_head (n : Nat) (left tail : List Bool) :
    (returnTrace n left tail).head?=some (state 5 left (ones n++false::tail)) := by cases n <;> rfl
theorem return_last (n : Nat) (left tail : List Bool) :
    (returnTrace n left tail).getLast?=some (state 6 (false::(ones n++left)) tail) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
    have hne : returnTrace n (true::left) tail≠[] := by
      intro h
      have hh:=return_head n (true::left) tail
      simp [h] at hh
    rw [returnTrace,List.getLast?_cons_of_ne_nil hne,ih]
    have h : ones n++true::left=ones (n+1)++left := by simp [ones,List.replicate_succ',List.append_assoc]
    rw [h]
theorem return_length (n : Nat) (left tail : List Bool) : (returnTrace n left tail).length=n+2 := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih => simp only [returnTrace,List.length_cons,ih]
theorem return_chain (n : Nat) (left tail : List Bool) :
    (returnTrace n left tail).IsChain (fun before after => Turing.TM0.step popMachine before=some after) := by
  induction n generalizing left with
  | zero => simp [returnTrace,List.isChain_cons_cons,Turing.TM0.step,popMachine,state,Turing.Tape.mk₂]
  | succ n ih =>
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [return_head] at ha
      have he:=Option.mem_some_iff.mp ha
      subst after
      simp [Turing.TM0.step,popMachine,state,Turing.Tape.mk₂,ones,List.replicate_succ]
    · exact ih _

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDPop016

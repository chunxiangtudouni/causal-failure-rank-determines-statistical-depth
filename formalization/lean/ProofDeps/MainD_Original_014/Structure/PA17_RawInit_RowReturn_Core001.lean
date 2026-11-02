module
public import Common.PSTR_WordBool_RawInit_Shape001
public import Common.PSTR_TM_Seq_005

/-! Fixed35-control row return. Entry ignores the unread symbol, even TRUE.
Every33 LEFTs reaches a physical row first cell. FALSE performs a charged
write-self and repeats; TRUE moves once LEFT and seeks the real sentinel. -/
@[expose] public section
namespace PaperProofs.Common.Native.PA17RawInitRowReturn
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005

def machine : Machine 34 := fun q symbol =>
  if h : q.val<33 then some (⟨q.val+1,by omega⟩,.move .left)
  else if q.val=33 then
    if symbol then some (34,.move .left) else some (0,.write false)
  else if symbol then none else some (34,.move .left)

def state (q : Fin 35) (tape : Tape Bool) : MachineState 34 := ⟨q,tape⟩

def moveTrace : (steps start : Nat) → start+steps≤33 → Tape Bool → List (MachineState 34)
  | 0,start,bound,tape => [state ⟨start,by omega⟩ tape]
  | steps+1,start,bound,tape =>
    state ⟨start,by omega⟩ tape :: moveTrace steps (start+1) (by omega) (tape.move .left)

theorem moveTrace_head (steps start : Nat) (bound : start+steps≤33) (tape : Tape Bool) :
    (moveTrace steps start bound tape).head?=some (state ⟨start,by omega⟩ tape) := by
  cases steps <;> rfl

theorem moveTrace_length (steps start : Nat) (bound : start+steps≤33) (tape : Tape Bool) :
    (moveTrace steps start bound tape).length=steps+1 := by
  induction steps generalizing start tape with
  | zero => rfl
  | succ steps ih => simp only [moveTrace,List.length_cons,ih]

theorem moveTrace_last (steps start : Nat) (bound : start+steps≤33) (tape : Tape Bool) :
    (moveTrace steps start bound tape).getLast?=
      some (state ⟨start+steps,by omega⟩ ((Tape.move .left)^[steps] tape)) := by
  induction steps generalizing start tape with
  | zero => simp only [moveTrace,List.getLast?_singleton,Nat.add_zero,Function.iterate_zero, id_eq]
  | succ steps ih =>
    rw [moveTrace,List.getLast?_cons,ih]
    have add : start+1+steps=start+(steps+1) := by omega
    simp only [Option.getD_some,add,Function.iterate_succ_apply]

theorem moveTrace_chain (steps start : Nat) (bound : start+steps≤33) (tape : Tape Bool) :
    (moveTrace steps start bound tape).IsChain (fun first last=>TM0.step machine first=some last) := by
  induction steps generalizing start tape with
  | zero => exact List.IsChain.singleton _
  | succ steps ih =>
    apply List.IsChain.cons (ih (start+1) (by omega) (tape.move .left))
    intro next member
    rw [moveTrace_head] at member
    have same : next=state ⟨start+1,by omega⟩ (tape.move .left) := (Option.mem_some_iff.mp member).symm
    subst next
    have small : start<33 := by omega
    simp [state,TM0.step,machine,small]

theorem move_left_word (word left suffix : List Bool) :
    (Tape.move .left)^[word.length] (Tape.mk₂ (word.reverse++left) suffix)=
      Tape.mk₂ left (word++suffix) := by
  induction word using List.reverseRecOn generalizing suffix with
  | nil => rfl
  | append_singleton word bit ih =>
    simp only [List.reverse_append,List.reverse_singleton,List.singleton_append,List.append_assoc,
      List.length_append,List.length_singleton,Function.iterate_succ_apply]
    simpa [Tape.mk₂] using ih (bit::suffix)

theorem row_moves (bottom bit : Bool) (left suffix : List Bool) :
    (Tape.move .left)^[33] (Tape.mk₂ ((PSTRWordBool.RawInit.rowBits bottom bit).reverse++left) suffix)=
      Tape.mk₂ left (PSTRWordBool.RawInit.rowBits bottom bit++suffix) := by
  simpa only [PSTRWordBool.RawInit.rowBits_length] using move_left_word (PSTRWordBool.RawInit.rowBits bottom bit) left suffix

theorem scan_halt (left right : List Bool) : TM0.step machine (state 34 (Tape.mk₂ left (true::right)))=none := by
  simp [TM0.step,machine,state,Tape.mk₂]

end PaperProofs.Common.Native.PA17RawInitRowReturn

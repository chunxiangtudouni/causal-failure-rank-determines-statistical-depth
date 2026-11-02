module
public import PaperProofs.Common.PSTR_TM_MulExpandLift_096

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulExpandUnit097
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulExpandCode095

def modeLabel (base : Fin 111) (bit : Bool) : Fin 112 :=
  ⟨base.val+bit.toNat,by have hb := base.isLt; have hc := Bool.toNat_le bit; omega⟩
def markTrace (digits : List Bool) (a b : Bool) (tail : List Bool) : List (MachineState 111) :=
  let left := PSTRTMRawNat010.leftBlocks digits.reverse
  [state 0 left (a::true::b::true::tail),
    state (modeLabel 1 a) (a::left) (true::b::true::tail),
    state (modeLabel 3 a) left (a::true::b::true::tail),
    state (modeLabel 5 a) left (true::true::b::true::tail),
    state (modeLabel 7 a) (true::left) (true::b::true::tail),
    state (modeLabel 9 a) (true::left) (false::b::true::tail)]
def restoreTrace (digits : List Bool) (a b : Bool) (tail : List Bool) : List (MachineState 111) :=
  let left := PSTRTMRawNat010.leftBlocks digits.reverse
  [state (modeLabel 93 a) left (false::false::true::false::b::true::tail),
    state (modeLabel 95 a) (false::left) (false::true::false::b::true::tail),
    state (modeLabel 97 a) (false::left) (true::true::false::b::true::tail),
    state (modeLabel 99 a) (true::false::left) (true::false::b::true::tail),
    state (modeLabel 101 a) (true::false::left) (a::false::b::true::tail),
    state (modeLabel 103 a) (a::true::false::left) (false::b::true::tail),
    state 105 (a::true::false::left) (true::b::true::tail),
    state 106 (true::a::true::false::left) (b::true::tail),
    state 107 (b::true::a::true::false::left) (true::tail)]
def unitTrace (digits : List Bool) (a b : Bool) (tail : List Bool) : List (MachineState 111) :=
  markTrace digits a b tail ++ (PSTRTMPadTrace035.padTrace digits (b::true::tail)).map (liftPad a) ++
    restoreTrace digits a b tail

theorem mark_head (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (markTrace digits a b tail).head?=some (state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (a::true::b::true::tail)) := rfl
theorem mark_last (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (markTrace digits a b tail).getLast?=some (state (modeLabel 9 a)
      (true::PSTRTMRawNat010.leftBlocks digits.reverse) (false::b::true::tail)) := rfl
theorem restore_head (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (restoreTrace digits a b tail).head?=some (state (modeLabel 93 a)
      (PSTRTMRawNat010.leftBlocks digits.reverse) (false::false::true::false::b::true::tail)) := rfl
theorem restore_last (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (restoreTrace digits a b tail).getLast?=some (state 107
      (b::true::a::true::false::PSTRTMRawNat010.leftBlocks digits.reverse) (true::tail)) := rfl

theorem mark_chain (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (markTrace digits a b tail).IsChain (fun x y => Turing.TM0.step expandMachine x=some y) := by
  cases a <;> simp [markTrace,modeLabel,List.isChain_cons_cons,Turing.TM0.step,expandMachine,state,Turing.Tape.mk₂]
theorem restore_chain (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (restoreTrace digits a b tail).IsChain (fun x y => Turing.TM0.step expandMachine x=some y) := by
  cases a <;> simp [restoreTrace,modeLabel,List.isChain_cons_cons,Turing.TM0.step,expandMachine,state,Turing.Tape.mk₂]

theorem mark_advance (digits : List Bool) (a b : Bool) (tail : List Bool) :
    Turing.TM0.step expandMachine (state (modeLabel 9 a) (true::PSTRTMRawNat010.leftBlocks digits.reverse) (false::b::true::tail))=
      some (liftPad a (PSTRTMPadInsert034.state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (true::false::b::true::tail))) := by
  cases a <;> simp [modeLabel,Turing.TM0.step,expandMachine,state,liftPad,padLabel,PSTRTMPadInsert034.state,Turing.Tape.mk₂]
theorem pad_advance (digits : List Bool) (a b : Bool) (tail : List Bool) :
    Turing.TM0.step expandMachine (liftPad a (PSTRTMPadInsert034.state 40
      (PSTRTMRawNat010.leftBlocks digits.reverse) (false::false::true::false::b::true::tail)))=
      some (state (modeLabel 93 a) (PSTRTMRawNat010.leftBlocks digits.reverse) (false::false::true::false::b::true::tail)) := by
  cases a <;> simp [modeLabel,Turing.TM0.step,expandMachine,state,liftPad,padLabel,PSTRTMPadInsert034.state,Turing.Tape.mk₂]
theorem restore_advance (digits : List Bool) (a b : Bool) (tail : List Bool) :
    Turing.TM0.step expandMachine (state 107
      (b::true::a::true::false::PSTRTMRawNat010.leftBlocks digits.reverse) (true::tail))=
      some (state 0 (PSTRTMRawNat010.leftBlocks (digits++[false,a,b]).reverse) tail) := by
  simp [Turing.TM0.step,expandMachine,state,Turing.Tape.mk₂,PSTRTMRawNat010.leftBlocks,
    List.reverse_append]

private theorem append_link (xs ys : List (MachineState 111)) (last first : MachineState 111)
    (hx : xs.IsChain (fun a b => Turing.TM0.step expandMachine a=some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step expandMachine a=some b))
    (hl : xs.getLast?=some last) (hh : ys.head?=some first)
    (hs : Turing.TM0.step expandMachine last=some first) :
    (xs++ys).IsChain (fun a b => Turing.TM0.step expandMachine a=some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

theorem unit_head (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (unitTrace digits a b tail).head?=some (state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (a::true::b::true::tail)) := by
  simp only [unitTrace,List.head?_append,mark_head,Option.some_or]
theorem unit_last (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (unitTrace digits a b tail).getLast?=some (state 107
      (b::true::a::true::false::PSTRTMRawNat010.leftBlocks digits.reverse) (true::tail)) := by
  simp only [unitTrace,List.getLast?_append,restore_last,Option.some_or]
theorem unit_length (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (unitTrace digits a b tail).length=12*digits.length+25 := by
  simp only [unitTrace,List.length_append,List.length_map,PSTRTMPadTrace035.pad_length,
    markTrace,restoreTrace,List.length_cons,List.length_nil]
  omega

/-- Actual insertion of ONE zero accumulator pair with original A/B kept.
Every marker write, two-cell prefix copy, saved-A restore and move is in
unitTrace. Prefix-shift cost depends on its ACTUAL data length. -/
theorem unit_chain (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (unitTrace digits a b tail).IsChain (fun x y => Turing.TM0.step expandMachine x=some y) := by
  unfold unitTrace
  refine append_link _ _
    (liftPad a (PSTRTMPadInsert034.state 40 (PSTRTMRawNat010.leftBlocks digits.reverse) (false::false::true::false::b::true::tail)))
    _ ?_ (restore_chain digits a b tail) ?_ (restore_head digits a b tail) (pad_advance digits a b tail)
  · exact append_link _ _ _ _ (mark_chain digits a b tail)
      (PSTRTMMulExpandLift096.pad_chain a _ (PSTRTMPadTrace035.pad_chain digits (b::true::tail)))
      (mark_last digits a b tail)
      (by simp only [List.head?_map,PSTRTMPadTrace035.pad_head,Option.map_some])
      (mark_advance digits a b tail)
  · simp only [List.getLast?_append,List.getLast?_map,PSTRTMPadTrace035.pad_last,Option.map_some,Option.some_or]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulExpandUnit097

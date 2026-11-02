module
public import PaperProofs.Common.PSTR_TM_CompactCode_046
public import PaperProofs.Common.PSTR_TM_PackFinish_039

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompactCopy047
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMCompactCode046

def copyUnit (bit x y : Bool) (left right : List Bool) : List (MachineState 54) :=
  (PSTRTMPadTrace035.copyUnit bit x y left right).map liftCopy

theorem copyUnit_head (bit x y : Bool) (left right : List Bool) :
    (copyUnit bit x y left right).head? = some (state 17 (y :: x :: left) (bit :: true :: right)) := by
  simp [copyUnit, List.head?_map, PSTRTMPadTrace035.copyUnit_head, liftCopy, embedCopy,
    PSTRTMPadInsert034.state, state]

theorem copyUnit_last (bit x y : Bool) (left right : List Bool) :
    (copyUnit bit x y left right).getLast? = some (state 31 (bit :: true :: bit :: left) (true :: right)) := by
  simp [copyUnit, List.getLast?_map, PSTRTMPadTrace035.copyUnit_last, liftCopy, embedCopy,
    PSTRTMPadInsert034.state, state]

theorem copyUnit_length (bit x y : Bool) (left right : List Bool) :
    (copyUnit bit x y left right).length = 10 := by
  simp only [copyUnit, List.length_map, PSTRTMPadTrace035.copyUnit_length]

set_option maxHeartbeats 1600000 in
theorem copyUnit_chain (bit x y : Bool) (left right : List Bool) :
    (copyUnit bit x y left right).IsChain (fun before after => Turing.TM0.step compactMachine before = some after) := by
  cases bit <;> simp [copyUnit, PSTRTMPadTrace035.copyUnit, List.isChain_cons_cons,
    Turing.TM0.step, compactMachine, liftCopy, embedCopy, PSTRTMPadInsert034.state,
    PSTRTMPadInsert034.padMachine, PSTRTMPadInsert034.flagMode, PSTRTMPadInsert034.backOne,
    PSTRTMPadInsert034.backTwo, PSTRTMPadInsert034.writeMode, PSTRTMPadInsert034.afterWrite, Turing.Tape.mk₂]

theorem copyUnit_advance (bit : Bool) (left right : List Bool) :
    Turing.TM0.step compactMachine (state 31 (bit :: true :: bit :: left) (true :: right)) =
      some (state 17 (true :: bit :: true :: bit :: left) right) := by
  simp [Turing.TM0.step, compactMachine, state, PSTRTMPadInsert034.padMachine, embedCopy, Turing.Tape.mk₂]

/-- Relocate the endmarker LEFT by two actual cells, erasing its old1.
The new marker flag and every cell beyond it are real false cells. -/
def endTrace (x y : Bool) (left : List Bool) : List (MachineState 54) :=
  [state 17 (y :: x :: left) [true,false],
    state 19 (true :: y :: x :: left) [false],
    state 36 (y :: x :: left) [true,false],
    state 37 (y :: x :: left) [false,false],
    state 38 (x :: left) [y,false,false],
    state 39 (x :: left) [false,false,false],
    state 40 left [x,false,false,false],
    state 41 left [true,false,false,false]]

theorem end_head (x y : Bool) (left : List Bool) :
    (endTrace x y left).head? = some (state 17 (y :: x :: left) [true,false]) := rfl

theorem end_length (x y : Bool) (left : List Bool) : (endTrace x y left).length = 8 := rfl

theorem end_last (x y : Bool) (left : List Bool) :
    (endTrace x y left).getLast? = some (state 41 left [true,false]) := by
  have hb : Turing.ListBlank.mk [true,false,false,false] = Turing.ListBlank.mk [true,false] := by
    simpa only [List.cons_append, List.nil_append, List.replicate_succ, List.replicate_zero] using
      PSTRTMPackFinish039.blank_false_suffix [true,false] 2
  change some (state 41 left [true,false,false,false]) = some (state 41 left [true,false])
  simp only [state, Turing.Tape.mk₂]
  rw [hb]

set_option maxHeartbeats 800000 in
theorem end_chain (x y : Bool) (left : List Bool) :
    (endTrace x y left).IsChain (fun before after => Turing.TM0.step compactMachine before = some after) := by
  simp [endTrace, List.isChain_cons_cons, Turing.TM0.step, compactMachine, state,
    PSTRTMPadInsert034.padMachine, embedCopy, Turing.Tape.mk₂]

private theorem append_link (xs ys : List (MachineState 54)) (last first : MachineState 54)
    (hx : xs.IsChain (fun a b => Turing.TM0.step compactMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step compactMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step compactMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step compactMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def copyTrace (context previous : List Bool) : List Bool → Bool → Bool → List (MachineState 54)
  | [], x, y => endTrace x y (PSTRTMRawNat010.leftBlocks previous ++ context)
  | bit :: later, x, y =>
    copyUnit bit x y (PSTRTMRawNat010.leftBlocks previous ++ context)
      (PSTRTMIncrement009.blocks later ++ [true,false]) ++ copyTrace context (bit :: previous) later bit true

theorem copy_head (context previous digits : List Bool) (x y : Bool) :
    (copyTrace context previous digits x y).head? = some
      (state 17 (y :: x :: (PSTRTMRawNat010.leftBlocks previous ++ context))
        (PSTRTMIncrement009.blocks digits ++ [true,false])) := by
  cases digits with
  | nil => rfl
  | cons bit later => simp [copyTrace, List.head?_append, copyUnit_head, PSTRTMIncrement009.blocks]

theorem copy_last (context previous digits : List Bool) (x y : Bool) :
    (copyTrace context previous digits x y).getLast? = some
      (state 41 (PSTRTMRawNat010.leftBlocks (digits.reverse ++ previous) ++ context) [true,false]) := by
  induction digits generalizing previous x y with
  | nil => exact end_last x y _
  | cons bit later ih =>
    simp [copyTrace, List.getLast?_append, ih, List.reverse_cons, List.append_assoc]

theorem copy_length (context previous digits : List Bool) (x y : Bool) :
    (copyTrace context previous digits x y).length = 10 * digits.length + 8 := by
  induction digits generalizing previous x y with
  | nil => rfl
  | cons bit later ih =>
    simp only [copyTrace, List.length_append, copyUnit_length, ih, List.length_cons]
    omega

theorem copy_chain (context previous digits : List Bool) (x y : Bool) :
    (copyTrace context previous digits x y).IsChain (fun before after => Turing.TM0.step compactMachine before = some after) := by
  induction digits generalizing previous x y with
  | nil => exact end_chain x y _
  | cons bit later ih =>
    rw [copyTrace]
    apply append_link _ _ _ _ (copyUnit_chain bit x y _ _) (ih (bit :: previous) bit true)
      (copyUnit_last bit x y _ _) (copy_head context (bit :: previous) later bit true)
    simpa only [PSTRTMRawNat010.leftBlocks, List.flatMap_cons, List.cons_append, List.nil_append] using
      copyUnit_advance bit (PSTRTMRawNat010.leftBlocks previous ++ context)
        (PSTRTMIncrement009.blocks later ++ [true,false])

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompactCopy047

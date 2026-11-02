module
public import PaperProofs.Common.PSTR_TM_PackLift_037

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackColumns038
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036 PSTRTMPackLift037

private theorem append_link (xs ys : List (MachineState 193)) (last first : MachineState 193)
    (hx : xs.IsChain (fun a b => Turing.TM0.step packMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step packMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step packMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step packMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def dispatchFlag (a : Bool) : Fin 194 := if a then 2 else 1

def dispatchTrace (a : Bool) (left right : List Bool) : List (MachineState 193) :=
  [state 0 left (a :: true :: right), state (dispatchFlag a) (a :: left) (true :: right)]

theorem dispatch_chain (a : Bool) (left right : List Bool) :
    (dispatchTrace a left right).IsChain (fun before after => Turing.TM0.step packMachine before = some after) := by
  cases a <;> simp [dispatchTrace, List.isChain_cons_cons, dispatchFlag,
    Turing.TM0.step, packMachine, state, Turing.Tape.mk₂]

theorem dispatch_enter (a : Bool) (left right : List Bool) :
    Turing.TM0.step packMachine (state (dispatchFlag a) (a :: left) (true :: right)) =
      some (liftAlign (PSTRTMAlignCode030.state 0 left (a :: true :: right))) := by
  cases a <;> simp [dispatchFlag, Turing.TM0.step, packMachine, state,
    liftAlign, embedAlign, PSTRTMAlignCode030.state, Turing.Tape.mk₂]

/-- Both nonempty operands consume exactly one real digit each. -/
def columnTrace (a b : Bool) (left first tail : List Bool) : List (MachineState 193) :=
  let right := PSTRTMIncrement009.blocks first ++ false :: false :: true :: false :: b :: true :: tail
  dispatchTrace a left right ++
    ((PSTRTMAlignUnit032.alignTrace a b left first tail).map liftAlign ++
      [state 0 (true :: b :: true :: a :: left)
        (PSTRTMIncrement009.blocks first ++ false :: false :: true :: false :: tail)])

theorem column_head (a b : Bool) (left first tail : List Bool) :
    (columnTrace a b left first tail).head? = some
      (state 0 left (a :: true :: (PSTRTMIncrement009.blocks first ++ false :: false :: true :: false :: b :: true :: tail))) := rfl

theorem column_last (a b : Bool) (left first tail : List Bool) :
    (columnTrace a b left first tail).getLast? = some
      (state 0 (true :: b :: true :: a :: left)
        (PSTRTMIncrement009.blocks first ++ false :: false :: true :: false :: tail)) := by
  simp [columnTrace, List.getLast?_append]

theorem column_length (a b : Bool) (left first tail : List Bool) :
    (columnTrace a b left first tail).length = 12 * first.length + 40 := by
  simp only [columnTrace, dispatchTrace, List.length_append, List.length_map,
    List.length_cons, List.length_nil, PSTRTMAlignUnit032.align_length]
  omega

theorem column_chain (a b : Bool) (left first tail : List Bool) :
    (columnTrace a b left first tail).IsChain (fun before after => Turing.TM0.step packMachine before = some after) := by
  let right := PSTRTMIncrement009.blocks first ++ false :: false :: true :: false :: b :: true :: tail
  have htail := append_link
    ((PSTRTMAlignUnit032.alignTrace a b left first tail).map liftAlign)
    [state 0 (true :: b :: true :: a :: left)
      (PSTRTMIncrement009.blocks first ++ false :: false :: true :: false :: tail)] _ _
    (PSTRTMPackLift037.align_chain _ (PSTRTMAlignUnit032.align_chain a b left first tail)) (.singleton _)
    (by simp only [List.getLast?_map, PSTRTMAlignUnit032.align_last, Option.map_some]) rfl
    (align_transfer _ _)
  have hh : (((PSTRTMAlignUnit032.alignTrace a b left first tail).map liftAlign) ++
      [state 0 (true :: b :: true :: a :: left)
        (PSTRTMIncrement009.blocks first ++ false :: false :: true :: false :: tail)]).head? = some
          (liftAlign (PSTRTMAlignCode030.state 0 left (a :: true :: right))) := by
    simp [List.head?_append, List.head?_map, PSTRTMAlignUnit032.align_head, right]
  exact append_link _ _ _ _ (dispatch_chain a left right) htail rfl hh (dispatch_enter a left right)

/-- The dispatch recognizes the actual remaining10 pair and calls the
real two-cell repair program on the retained output prefix. -/
def repairTrace (digits tail : List Bool) : List (MachineState 193) :=
  [state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (true :: false :: tail),
    state 2 (true :: PSTRTMRawNat010.leftBlocks digits.reverse) (false :: tail)] ++
  ((PSTRTMPadTrace035.padTrace digits tail).map liftPad ++
    [state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (false :: false :: true :: false :: tail)])

theorem repair_head (digits tail : List Bool) :
    (repairTrace digits tail).head? = some
      (state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (true :: false :: tail)) := rfl

theorem repair_last (digits tail : List Bool) :
    (repairTrace digits tail).getLast? = some
      (state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (false :: false :: true :: false :: tail)) := by
  rw [repairTrace, ← List.append_assoc, List.getLast?_append]
  rfl

theorem repair_length (digits tail : List Bool) :
    (repairTrace digits tail).length = 12 * digits.length + 13 := by
  simp only [repairTrace, List.length_append, List.length_map, List.length_cons,
    List.length_nil, PSTRTMPadTrace035.pad_length]
  omega

theorem repair_chain (digits tail : List Bool) :
    (repairTrace digits tail).IsChain (fun before after => Turing.TM0.step packMachine before = some after) := by
  have htail := append_link
    ((PSTRTMPadTrace035.padTrace digits tail).map liftPad)
    [state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (false :: false :: true :: false :: tail)] _ _
    (PSTRTMPackLift037.pad_chain _ (PSTRTMPadTrace035.pad_chain digits tail)) (.singleton _)
    (by simp only [List.getLast?_map, PSTRTMPadTrace035.pad_last, Option.map_some]) rfl
    (pad_transfer _ _)
  have hh : (((PSTRTMPadTrace035.padTrace digits tail).map liftPad) ++
      [state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (false :: false :: true :: false :: tail)]).head? = some
        (liftPad (PSTRTMPadInsert034.state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (true :: false :: tail))) := by
    simp [List.head?_append, List.head?_map, PSTRTMPadTrace035.pad_head]
  refine append_link _ _ _ _ ?_ htail rfl hh ?_
  · simp [List.isChain_cons_cons, Turing.TM0.step, packMachine, state, Turing.Tape.mk₂]
  · simp [Turing.TM0.step, packMachine, state, liftPad, embedPad, PSTRTMPadInsert034.state, Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackColumns038

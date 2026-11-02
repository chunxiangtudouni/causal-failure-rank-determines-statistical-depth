module
public import Common.PSTR_TM_PackColumns_038

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackZeroA041
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036

private theorem nextPhase_one : PSTRTMAlignCode030.nextPhase (1 : Fin 3) = 0 := by decide

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

def endATrace (bit : Bool) (left tail : List Bool) : List (MachineState 193) :=
  [state 0 left (false :: false :: true :: false :: bit :: true :: tail),
    state 1 (false :: left) (false :: true :: false :: bit :: true :: tail),
    state 3 (false :: false :: left) (true :: false :: bit :: true :: tail),
    state 4 (true :: false :: false :: left) (false :: bit :: true :: tail),
    state 5 (false :: true :: false :: false :: left) (bit :: true :: tail),
    state (if bit then 7 else 6) (bit :: false :: true :: false :: false :: left) (true :: tail)]

set_option maxHeartbeats 800000 in
theorem endA_chain (bit : Bool) (left tail : List Bool) :
    (endATrace bit left tail).IsChain (fun before after => Turing.TM0.step packMachine before = some after) := by
  cases bit <;> simp [endATrace, List.isChain_cons_cons, Turing.TM0.step, packMachine, state, Turing.Tape.mk₂]

theorem endA_enter (bit : Bool) (left tail : List Bool) :
    Turing.TM0.step packMachine
      (state (if bit then 7 else 6) (bit :: false :: true :: false :: false :: left) (true :: tail)) =
      some (liftAlign (PSTRTMAlignCode030.state (PSTRTMAlignCode030.hole 1 bit)
        (false :: true :: false :: false :: left) (bit :: true :: tail))) := by
  cases bit <;> simp [Turing.TM0.step, packMachine, state, liftAlign, embedAlign,
    PSTRTMAlignCode030.state, PSTRTMAlignCode030.hole, Turing.Tape.mk₂]

def oneSeparatorTrace (bit : Bool) (left tail : List Bool) : List (MachineState 134) :=
  PSTRTMAlignShift031.shiftTrace 1 bit false true (false :: false :: left) bit true tail ++
    PSTRTMAlignShift031.fillTrace bit false left true false (true :: false :: tail)

theorem oneSeparator_head (bit : Bool) (left tail : List Bool) :
    (oneSeparatorTrace bit left tail).head? = some
      (PSTRTMAlignCode030.state (PSTRTMAlignCode030.hole 1 bit)
        (false :: true :: false :: false :: left) (bit :: true :: tail)) := by
  simp [oneSeparatorTrace, List.head?_append, PSTRTMAlignShift031.shift_head]

theorem oneSeparator_last (bit : Bool) (left tail : List Bool) :
    (oneSeparatorTrace bit left tail).getLast? = some
      (PSTRTMAlignCode030.state 134 (true :: bit :: true :: false :: left) (true :: false :: tail)) := by
  simp [oneSeparatorTrace, List.getLast?_append, PSTRTMAlignShift031.fill_last]

theorem oneSeparator_length (bit : Bool) (left tail : List Bool) :
    (oneSeparatorTrace bit left tail).length = 18 := by
  simp only [oneSeparatorTrace, List.length_append, PSTRTMAlignShift031.shift_length,
    PSTRTMAlignShift031.fill_length]

theorem oneSeparator_chain (bit : Bool) (left tail : List Bool) :
    (oneSeparatorTrace bit left tail).IsChain (fun before after =>
      Turing.TM0.step PSTRTMAlignCode030.alignMachine before = some after) := by
  apply (PSTRTMAlignShift031.shift_chain 1 bit false true (false :: false :: left) bit true tail
    (Or.inl (by decide))).append (PSTRTMAlignShift031.fill_chain bit false left true false (true :: false :: tail))
  intro before hb after ha
  simp only [PSTRTMAlignShift031.shift_last, Option.mem_some_iff] at hb
  simp only [PSTRTMAlignShift031.fill_head, Option.mem_some_iff] at ha
  subst before
  subst after
  simpa only [nextPhase_one] using
    PSTRTMAlignShift031.shift_advance 1 bit false true (false :: false :: left) tail

/-- An actual B digit is paired with0 when A is empty. The old00 pad
is consumed as the virtual A pair; the resulting10 is repaired by034. -/
def zeroATrace (bit : Bool) (left tail : List Bool) : List (MachineState 193) :=
  endATrace bit left tail ++ ((oneSeparatorTrace bit left tail).map liftAlign ++
    [state 0 (true :: bit :: true :: false :: left) (true :: false :: tail)])

theorem zeroA_head (bit : Bool) (left tail : List Bool) :
    (zeroATrace bit left tail).head? = some
      (state 0 left (false :: false :: true :: false :: bit :: true :: tail)) := rfl

theorem zeroA_last (bit : Bool) (left tail : List Bool) :
    (zeroATrace bit left tail).getLast? = some
      (state 0 (true :: bit :: true :: false :: left) (true :: false :: tail)) := by
  simp [zeroATrace, List.getLast?_append]

theorem zeroA_length (bit : Bool) (left tail : List Bool) :
    (zeroATrace bit left tail).length = 25 := by
  simp only [zeroATrace, List.length_append, List.length_map, oneSeparator_length,
    endATrace, List.length_cons, List.length_nil]

theorem zeroA_chain (bit : Bool) (left tail : List Bool) :
    (zeroATrace bit left tail).IsChain (fun before after => Turing.TM0.step packMachine before = some after) := by
  have htail := append_link ((oneSeparatorTrace bit left tail).map liftAlign)
    [state 0 (true :: bit :: true :: false :: left) (true :: false :: tail)] _ _
    (PSTRTMPackLift037.align_chain _ (oneSeparator_chain bit left tail)) (.singleton _)
    (by simp only [List.getLast?_map, oneSeparator_last, Option.map_some]) rfl
    (PSTRTMPackLift037.align_transfer _ _)
  have hh : (((oneSeparatorTrace bit left tail).map liftAlign) ++
      [state 0 (true :: bit :: true :: false :: left) (true :: false :: tail)]).head? = some
        (liftAlign (PSTRTMAlignCode030.state (PSTRTMAlignCode030.hole 1 bit)
          (false :: true :: false :: false :: left) (bit :: true :: tail))) := by
    simp [List.head?_append, List.head?_map, oneSeparator_head]
  exact append_link _ _ _ _ (endA_chain bit left tail) htail rfl hh (endA_enter bit left tail)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackZeroA041

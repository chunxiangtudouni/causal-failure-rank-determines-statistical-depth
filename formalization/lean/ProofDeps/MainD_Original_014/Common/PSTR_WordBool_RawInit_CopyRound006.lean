module

public import Common.PSTR_WordBool_RawInit_CopyWalk005

/-! One real MSB-to-LSB header-copy round. The selected source flag alone
is zero during the shuttle; its bit is held in finite control, appended to
the far-left bank, and its source flag is restored before LEFT2 selects
the next bit. Neither the code nor this witness construction is given a
runtime length or an externally computed count. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.HeaderCopy

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMRawNat010 PSTRTMIncrement009

def bank (copied : List Bool) : List Bool := leftBlocks copied.reverse

theorem bank_cons (bit : Bool) (copied : List Bool) :
    bank (bit :: copied) = bank copied ++ [true,bit] := by
  simp only [bank, List.reverse_cons, leftBlocks, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

def workRight (copied tail : List Bool) : List Bool := blocks copied ++ false :: false :: tail

def loopStart (remaining copied tail : List Bool) : MachineState 41 :=
  match remaining with
  | [] => coreState 2 (false :: bank copied) (false :: workRight copied tail)
  | bit :: lower => coreState 2
      (bit :: (leftBlocks lower ++ false :: false :: bank copied)) (true :: workRight copied tail)

def roundLast (bit : Bool) (lower copied tail : List Bool) : MachineState 41 :=
  coreState (roundLabel bit 17) (leftBlocks lower ++ false :: false :: bank (bit :: copied))
    (bit :: true :: workRight copied tail)

def prefixPart (bit : Bool) (lower copied tail : List Bool) : List (MachineState 41) :=
  [loopStart (bit :: lower) copied tail,
   coreState 3 (leftBlocks lower ++ false :: false :: bank copied)
     (bit :: true :: workRight copied tail),
   coreState (roundLabel bit 0) (bit :: (leftBlocks lower ++ false :: false :: bank copied))
     (true :: workRight copied tail),
   coreState (roundLabel bit 1) (bit :: (leftBlocks lower ++ false :: false :: bank copied))
     (false :: workRight copied tail),
   coreState (roundLabel bit 2) (leftBlocks lower ++ false :: false :: bank copied)
     (bit :: false :: workRight copied tail)]

def workLeftPart (bit : Bool) (lower copied tail : List Bool) : List (MachineState 41) :=
  leftTrace false bit (false :: bank copied) lower (bit :: false :: workRight copied tail)

def bankBridge (bit : Bool) (lower copied tail : List Bool) : List (MachineState 41) :=
  [coreState (roundLabel bit 5) (bank copied)
    (false :: false :: (blocks lower.reverse ++ bit :: false :: workRight copied tail))]

def bankLeftPart (bit : Bool) (lower copied tail : List Bool) : List (MachineState 41) :=
  leftTrace true bit [] copied.reverse
    (false :: false :: (blocks lower.reverse ++ bit :: false :: workRight copied tail))

def bankWrites (bit : Bool) (lower copied tail : List Bool) : List (MachineState 41) :=
  [coreState (roundLabel bit 8) []
     (true :: (blocks copied ++ false :: false :: (blocks lower.reverse ++ bit :: false :: workRight copied tail))),
   coreState (roundLabel bit 9) []
     (false :: true :: (blocks copied ++ false :: false :: (blocks lower.reverse ++ bit :: false :: workRight copied tail))),
   coreState (roundLabel bit 10) []
     (bit :: true :: (blocks copied ++ false :: false :: (blocks lower.reverse ++ bit :: false :: workRight copied tail))),
   coreState (roundLabel bit 11) [bit]
     (true :: (blocks copied ++ false :: false :: (blocks lower.reverse ++ bit :: false :: workRight copied tail)))]

def bankRightPart (bit : Bool) (lower copied tail : List Bool) : List (MachineState 41) :=
  rightTrace 0 bit [true,bit] copied false (blocks lower.reverse ++ bit :: false :: workRight copied tail)

def workRightPart (bit : Bool) (lower copied tail : List Bool) : List (MachineState 41) :=
  rightTrace 1 bit (false :: false :: bank (bit :: copied)) lower.reverse bit (workRight copied tail)

def restorePart (bit : Bool) (lower copied tail : List Bool) : List (MachineState 41) :=
  [coreState (roundLabel bit 16) (bit :: (leftBlocks lower ++ false :: false :: bank (bit :: copied)))
     (true :: workRight copied tail),
   roundLast bit lower copied tail]

def roundTrace (bit : Bool) (lower copied tail : List Bool) : List (MachineState 41) :=
  prefixPart bit lower copied tail ++ workLeftPart bit lower copied tail ++
    bankBridge bit lower copied tail ++ bankLeftPart bit lower copied tail ++
    bankWrites bit lower copied tail ++ bankRightPart bit lower copied tail ++
    workRightPart bit lower copied tail ++ restorePart bit lower copied tail

theorem round_head (bit : Bool) (lower copied tail : List Bool) :
    (roundTrace bit lower copied tail).head? = some (loopStart (bit :: lower) copied tail) := by
  simp only [roundTrace, prefixPart, List.head?_append, List.head?_cons, Option.some_or]

theorem round_last (bit : Bool) (lower copied tail : List Bool) :
    (roundTrace bit lower copied tail).getLast? = some (roundLast bit lower copied tail) := by
  simp only [roundTrace, restorePart, List.getLast?_append,
    List.getLast?_cons_cons, List.getLast?_singleton, Option.some_or]

theorem round_length (bit : Bool) (lower copied tail : List Bool) :
    (roundTrace bit lower copied tail).length = 4 * (lower.length + copied.length) + 18 := by
  simp only [roundTrace, prefixPart, workLeftPart, bankBridge, bankLeftPart, bankWrites,
    bankRightPart, workRightPart, restorePart, List.length_append, List.length_cons,
    List.length_nil, left_length, right_length, List.length_reverse]
  omega

theorem prefix_chain (bit : Bool) (lower copied tail : List Bool) :
    (prefixPart bit lower copied tail).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
  cases bit <;> simp [prefixPart, loopStart, List.isChain_cons_cons, coreState,
    TM0.step, coreMachine, roundLabel, roundCode, Tape.mk₂]

theorem writes_chain (bit : Bool) (lower copied tail : List Bool) :
    (bankWrites bit lower copied tail).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
  cases bit <;> simp [bankWrites, List.isChain_cons_cons, coreState,
    TM0.step, coreMachine, roundLabel, roundCode, Tape.mk₂]

theorem restore_chain (bit : Bool) (lower copied tail : List Bool) :
    (restorePart bit lower copied tail).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
  cases bit <;> simp [restorePart, roundLast, List.isChain_cons_cons, coreState,
    TM0.step, coreMachine, roundLabel, roundCode, Tape.mk₂]

private theorem join_chain
    {first second : List (MachineState 41)} {last next : MachineState 41}
    (hf : first.IsChain (fun before after => TM0.step coreMachine before = some after))
    (hs : second.IsChain (fun before after => TM0.step coreMachine before = some after))
    (hl : first.getLast? = some last) (hh : second.head? = some next)
    (edge : TM0.step coreMachine last = some next) :
    (first ++ second).IsChain (fun before after => TM0.step coreMachine before = some after) := by
  apply hf.append hs
  intro before beforeLast after afterHead
  simp only [hl, Option.mem_some_iff] at beforeLast
  simp only [hh, Option.mem_some_iff] at afterHead
  subst before
  subst after
  exact edge

theorem round_chain (bit : Bool) (lower copied tail : List Bool) :
    (roundTrace bit lower copied tail).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
  have h1 : (prefixPart bit lower copied tail ++ workLeftPart bit lower copied tail).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
    apply join_chain (prefix_chain bit lower copied tail)
      (left_chain false bit (false :: bank copied) lower (bit :: false :: workRight copied tail))
      (by rfl) (left_head false bit (false :: bank copied) lower (bit :: false :: workRight copied tail))
    cases lower <;> cases bit <;>
      simp [leftStart, leftFlag, coreState, TM0.step, coreMachine, roundLabel, roundCode, Tape.mk₂, leftBlocks]
  have h2 : ((prefixPart bit lower copied tail ++ workLeftPart bit lower copied tail) ++
      bankBridge bit lower copied tail).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
    apply join_chain h1 (.singleton _)
      (by
        simp only [List.getLast?_append, workLeftPart, left_last, Option.some_or]
        rfl) (by rfl)
    cases bit <;> simp [leftFlag, coreState, TM0.step, coreMachine, roundLabel, roundCode, Tape.mk₂]
  have h3 : (((prefixPart bit lower copied tail ++ workLeftPart bit lower copied tail) ++
      bankBridge bit lower copied tail) ++ bankLeftPart bit lower copied tail).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
    apply join_chain h2
      (left_chain true bit [] copied.reverse
        (false :: false :: (blocks lower.reverse ++ bit :: false :: workRight copied tail)))
      (by
        simp only [List.getLast?_append, bankBridge, List.getLast?_singleton, Option.some_or]
        rfl)
      (left_head true bit [] copied.reverse
        (false :: false :: (blocks lower.reverse ++ bit :: false :: workRight copied tail)))
    cases shape : copied.reverse <;> cases bit <;>
      simp [leftStart, leftFlag, bank, shape, coreState, TM0.step, coreMachine,
        roundLabel, roundCode, Tape.mk₂, leftBlocks]
    all_goals simp only [← List.cons_append, blank_append_false]
  have h4 : ((((prefixPart bit lower copied tail ++ workLeftPart bit lower copied tail) ++
      bankBridge bit lower copied tail) ++ bankLeftPart bit lower copied tail) ++
      bankWrites bit lower copied tail).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
    apply join_chain h3 (writes_chain bit lower copied tail)
      (by
        simp only [List.getLast?_append, bankLeftPart, left_last, List.reverse_reverse, Option.some_or]
        rfl)
      (by rfl)
    cases bit <;> simp [leftFlag, coreState, TM0.step, coreMachine, roundLabel, roundCode, Tape.mk₂]
  have h5 : (((((prefixPart bit lower copied tail ++ workLeftPart bit lower copied tail) ++
      bankBridge bit lower copied tail) ++ bankLeftPart bit lower copied tail) ++
      bankWrites bit lower copied tail) ++ bankRightPart bit lower copied tail).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
    apply join_chain h4
      (right_chain 0 bit false [true,bit] copied (blocks lower.reverse ++ bit :: false :: workRight copied tail))
      (by
        simp only [List.getLast?_append, bankWrites, List.getLast?_cons_cons,
        List.getLast?_singleton, Option.some_or]
        rfl)
      (right_head 0 bit false [true,bit] copied (blocks lower.reverse ++ bit :: false :: workRight copied tail))
    cases bit <;> simp [rightData, coreState, TM0.step, coreMachine, roundLabel, roundCode, Tape.mk₂]
  have h6 : ((((((prefixPart bit lower copied tail ++ workLeftPart bit lower copied tail) ++
      bankBridge bit lower copied tail) ++ bankLeftPart bit lower copied tail) ++
      bankWrites bit lower copied tail) ++ bankRightPart bit lower copied tail) ++
      workRightPart bit lower copied tail).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
    apply join_chain h5
      (right_chain 1 bit bit (false :: false :: bank (bit :: copied)) lower.reverse (workRight copied tail))
      (by
        simp only [List.getLast?_append, bankRightPart, right_last, Option.some_or]
        rfl)
      (right_head 1 bit bit (false :: false :: bank (bit :: copied)) lower.reverse (workRight copied tail))
    cases bit <;> simp [rightFlag, rightData, bank_cons, coreState, TM0.step,
      coreMachine, roundLabel, roundCode, Tape.mk₂]
    all_goals rfl
  have h7 : (((((((prefixPart bit lower copied tail ++ workLeftPart bit lower copied tail) ++
      bankBridge bit lower copied tail) ++ bankLeftPart bit lower copied tail) ++
      bankWrites bit lower copied tail) ++ bankRightPart bit lower copied tail) ++
      workRightPart bit lower copied tail) ++ restorePart bit lower copied tail).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
    apply join_chain h6 (restore_chain bit lower copied tail)
      (by
        simp only [List.getLast?_append, workRightPart, right_last, List.reverse_reverse, Option.some_or]
        rfl)
      (by rfl)
    cases bit <;> simp [rightFlag, coreState, TM0.step, coreMachine, roundLabel, roundCode, Tape.mk₂]
  exact h7

theorem round_next (bit : Bool) (lower copied tail : List Bool) :
    TM0.step coreMachine (roundLast bit lower copied tail) =
      some (loopStart lower (bit :: copied) tail) := by
  cases lower <;> cases bit <;>
    simp [roundLast, loopStart, workRight, blocks, leftBlocks, coreState,
      TM0.step, coreMachine, roundLabel, roundCode, Tape.mk₂]

end PaperProofs.Common.Native.PSTRWordBool.RawInit.HeaderCopy

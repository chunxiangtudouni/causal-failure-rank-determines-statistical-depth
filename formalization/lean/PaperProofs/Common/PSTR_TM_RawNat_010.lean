module
public import PaperProofs.Common.PSTR_TM_Header_003
public import PaperProofs.Common.PSTR_TM_Increment_009
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMRawNat010
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrace002 PSTRTMHeader003

/-- Actual in-place decoder of a unary BIT-LENGTH header followed by that
many binary payload bits. No numeric operand has been changed to unary. -/
def rawNatMachine : Machine 16 := fun q symbol =>
  match q.val with
  | 0 => if symbol then some (1, .write false) else some (12, .move .left)
  | 1 => some (2, .move .right)
  | 2 => some (if symbol then 2 else 3, .move .right)
  | 3 => some (if symbol then 5 else 4, .write false)
  | 4 => some (6, .move .left)
  | 5 => some (7, .move .left)
  | 6 => some (8, .write true)
  | 7 => some (9, .write true)
  | 8 => some (10, .move .left)
  | 9 => some (11, .move .left)
  | 10 => if symbol then some (10, .move .left) else some (14, .write false)
  | 11 => if symbol then some (11, .move .left) else some (14, .write true)
  | 12 => some (if symbol then 13 else 16, if symbol then .move .left else .move .right)
  | 13 => some (12, .move .left)
  | 14 => some (15, .move .right)
  | 15 => some (0, .move .right)
  | _ => none

def state (q : Fin 17) (left right : List Bool) : MachineState 16 :=
  ⟨q, Turing.Tape.mk₂ left right⟩

def scanRight : Nat → List Bool → List Bool → List (MachineState 16)
  | 0, left, tail => [state 2 left (false :: tail)]
  | n + 1, left, tail =>
    state 2 left (List.replicate (n + 1) true ++ false :: tail) :: scanRight n (true :: left) tail

theorem scanRight_head (n : Nat) (left tail : List Bool) :
    (scanRight n left tail).head? = some (state 2 left (List.replicate n true ++ false :: tail)) := by
  cases n <;> rfl

theorem scanRight_length (n : Nat) (left tail : List Bool) : (scanRight n left tail).length = n + 1 := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih => simp only [scanRight, List.length_cons, ih]

theorem scanRight_chain (n : Nat) (left tail : List Bool) :
    (scanRight n left tail).IsChain (fun before after =>
      Turing.TM0.step rawNatMachine before = some after) := by
  induction n generalizing left with
  | zero => exact .singleton _
  | succ n ih =>
    rw [scanRight]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      simp only [scanRight_head, Option.mem_some_iff] at ha
      subst after
      simp [Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂, List.replicate_succ]
    · exact ih _

theorem scanRight_last (n : Nat) (left tail : List Bool) :
    (scanRight n left tail).getLast? =
      some (state 2 (List.replicate n true ++ left) (false :: tail)) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
    have hne : scanRight n (true :: left) tail ≠ [] := by
      have hlen := scanRight_length n (true :: left) tail
      intro h
      simp [h] at hlen
    rw [scanRight, List.getLast?_cons_of_ne_nil hne, ih, replicate_push]

def leftMode (bit : Bool) : Fin 17 := if bit then 11 else 10

def scanLeftInitial (bit : Bool) : Nat → List Bool → List Bool → MachineState 16
  | 0, left, tail => state (leftMode bit) left (false :: tail)
  | n + 1, left, tail =>
    state (leftMode bit) (List.replicate n true ++ false :: left) (true :: tail)

def scanLeft (bit : Bool) : Nat → List Bool → List Bool → List (MachineState 16)
  | 0, left, tail => [state (leftMode bit) left (false :: tail)]
  | n + 1, left, tail =>
    state (leftMode bit) (List.replicate n true ++ false :: left) (true :: tail) ::
      scanLeft bit n left (true :: tail)

theorem scanLeft_head (bit : Bool) (n : Nat) (left tail : List Bool) :
    (scanLeft bit n left tail).head? = some (scanLeftInitial bit n left tail) := by
  cases n <;> rfl

theorem scanLeft_length (bit : Bool) (n : Nat) (left tail : List Bool) :
    (scanLeft bit n left tail).length = n + 1 := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih => simp only [scanLeft, List.length_cons, ih]

theorem scanLeft_chain (bit : Bool) (n : Nat) (left tail : List Bool) :
    (scanLeft bit n left tail).IsChain (fun before after =>
      Turing.TM0.step rawNatMachine before = some after) := by
  induction n generalizing tail with
  | zero => exact .singleton _
  | succ n ih =>
    rw [scanLeft]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      simp only [scanLeft_head, Option.mem_some_iff] at ha
      subst after
      cases n <;> cases bit <;>
        simp [scanLeftInitial, leftMode, Turing.TM0.step, rawNatMachine, state,
          Turing.Tape.mk₂, List.replicate_succ]
    · exact ih _

theorem scanLeft_last (bit : Bool) (n : Nat) (left tail : List Bool) :
    (scanLeft bit n left tail).getLast? =
      some (state (leftMode bit) left (false :: (List.replicate n true ++ tail))) := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih =>
    have hne : scanLeft bit n left (true :: tail) ≠ [] := by
      have hlen := scanLeft_length bit n left (true :: tail)
      intro h
      simp [h] at hlen
    rw [scanLeft, List.getLast?_cons_of_ne_nil hne, ih, replicate_push]

/-- Nearest logical digit first; each left-facing cell is flag then data. -/
def leftBlocks (reversedDigits : List Bool) : List Bool :=
  reversedDigits.flatMap (fun bit => [true, bit])

def rewindInitial : List Bool → List Bool → MachineState 16
  | [], right => state 12 [] (false :: right)
  | bit :: previous, right => state 12 (bit :: leftBlocks previous) (true :: right)

def rewindTrace : List Bool → List Bool → List (MachineState 16)
  | [], right => [state 12 [] (false :: right), state 16 [false] right]
  | bit :: previous, right =>
    state 12 (bit :: leftBlocks previous) (true :: right) ::
    state 13 (leftBlocks previous) (bit :: true :: right) :: rewindTrace previous (bit :: true :: right)

theorem rewind_head (previous right : List Bool) :
    (rewindTrace previous right).head? = some (rewindInitial previous right) := by
  cases previous <;> rfl

theorem rewind_length (previous right : List Bool) :
    (rewindTrace previous right).length = 2 * previous.length + 2 := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    have h := ih (bit :: true :: right)
    change (rewindTrace previous (bit :: true :: right)).length + 1 + 1 = 2 * (previous.length + 1) + 2
    omega

theorem rewind_chain (previous right : List Bool) :
    (rewindTrace previous right).IsChain (fun before after =>
      Turing.TM0.step rawNatMachine before = some after) := by
  induction previous generalizing right with
  | nil =>
    simp only [rewindTrace, List.isChain_cons_cons, List.isChain_singleton, and_true]
    simp [Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂]
  | cons bit previous ih =>
    rw [rewindTrace]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      simp only [rewind_head, Option.mem_some_iff] at ha
      subst after
      cases previous <;>
        simp [rewindInitial, leftBlocks, Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂]
    · exact ih _

theorem rewind_last (previous right : List Bool) :
    (rewindTrace previous right).getLast? =
      some (state 16 [false] (PSTRTMIncrement009.blocks previous.reverse ++ right)) := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    have hne : rewindTrace previous (bit :: true :: right) ≠ [] := by
      have hlen := rewind_length previous (bit :: true :: right)
      intro h
      simp [h] at hlen
    simp only [rewindTrace, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp [PSTRTMIncrement009.blocks, List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem rawNat_halt (left right : List Bool) :
    Turing.TM0.step rawNatMachine (state 16 left right) = none := by
  simp [Turing.TM0.step, rawNatMachine, state]

def doneTrace (previous suffix : List Bool) : List (MachineState 16) :=
  state 0 (leftBlocks previous) (false :: suffix) :: rewindTrace previous (false :: suffix)

theorem done_head (previous suffix : List Bool) :
    (doneTrace previous suffix).head? = some (state 0 (leftBlocks previous) (false :: suffix)) := rfl

theorem done_chain (previous suffix : List Bool) :
    (doneTrace previous suffix).IsChain (fun before after =>
      Turing.TM0.step rawNatMachine before = some after) := by
  rw [doneTrace]
  apply List.isChain_cons.mpr
  constructor
  · intro after ha
    simp only [rewind_head, Option.mem_some_iff] at ha
    subst after
    cases previous <;>
      simp [rewindInitial, leftBlocks, Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂]
  · exact rewind_chain _ _

theorem done_length (previous suffix : List Bool) :
    (doneTrace previous suffix).length = 2 * previous.length + 3 := by
  have h := rewind_length previous (false :: suffix)
  change (rewindTrace previous (false :: suffix)).length + 1 = _
  omega

theorem done_last (previous suffix : List Bool) :
    (doneTrace previous suffix).getLast? =
      some (state 16 [false] (PSTRTMIncrement009.blocks previous.reverse ++ false :: suffix)) := by
  have hne : rewindTrace previous (false :: suffix) ≠ [] := by
    have hlen := rewind_length previous (false :: suffix)
    intro h
    simp [h] at hlen
  exact (List.getLast?_cons_of_ne_nil hne).trans (rewind_last previous _)

def payloadMode (bit : Bool) : Fin 17 := if bit then 5 else 4
def markerMode (bit : Bool) : Fin 17 := if bit then 7 else 6
def leftStartMode (bit : Bool) : Fin 17 := if bit then 9 else 8

/-- One in-place rotation 1^(k+1) 0 b rest ↦ b 1^(k+1) 0 rest.
The final state15 is immediately followed by the next real state0 call;
no semantic state is supplied to the runtime. All metadata is on the tape. -/
def unitTrace (bit : Bool) (previous later suffix : List Bool) : List (MachineState 16) :=
  let k := later.length
  let left := leftBlocks previous
  let tail := later ++ suffix
  [state 0 left (List.replicate (k + 1) true ++ false :: bit :: tail),
    state 1 left (false :: (List.replicate k true ++ false :: bit :: tail))] ++
    scanRight k (false :: left) (bit :: tail) ++
    [state 3 (false :: (List.replicate k true ++ false :: left)) (bit :: tail),
      state (payloadMode bit) (false :: (List.replicate k true ++ false :: left)) (false :: tail),
      state (markerMode bit) (List.replicate k true ++ false :: left) (false :: false :: tail),
      state (leftStartMode bit) (List.replicate k true ++ false :: left) (true :: false :: tail)] ++
    scanLeft bit k left (true :: false :: tail) ++
    [state 14 left (bit :: (List.replicate (k + 1) true ++ false :: tail)),
      state 15 (bit :: left) (List.replicate (k + 1) true ++ false :: tail)]

theorem unit_head (bit : Bool) (previous later suffix : List Bool) :
    (unitTrace bit previous later suffix).head? = some
      (state 0 (leftBlocks previous) (List.replicate (later.length + 1) true ++ false :: bit :: (later ++ suffix))) := rfl

theorem unit_length (bit : Bool) (previous later suffix : List Bool) :
    (unitTrace bit previous later suffix).length = 2 * later.length + 10 := by
  simp only [unitTrace, List.length_append, List.length_cons, List.length_nil,
    scanRight_length, scanLeft_length]
  omega

theorem unit_last (bit : Bool) (previous later suffix : List Bool) :
    (unitTrace bit previous later suffix).getLast? = some
      (state 15 (bit :: leftBlocks previous) (List.replicate (later.length + 1) true ++ false :: (later ++ suffix))) := by
  unfold unitTrace
  rw [List.getLast?_append]
  rfl

private theorem append_link (xs ys : List (MachineState 16)) (last first : MachineState 16)
    (hx : xs.IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step rawNatMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

/-- A full marker/scan/restore rotation of one actual payload bit. -/
theorem unit_chain (bit : Bool) (previous later suffix : List Bool) :
    (unitTrace bit previous later suffix).IsChain (fun before after =>
      Turing.TM0.step rawNatMachine before = some after) := by
  let k := later.length
  let left := leftBlocks previous
  let tail := later ++ suffix
  let first := [state 0 left (List.replicate (k + 1) true ++ false :: bit :: tail),
    state 1 left (false :: (List.replicate k true ++ false :: bit :: tail))]
  let middle := [state 3 (false :: (List.replicate k true ++ false :: left)) (bit :: tail),
    state (payloadMode bit) (false :: (List.replicate k true ++ false :: left)) (false :: tail),
    state (markerMode bit) (List.replicate k true ++ false :: left) (false :: false :: tail),
    state (leftStartMode bit) (List.replicate k true ++ false :: left) (true :: false :: tail)]
  let last := [state 14 left (bit :: (List.replicate (k + 1) true ++ false :: tail)),
    state 15 (bit :: left) (List.replicate (k + 1) true ++ false :: tail)]
  have hfirst : first.IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b) := by
    simp [first, List.isChain_cons_cons, Turing.TM0.step, rawNatMachine, state,
      Turing.Tape.mk₂, List.replicate_succ]
  have hmiddle : middle.IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b) := by
    cases bit <;> simp [middle, List.isChain_cons_cons, payloadMode, markerMode, leftStartMode,
      Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂]
  have hlast : last.IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b) := by
    simp [last, List.isChain_cons_cons, Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂]
  have hleftLast : Turing.TM0.step rawNatMachine
      (state (leftMode bit) left (false :: (List.replicate k true ++ true :: false :: tail))) =
        some (state 14 left (bit :: (List.replicate (k + 1) true ++ false :: tail))) := by
    cases bit <;> simp [leftMode, Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂, replicate_push]
  have hleft := append_link (scanLeft bit k left (true :: false :: tail)) last _ _
    (scanLeft_chain _ _ _ _) hlast (scanLeft_last _ _ _ _) (by rfl) hleftLast
  have hleftHead : (scanLeft bit k left (true :: false :: tail) ++ last).head? =
      some (scanLeftInitial bit k left (true :: false :: tail)) := by
    simp [List.head?_append, scanLeft_head]
  have hboundary : Turing.TM0.step rawNatMachine
      (state (leftStartMode bit) (List.replicate k true ++ false :: left) (true :: false :: tail)) =
        some (scanLeftInitial bit k left (true :: false :: tail)) := by
    cases k <;> cases bit <;> simp [scanLeftInitial, leftStartMode, leftMode, Turing.TM0.step,
      rawNatMachine, state, Turing.Tape.mk₂, List.replicate_succ]
  have hmiddleRest := append_link middle (scanLeft bit k left (true :: false :: tail) ++ last) _ _
    hmiddle hleft (by rfl) hleftHead hboundary
  have hmiddleHead : (middle ++ scanLeft bit k left (true :: false :: tail) ++ last).head? =
      some (state 3 (false :: (List.replicate k true ++ false :: left)) (bit :: tail)) := by
    simp [middle]
  have hscanBoundary : Turing.TM0.step rawNatMachine
      (state 2 (List.replicate k true ++ false :: left) (false :: bit :: tail)) =
        some (state 3 (false :: (List.replicate k true ++ false :: left)) (bit :: tail)) := by
    simp [Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂]
  have hright := append_link (scanRight k (false :: left) (bit :: tail))
    (middle ++ scanLeft bit k left (true :: false :: tail) ++ last) _ _
    (scanRight_chain _ _ _) hmiddleRest (scanRight_last _ _ _) hmiddleHead hscanBoundary
  have hrightHead : (scanRight k (false :: left) (bit :: tail) ++ middle ++
      scanLeft bit k left (true :: false :: tail) ++ last).head? =
        some (state 2 (false :: left) (List.replicate k true ++ false :: bit :: tail)) := by
    simp [List.head?_append, scanRight_head]
  change (first ++ scanRight k (false :: left) (bit :: tail) ++ middle ++
    scanLeft bit k left (true :: false :: tail) ++ last).IsChain _
  have hfinal := append_link first
    (scanRight k (false :: left) (bit :: tail) ++ (middle ++ (scanLeft bit k left (true :: false :: tail) ++ last))) _ _
    hfirst (by simpa only [List.append_assoc] using hright) (by rfl)
    (by simpa only [List.append_assoc] using hrightHead)
    (by simp [Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂])
  simpa only [List.append_assoc] using hfinal

/-- Whole uniform decoder trace. Previous digits are proof invariants of
this very tape, not external input or preprocessing answers. -/
def rawTrace (previous : List Bool) : List Bool → List Bool → List (MachineState 16)
  | [], suffix => doneTrace previous suffix
  | bit :: later, suffix => unitTrace bit previous later suffix ++ rawTrace (bit :: previous) later suffix

theorem raw_head (previous digits suffix : List Bool) :
    (rawTrace previous digits suffix).head? = some
      (state 0 (leftBlocks previous) (List.replicate digits.length true ++ false :: (digits ++ suffix))) := by
  cases digits with
  | nil => rfl
  | cons bit later => simp [rawTrace, List.head?_append, unit_head]

theorem raw_length (previous digits suffix : List Bool) :
    (rawTrace previous digits suffix).length = digits.length ^ 2 + 11 * digits.length + 2 * previous.length + 3 := by
  induction digits generalizing previous with
  | nil => simpa [rawTrace] using done_length previous suffix
  | cons bit later ih =>
    simp only [rawTrace, List.length_append, unit_length, ih, List.length_cons]
    ring

theorem raw_last (previous digits suffix : List Bool) :
    (rawTrace previous digits suffix).getLast? = some
      (state 16 [false] (PSTRTMIncrement009.blocks (previous.reverse ++ digits) ++ false :: suffix)) := by
  induction digits generalizing previous with
  | nil => simpa [rawTrace] using done_last previous suffix
  | cons bit later ih =>
    simp [rawTrace, List.getLast?_append, ih, List.reverse_cons, List.append_assoc]

theorem raw_chain (previous digits suffix : List Bool) :
    (rawTrace previous digits suffix).IsChain (fun before after =>
      Turing.TM0.step rawNatMachine before = some after) := by
  induction digits generalizing previous with
  | nil => exact done_chain previous suffix
  | cons bit later ih =>
    rw [rawTrace]
    apply append_link _ _ _ _ (unit_chain bit previous later suffix) (ih (bit :: previous))
      (unit_last bit previous later suffix) (raw_head (bit :: previous) later suffix)
    simp [Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂, leftBlocks, List.replicate_succ]

/-- Actual complete finite-control Bool run from the original unexpanded
length header/payload, preserving every arbitrary suffix bit. -/
theorem raw_runs (digits suffix : List Bool) :
    Runs rawNatMachine (List.replicate digits.length true ++ false :: (digits ++ suffix))
      (rawTrace [] digits suffix)
      (state 16 [false] (PSTRTMIncrement009.blocks digits ++ false :: suffix)) := by
  apply runs_of_chain
  · simpa [Turing.TM0.init, Turing.Tape.mk₁, state, leftBlocks] using raw_head [] digits suffix
  · exact raw_chain [] digits suffix
  · simpa using raw_last [] digits suffix
  · exact rawNat_halt _ _

/-- The frame is exact, but this SINGLE false separator does not establish
009's blank-tail contract for arbitrary suffix! See SuffixCounterexample011. -/
theorem rawNat_computes_frame (digits suffix : List Bool) :
    computes rawNatMachine (List.replicate digits.length true ++ false :: (digits ++ suffix))
      (PSTRTMIncrement009.blocks digits ++ false :: suffix)
      (32 * (digits.length + 1) ^ 2) (32 * (digits.length + 1) ^ 2 + suffix.length) := by
  refine ⟨rawTrace [] digits suffix, state 16 [false] (PSTRTMIncrement009.blocks digits ++ false :: suffix),
    raw_runs digits suffix, ?_, ?_, ?_⟩
  · simp [state, Turing.Tape.mk₂]
  · rw [raw_length]
    simp only [List.length_nil]
    nlinarith
  · have hspace := visitedSpace_le rawNatMachine
      (List.replicate digits.length true ++ false :: (digits ++ suffix)).length (rawTrace [] digits suffix)
    have htime := raw_length [] digits suffix
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil] at hspace htime ⊢
    nlinarith

theorem blank_append_false (bits : List Bool) :
    Turing.ListBlank.mk (bits ++ [false]) = Turing.ListBlank.mk bits := by
  apply Quotient.sound
  exact Or.inr ⟨1, by rfl⟩

theorem blank_single_false : Turing.ListBlank.mk [false] = Turing.ListBlank.mk ([] : List Bool) :=
  blank_append_false []

/-- EMPTY-suffix transport returns the exact entire standard initialized
tape, not merely a string ending in one false bit. Hence all tail cells are
real blanks and 009 may be connected once this equality is transported. -/
theorem isolated_final_tape (digits : List Bool) :
    (state 16 [false] (PSTRTMIncrement009.blocks digits ++ [false])).Tape =
      Turing.Tape.mk₁ (PSTRTMIncrement009.blocks digits) := by
  simp only [state, Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [blank_single_false, blank_append_false]

/-- Every real cell after the payload is blank in the isolated case;
particular offsets 0 and 1 supply the required actual 00 end region. -/
theorem isolated_tail_blank (digits : List Bool) (offset : Nat) :
    ((state 16 [false] (PSTRTMIncrement009.blocks digits ++ [false])).Tape.right₀).nth
      ((PSTRTMIncrement009.blocks digits).length + offset) = false := by
  rw [isolated_final_tape]
  simp only [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_right₀, Turing.ListBlank.nth_mk]
  exact List.getI_eq_default (PSTRTMIncrement009.blocks digits) (by omega)

theorem isolated_double_blank (digits : List Bool) :
    ((state 16 [false] (PSTRTMIncrement009.blocks digits ++ [false])).Tape.right₀).nth
      (PSTRTMIncrement009.blocks digits).length = false ∧
    ((state 16 [false] (PSTRTMIncrement009.blocks digits ++ [false])).Tape.right₀).nth
      ((PSTRTMIncrement009.blocks digits).length + 1) = false := by
  exact ⟨by simpa using isolated_tail_blank digits 0, isolated_tail_blank digits 1⟩

theorem rawNat_computes (digits : List Bool) :
    computes rawNatMachine (List.replicate digits.length true ++ false :: digits)
      (PSTRTMIncrement009.blocks digits)
      (32 * (digits.length + 1) ^ 2) (32 * (digits.length + 1) ^ 2) := by
  obtain ⟨trace, final, hr, ho, ht, hs⟩ := rawNat_computes_frame digits []
  refine ⟨trace, final, ?_, ?_, ht, ?_⟩
  · simpa using hr
  · simpa only [blank_append_false] using ho
  · simpa using hs

/-- Original B23 encodeNat input, no pre-encoded block input or oracle. -/
theorem encodeNat_blocks_computes (value : Nat) :
    let payload := List.ofFn (fun i : Fin (natBits value) => value.testBit i.val)
    computes rawNatMachine (encodeNat value) (PSTRTMIncrement009.blocks payload)
      (32 * (natBits value + 1) ^ 2) (32 * (natBits value + 1) ^ 2) := by
  dsimp only
  have h := rawNat_computes (List.ofFn (fun i : Fin (natBits value) => value.testBit i.val))
  simpa [encodeNat, List.append_assoc] using h

/-- Actual fixed-code sequence, for an ISOLATED raw Nat only. Arbitrary
suffix composition would be false; its explicit regression is batch011. -/
def rawIncrementMachine : Machine 31 := PSTRTMSeq005.seqMachine rawNatMachine PSTRTMIncrement009.incrementMachine

def rawIncrementTrace (digits : List Bool) : List (MachineState 31) :=
  (rawTrace [] digits []).map (PSTRTMSeq005.leftCfg (b := 14)) ++
    (PSTRTMIncrement009.computeTrace 0 digits).map (PSTRTMSeq005.rightCfg (a := 16))

def rawIncrementFinal (digits : List Bool) : MachineState 31 :=
  PSTRTMSeq005.rightCfg (a := 16)
    (PSTRTMIncrement009.state 14 [false] (PSTRTMIncrement009.blocks (PSTRTMIncrement009.bumpDigits digits)))

theorem raw_increment_runs (digits : List Bool) :
    Runs rawIncrementMachine (List.replicate digits.length true ++ false :: digits)
      (rawIncrementTrace digits) (rawIncrementFinal digits) := by
  apply PSTRTMSeq005.seq_runs rawNatMachine PSTRTMIncrement009.incrementMachine
    (List.replicate digits.length true ++ false :: digits)
    (state 16 [false] (PSTRTMIncrement009.blocks digits ++ [false]))
    (PSTRTMIncrement009.state 14 [false] (PSTRTMIncrement009.blocks (PSTRTMIncrement009.bumpDigits digits)))
    (rawTrace [] digits []) (PSTRTMIncrement009.computeTrace 0 digits)
  · simpa using raw_runs digits []
  · have h := PSTRTMIncrement009.increment_runs digits
    refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2.1⟩
    rw [isolated_final_tape]
    exact h.1

theorem raw_increment_length_le (digits : List Bool) :
    (rawIncrementTrace digits).length ≤ digits.length ^ 2 + 19 * digits.length + 12 := by
  have h := PSTRTMIncrement009.computeTrace_length_le 0 digits
  simp only [rawIncrementTrace, List.length_append, List.length_map, raw_length, List.length_nil]
  nlinarith

/-- A genuine raw-input binary-increment computation. The result is in the
explicit internal cell encoding; output re-encoding and multi-field operands
remain separate original obligations. All conversion/transfer costs count. -/
theorem raw_increment_computes (digits : List Bool) :
    computes rawIncrementMachine (List.replicate digits.length true ++ false :: digits)
      (PSTRTMIncrement009.blocks (PSTRTMIncrement009.bumpDigits digits))
      (128 * (digits.length + 1) ^ 2) (128 * (digits.length + 1) ^ 2) := by
  refine ⟨rawIncrementTrace digits, rawIncrementFinal digits, raw_increment_runs digits, ?_, ?_, ?_⟩
  · simp [rawIncrementFinal, PSTRTMSeq005.rightCfg, PSTRTMIncrement009.state, Turing.Tape.mk₂]
  · have h := raw_increment_length_le digits
    nlinarith
  · have hspace := visitedSpace_le rawIncrementMachine
      (List.replicate digits.length true ++ false :: digits).length (rawIncrementTrace digits)
    have htime := raw_increment_length_le digits
    simp only [List.length_append, List.length_replicate, List.length_cons] at hspace ⊢
    nlinarith

theorem encodeNat_raw_increment_computes (value : Nat) :
    let payload := List.ofFn (fun i : Fin (natBits value) => value.testBit i.val)
    computes rawIncrementMachine (encodeNat value)
      (PSTRTMIncrement009.blocks (PSTRTMIncrement009.bumpDigits payload))
      (128 * (natBits value + 1) ^ 2) (128 * (natBits value + 1) ^ 2) := by
  dsimp only
  have h := raw_increment_computes (List.ofFn (fun i : Fin (natBits value) => value.testBit i.val))
  simpa [encodeNat, List.append_assoc] using h

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMRawNat010









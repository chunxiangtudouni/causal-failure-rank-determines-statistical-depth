module

public import Structure.PA17_TM_Division_Loop_002c

/-! Genuine source fetching from the retained archive. The returned bit
and exhausted/not-exhausted choice are read from real pending flags and
source cells. The exact whole tape and resident head are preserved. -/

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2200000

namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002

open PSTRTMCompareCode054 PSTRTMBinaryAdd024

def scanMode : List (Bool × Bool) → Fin 3
  | [] => 0
  | (_,false) :: lower => scanMode lower
  | (bit,true) :: _ => bitMode bit

def scanInitial (context : List Bool) : List (Bool × Bool) → List (Bool × Bool) → List Bool → MachineState 27
  | [], higher, resident => sourceState 4 context (false :: (operandColumns higher ++ false :: false :: false :: resident))
  | (a,p) :: lower, higher, resident =>
    sourceState 4 (p :: true :: a :: (leftColumns lower ++ false :: context))
      (true :: (operandColumns higher ++ false :: false :: false :: resident))

def skipSourceTrace (a : Bool) (left right : List Bool) : List (MachineState 27) :=
  [sourceState 4 (false :: true :: a :: left) (true :: right),
   sourceState 5 (true :: a :: left) (false :: true :: right),
   sourceState 6 (a :: left) (true :: false :: true :: right),
   sourceState 8 left (a :: true :: false :: true :: right)]

def foundSourceTrace (a : Bool) (left right : List Bool) : List (MachineState 27) :=
  [sourceState 4 (true :: true :: a :: left) (true :: right),
   sourceState 5 (true :: a :: left) (true :: true :: right),
   sourceState 7 (a :: left) (true :: true :: true :: right),
   sourceState 9 left (a :: true :: true :: true :: right)]

theorem skip_source_head (a : Bool) (left right : List Bool) :
    (skipSourceTrace a left right).head? = some (sourceState 4 (false :: true :: a :: left) (true :: right)) := rfl

theorem skip_source_last (a : Bool) (left right : List Bool) :
    (skipSourceTrace a left right).getLast? = some (sourceState 8 left (a :: true :: false :: true :: right)) := rfl

theorem found_source_head (a : Bool) (left right : List Bool) :
    (foundSourceTrace a left right).head? = some (sourceState 4 (true :: true :: a :: left) (true :: right)) := rfl

theorem found_source_last (a : Bool) (left right : List Bool) :
    (foundSourceTrace a left right).getLast? = some (sourceState 9 left (a :: true :: true :: true :: right)) := rfl

theorem skip_source_chain (a : Bool) (left right : List Bool) :
    (skipSourceTrace a left right).IsChain (fun before after => Turing.TM0.step sourceMachine before = some after) := by
  simp [skipSourceTrace, List.isChain_cons_cons, Turing.TM0.step, sourceMachine, sourceState, Turing.Tape.mk₂]

theorem found_source_chain (a : Bool) (left right : List Bool) :
    (foundSourceTrace a left right).IsChain (fun before after => Turing.TM0.step sourceMachine before = some after) := by
  simp [foundSourceTrace, List.isChain_cons_cons, Turing.TM0.step, sourceMachine, sourceState, Turing.Tape.mk₂]

def scanTrace (context : List Bool) : List (Bool × Bool) → List (Bool × Bool) → List Bool → List (MachineState 27)
  | [], higher, resident =>
    [sourceState 4 context (false :: (operandColumns higher ++ false :: false :: false :: resident))] ++
      returnTrace 0 (false :: context) [] higher resident
  | (a,false) :: lower, higher, resident =>
    skipSourceTrace a (leftColumns lower ++ false :: context)
      (operandColumns higher ++ false :: false :: false :: resident) ++
      scanTrace context lower ((a,false) :: higher) resident
  | (a,true) :: lower, higher, resident =>
    foundSourceTrace a (leftColumns lower ++ false :: context)
      (operandColumns higher ++ false :: false :: false :: resident) ++
      returnTrace (bitMode a) (leftColumns lower ++ false :: context) [] ((a,true) :: higher) resident

theorem scan_head (context : List Bool) (remaining higher : List (Bool × Bool)) (resident : List Bool) :
    (scanTrace context remaining higher resident).head? = some (scanInitial context remaining higher resident) := by
  cases remaining with
  | nil => rfl
  | cons pair lower =>
    obtain ⟨a,p⟩ := pair
    cases p <;> simp [scanTrace, scanInitial, List.head?_append, skip_source_head, found_source_head]

theorem scan_last (context : List Bool) (remaining higher : List (Bool × Bool)) (resident : List Bool) :
    (scanTrace context remaining higher resident).getLast? = some
      (sourceState (sourceHalt (scanMode remaining))
        (false :: false :: false :: (leftColumns (higher.reverse ++ remaining) ++ false :: context)) resident) := by
  induction remaining generalizing higher with
  | nil =>
    have hne : returnTrace 0 (false :: context) [] higher resident ≠ [] := by
      intro he
      have hl := return_length 0 (false :: context) [] higher resident
      simp [he] at hl
    change (sourceState 4 context (false :: (operandColumns higher ++ false :: false :: false :: resident)) ::
      returnTrace 0 (false :: context) [] higher resident).getLast? = _
    rw [List.getLast?_cons_of_ne_nil hne, return_last]
    simp only [scanMode, List.append_nil]
  | cons pair lower ih =>
    obtain ⟨a,p⟩ := pair
    cases p with
    | false =>
      simp [scanTrace, List.getLast?_append, ih, scanMode, List.reverse_cons, List.append_assoc]
    | true =>
      simp [scanTrace, List.getLast?_append, return_last, scanMode, List.reverse_cons,
        leftColumns, List.flatMap_append, List.append_assoc]

theorem scan_length_le (context : List Bool) (remaining higher : List (Bool × Bool)) (resident : List Bool) :
    (scanTrace context remaining higher resident).length ≤ 8 * remaining.length + 4 * higher.length + 5 := by
  induction remaining generalizing higher with
  | nil =>
    simp only [scanTrace, List.length_append, List.length_cons, List.length_nil, return_length]
    omega
  | cons pair lower ih =>
    obtain ⟨a,p⟩ := pair
    cases p with
    | false =>
      have hs := ih ((a,false) :: higher)
      simp only [scanTrace, List.length_append, skipSourceTrace, List.length_cons, List.length_nil] at hs ⊢
      omega
    | true =>
      simp only [scanTrace, List.length_append, foundSourceTrace, List.length_cons, List.length_nil, return_length]
      omega

theorem scan_chain (context : List Bool) (remaining higher : List (Bool × Bool)) (resident : List Bool) :
    (scanTrace context remaining higher resident).IsChain (fun before after => Turing.TM0.step sourceMachine before = some after) := by
  induction remaining generalizing higher with
  | nil =>
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      change after ∈ (returnTrace 0 (false :: context) [] higher resident).head? at ha
      rw [return_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      simp [Turing.TM0.step, sourceMachine, sourceState, Turing.Tape.mk₂,
        leftColumns, List.flatMap_nil, List.nil_append]
    · exact return_chain 0 (false :: context) [] higher resident
  | cons pair lower ih =>
    obtain ⟨a,p⟩ := pair
    cases p with
    | false =>
      rw [scanTrace]
      apply (skip_source_chain a _ _).append (ih ((a,false) :: higher))
      intro before hb after ha
      simp only [skip_source_last, Option.mem_some_iff] at hb
      simp only [scan_head, Option.mem_some_iff] at ha
      subst before
      subst after
      cases lower with
      | nil => simp [scanInitial, Turing.TM0.step, sourceMachine, sourceState, leftColumns, operandColumns, Turing.Tape.mk₂]
      | cons pair rest =>
        obtain ⟨b,p⟩ := pair
        simp [scanInitial, Turing.TM0.step, sourceMachine, sourceState, leftColumns, operandColumns, Turing.Tape.mk₂]
    | true =>
      rw [scanTrace]
      apply (found_source_chain a _ _).append (return_chain (bitMode a) (leftColumns lower ++ false :: context) [] ((a,true) :: higher) resident)
      intro before hb after ha
      simp only [found_source_last, Option.mem_some_iff] at hb
      simp only [return_head, Option.mem_some_iff] at ha
      subst before
      subst after
      cases a <;> simp [Turing.TM0.step, sourceMachine, sourceState, bitMode, leftColumns,
        operandColumns, Turing.Tape.mk₂]

def startupTrace (context : List Bool) (archive : List (Bool × Bool)) (resident : List Bool) : List (MachineState 27) :=
  let saved := leftColumns archive.reverse ++ false :: context
  [sourceState 0 (false :: false :: false :: saved) resident,
   sourceState 1 (false :: false :: saved) (false :: resident),
   sourceState 2 (false :: saved) (false :: false :: resident),
   sourceState 3 saved (false :: false :: false :: resident)]

def sourceTrace (context : List Bool) (archive : List (Bool × Bool)) (resident : List Bool) : List (MachineState 27) :=
  startupTrace context archive resident ++ scanTrace context archive.reverse [] resident

theorem startup_chain (context : List Bool) (archive : List (Bool × Bool)) (resident : List Bool) :
    (startupTrace context archive resident).IsChain (fun before after => Turing.TM0.step sourceMachine before = some after) := by
  simp [startupTrace, List.isChain_cons_cons, Turing.TM0.step, sourceMachine, sourceState, Turing.Tape.mk₂]

theorem source_head (context : List Bool) (archive : List (Bool × Bool)) (resident : List Bool) :
    (sourceTrace context archive resident).head? = some
      (sourceState 0 (false :: false :: false :: (leftColumns archive.reverse ++ false :: context)) resident) := by
  simp [sourceTrace, startupTrace]

theorem source_last (context : List Bool) (archive : List (Bool × Bool)) (resident : List Bool) :
    (sourceTrace context archive resident).getLast? = some
      (sourceState (sourceHalt (scanMode archive.reverse))
        (false :: false :: false :: (leftColumns archive.reverse ++ false :: context)) resident) := by
  simp [sourceTrace, List.getLast?_append, scan_last]

theorem source_length_le (context : List Bool) (archive : List (Bool × Bool)) (resident : List Bool) :
    (sourceTrace context archive resident).length ≤ 8 * archive.length + 9 := by
  have hs := scan_length_le context archive.reverse [] resident
  simp only [sourceTrace, List.length_append, startupTrace, List.length_cons, List.length_nil,
    List.length_reverse] at hs ⊢
  omega

theorem source_chain (context : List Bool) (archive : List (Bool × Bool)) (resident : List Bool) :
    (sourceTrace context archive resident).IsChain (fun before after => Turing.TM0.step sourceMachine before = some after) := by
  apply (startup_chain context archive resident).append (scan_chain context archive.reverse [] resident)
  intro before hb after ha
  simp [startupTrace] at hb
  simp only [scan_head, Option.mem_some_iff] at ha
  subst before
  subst after
  generalize he : archive.reverse = remaining
  cases remaining with
  | nil => simp [scanInitial, Turing.TM0.step, sourceMachine, sourceState, leftColumns, operandColumns, Turing.Tape.mk₂]
  | cons pair lower =>
    obtain ⟨a,p⟩ := pair
    simp [scanInitial, Turing.TM0.step, sourceMachine, sourceState, leftColumns, operandColumns, Turing.Tape.mk₂]

theorem source_runsFrom (context : List Bool) (archive : List (Bool × Bool)) (resident : List Bool) :
    PSTRTMSeq005.RunsFrom sourceMachine
      (sourceState 0 (false :: false :: false :: (leftColumns archive.reverse ++ false :: context)) resident)
      (sourceTrace context archive resident)
      (sourceState (sourceHalt (scanMode archive.reverse))
        (false :: false :: false :: (leftColumns archive.reverse ++ false :: context)) resident) :=
  ⟨source_head context archive resident, source_chain context archive resident,
    source_last context archive resident, source_halt _ _ _⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002

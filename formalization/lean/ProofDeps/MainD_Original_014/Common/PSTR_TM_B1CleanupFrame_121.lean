module
public import Common.PSTR_TM_B1IterationFrame_120
public import Common.PSTR_TM_B1Invariant_075

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1CleanupFrame121
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMB1LoopCode071 PSTRTMB1CounterCall073

def scanTrace (archive : List Bool) (digits : List Bool) (previous : Nat) : Nat → List (MachineState 81)
  | 0 =>
    [state 78 (List.replicate previous false ++ archive) (true :: false :: PSTRTMIncrement009.blocks digits),
      state 79 (List.replicate previous false ++ archive) (false :: false :: PSTRTMIncrement009.blocks digits),
      state 80 (false :: (List.replicate previous false ++ archive)) (false :: PSTRTMIncrement009.blocks digits),
      state 81 (false :: false :: (List.replicate previous false ++ archive)) (PSTRTMIncrement009.blocks digits)]
  | count + 1 =>
    state 78 (List.replicate previous false ++ archive)
      ((false :: List.replicate count false) ++ true :: false :: PSTRTMIncrement009.blocks digits) ::
      scanTrace archive digits (previous + 1) count

theorem scan_head (archive : List Bool) (digits : List Bool) (previous count : Nat) : (scanTrace archive digits previous count).head? = some
    (state 78 (List.replicate previous false ++ archive) (List.replicate count false ++ true :: false :: PSTRTMIncrement009.blocks digits)) := by
  cases count <;> simp [scanTrace, List.replicate_succ]

theorem scan_length (archive : List Bool) (digits : List Bool) (previous count : Nat) : (scanTrace archive digits previous count).length = count + 4 := by
  induction count generalizing previous with
  | zero => rfl
  | succ count ih => simp only [scanTrace, List.length_cons, ih]

theorem scan_last (archive : List Bool) (digits : List Bool) (previous count : Nat) : (scanTrace archive digits previous count).getLast? = some
    (state 81 (List.replicate (previous+count+2) false ++ archive) (PSTRTMIncrement009.blocks digits)) := by
  induction count generalizing previous with
  | zero => simp [scanTrace, List.replicate_succ]
  | succ count ih =>
    have hne : scanTrace archive digits (previous+1) count ≠ [] := by
      intro h
      have hh := scan_head archive digits (previous+1) count
      simp [h] at hh
    rw [scanTrace,List.getLast?_cons_of_ne_nil hne,ih]
    have he : previous+1+count+2 = previous+(count+1)+2 := by omega
    rw [he]

theorem scan_chain (archive : List Bool) (digits : List Bool) (previous count : Nat) :
    (scanTrace archive digits previous count).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  induction count generalizing previous with
  | zero => simp [scanTrace, List.isChain_cons_cons, Turing.TM0.step, loopMachine, state, Turing.Tape.mk₂]
  | succ count ih =>
    rw [scanTrace]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [scan_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      simp [Turing.TM0.step,loopMachine,state,Turing.Tape.mk₂,List.replicate_succ]
    · exact ih (previous+1)

def eraseLeft (archive : List Bool) (previous : List Bool) : List Bool := PSTRTMRawNat010.leftBlocks previous ++ false::archive

def eraseInitial (archive : List Bool) : List Bool → Nat → List Bool → MachineState 81
  | [], cleared, digits => state 74 archive ((false :: List.replicate cleared false) ++ endRegion digits)
  | bit :: previous, cleared, digits =>
    state 74 (bit :: eraseLeft archive previous) ((true :: List.replicate cleared false) ++ endRegion digits)

def eraseUnit (archive : List Bool) (bit : Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) : List (MachineState 81) :=
  [state 74 (bit :: eraseLeft archive previous) ((true :: List.replicate cleared false) ++ endRegion digits),
    state 75 (bit :: eraseLeft archive previous) ((false :: List.replicate cleared false) ++ endRegion digits),
    state 76 (eraseLeft archive previous) ((bit :: false :: List.replicate cleared false) ++ endRegion digits),
    state 77 (eraseLeft archive previous) ((false :: false :: List.replicate cleared false) ++ endRegion digits)]

theorem unit_head (archive : List Bool) (bit : Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseUnit archive bit previous cleared digits).head? = some (eraseInitial archive (bit :: previous) cleared digits) := rfl

theorem unit_last (archive : List Bool) (bit : Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseUnit archive bit previous cleared digits).getLast? = some
      (state 77 (eraseLeft archive previous) ((false :: false :: List.replicate cleared false) ++ endRegion digits)) := rfl

theorem unit_length (archive : List Bool) (bit : Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseUnit archive bit previous cleared digits).length = 4 := rfl

theorem unit_chain (archive : List Bool) (bit : Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseUnit archive bit previous cleared digits).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  simp [eraseUnit, List.isChain_cons_cons,Turing.TM0.step,loopMachine,state,Turing.Tape.mk₂]

theorem unit_advance (archive : List Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    Turing.TM0.step loopMachine
      (state 77 (eraseLeft archive previous) ((false :: false :: List.replicate cleared false) ++ endRegion digits)) =
      some (eraseInitial archive previous (cleared+2) digits) := by
  cases previous <;> simp [eraseLeft,eraseInitial,PSTRTMRawNat010.leftBlocks,
    Turing.TM0.step,loopMachine,state,Turing.Tape.mk₂,List.replicate_succ]

private theorem zeros_endRegion (cleared : Nat) (digits : List Bool) :
    List.replicate cleared false ++ endRegion digits =
      List.replicate (cleared+2) false ++ true :: false :: PSTRTMIncrement009.blocks digits := by
  simp [endRegion,List.replicate_add,List.append_assoc]

theorem empty_advance (archive : List Bool) (cleared : Nat) (digits : List Bool) :
    Turing.TM0.step loopMachine (eraseInitial archive [] cleared digits) = some
      (state 78 (List.replicate 1 false ++ archive) (List.replicate (cleared+2) false ++ true :: false :: PSTRTMIncrement009.blocks digits)) := by
  rw [←zeros_endRegion cleared digits]
  simp [eraseInitial,Turing.TM0.step,loopMachine,state,Turing.Tape.mk₂]

private theorem append_link (xs ys : List (MachineState 81)) (last first : MachineState 81)
    (hx : xs.IsChain (fun a b => Turing.TM0.step loopMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step loopMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step loopMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def eraseTrace (archive : List Bool) : List Bool → Nat → List Bool → List (MachineState 81)
  | [], cleared, digits => eraseInitial archive [] cleared digits :: scanTrace archive digits 1 (cleared+2)
  | bit :: previous, cleared, digits => eraseUnit archive bit previous cleared digits ++ eraseTrace archive previous (cleared+2) digits

theorem erase_head (archive : List Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseTrace archive previous cleared digits).head? = some (eraseInitial archive previous cleared digits) := by
  cases previous with
  | nil => rfl
  | cons bit previous => simp only [eraseTrace,List.head?_append,unit_head,Option.some_or]

theorem erase_last (archive : List Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseTrace archive previous cleared digits).getLast? = some
      (state 81 (List.replicate (cleared+2*previous.length+5) false ++ archive) (PSTRTMIncrement009.blocks digits)) := by
  induction previous generalizing cleared with
  | nil =>
    have hne : scanTrace archive digits 1 (cleared+2) ≠ [] := by
      intro h
      have hh := scan_head archive digits 1 (cleared+2)
      simp [h] at hh
    rw [eraseTrace,List.getLast?_cons_of_ne_nil hne,scan_last]
    simp only [List.length_nil,Nat.mul_zero,Nat.add_zero]
    have he : 1+(cleared+2)+2 = cleared+5 := by omega
    rw [he]
  | cons bit previous ih =>
    simp only [eraseTrace,List.getLast?_append,ih,Option.some_or,List.length_cons]
    have he : cleared+2+2*previous.length+5 = cleared+2*(previous.length+1)+5 := by omega
    rw [he]

theorem erase_length (archive : List Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseTrace archive previous cleared digits).length = 6*previous.length+cleared+7 := by
  induction previous generalizing cleared with
  | nil => simp only [eraseTrace,List.length_cons,scan_length,List.length_nil]; omega
  | cons bit previous ih => simp only [eraseTrace,List.length_append,unit_length,ih,List.length_cons]; omega

theorem erase_chain (archive : List Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseTrace archive previous cleared digits).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  induction previous generalizing cleared with
  | nil =>
    rw [eraseTrace]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [scan_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      exact empty_advance archive cleared digits
    · exact scan_chain archive digits 1 (cleared+2)
  | cons bit previous ih =>
    rw [eraseTrace]
    exact append_link _ _ _ _ (unit_chain archive bit previous cleared digits) (ih (cleared+2))
      (unit_last archive bit previous cleared digits) (erase_head archive previous (cleared+2) digits)
      (unit_advance archive previous cleared digits)

theorem terminal_transfer (archive : List Bool) (relation : Fin 3) (notLess : relation ≠ 1) (previous digits : List Bool) :
    Turing.TM0.step loopMachine (liftCompare (PSTRTMCompareCode054.state (PSTRTMCompareCode054.haltLabel relation)
      (eraseLeft archive previous) (endRegion digits))) = some (eraseInitial archive previous 0 digits) := by
  have hr := relation.isLt
  have hn : relation.val ≠ 1 := by intro h; apply notLess; apply Fin.ext; exact h
  have he : relation.val=0 ∨ relation.val=2 := by omega
  rcases he with he | he <;> cases previous <;>
    simp [Turing.TM0.step,loopMachine,liftCompare,compareLabel,PSTRTMCompareCode054.state,
      PSTRTMCompareCode054.haltLabel,he,eraseInitial,eraseLeft,PSTRTMRawNat010.leftBlocks,
      state,endRegion,Turing.Tape.mk₂]

def cleanupTrace (archive : List Bool) (pairs : List (Bool × Bool)) (digits : List Bool) : List (MachineState 81) :=
  eraseTrace archive (PSTRTMPackLoop043.pairedDigits pairs).reverse 0 digits

def cleanupFinal (archive : List Bool) (pairs : List (Bool × Bool)) (digits : List Bool) : MachineState 81 :=
  state 81 (List.replicate (4*pairs.length+5) false ++ archive) (PSTRTMIncrement009.blocks digits)

theorem cleanup_head (archive : List Bool) (pairs : List (Bool × Bool)) (digits : List Bool) :
    (cleanupTrace archive pairs digits).head? = some (eraseInitial archive (PSTRTMPackLoop043.pairedDigits pairs).reverse 0 digits) :=
  erase_head archive _ 0 digits

theorem cleanup_last (archive : List Bool) (pairs : List (Bool × Bool)) (digits : List Bool) :
    (cleanupTrace archive pairs digits).getLast? = some (cleanupFinal archive pairs digits) := by
  rw [cleanupTrace,erase_last,List.length_reverse,PSTRTMCompareRun059.pairedDigits_length]
  have he : 0+2*(2*pairs.length)+5 = 4*pairs.length+5 := by omega
  rw [he]
  rfl

theorem cleanup_length (archive : List Bool) (pairs : List (Bool × Bool)) (digits : List Bool) :
    (cleanupTrace archive pairs digits).length = 12*pairs.length+7 := by
  simp only [cleanupTrace,erase_length,List.length_reverse,PSTRTMCompareRun059.pairedDigits_length]
  omega

theorem cleanup_runsFrom (archive : List Bool) (pairs : List (Bool × Bool)) (digits : List Bool) :
    PSTRTMSeq005.RunsFrom loopMachine (eraseInitial archive (PSTRTMPackLoop043.pairedDigits pairs).reverse 0 digits)
      (cleanupTrace archive pairs digits) (cleanupFinal archive pairs digits) :=
  ⟨cleanup_head archive pairs digits,erase_chain archive _ 0 digits,cleanup_last archive pairs digits,loop_halt _ _⟩

/-- The actual counter head is reached after clearing all source/marker
cells. Every bit of the left archive remains in the ENTIRE tape. -/
theorem cleanup_final_tape (archive : List Bool) (pairs : List (Bool × Bool)) (digits : List Bool) :
    (cleanupFinal archive pairs digits).Tape = Turing.Tape.mk₂
      (List.replicate (4*pairs.length+5) false ++ archive) (PSTRTMIncrement009.blocks digits) := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1CleanupFrame121

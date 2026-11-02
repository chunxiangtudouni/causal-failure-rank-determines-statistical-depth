module
public import PaperProofs.Common.PSTR_TM_B1Invariant_075

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1Cleanup076
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMB1LoopCode071 PSTRTMB1CounterCall073

def scanTrace (digits : List Bool) (previous : Nat) : Nat → List (MachineState 81)
  | 0 =>
    [state 78 (List.replicate previous false) (true :: false :: PSTRTMIncrement009.blocks digits),
      state 79 (List.replicate previous false) (false :: false :: PSTRTMIncrement009.blocks digits),
      state 80 (false :: List.replicate previous false) (false :: PSTRTMIncrement009.blocks digits),
      state 81 (false :: false :: List.replicate previous false) (PSTRTMIncrement009.blocks digits)]
  | count + 1 =>
    state 78 (List.replicate previous false)
      ((false :: List.replicate count false) ++ true :: false :: PSTRTMIncrement009.blocks digits) ::
      scanTrace digits (previous + 1) count

theorem scan_head (digits : List Bool) (previous count : Nat) : (scanTrace digits previous count).head? = some
    (state 78 (List.replicate previous false) (List.replicate count false ++ true :: false :: PSTRTMIncrement009.blocks digits)) := by
  cases count <;> simp [scanTrace, List.replicate_succ]

theorem scan_length (digits : List Bool) (previous count : Nat) : (scanTrace digits previous count).length = count + 4 := by
  induction count generalizing previous with
  | zero => rfl
  | succ count ih => simp only [scanTrace, List.length_cons, ih]

theorem scan_last (digits : List Bool) (previous count : Nat) : (scanTrace digits previous count).getLast? = some
    (state 81 (List.replicate (previous+count+2) false) (PSTRTMIncrement009.blocks digits)) := by
  induction count generalizing previous with
  | zero => simp [scanTrace, List.replicate_succ]
  | succ count ih =>
    have hne : scanTrace digits (previous+1) count ≠ [] := by
      intro h
      have hh := scan_head digits (previous+1) count
      simp [h] at hh
    rw [scanTrace,List.getLast?_cons_of_ne_nil hne,ih]
    have he : previous+1+count+2 = previous+(count+1)+2 := by omega
    rw [he]

theorem scan_chain (digits : List Bool) (previous count : Nat) :
    (scanTrace digits previous count).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
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

def eraseLeft (previous : List Bool) : List Bool := PSTRTMRawNat010.leftBlocks previous ++ [false]

def eraseInitial : List Bool → Nat → List Bool → MachineState 81
  | [], cleared, digits => state 74 [] ((false :: List.replicate cleared false) ++ endRegion digits)
  | bit :: previous, cleared, digits =>
    state 74 (bit :: eraseLeft previous) ((true :: List.replicate cleared false) ++ endRegion digits)

def eraseUnit (bit : Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) : List (MachineState 81) :=
  [state 74 (bit :: eraseLeft previous) ((true :: List.replicate cleared false) ++ endRegion digits),
    state 75 (bit :: eraseLeft previous) ((false :: List.replicate cleared false) ++ endRegion digits),
    state 76 (eraseLeft previous) ((bit :: false :: List.replicate cleared false) ++ endRegion digits),
    state 77 (eraseLeft previous) ((false :: false :: List.replicate cleared false) ++ endRegion digits)]

theorem unit_head (bit : Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseUnit bit previous cleared digits).head? = some (eraseInitial (bit :: previous) cleared digits) := rfl

theorem unit_last (bit : Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseUnit bit previous cleared digits).getLast? = some
      (state 77 (eraseLeft previous) ((false :: false :: List.replicate cleared false) ++ endRegion digits)) := rfl

theorem unit_length (bit : Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseUnit bit previous cleared digits).length = 4 := rfl

theorem unit_chain (bit : Bool) (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseUnit bit previous cleared digits).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  simp [eraseUnit, List.isChain_cons_cons,Turing.TM0.step,loopMachine,state,Turing.Tape.mk₂]

theorem unit_advance (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    Turing.TM0.step loopMachine
      (state 77 (eraseLeft previous) ((false :: false :: List.replicate cleared false) ++ endRegion digits)) =
      some (eraseInitial previous (cleared+2) digits) := by
  cases previous <;> simp [eraseLeft,eraseInitial,PSTRTMRawNat010.leftBlocks,
    Turing.TM0.step,loopMachine,state,Turing.Tape.mk₂,List.replicate_succ]

private theorem zeros_endRegion (cleared : Nat) (digits : List Bool) :
    List.replicate cleared false ++ endRegion digits =
      List.replicate (cleared+2) false ++ true :: false :: PSTRTMIncrement009.blocks digits := by
  simp [endRegion,List.replicate_add,List.append_assoc]

theorem empty_advance (cleared : Nat) (digits : List Bool) :
    Turing.TM0.step loopMachine (eraseInitial [] cleared digits) = some
      (state 78 (List.replicate 1 false) (List.replicate (cleared+2) false ++ true :: false :: PSTRTMIncrement009.blocks digits)) := by
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

def eraseTrace : List Bool → Nat → List Bool → List (MachineState 81)
  | [], cleared, digits => eraseInitial [] cleared digits :: scanTrace digits 1 (cleared+2)
  | bit :: previous, cleared, digits => eraseUnit bit previous cleared digits ++ eraseTrace previous (cleared+2) digits

theorem erase_head (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseTrace previous cleared digits).head? = some (eraseInitial previous cleared digits) := by
  cases previous with
  | nil => rfl
  | cons bit previous => simp only [eraseTrace,List.head?_append,unit_head,Option.some_or]

theorem erase_last (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseTrace previous cleared digits).getLast? = some
      (state 81 (List.replicate (cleared+2*previous.length+5) false) (PSTRTMIncrement009.blocks digits)) := by
  induction previous generalizing cleared with
  | nil =>
    have hne : scanTrace digits 1 (cleared+2) ≠ [] := by
      intro h
      have hh := scan_head digits 1 (cleared+2)
      simp [h] at hh
    rw [eraseTrace,List.getLast?_cons_of_ne_nil hne,scan_last]
    simp only [List.length_nil,Nat.mul_zero,Nat.add_zero]
    have he : 1+(cleared+2)+2 = cleared+5 := by omega
    rw [he]
  | cons bit previous ih =>
    simp only [eraseTrace,List.getLast?_append,ih,Option.some_or,List.length_cons]
    have he : cleared+2+2*previous.length+5 = cleared+2*(previous.length+1)+5 := by omega
    rw [he]

theorem erase_length (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseTrace previous cleared digits).length = 6*previous.length+cleared+7 := by
  induction previous generalizing cleared with
  | nil => simp only [eraseTrace,List.length_cons,scan_length,List.length_nil]; omega
  | cons bit previous ih => simp only [eraseTrace,List.length_append,unit_length,ih,List.length_cons]; omega

theorem erase_chain (previous : List Bool) (cleared : Nat) (digits : List Bool) :
    (eraseTrace previous cleared digits).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  induction previous generalizing cleared with
  | nil =>
    rw [eraseTrace]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [scan_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      exact empty_advance cleared digits
    · exact scan_chain digits 1 (cleared+2)
  | cons bit previous ih =>
    rw [eraseTrace]
    exact append_link _ _ _ _ (unit_chain bit previous cleared digits) (ih (cleared+2))
      (unit_last bit previous cleared digits) (erase_head previous (cleared+2) digits)
      (unit_advance previous cleared digits)

theorem terminal_transfer (relation : Fin 3) (notLess : relation ≠ 1) (previous digits : List Bool) :
    Turing.TM0.step loopMachine (liftCompare (PSTRTMCompareCode054.state (PSTRTMCompareCode054.haltLabel relation)
      (eraseLeft previous) (endRegion digits))) = some (eraseInitial previous 0 digits) := by
  have hr := relation.isLt
  have hn : relation.val ≠ 1 := by intro h; apply notLess; apply Fin.ext; exact h
  have he : relation.val=0 ∨ relation.val=2 := by omega
  rcases he with he | he <;> cases previous <;>
    simp [Turing.TM0.step,loopMachine,liftCompare,compareLabel,PSTRTMCompareCode054.state,
      PSTRTMCompareCode054.haltLabel,he,eraseInitial,eraseLeft,PSTRTMRawNat010.leftBlocks,
      state,endRegion,Turing.Tape.mk₂]

def cleanupTrace (pairs : List (Bool × Bool)) (digits : List Bool) : List (MachineState 81) :=
  eraseTrace (PSTRTMPackLoop043.pairedDigits pairs).reverse 0 digits

def cleanupFinal (pairs : List (Bool × Bool)) (digits : List Bool) : MachineState 81 :=
  state 81 (List.replicate (4*pairs.length+5) false) (PSTRTMIncrement009.blocks digits)

theorem cleanup_head (pairs : List (Bool × Bool)) (digits : List Bool) :
    (cleanupTrace pairs digits).head? = some (eraseInitial (PSTRTMPackLoop043.pairedDigits pairs).reverse 0 digits) :=
  erase_head _ 0 digits

theorem cleanup_last (pairs : List (Bool × Bool)) (digits : List Bool) :
    (cleanupTrace pairs digits).getLast? = some (cleanupFinal pairs digits) := by
  rw [cleanupTrace,erase_last,List.length_reverse,PSTRTMCompareRun059.pairedDigits_length]
  have he : 0+2*(2*pairs.length)+5 = 4*pairs.length+5 := by omega
  rw [he]
  rfl

theorem cleanup_length (pairs : List (Bool × Bool)) (digits : List Bool) :
    (cleanupTrace pairs digits).length = 12*pairs.length+7 := by
  simp only [cleanupTrace,erase_length,List.length_reverse,PSTRTMCompareRun059.pairedDigits_length]
  omega

theorem cleanup_runsFrom (pairs : List (Bool × Bool)) (digits : List Bool) :
    PSTRTMSeq005.RunsFrom loopMachine (eraseInitial (PSTRTMPackLoop043.pairedDigits pairs).reverse 0 digits)
      (cleanupTrace pairs digits) (cleanupFinal pairs digits) :=
  ⟨cleanup_head pairs digits,erase_chain _ 0 digits,cleanup_last pairs digits,loop_halt _ _⟩

/-- All real operands/marker cells are actually erased, and the actual
head reaches the retained counter. This ENTIRE tape equality permits018
without any reset, free copy or assumed archive blankness. -/
theorem cleanup_final_tape (pairs : List (Bool × Bool)) (digits : List Bool) :
    (cleanupFinal pairs digits).Tape = Turing.Tape.mk₁ (PSTRTMIncrement009.blocks digits) := by
  have hb : Turing.ListBlank.mk (List.replicate (4*pairs.length+5) false) = Turing.ListBlank.mk ([] : List Bool) := by
    simpa only [List.nil_append] using PSTRTMPackFinish039.blank_false_suffix [] (4*pairs.length+5)
  simp only [cleanupFinal,state,Turing.Tape.mk₁,Turing.Tape.mk₂]
  rw [hb]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1Cleanup076

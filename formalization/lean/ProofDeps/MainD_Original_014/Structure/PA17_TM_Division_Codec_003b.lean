module
public import Structure.PA17_TM_Division_Codec_003a
public import Common.PSTR_TM_ColumnRewind_067

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
open PaperProofs.Common.Native.RationalControllerComputation

/-- Actual projection of the A track: each B data cell is written false;
the two true flags, arbitrary left context and complete owned-00 suffix
are retained. -/
def clearBMachine : Machine 5 := fun q symbol =>
  match q.val with
  | 0 => some (1, .move .right)
  | 1 => if symbol then some (2, .move .right) else some (5, .move .left)
  | 2 => some (3, .write false)
  | 3 => some (4, .move .right)
  | 4 => if symbol then some (0, .move .right) else none
  | _ => none

def clearBState (q : Fin 6) (left right : List Bool) : MachineState 5 :=
  ⟨q, Turing.Tape.mk₂ left right⟩

def clearBPairs (pairs : List (Bool × Bool)) : List (Bool × Bool) :=
  pairs.map (fun pair => (pair.1, false))

def clearBUnit (a b : Bool) (left right : List Bool) : List (MachineState 5) :=
  [clearBState 0 left (a :: true :: b :: true :: right),
   clearBState 1 (a :: left) (true :: b :: true :: right),
   clearBState 2 (true :: a :: left) (b :: true :: right),
   clearBState 3 (true :: a :: left) (false :: true :: right),
   clearBState 4 (false :: true :: a :: left) (true :: right)]

theorem clearBUnit_chain (a b : Bool) (left right : List Bool) :
    (clearBUnit a b left right).IsChain
      (fun before after => Turing.TM0.step clearBMachine before = some after) := by
  simp [clearBUnit, List.isChain_cons_cons, Turing.TM0.step, clearBMachine,
    clearBState, Turing.Tape.mk₂]

def clearBTrace (context : List Bool) (previous : List (Bool × Bool)) :
    List (Bool × Bool) → List Bool → List (MachineState 5)
  | [], suffix =>
      let left := PSTRTMCompareCode054.leftColumns previous ++ context
      [clearBState 0 left (false :: false :: suffix),
       clearBState 1 (false :: left) (false :: suffix),
       clearBState 5 left (false :: false :: suffix)]
  | (a,b) :: later, suffix =>
      clearBUnit a b (PSTRTMCompareCode054.leftColumns previous ++ context)
        (PSTRTMBinaryAdd024.operandColumns later ++ false :: false :: suffix) ++
      clearBTrace context ((a,false) :: previous) later suffix

theorem clearBTrace_head (context : List Bool) (previous pairs : List (Bool × Bool))
    (suffix : List Bool) :
    (clearBTrace context previous pairs suffix).head? = some
      (clearBState 0 (PSTRTMCompareCode054.leftColumns previous ++ context)
        (PSTRTMBinaryAdd024.operandColumns pairs ++ false :: false :: suffix)) := by
  cases pairs <;> simp [clearBTrace, clearBUnit, PSTRTMBinaryAdd024.operandColumns]

theorem clearBTrace_last (context : List Bool) (previous pairs : List (Bool × Bool))
    (suffix : List Bool) :
    (clearBTrace context previous pairs suffix).getLast? = some
      (clearBState 5
        (PSTRTMCompareCode054.leftColumns ((clearBPairs pairs).reverse ++ previous) ++ context)
        (false :: false :: suffix)) := by
  induction pairs generalizing previous with
  | nil => rfl
  | cons pair later ih =>
      obtain ⟨a,b⟩ := pair
      simp [clearBTrace, ih, clearBPairs, List.reverse_cons, List.append_assoc]

theorem clearBTrace_length (context : List Bool) (previous pairs : List (Bool × Bool))
    (suffix : List Bool) :
    (clearBTrace context previous pairs suffix).length = 5 * pairs.length + 3 := by
  induction pairs generalizing previous with
  | nil => rfl
  | cons pair later ih =>
      obtain ⟨a,b⟩ := pair
      simp only [clearBTrace, List.length_append, clearBUnit, List.length_cons,
        List.length_nil, ih]
      omega

theorem clearBTrace_chain (context : List Bool) (previous pairs : List (Bool × Bool))
    (suffix : List Bool) :
    (clearBTrace context previous pairs suffix).IsChain
      (fun before after => Turing.TM0.step clearBMachine before = some after) := by
  induction pairs generalizing previous with
  | nil =>
      simp [clearBTrace, List.isChain_cons_cons, Turing.TM0.step, clearBMachine,
        clearBState, Turing.Tape.mk₂]
  | cons pair later ih =>
      obtain ⟨a,b⟩ := pair
      apply (clearBUnit_chain a b _ _).append (ih ((a,false) :: previous))
      intro before hb after ha
      simp only [clearBUnit, List.getLast?_cons_cons, List.getLast?_singleton,
        Option.mem_some_iff] at hb
      rw [clearBTrace_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst before
      subst after
      simp [Turing.TM0.step, clearBMachine, clearBState,
        PSTRTMCompareCode054.leftColumns, Turing.Tape.mk₂]

theorem clearB_runsFrom (context : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom clearBMachine
      (clearBState 0 context (PSTRTMBinaryAdd024.operandColumns pairs ++ false :: false :: suffix))
      (clearBTrace context [] pairs suffix)
      (clearBState 5 (PSTRTMCompareCode054.leftColumns (clearBPairs pairs).reverse ++ context)
        (false :: false :: suffix)) := by
  refine ⟨?_, clearBTrace_chain context [] pairs suffix, ?_, ?_⟩
  · simpa only [PSTRTMCompareCode054.leftColumns, List.flatMap_nil, List.nil_append] using
      clearBTrace_head context [] pairs suffix
  · simpa only [List.append_nil] using clearBTrace_last context [] pairs suffix
  · simp [Turing.TM0.step, clearBMachine, clearBState]

/-- Projection followed by the real frozen EOF-to-first-column rewind. -/
def projectAMachine : Machine 11 :=
  PSTRTMSeq005.seqMachine clearBMachine PSTRTMColumnRewind067.rewindMachine

def projectATrace (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    List (MachineState 11) :=
  (clearBTrace (false :: archive) [] pairs suffix).map (PSTRTMSeq005.leftCfg (b := 5)) ++
    (PSTRTMColumnRewind067.fullTrace archive (clearBPairs pairs).reverse
      (false :: false :: suffix)).map (PSTRTMSeq005.rightCfg (a := 5))

theorem projectA_runsFrom (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom projectAMachine
      (PSTRTMSeq005.leftCfg (b := 5)
        (clearBState 0 (false :: archive)
          (PSTRTMBinaryAdd024.operandColumns pairs ++ false :: false :: suffix)))
      (projectATrace archive pairs suffix)
      (PSTRTMSeq005.rightCfg (a := 5)
        (PSTRTMColumnRewind067.state 5 (false :: archive)
          (PSTRTMBinaryAdd024.operandColumns (clearBPairs pairs) ++ false :: false :: suffix))) := by
  apply PSTRTMSeq005.seq_runsFrom clearBMachine PSTRTMColumnRewind067.rewindMachine
    _ _ _ _ _ (clearB_runsFrom (false :: archive) pairs suffix)
  exact PSTRTMColumnRewind067.rewind_runsFrom archive (clearBPairs pairs) (false :: false :: suffix)

theorem projectATrace_length (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    (projectATrace archive pairs suffix).length = 9 * pairs.length + 6 := by
  simp only [projectATrace, List.length_append, List.length_map, clearBTrace_length,
    PSTRTMColumnRewind067.full_length, List.length_reverse, clearBPairs]
  omega

theorem projectATrace_visitedSpace_le (inputLength : Nat) (archive : List Bool)
    (pairs : List (Bool × Bool)) (suffix : List Bool) :
    visitedSpace projectAMachine inputLength (projectATrace archive pairs suffix) ≤
      inputLength + 18 * pairs.length + 13 := by
  have hs := PSTRTMTrace002.visitedSpace_le projectAMachine inputLength (projectATrace archive pairs suffix)
  rw [projectATrace_length] at hs
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003

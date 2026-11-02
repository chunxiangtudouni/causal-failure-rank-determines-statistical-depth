module
public import Common.ROOT_TM_GCD_MapCode_004

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDMap004
open PaperProofs.Common.Native.RationalControllerComputation
local notation "cols" => PSTRTMBinaryAdd024.operandColumns
local notation "leftCols" => PSTRTMCompareCode054.leftColumns

private theorem commands (f : Pair → Pair) (a b : Bool) :
    mapScanMachine f 0 a = some (flagA a, .move .right) ∧
    mapScanMachine f (flagA a) true = some (readB a, .move .right) ∧
    mapScanMachine f (readB a) b = some (pairLabel 0 a b, .move .left) ∧
    mapScanMachine f (pairLabel 0 a b) true = some (pairLabel 1 a b, .move .left) ∧
    mapScanMachine f (pairLabel 1 a b) a = some (pairLabel 2 a b, .write (f (a,b)).1) ∧
    mapScanMachine f (pairLabel 2 a b) (f (a,b)).1 = some (pairLabel 3 a b, .move .right) ∧
    mapScanMachine f (pairLabel 3 a b) true = some (pairLabel 4 a b, .move .right) ∧
    mapScanMachine f (pairLabel 4 a b) b = some (pairLabel 5 a b, .write (f (a,b)).2) ∧
    mapScanMachine f (pairLabel 5 a b) (f (a,b)).2 = some (29, .move .right) := by
  cases a <;> cases b <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def unitTrace (f : Pair → Pair) (a b : Bool) (left right : List Bool) : List (MachineState 30) :=
  [mapState 0 left (a :: true :: b :: true :: right),
    mapState (flagA a) (a :: left) (true :: b :: true :: right),
    mapState (readB a) (true :: a :: left) (b :: true :: right),
    mapState (pairLabel 0 a b) (a :: left) (true :: b :: true :: right),
    mapState (pairLabel 1 a b) left (a :: true :: b :: true :: right),
    mapState (pairLabel 2 a b) left ((f (a,b)).1 :: true :: b :: true :: right),
    mapState (pairLabel 3 a b) ((f (a,b)).1 :: left) (true :: b :: true :: right),
    mapState (pairLabel 4 a b) (true :: (f (a,b)).1 :: left) (b :: true :: right),
    mapState (pairLabel 5 a b) (true :: (f (a,b)).1 :: left) ((f (a,b)).2 :: true :: right),
    mapState 29 ((f (a,b)).2 :: true :: (f (a,b)).1 :: left) (true :: right)]

theorem unit_head (f : Pair → Pair) (a b : Bool) (left right : List Bool) :
    (unitTrace f a b left right).head? = some (mapState 0 left (a :: true :: b :: true :: right)) := rfl
theorem unit_last (f : Pair → Pair) (a b : Bool) (left right : List Bool) :
    (unitTrace f a b left right).getLast? = some
      (mapState 29 ((f (a,b)).2 :: true :: (f (a,b)).1 :: left) (true :: right)) := rfl
theorem unit_length (f : Pair → Pair) (a b : Bool) (left right : List Bool) :
    (unitTrace f a b left right).length = 10 := rfl

theorem unit_chain (f : Pair → Pair) (a b : Bool) (left right : List Bool) :
    (unitTrace f a b left right).IsChain (fun before after => Turing.TM0.step (mapScanMachine f) before = some after) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := commands f a b
  simp [unitTrace, List.isChain_cons_cons, Turing.TM0.step, mapState, Turing.Tape.mk₂,
    h1,h2,h3,h4,h5,h6,h7,h8,h9]

theorem unit_advance (f : Pair → Pair) (left right : List Bool) :
    Turing.TM0.step (mapScanMachine f) (mapState 29 left (true :: right)) =
      some (mapState 0 (true :: left) right) := by
  simp [Turing.TM0.step, mapScanMachine, mapState, Turing.Tape.mk₂]

def endTrace (left suffix : List Bool) : List (MachineState 30) :=
  [mapState 0 left (false :: false :: suffix),
    mapState (flagA false) (false :: left) (false :: suffix),
    mapState 30 left (false :: false :: suffix)]

theorem end_head (left suffix : List Bool) : (endTrace left suffix).head? = some (mapState 0 left (false :: false :: suffix)) := rfl
theorem end_last (left suffix : List Bool) : (endTrace left suffix).getLast? = some (mapState 30 left (false :: false :: suffix)) := rfl
theorem end_length (left suffix : List Bool) : (endTrace left suffix).length = 3 := rfl
theorem end_chain (f : Pair → Pair) (left suffix : List Bool) :
    (endTrace left suffix).IsChain (fun before after => Turing.TM0.step (mapScanMachine f) before = some after) := by
  simp [endTrace, List.isChain_cons_cons, Turing.TM0.step, mapState, mapScanMachine, flagA, Turing.Tape.mk₂]

def mapTrace (f : Pair → Pair) (context : List Bool) (previous : List Pair) :
    List Pair → List Bool → List (MachineState 30)
  | [], suffix => endTrace (leftCols previous ++ context) suffix
  | (a,b) :: later, suffix => unitTrace f a b (leftCols previous ++ context)
      (cols later ++ false :: false :: suffix) ++ mapTrace f context (f (a,b) :: previous) later suffix

theorem map_head (f : Pair → Pair) (context : List Bool) (previous pairs : List Pair) (suffix : List Bool) :
    (mapTrace f context previous pairs suffix).head? = some
      (mapState 0 (leftCols previous ++ context) (cols pairs ++ false :: false :: suffix)) := by
  cases pairs with
  | nil => rfl
  | cons pair later =>
    obtain ⟨a,b⟩ := pair
    simp [mapTrace, List.head?_append, unit_head, PSTRTMBinaryAdd024.operandColumns]

theorem map_last (f : Pair → Pair) (context : List Bool) (previous pairs : List Pair) (suffix : List Bool) :
    (mapTrace f context previous pairs suffix).getLast? = some
      (mapState 30 (leftCols ((pairs.map f).reverse ++ previous) ++ context) (false :: false :: suffix)) := by
  induction pairs generalizing previous with
  | nil => simpa only [mapTrace, List.map_nil, List.reverse_nil, List.nil_append] using end_last _ suffix
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp [mapTrace, List.getLast?_append, ih, List.map_cons, List.reverse_cons, List.append_assoc]

theorem map_length (f : Pair → Pair) (context : List Bool) (previous pairs : List Pair) (suffix : List Bool) :
    (mapTrace f context previous pairs suffix).length = 10 * pairs.length + 3 := by
  induction pairs generalizing previous with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp only [mapTrace, List.length_append, unit_length, ih, List.length_cons]
    omega

theorem map_chain (f : Pair → Pair) (context : List Bool) (previous pairs : List Pair) (suffix : List Bool) :
    (mapTrace f context previous pairs suffix).IsChain (fun before after => Turing.TM0.step (mapScanMachine f) before = some after) := by
  induction pairs generalizing previous with
  | nil => exact end_chain f _ suffix
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    rw [mapTrace]
    apply (unit_chain f a b _ _).append (ih (f (a,b) :: previous))
    intro before hb after ha
    simp only [unit_last, Option.mem_some_iff] at hb
    simp only [map_head, Option.mem_some_iff] at ha
    subst before
    subst after
    simpa only [PSTRTMCompareCode054.leftColumns, List.flatMap_cons, List.cons_append, List.nil_append] using
      unit_advance f ((f (a,b)).2 :: true :: (f (a,b)).1 :: (leftCols previous ++ context))
        (cols later ++ false :: false :: suffix)

theorem map_runsFrom (f : Pair → Pair) (context : List Bool) (pairs : List Pair) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (mapScanMachine f) (mapState 0 context (cols pairs ++ false :: false :: suffix))
      (mapTrace f context [] pairs suffix)
      (mapState 30 (leftCols (pairs.map f).reverse ++ context) (false :: false :: suffix)) := by
  refine ⟨?_, map_chain f context [] pairs suffix, ?_, map_halt f _ _⟩
  · simpa only [PSTRTMCompareCode054.leftColumns, List.flatMap_nil, List.nil_append] using map_head f context [] pairs suffix
  · simpa only [List.append_nil] using map_last f context [] pairs suffix

def residentMapMachine (f : Pair → Pair) : Machine 36 :=
  PSTRTMSeq005.seqMachine (mapScanMachine f) PSTRTMColumnRewind067.rewindMachine

def residentMapTrace (f : Pair → Pair) (archive : List Bool) (pairs : List Pair) (suffix : List Bool) :
    List (MachineState 36) :=
  (mapTrace f (false :: archive) [] pairs suffix).map (PSTRTMSeq005.leftCfg (b:=5)) ++
    (PSTRTMColumnRewind067.fullTrace archive (pairs.map f).reverse (false :: false :: suffix)).map
      (PSTRTMSeq005.rightCfg (a:=30))

def residentMapInitial (archive : List Bool) (pairs : List Pair) (suffix : List Bool) : MachineState 36 :=
  PSTRTMSeq005.leftCfg (b:=5) (mapState 0 (false :: archive) (cols pairs ++ false :: false :: suffix))
def residentMapFinal (f : Pair → Pair) (archive : List Bool) (pairs : List Pair) (suffix : List Bool) : MachineState 36 :=
  PSTRTMSeq005.rightCfg (a:=30) (PSTRTMColumnRewind067.state 5 (false :: archive)
    (cols (pairs.map f) ++ false :: false :: suffix))

/-- Full true framed transduction with real EOF-to-start rewind. This is
an actual finite Bool TM trace, not a semantic list-map assumption. -/
theorem residentMap_runsFrom (f : Pair → Pair) (archive : List Bool) (pairs : List Pair) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (residentMapMachine f) (residentMapInitial archive pairs suffix)
      (residentMapTrace f archive pairs suffix) (residentMapFinal f archive pairs suffix) := by
  apply PSTRTMSeq005.seq_runsFrom (mapScanMachine f) PSTRTMColumnRewind067.rewindMachine
    (mapState 0 (false :: archive) (cols pairs ++ false :: false :: suffix))
    (mapState 30 (leftCols (pairs.map f).reverse ++ false :: archive) (false :: false :: suffix))
    (PSTRTMColumnRewind067.state 5 (false :: archive) (cols (pairs.map f) ++ false :: false :: suffix))
    (mapTrace f (false :: archive) [] pairs suffix)
    (PSTRTMColumnRewind067.fullTrace archive (pairs.map f).reverse (false :: false :: suffix))
  · exact map_runsFrom f (false :: archive) pairs suffix
  · exact PSTRTMColumnRewind067.rewind_runsFrom archive (pairs.map f) (false :: false :: suffix)

theorem residentMap_length (f : Pair → Pair) (archive : List Bool) (pairs : List Pair) (suffix : List Bool) :
    (residentMapTrace f archive pairs suffix).length = 14 * pairs.length + 6 := by
  simp only [residentMapTrace, List.length_append, List.length_map, map_length,
    PSTRTMColumnRewind067.full_length, List.length_reverse]
  omega

theorem residentMap_final_tape (f : Pair → Pair) (archive : List Bool) (pairs : List Pair) (suffix : List Bool) :
    (residentMapFinal f archive pairs suffix).Tape =
      Turing.Tape.mk₂ (false :: archive) (cols (pairs.map f) ++ false :: false :: suffix) := rfl

theorem residentMap_visitedSpace_le (f : Pair → Pair) (archive : List Bool) (pairs : List Pair)
    (suffix : List Bool) (inputLength : Nat) :
    visitedSpace (residentMapMachine f) inputLength (residentMapTrace f archive pairs suffix) ≤
      inputLength + 28 * pairs.length + 13 := by
  have h := PSTRTMTrace002.visitedSpace_le (residentMapMachine f) inputLength (residentMapTrace f archive pairs suffix)
  rw [residentMap_length] at h
  omega

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDMap004

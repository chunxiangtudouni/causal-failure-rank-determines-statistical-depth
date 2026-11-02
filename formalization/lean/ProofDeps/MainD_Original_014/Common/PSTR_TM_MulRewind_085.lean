module
public import Common.PSTR_TM_MulPassTrace_081

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulRewind085
open PaperProofs.Common.Native.RationalControllerComputation
local notation "Triple" => PSTRTMMulPassCode079.Triple
local notation "cols" => PSTRTMMulPassCode079.columns
local notation "leftCols" => PSTRTMMulPassCode079.leftColumns

/-- Existing true-flag pair rewind pattern, reused three times per tuple.
Four fixed labels; every flag/data movement and actual false guard is read. -/
def rewindMachine : Machine 3 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .left)
  | 1 => some (if symbol then 2 else 3,if symbol then .move .left else .move .right)
  | 2 => some (1,.move .left)
  | _ => none
def state (q : Fin 4) (left right : List Bool) : MachineState 3 := ⟨q,Turing.Tape.mk₂ left right⟩

def initial (archive : List Bool) : List Triple → List Bool → MachineState 3
  | [],tail => state 1 archive (false::tail)
  | (c,a,b)::earlier,tail => state 1 (b::true::a::true::c::(leftCols earlier++false::archive)) (true::tail)

def rewindTrace (archive : List Bool) : List Triple → List Bool → List (MachineState 3)
  | [],tail => [initial archive [] tail,state 3 (false::archive) tail]
  | (c,a,b)::earlier,tail =>
    initial archive ((c,a,b)::earlier) tail ::
    state 2 (true::a::true::c::(leftCols earlier++false::archive)) (b::true::tail) ::
    state 1 (a::true::c::(leftCols earlier++false::archive)) (true::b::true::tail) ::
    state 2 (true::c::(leftCols earlier++false::archive)) (a::true::b::true::tail) ::
    state 1 (c::(leftCols earlier++false::archive)) (true::a::true::b::true::tail) ::
    state 2 (leftCols earlier++false::archive) (c::true::a::true::b::true::tail) ::
      rewindTrace archive earlier (c::true::a::true::b::true::tail)

theorem rewind_head (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (rewindTrace archive previous tail).head?=some (initial archive previous tail) := by cases previous <;> rfl
theorem rewind_length (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (rewindTrace archive previous tail).length=6*previous.length+2 := by
  induction previous generalizing tail with
  | nil => rfl
  | cons triple earlier ih =>
    obtain ⟨c,a,b⟩ := triple
    simp only [rewindTrace,List.length_cons,ih]
    omega
theorem rewind_last (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (rewindTrace archive previous tail).getLast?=some (state 3 (false::archive) (cols previous.reverse++tail)) := by
  induction previous generalizing tail with
  | nil => rfl
  | cons triple earlier ih =>
    obtain ⟨c,a,b⟩ := triple
    have hne : rewindTrace archive earlier (c::true::a::true::b::true::tail)≠[] := by
      intro h
      have hh := rewind_head archive earlier (c::true::a::true::b::true::tail)
      simp [h] at hh
    simp only [rewindTrace,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMMulPassCode079.columns,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem rewind_chain (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (rewindTrace archive previous tail).IsChain (fun before after => Turing.TM0.step rewindMachine before=some after) := by
  induction previous generalizing tail with
  | nil => simp [rewindTrace,initial,List.isChain_cons_cons,Turing.TM0.step,rewindMachine,state,Turing.Tape.mk₂]
  | cons triple earlier ih =>
    obtain ⟨c,a,b⟩ := triple
    simp only [rewindTrace,List.isChain_cons_cons]
    refine ⟨by simp [initial,Turing.TM0.step,rewindMachine,state,Turing.Tape.mk₂],
      by simp [Turing.TM0.step,rewindMachine,state,Turing.Tape.mk₂],
      by simp [Turing.TM0.step,rewindMachine,state,Turing.Tape.mk₂],
      by simp [Turing.TM0.step,rewindMachine,state,Turing.Tape.mk₂],
      by simp [Turing.TM0.step,rewindMachine,state,Turing.Tape.mk₂],?_⟩
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [rewind_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      cases earlier with
      | nil => simp [initial,PSTRTMMulPassCode079.leftColumns,Turing.TM0.step,rewindMachine,state,Turing.Tape.mk₂]
      | cons triple earlier =>
        obtain ⟨cc,aa,bb⟩ := triple
        simp [initial,PSTRTMMulPassCode079.leftColumns,Turing.TM0.step,rewindMachine,state,Turing.Tape.mk₂]
    · exact ih _

def fullTrace (archive : List Bool) (previous : List Triple) (tail : List Bool) : List (MachineState 3) :=
  state 0 (leftCols previous++false::archive) tail :: rewindTrace archive previous tail
theorem full_head (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (fullTrace archive previous tail).head?=some (state 0 (leftCols previous++false::archive) tail) := rfl
theorem full_length (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (fullTrace archive previous tail).length=6*previous.length+3 := by simp only [fullTrace,List.length_cons,rewind_length]
theorem full_last (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (fullTrace archive previous tail).getLast?=some (state 3 (false::archive) (cols previous.reverse++tail)) := by
  have hne : rewindTrace archive previous tail≠[] := by
    intro h
    have hh := rewind_head archive previous tail
    simp [h] at hh
  rw [fullTrace,List.getLast?_cons_of_ne_nil hne,rewind_last]
theorem full_chain (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (fullTrace archive previous tail).IsChain (fun before after => Turing.TM0.step rewindMachine before=some after) := by
  apply List.isChain_cons.mpr
  constructor
  · intro after ha
    rw [rewind_head] at ha
    have he := Option.mem_some_iff.mp ha
    subst after
    cases previous with
    | nil => simp [initial,PSTRTMMulPassCode079.leftColumns,Turing.TM0.step,rewindMachine,state,Turing.Tape.mk₂]
    | cons triple earlier =>
      obtain ⟨c,a,b⟩ := triple
      simp [initial,PSTRTMMulPassCode079.leftColumns,Turing.TM0.step,rewindMachine,state,Turing.Tape.mk₂]
  · exact rewind_chain archive previous tail

theorem rewind_runsFrom (archive : List Bool) (triples : List Triple) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom rewindMachine (state 0 (leftCols triples.reverse++false::archive) tail)
      (fullTrace archive triples.reverse tail) (state 3 (false::archive) (cols triples++tail)) := by
  refine ⟨full_head _ _ _,full_chain _ _ _,?_,?_⟩
  · simpa only [List.reverse_reverse] using full_last archive triples.reverse tail
  · simp [Turing.TM0.step,rewindMachine,state]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulRewind085

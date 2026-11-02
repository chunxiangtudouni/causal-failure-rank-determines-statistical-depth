module
public import Structure.PA17_TM_Division_Init_004b

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionInit004
open PSTRTMBinaryAdd024
open PSTRTMCompareCode054 (leftColumns)

def backInitial (saved : Bool) (archive : List Bool) : List (Bool × Bool) → List Bool → MachineState 66
  | [], tail => state (keep 4 saved) (false::false::archive) (false::tail)
  | (a,b)::previous, tail => state (keep 4 saved)
      (b::true::a::(leftColumns previous ++ sep archive)) (true::tail)

def backTrace (saved : Bool) (archive : List Bool) : List (Bool × Bool) → List Bool → List (MachineState 66)
  | [], tail => [state (keep 4 saved) (false::false::archive) (false::tail),
      state (keep 8 saved) (false::archive) (false::false::tail),
      state (keep 9 saved) archive (false::false::false::tail)]
  | (a,b)::previous, tail =>
    state (keep 4 saved) (b::true::a::(leftColumns previous ++ sep archive)) (true::tail) ::
    state (keep 5 saved) (true::a::(leftColumns previous ++ sep archive)) (b::true::tail) ::
    state (keep 6 saved) (a::(leftColumns previous ++ sep archive)) (true::b::true::tail) ::
    state (keep 7 saved) (leftColumns previous ++ sep archive) (a::true::b::true::tail) ::
      backTrace saved archive previous (a::true::b::true::tail)

theorem back_head (saved : Bool) (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (backTrace saved archive previous tail).head? = some (backInitial saved archive previous tail) := by
  cases previous <;> rfl

theorem back_last (saved : Bool) (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (backTrace saved archive previous tail).getLast? = some
      (state (keep 9 saved) archive (sep (operandColumns previous.reverse ++ tail))) := by
  induction previous generalizing tail with
  | nil => rfl
  | cons pair previous ih =>
    obtain ⟨a,b⟩ := pair
    have hn : backTrace saved archive previous (a::true::b::true::tail) ≠ [] := by
      intro he; have hh := back_head saved archive previous (a::true::b::true::tail); simp [he] at hh
    simp only [backTrace,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hn,ih]
    simp [sep,operandColumns,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem back_length (saved : Bool) (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (backTrace saved archive previous tail).length = 4*previous.length+3 := by
  induction previous generalizing tail with
  | nil => rfl
  | cons pair previous ih => obtain ⟨a,b⟩ := pair; simp only [backTrace,List.length_cons,ih]; omega

theorem back_chain (saved : Bool) (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (backTrace saved archive previous tail).IsChain (fun before after => Turing.TM0.step prefixMachine before = some after) := by
  induction previous generalizing tail with
  | nil => cases saved <;> simp [backTrace,List.isChain_cons_cons,Turing.TM0.step,prefixMachine,state,keep,Turing.Tape.mk₂]
  | cons pair previous ih =>
    obtain ⟨a,b⟩ := pair
    simp only [backTrace,List.isChain_cons_cons]
    refine ⟨?_,?_,?_,?_⟩
    · cases saved <;> simp [Turing.TM0.step,prefixMachine,state,keep,Turing.Tape.mk₂]
    · cases saved <;> simp [Turing.TM0.step,prefixMachine,state,keep,Turing.Tape.mk₂]
    · cases saved <;> simp [Turing.TM0.step,prefixMachine,state,keep,Turing.Tape.mk₂]
    · apply List.isChain_cons.mpr
      refine ⟨?_,ih _⟩
      intro after ha
      rw [back_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      cases previous <;> cases saved <;> simp [backInitial,leftColumns,sep,Turing.TM0.step,prefixMachine,state,keep,Turing.Tape.mk₂]

def fullBackTrace (saved : Bool) (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) : List (MachineState 66) :=
  state (keep 3 saved) (leftColumns previous ++ sep archive) tail :: backTrace saved archive previous tail

theorem fullBack_segment (saved : Bool) (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    Segment (state (keep 3 saved) (leftColumns previous ++ sep archive) tail) (fullBackTrace saved archive previous tail)
      (state (keep 9 saved) archive (sep (operandColumns previous.reverse ++ tail))) := by
  refine ⟨rfl,?_,?_⟩
  · apply List.isChain_cons.mpr
    refine ⟨?_,back_chain saved archive previous tail⟩
    intro after ha
    rw [back_head] at ha
    have he := Option.mem_some_iff.mp ha
    subst after
    cases previous <;> cases saved <;> simp [backInitial,leftColumns,sep,Turing.TM0.step,prefixMachine,state,keep,Turing.Tape.mk₂]
  · have hn : backTrace saved archive previous tail ≠ [] := by
      intro he; have hh := back_head saved archive previous tail; simp [he] at hh
    rw [fullBackTrace,List.getLast?_cons_of_ne_nil hn,back_last]

theorem fullBack_length (saved : Bool) (archive : List Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (fullBackTrace saved archive previous tail).length = 4*previous.length+4 := by
  simp only [fullBackTrace,List.length_cons,back_length]

def archiveInitial (saved : Bool) : List (Bool × Bool) → List Bool → MachineState 66
  | [], tail => state (keep 10 saved) [] (false::tail)
  | (a,b)::previous, tail => state (keep 10 saved) (b::true::a::leftColumns previous) (true::tail)

def archiveTrace (saved : Bool) : List (Bool × Bool) → List Bool → List (MachineState 66)
  | [], tail =>
    [state (keep 10 saved) [] (false::tail),state (keep 14 saved) [] (true::tail),
      state (keep 15 saved) [] (false::true::tail),state (keep 16 saved) [] (true::true::tail),
      state (keep 17 saved) [] (false::true::true::tail),state (keep 18 saved) [] (true::true::true::tail),
      state (keep 19 saved) [] (false::true::true::true::tail),state 50 [] (saved::true::true::true::tail)]
  | (a,b)::previous, tail =>
    state (keep 10 saved) (b::true::a::leftColumns previous) (true::tail) ::
    state (keep 11 saved) (true::a::leftColumns previous) (b::true::tail) ::
    state (keep 12 saved) (a::leftColumns previous) (true::b::true::tail) ::
    state (keep 13 saved) (leftColumns previous) (a::true::b::true::tail) ::
      archiveTrace saved previous (a::true::b::true::tail)

theorem archive_head (saved : Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (archiveTrace saved previous tail).head? = some (archiveInitial saved previous tail) := by cases previous <;> rfl

theorem archive_last (saved : Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (archiveTrace saved previous tail).getLast? = some
      (state 50 [] (operandColumns ((saved,true)::previous.reverse) ++ tail)) := by
  induction previous generalizing tail with
  | nil => rfl
  | cons pair previous ih =>
    obtain ⟨a,b⟩ := pair
    have hn : archiveTrace saved previous (a::true::b::true::tail) ≠ [] := by
      intro he; have hh := archive_head saved previous (a::true::b::true::tail); simp [he] at hh
    simp only [archiveTrace,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hn,ih]
    simp [operandColumns,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem archive_length (saved : Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (archiveTrace saved previous tail).length = 4*previous.length+8 := by
  induction previous generalizing tail with
  | nil => rfl
  | cons pair previous ih => obtain ⟨a,b⟩ := pair; simp only [archiveTrace,List.length_cons,ih]; omega

theorem archive_chain (saved : Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (archiveTrace saved previous tail).IsChain (fun before after => Turing.TM0.step prefixMachine before = some after) := by
  induction previous generalizing tail with
  | nil => cases saved <;> simp [archiveTrace,List.isChain_cons_cons,Turing.TM0.step,prefixMachine,state,keep,Turing.Tape.mk₂]
  | cons pair previous ih =>
    obtain ⟨a,b⟩ := pair
    simp only [archiveTrace,List.isChain_cons_cons]
    refine ⟨?_,?_,?_,?_⟩
    · cases saved <;> simp [Turing.TM0.step,prefixMachine,state,keep,Turing.Tape.mk₂]
    · cases saved <;> simp [Turing.TM0.step,prefixMachine,state,keep,Turing.Tape.mk₂]
    · cases saved <;> simp [Turing.TM0.step,prefixMachine,state,keep,Turing.Tape.mk₂]
    · apply List.isChain_cons.mpr
      refine ⟨?_,ih _⟩
      intro after ha
      rw [archive_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      cases previous <;> cases saved <;> simp [archiveInitial,leftColumns,Turing.TM0.step,prefixMachine,state,keep,Turing.Tape.mk₂]

def fullArchiveTrace (saved : Bool) (previous : List (Bool × Bool)) (tail : List Bool) : List (MachineState 66) :=
  state (keep 9 saved) (leftColumns previous) tail :: archiveTrace saved previous tail

theorem fullArchive_segment (saved : Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    Segment (state (keep 9 saved) (leftColumns previous) tail) (fullArchiveTrace saved previous tail)
      (state 50 [] (operandColumns ((saved,true)::previous.reverse) ++ tail)) := by
  refine ⟨rfl,?_,?_⟩
  · apply List.isChain_cons.mpr
    refine ⟨?_,archive_chain saved previous tail⟩
    intro after ha
    rw [archive_head] at ha
    have he := Option.mem_some_iff.mp ha
    subst after
    cases previous <;> cases saved <;> simp [archiveInitial,leftColumns,Turing.TM0.step,prefixMachine,state,keep,Turing.Tape.mk₂]
  · have hn : archiveTrace saved previous tail ≠ [] := by
      intro he; have hh := archive_head saved previous tail; simp [he] at hh
    rw [fullArchiveTrace,List.getLast?_cons_of_ne_nil hn,archive_last]

theorem fullArchive_length (saved : Bool) (previous : List (Bool × Bool)) (tail : List Bool) :
    (fullArchiveTrace saved previous tail).length = 4*previous.length+9 := by
  simp only [fullArchiveTrace,List.length_cons,archive_length]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionInit004

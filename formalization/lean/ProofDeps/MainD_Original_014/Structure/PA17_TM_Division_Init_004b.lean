module
public import Structure.PA17_TM_Division_Init_004a

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionInit004
open PSTRTMBinaryAdd024
open PSTRTMCompareCode054 (leftColumns)

def seekTrace (left : List Bool) : List (Bool × Bool) → List Bool → List (MachineState 66)
  | [], tail => [state 0 left (false::false::tail), state 1 (false::left) (false::tail), state 5 left (false::false::tail)]
  | (a,b)::later, tail =>
    [state 0 left (a::true::b::true::(operandColumns later ++ false::false::tail)),
      state 1 (a::left) (true::b::true::(operandColumns later ++ false::false::tail)),
      state 2 (true::a::left) (b::true::(operandColumns later ++ false::false::tail)),
      state 3 (b::true::a::left) (true::(operandColumns later ++ false::false::tail))] ++
      seekTrace (true::b::true::a::left) later tail

theorem seek_head (left : List Bool) (pairs : List (Bool × Bool)) (tail : List Bool) :
    (seekTrace left pairs tail).head? = some (state 0 left (operandColumns pairs ++ false::false::tail)) := by
  cases pairs with
  | nil => rfl
  | cons pair later => obtain ⟨a,b⟩ := pair; rfl

theorem seek_last (left : List Bool) (pairs : List (Bool × Bool)) (tail : List Bool) :
    (seekTrace left pairs tail).getLast? = some
      (state 5 (leftColumns pairs.reverse ++ left) (false::false::tail)) := by
  induction pairs generalizing left with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp only [seekTrace, List.getLast?_append, ih, Option.some_or]
    congr 2
    simp [leftColumns, List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem seek_length (left : List Bool) (pairs : List (Bool × Bool)) (tail : List Bool) :
    (seekTrace left pairs tail).length = 4*pairs.length + 3 := by
  induction pairs generalizing left with
  | nil => rfl
  | cons pair later ih => obtain ⟨a,b⟩ := pair; simp only [seekTrace,List.length_append,List.length_cons,List.length_nil,ih]; omega

theorem seek_chain (left : List Bool) (pairs : List (Bool × Bool)) (tail : List Bool) :
    (seekTrace left pairs tail).IsChain (fun before after => Turing.TM0.step prefixMachine before = some after) := by
  induction pairs generalizing left with
  | nil => simp [seekTrace,List.isChain_cons_cons,Turing.TM0.step,prefixMachine,state,Turing.Tape.mk₂]
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    rw [seekTrace]
    apply List.IsChain.append
    · simp [List.isChain_cons_cons,Turing.TM0.step,prefixMachine,state,Turing.Tape.mk₂]
    · exact ih _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [seek_head,Option.mem_some_iff] at ha
      subst before
      subst after
      simp [Turing.TM0.step,prefixMachine,state,Turing.Tape.mk₂]

theorem seek_segment (left : List Bool) (pairs : List (Bool × Bool)) (tail : List Bool) :
    Segment (state 0 left (operandColumns pairs ++ false::false::tail)) (seekTrace left pairs tail)
      (state 5 (leftColumns pairs.reverse ++ left) (false::false::tail)) :=
  ⟨seek_head left pairs tail, seek_chain left pairs tail, seek_last left pairs tail⟩

def extractTrace (a b : Bool) (left right : List Bool) : List (MachineState 66) :=
  [state 5 (true::b::true::a::left) right,
    state 6 (b::true::a::left) (true::right),
    state 7 (true::a::left) (b::true::right),
    state 8 (a::left) (true::b::true::right),
    state 9 left (a::true::b::true::right),
    state (keep 0 a) left (false::true::b::true::right),
    state (keep 1 a) (false::left) (true::b::true::right),
    state (keep 2 a) (false::left) (false::b::true::right),
    state (keep 3 a) left (false::false::b::true::right)]

theorem extract_head (a b : Bool) (left right : List Bool) :
    (extractTrace a b left right).head? = some (state 5 (true::b::true::a::left) right) := rfl
theorem extract_last (a b : Bool) (left right : List Bool) :
    (extractTrace a b left right).getLast? = some (state (keep 3 a) left (false::false::b::true::right)) := rfl
theorem extract_length (a b : Bool) (left right : List Bool) : (extractTrace a b left right).length = 9 := rfl

theorem extract_chain (a b : Bool) (left right : List Bool) :
    (extractTrace a b left right).IsChain (fun before after => Turing.TM0.step prefixMachine before = some after) := by
  cases a <;> simp [extractTrace,List.isChain_cons_cons,Turing.TM0.step,prefixMachine,state,keep,Turing.Tape.mk₂]

theorem extract_segment (a b : Bool) (left right : List Bool) :
    Segment (state 5 (true::b::true::a::left) right) (extractTrace a b left right)
      (state (keep 3 a) left (false::false::b::true::right)) :=
  ⟨extract_head a b left right,extract_chain a b left right,extract_last a b left right⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionInit004

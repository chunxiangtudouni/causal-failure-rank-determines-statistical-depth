module
public import Structure.PA17_TM_Division_Init_004c

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionInit004
open PSTRTMBinaryAdd024
open PSTRTMCompareCode054 (leftColumns)

def returnLabel (first : Bool) : Fin 67 := if first then 50 else 54
def returnTrace (first : Bool) (left : List Bool) : List (Bool × Bool) → List Bool → List (MachineState 66)
  | [], tail => [state (returnLabel first) left (sep tail),state 51 (false::left) (false::false::tail),
      state 56 (false::false::left) (false::tail),state 0 (sep left) tail]
  | (a,b)::later, tail =>
    [state (returnLabel first) left (a::true::b::true::(operandColumns later ++ sep tail)),
      state 51 (a::left) (true::b::true::(operandColumns later ++ sep tail)),
      state 52 (true::a::left) (b::true::(operandColumns later ++ sep tail)),
      state 53 (b::true::a::left) (true::(operandColumns later ++ sep tail))] ++
      returnTrace false (true::b::true::a::left) later tail

theorem return_head (first : Bool) (left : List Bool) (pairs : List (Bool × Bool)) (tail : List Bool) :
    (returnTrace first left pairs tail).head? = some (state (returnLabel first) left (operandColumns pairs ++ sep tail)) := by
  cases pairs with
  | nil => rfl
  | cons pair later => obtain ⟨a,b⟩ := pair; rfl

theorem return_last (first : Bool) (left : List Bool) (pairs : List (Bool × Bool)) (tail : List Bool) :
    (returnTrace first left pairs tail).getLast? = some (state 0 (sep (leftColumns pairs.reverse ++ left)) tail) := by
  induction pairs generalizing first left with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp only [returnTrace,List.getLast?_append,ih,Option.some_or]
    congr 2
    simp [sep,leftColumns,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem return_length (first : Bool) (left : List Bool) (pairs : List (Bool × Bool)) (tail : List Bool) :
    (returnTrace first left pairs tail).length = 4*pairs.length+4 := by
  induction pairs generalizing first left with
  | nil => rfl
  | cons pair later ih => obtain ⟨a,b⟩ := pair; simp only [returnTrace,List.length_append,List.length_cons,List.length_nil,ih]; omega

theorem return_chain (first : Bool) (left : List Bool) (pairs : List (Bool × Bool)) (tail : List Bool) :
    (returnTrace first left pairs tail).IsChain (fun before after => Turing.TM0.step prefixMachine before = some after) := by
  induction pairs generalizing first left with
  | nil => cases first <;> simp [returnTrace,returnLabel,sep,List.isChain_cons_cons,Turing.TM0.step,prefixMachine,state,Turing.Tape.mk₂]
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    rw [returnTrace]
    apply List.IsChain.append
    · cases first <;> simp [returnLabel,List.isChain_cons_cons,Turing.TM0.step,prefixMachine,state,Turing.Tape.mk₂]
    · exact ih _ _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [return_head,Option.mem_some_iff] at ha
      subst before
      subst after
      simp [returnLabel,Turing.TM0.step,prefixMachine,state,Turing.Tape.mk₂]

theorem return_segment (first : Bool) (left : List Bool) (pairs : List (Bool × Bool)) (tail : List Bool) :
    Segment (state (returnLabel first) left (operandColumns pairs ++ sep tail)) (returnTrace first left pairs tail)
      (state 0 (sep (leftColumns pairs.reverse ++ left)) tail) :=
  ⟨return_head first left pairs tail,return_chain first left pairs tail,return_last first left pairs tail⟩

def markerTail : List (Bool × Bool) → List Bool
  | [] => []
  | (_,b)::later => b::true::(markedColumns later ++ [false,false])

theorem marked_decompose (pairs : List (Bool × Bool)) :
    markedColumns pairs ++ [false,false] = false::false::markerTail pairs := by
  cases pairs with
  | nil => rfl
  | cons pair later => obtain ⟨a,b⟩ := pair; rfl

def triggerTrace (archive tail : List Bool) : List (MachineState 66) :=
  [state 0 (sep archive) (false::false::tail),state 1 (false::sep archive) (false::tail),
    state 5 (sep archive) (false::false::tail),state 6 (false::false::archive) (false::false::false::tail),
    state 60 (sep archive) (false::false::tail)]

theorem trigger_segment (archive tail : List Bool) :
    Segment (state 0 (sep archive) (false::false::tail)) (triggerTrace archive tail)
      (state 60 (sep archive) (false::false::tail)) := by
  refine ⟨rfl,?_,rfl⟩
  simp [triggerTrace,sep,List.isChain_cons_cons,Turing.TM0.step,prefixMachine,state,Turing.Tape.mk₂]

theorem trigger_length (archive tail : List Bool) : (triggerTrace archive tail).length = 5 := rfl

def cleanupTrace (left : List Bool) : List (Bool × Bool) → List (MachineState 66)
  | [] => [state 60 left [false,false],state 61 (false::left) [false],
      state 62 (false::left) [true],state 63 (true::false::left) [],
      state 64 (false::true::false::left) [],state 65 (false::true::false::left) [true],
      state 66 (true::false::true::false::left) []]
  | (_,b)::later =>
    [state 60 left (false::false::b::true::(markedColumns later ++ [false,false])),
      state 61 (false::left) (false::b::true::(markedColumns later ++ [false,false])),
      state 62 (false::left) (true::b::true::(markedColumns later ++ [false,false])),
      state 63 (true::false::left) (b::true::(markedColumns later ++ [false,false])),
      state 64 (b::true::false::left) (true::(markedColumns later ++ [false,false]))] ++
      cleanupTrace (true::b::true::false::left) later

theorem cleanup_head (left : List Bool) (pairs : List (Bool × Bool)) :
    (cleanupTrace left pairs).head? = some (state 60 left (markedColumns pairs ++ [false,false])) := by
  cases pairs with
  | nil => rfl
  | cons pair later => obtain ⟨a,b⟩ := pair; rfl

theorem cleanup_last (left : List Bool) (pairs : List (Bool × Bool)) :
    (cleanupTrace left pairs).getLast? = some
      (state 66 (leftColumns (residentPairs pairs ++ [(false,false)]).reverse ++ left) []) := by
  induction pairs generalizing left with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp only [cleanupTrace,List.getLast?_append,ih,Option.some_or]
    congr 2
    simp [residentPairs,leftColumns,List.reverse_append,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem cleanup_length (left : List Bool) (pairs : List (Bool × Bool)) :
    (cleanupTrace left pairs).length = 5*pairs.length+7 := by
  induction pairs generalizing left with
  | nil => rfl
  | cons pair later ih => obtain ⟨a,b⟩ := pair; simp only [cleanupTrace,List.length_append,List.length_cons,List.length_nil,ih]; omega

theorem cleanup_chain (left : List Bool) (pairs : List (Bool × Bool)) :
    (cleanupTrace left pairs).IsChain (fun before after => Turing.TM0.step prefixMachine before = some after) := by
  induction pairs generalizing left with
  | nil => simp [cleanupTrace,List.isChain_cons_cons,Turing.TM0.step,prefixMachine,state,Turing.Tape.mk₂]
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    rw [cleanupTrace]
    apply List.IsChain.append
    · simp [List.isChain_cons_cons,Turing.TM0.step,prefixMachine,state,Turing.Tape.mk₂]
    · exact ih _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [cleanup_head,Option.mem_some_iff] at ha
      subst before
      subst after
      simp [Turing.TM0.step,prefixMachine,state,Turing.Tape.mk₂]

theorem cleanup_segment (left : List Bool) (pairs : List (Bool × Bool)) :
    Segment (state 60 left (markedColumns pairs ++ [false,false])) (cleanupTrace left pairs)
      (state 66 (leftColumns (residentPairs pairs ++ [(false,false)]).reverse ++ left) []) :=
  ⟨cleanup_head left pairs,cleanup_chain left pairs,cleanup_last left pairs⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionInit004

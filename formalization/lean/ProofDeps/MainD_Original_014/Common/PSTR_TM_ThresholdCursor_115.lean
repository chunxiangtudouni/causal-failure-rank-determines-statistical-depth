module
public import Common.PSTR_TM_ThresholdRisk_114

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCursor115
open PaperProofs.Common.Native.RationalControllerComputation

/-- Actual denominator-flag scan across the REAL00 formed by its decoder
guard and the original natural Datum tag. HALT is at the original depth
raw header; every earlier risk cell and every later depth cell is retained. -/
def cursorMachine : Machine 2 := fun q symbol => match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (if symbol then 0 else 2,.move .right)
  | _ => none
def state (q : Fin 3) (left right : List Bool) : MachineState 2 := ⟨q,Turing.Tape.mk₂ left right⟩
def cursorTrace (left : List Bool) : List Bool → List Bool → List (MachineState 2)
  | [],tail => [state 0 left (false::false::tail),state 1 (false::left) (false::tail),state 2 (false::false::left) tail]
  | bit::later,tail => [state 0 left (bit::true::(PSTRTMIncrement009.blocks later++false::false::tail)),
      state 1 (bit::left) (true::(PSTRTMIncrement009.blocks later++false::false::tail))] ++
      cursorTrace (true::bit::left) later tail

theorem cursor_head (left digits tail : List Bool) : (cursorTrace left digits tail).head?=some
    (state 0 left (PSTRTMIncrement009.blocks digits++false::false::tail)) := by cases digits <;> rfl
theorem cursor_last (left digits tail : List Bool) : (cursorTrace left digits tail).getLast?=some
    (state 2 (false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) tail) := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    have hne : cursorTrace (true::bit::left) later tail≠[] := by
      intro h
      have hh := cursor_head (true::bit::left) later tail
      simp [h] at hh
    simp only [cursorTrace,List.cons_append,List.nil_append,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMRawNat010.leftBlocks,List.reverse_cons,List.flatMap_append,List.append_assoc]
theorem cursor_length (left digits tail : List Bool) : (cursorTrace left digits tail).length=2*digits.length+3 := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih => simp only [cursorTrace,List.length_append,List.length_cons,List.length_nil,ih]; omega
theorem cursor_chain (left digits tail : List Bool) :
    (cursorTrace left digits tail).IsChain (fun before after => Turing.TM0.step cursorMachine before=some after) := by
  induction digits generalizing left with
  | nil => simp [cursorTrace,List.isChain_cons_cons,Turing.TM0.step,cursorMachine,state,Turing.Tape.mk₂]
  | cons bit later ih =>
    rw [cursorTrace]
    apply List.IsChain.append
    · simp [List.isChain_cons_cons,Turing.TM0.step,cursorMachine,state,Turing.Tape.mk₂]
    · exact ih _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [cursor_head,Option.mem_some_iff] at ha
      subst before
      subst after
      simp [Turing.TM0.step,cursorMachine,state,Turing.Tape.mk₂]
theorem cursor_halt (left right : List Bool) : Turing.TM0.step cursorMachine (state 2 left right)=none := by
  simp [Turing.TM0.step,cursorMachine,state]

theorem cursor_runsFrom (left digits tail : List Bool) :
    PSTRTMSeq005.RunsFrom cursorMachine (state 0 left (PSTRTMIncrement009.blocks digits++false::false::tail))
      (cursorTrace left digits tail) (state 2 (false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) tail) :=
  ⟨cursor_head left digits tail,cursor_chain left digits tail,cursor_last left digits tail,cursor_halt _ _⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCursor115

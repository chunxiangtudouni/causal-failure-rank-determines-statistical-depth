module
public import Common.PSTR_TM_B1PrepareTrace_070

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1PrepareFrame119
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMB1PrepareCode069 PSTRTMB1PrepareTrace070

/-- The SAME actual32-label B1 preparation, behind a real false guard.
No archive bit is erased or read as a flag; all allocation is on the right. -/
def prepareTrace (archive : List Bool) (pairs : List (Bool × Bool)) : List (MachineState 31) :=
  seekTrace (false::archive) pairs ++
    allocateTrace (PSTRTMCompareCode054.leftColumns pairs.reverse ++ false::archive) ++
    (PSTRTMColumnRewind067.fullTrace archive (paddedPairs pairs).reverse suffix).map liftRewind

def prepareFinal (archive : List Bool) (pairs : List (Bool × Bool)) : MachineState 31 :=
  state 31 (false::archive) (preparedWord pairs)

theorem allocate_advance (archive : List Bool) (pairs : List (Bool × Bool)) :
    Turing.TM0.step prepareMachine
      (state 25 ([false,true,false,true,false] ++ (PSTRTMCompareCode054.leftColumns pairs.reverse ++ false::archive))
        [false,true,false,false,true]) =
      some (liftRewind (PSTRTMColumnRewind067.state 0
        (PSTRTMCompareCode054.leftColumns (paddedPairs pairs).reverse ++ false::archive) suffix)) := by
  have hl : PSTRTMCompareCode054.leftColumns (paddedPairs pairs).reverse =
      [true,false,true,false] ++ PSTRTMCompareCode054.leftColumns pairs.reverse := by
    simp [paddedPairs, List.reverse_append, PSTRTMCompareCode054.leftColumns]
  rw [hl]
  simp [Turing.TM0.step,prepareMachine,state,liftRewind,embedRewind,
    PSTRTMColumnRewind067.state,suffix,Turing.Tape.mk₂]

private theorem append_link (xs ys : List (MachineState 31)) (last first : MachineState 31)
    (hx : xs.IsChain (fun a b => Turing.TM0.step prepareMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step prepareMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step prepareMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step prepareMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

theorem prepare_head (archive : List Bool) (pairs : List (Bool × Bool)) :
    (prepareTrace archive pairs).head? = some
      (state 0 (false::archive) (PSTRTMBinaryAdd024.operandColumns pairs)) := by
  simp only [prepareTrace,List.head?_append,seek_head,Option.some_or]

theorem prepare_last (archive : List Bool) (pairs : List (Bool × Bool)) :
    (prepareTrace archive pairs).getLast? = some (prepareFinal archive pairs) := by
  simp only [prepareTrace,List.getLast?_append,List.getLast?_map,PSTRTMColumnRewind067.full_last,
    List.reverse_reverse,Option.map_some,Option.some_or]
  rfl

theorem prepare_length (archive : List Bool) (pairs : List (Bool × Bool)) :
    (prepareTrace archive pairs).length = 8*pairs.length+33 := by
  simp only [prepareTrace,List.length_append,List.length_map,seek_length,allocate_length,
    PSTRTMColumnRewind067.full_length,List.length_reverse,paddedPairs,List.length_append,
    List.length_cons,List.length_nil]
  omega

theorem prepare_chain (archive : List Bool) (pairs : List (Bool × Bool)) :
    (prepareTrace archive pairs).IsChain (fun a b => Turing.TM0.step prepareMachine a = some b) := by
  unfold prepareTrace
  refine append_link _ _
    (state 25 ([false,true,false,true,false] ++ (PSTRTMCompareCode054.leftColumns pairs.reverse ++ false::archive))
      [false,true,false,false,true])
    (liftRewind (PSTRTMColumnRewind067.state 0
      (PSTRTMCompareCode054.leftColumns (paddedPairs pairs).reverse ++ false::archive) suffix)) ?_ ?_ ?_ ?_ (allocate_advance archive pairs)
  · exact append_link _ _ _ _ (seek_chain (false::archive) pairs) (allocate_chain _)
      (seek_last (false::archive) pairs) (allocate_head _) (seek_advance _)
  · exact rewind_chain _ (PSTRTMColumnRewind067.full_chain archive (paddedPairs pairs).reverse suffix)
  · simp only [List.getLast?_append,allocate_last,Option.some_or]
  · simp only [List.head?_map,PSTRTMColumnRewind067.full_head,Option.map_some]

theorem prepare_runsFrom (archive : List Bool) (pairs : List (Bool × Bool)) :
    PSTRTMSeq005.RunsFrom prepareMachine
      (state 0 (false::archive) (PSTRTMBinaryAdd024.operandColumns pairs))
      (prepareTrace archive pairs) (prepareFinal archive pairs) :=
  ⟨prepare_head archive pairs,prepare_chain archive pairs,prepare_last archive pairs,prepare_halt _ _⟩

theorem prepare_final_tape (archive : List Bool) (pairs : List (Bool × Bool)) :
    (prepareFinal archive pairs).Tape=Turing.Tape.mk₂ (false::archive) (preparedWord pairs) := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1PrepareFrame119

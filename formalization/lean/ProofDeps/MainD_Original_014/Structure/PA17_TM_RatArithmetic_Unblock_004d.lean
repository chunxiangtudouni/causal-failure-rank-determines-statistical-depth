module
public import Structure.PA17_TM_RatArithmetic_Unblock_004c

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticUnblock004
open PSTRTMUnblock018

/-- Reuse the dormant label13. The original second OWN false is really
written true, then the original inverse rotations run unchanged. -/
def markerMachine : Machine 19 := fun q symbol =>
  if q = 1 ∧ symbol = false then some (13, .write true)
  else if q = 13 then some (2, .move .left)
  else unblockMachine q symbol

def undoSafe (s : MachineState 19) : Prop := s.q ≠ 1 ∧ s.q ≠ 13

private theorem state_safe (q : Fin 20) (left right : List Bool) (hq : q ≠ 1 ∧ q ≠ 13) :
    undoSafe (state q left right) := hq

theorem scanRight_safe (bit : Bool) (k : Nat) (left tail : List Bool) :
    ∀ s ∈ scanRight bit k left tail, undoSafe s := by
  induction k generalizing left with
  | zero =>
    intro s hs
    simp only [scanRight,List.mem_singleton] at hs
    subst s
    cases bit <;> exact state_safe _ _ _ (by decide)
  | succ k ih =>
    intro s hs
    rcases List.mem_cons.mp hs with hs | hs
    · subst s
      cases bit <;> exact state_safe _ _ _ (by decide)
    · exact ih _ s hs

theorem scanLeft_safe (k : Nat) (left tail : List Bool) :
    ∀ s ∈ scanLeft k left tail, undoSafe s := by
  induction k generalizing tail with
  | zero =>
    intro s hs
    simp only [scanLeft,List.mem_singleton] at hs
    subst s
    exact state_safe _ _ _ (by decide)
  | succ k ih =>
    intro s hs
    rcases List.mem_cons.mp hs with hs | hs
    · subst s
      exact state_safe _ _ _ (by decide)
    · exact ih _ s hs

theorem inverseUnit_safe (bit : Bool) (k : Nat) (left tail : List Bool) :
    ∀ s ∈ inverseUnit bit k left tail, undoSafe s := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_append.mp hs with hs | hs
    · rcases List.mem_append.mp hs with hs | hs
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
        rcases hs with hs | hs | hs | hs
        · subst s; exact state_safe _ _ _ (by decide)
        · subst s; exact state_safe _ _ _ (by decide)
        · subst s; exact state_safe _ _ _ (by decide)
        · subst s; cases bit <;> exact state_safe _ _ _ (by decide)
      · exact scanRight_safe _ _ _ _ s hs
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with hs | hs | hs <;> subst s <;> exact state_safe _ _ _ (by decide)
  · exact scanLeft_safe _ _ _ s hs

theorem undo_safe (archive suffix previous tail : List Bool) :
    ∀ s ∈ undoTrace archive suffix previous tail, undoSafe s := by
  induction previous generalizing tail with
  | nil =>
    intro s hs
    simp only [undoTrace,doneTrace,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with hs | hs | hs <;> subst s <;> exact state_safe _ _ _ (by decide)
  | cons bit previous ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact inverseUnit_safe _ _ _ _ s hs
    · exact ih _ s hs

theorem marker_step_eq (s : MachineState 19) (hs : undoSafe s) :
    Turing.TM0.step markerMachine s = Turing.TM0.step unblockMachine s := by
  rcases s with ⟨q,tape⟩
  simp only [undoSafe] at hs
  simp [Turing.TM0.step,markerMachine,hs.1,hs.2]

theorem marker_undo_chain (archive suffix previous tail : List Bool) :
    (undoTrace archive suffix previous tail).IsChain
      (fun a b => Turing.TM0.step markerMachine a = some b) := by
  apply (undo_chain archive suffix previous tail).imp_of_mem_imp
  intro a b ha _ hab
  rw [marker_step_eq a (undo_safe archive suffix previous tail a ha)]
  exact hab

def markerSeek (archive suffix previous : List Bool) : List Bool → List (MachineState 19)
  | [] =>
    [state 0 (PSTRTMRawNat010.leftBlocks previous ++ false::archive) (false::false::suffix),
     state 1 (false::(PSTRTMRawNat010.leftBlocks previous ++ false::archive)) (false::suffix),
     state 13 (false::(PSTRTMRawNat010.leftBlocks previous ++ false::archive)) (true::suffix)]
  | bit::later =>
    state 0 (PSTRTMRawNat010.leftBlocks previous ++ false::archive)
      (PSTRTMIncrement009.blocks (bit::later) ++ false::false::suffix) ::
    state 1 (bit::(PSTRTMRawNat010.leftBlocks previous ++ false::archive))
      (true::(PSTRTMIncrement009.blocks later ++ false::false::suffix)) ::
    markerSeek archive suffix (bit::previous) later

theorem markerSeek_head (archive suffix previous digits : List Bool) :
    (markerSeek archive suffix previous digits).head? = some
      (state 0 (PSTRTMRawNat010.leftBlocks previous ++ false::archive)
        (PSTRTMIncrement009.blocks digits ++ false::false::suffix)) := by
  cases digits <;> rfl

theorem markerSeek_length (archive suffix previous digits : List Bool) :
    (markerSeek archive suffix previous digits).length = 2*digits.length+3 := by
  induction digits generalizing previous with
  | nil => rfl
  | cons bit later ih => simp only [markerSeek,List.length_cons,ih]; omega

theorem markerSeek_last (archive suffix previous digits : List Bool) :
    (markerSeek archive suffix previous digits).getLast? = some
      (state 13 (false::(PSTRTMRawNat010.leftBlocks (digits.reverse ++ previous) ++ false::archive))
        (true::suffix)) := by
  induction digits generalizing previous with
  | nil => rfl
  | cons bit later ih =>
    have hne : markerSeek archive suffix (bit::previous) later ≠ [] := by
      have hh := markerSeek_head archive suffix (bit::previous) later
      intro h
      simp [h] at hh
    simp only [markerSeek,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

theorem markerSeek_chain (archive suffix previous digits : List Bool) :
    (markerSeek archive suffix previous digits).IsChain
      (fun a b => Turing.TM0.step markerMachine a = some b) := by
  induction digits generalizing previous with
  | nil =>
    simp [markerSeek,List.isChain_cons_cons,Turing.TM0.step,markerMachine,
      unblockMachine,state,Turing.Tape.mk₂]
  | cons bit later ih =>
    rw [markerSeek]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step,markerMachine,unblockMachine,state,Turing.Tape.mk₂,PSTRTMIncrement009.blocks]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [markerSeek_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      simp [Turing.TM0.step,markerMachine,unblockMachine,state,Turing.Tape.mk₂,PSTRTMRawNat010.leftBlocks]
    · exact ih _

def markerTrace (archive digits suffix : List Bool) : List (MachineState 19) :=
  markerSeek archive suffix [] digits ++ undoTrace archive (true::suffix) digits.reverse []

theorem marker_length (archive digits suffix : List Bool) :
    (markerTrace archive digits suffix).length = digits.length^2+11*digits.length+6 := by
  simp only [markerTrace,List.length_append,markerSeek_length,undo_length,List.length_reverse,List.length_nil]
  ring

theorem marker_chain (archive digits suffix : List Bool) :
    (markerTrace archive digits suffix).IsChain
      (fun a b => Turing.TM0.step markerMachine a = some b) := by
  apply (markerSeek_chain archive suffix [] digits).append
    (marker_undo_chain archive (true::suffix) digits.reverse [])
  intro last hl first hf
  rw [markerSeek_last] at hl
  rw [undo_head] at hf
  have he := Option.mem_some_iff.mp hl
  have hg := Option.mem_some_iff.mp hf
  subst last
  subst first
  simp [Turing.TM0.step,markerMachine,state,Turing.Tape.mk₂,PSTRTMUnblockTrace019.rawWord]

theorem marker_runsFrom (archive digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom markerMachine
      (state 0 (false::archive) (PSTRTMIncrement009.blocks digits ++ false::false::suffix))
      (markerTrace archive digits suffix)
      (state 19 (false::archive) (PSTRTMUnblockTrace019.rawWord digits ++ true::suffix)) := by
  refine ⟨?_,marker_chain archive digits suffix,?_,?_⟩
  · simp [markerTrace,List.head?_append,markerSeek_head,PSTRTMRawNat010.leftBlocks]
  · simp [markerTrace,List.getLast?_append,undo_last]
  · simp [Turing.TM0.step,markerMachine,unblockMachine,state]

theorem marker_time_le (archive digits suffix : List Bool) :
    (markerTrace archive digits suffix).length ≤ 32*(digits.length+1)^2 := by
  rw [marker_length]
  nlinarith

theorem marker_visitedSpace_le (archive digits suffix : List Bool) (inputLength : Nat) :
    visitedSpace markerMachine inputLength (markerTrace archive digits suffix) ≤
      inputLength+64*(digits.length+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le markerMachine inputLength (markerTrace archive digits suffix)
  rw [marker_length] at hs
  nlinarith

theorem marker_originalNat_runsFrom (n : Nat) (archive suffix : List Bool) :
    PSTRTMSeq005.RunsFrom markerMachine
      (state 0 (false::archive)
        (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n) ++ false::false::suffix))
      (markerTrace archive (PSTRTMNatValue017.rawPayload n) suffix)
      (state 19 (false::archive) (encodeNat n ++ true::suffix)) := by
  rw [← rawWord_payload]
  exact marker_runsFrom archive (PSTRTMNatValue017.rawPayload n) suffix

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticUnblock004

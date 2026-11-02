module
public import Common.PSTR_TM_Seq_005
public import Common.PSTR_TM_RawNat_010
public import Common.PSTR_TM_Increment_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section
namespace RootB23.Threshold.Uncapped.Erase
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMIncrement009 PSTRTMRawNat010

/-- Erase one flagged field by its actual alternating TRUE flags. Its
two FALSE endpoint cells and every later suffix cell remain literal. -/
def rightCode : Machine 7 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (if symbol then 2 else 7, if symbol then .write false else .move .left)
  | 2 => some (3,.move .left)
  | 3 => some (4,.write false)
  | 4 => some (5,.move .right)
  | 5 => some (0,.move .right)
  | _ => none

def rstate (q : Fin 8) (left right : List Bool) : MachineState 7 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def rightTrace (left : List Bool) : List Bool → List Bool → List (MachineState 7)
  | [],tail => [rstate 0 left (false::false::tail),
      rstate 1 (false::left) (false::tail),rstate 7 left (false::false::tail)]
  | bit::later,tail =>
      [rstate 0 left (bit::true::(blocks later++false::false::tail)),
       rstate 1 (bit::left) (true::(blocks later++false::false::tail)),
       rstate 2 (bit::left) (false::(blocks later++false::false::tail)),
       rstate 3 left (bit::false::(blocks later++false::false::tail)),
       rstate 4 left (false::false::(blocks later++false::false::tail)),
       rstate 5 (false::left) (false::(blocks later++false::false::tail))] ++
      rightTrace (false::false::left) later tail

theorem right_head (left bits tail : List Bool) :
    (rightTrace left bits tail).head? = some (rstate 0 left (blocks bits++false::false::tail)) := by
  cases bits <;> rfl

theorem right_last (left bits tail : List Bool) :
    (rightTrace left bits tail).getLast? = some
      (rstate 7 (List.replicate (2*bits.length) false++left) (false::false::tail)) := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    simp only [rightTrace,List.getLast?_append,ih,Option.some_or,List.length_cons]
    congr 2
    rw [show 2*(later.length+1)=2*later.length+2 by omega,List.replicate_add]
    simp only [List.append_assoc,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append]

theorem right_length (left bits tail : List Bool) :
    (rightTrace left bits tail).length = 6*bits.length+3 := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    simp only [rightTrace,List.length_append,List.length_cons,List.length_nil,ih]
    omega

theorem right_chain (left bits tail : List Bool) :
    (rightTrace left bits tail).IsChain (fun a b => Turing.TM0.step rightCode a = some b) := by
  induction bits generalizing left with
  | nil => simp [rightTrace,List.isChain_cons_cons,rstate,rightCode,Turing.TM0.step,Turing.Tape.mk₂]
  | cons bit later ih =>
    apply List.IsChain.append
    · simp [List.isChain_cons_cons,rstate,rightCode,Turing.TM0.step,Turing.Tape.mk₂]
    · exact ih _
    · intro a ha b hb
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at ha
      rw [right_head] at hb
      have same := Option.mem_some_iff.mp hb
      subst a
      subst b
      simp [rstate,rightCode,Turing.TM0.step,Turing.Tape.mk₂]

theorem right_runsFrom (left bits tail : List Bool) :
    PSTRTMSeq005.RunsFrom rightCode (rstate 0 left (blocks bits++false::false::tail))
      (rightTrace left bits tail)
      (rstate 7 (List.replicate (2*bits.length) false++left) (false::false::tail)) :=
  ⟨right_head _ _ _,right_chain _ _ _,right_last _ _ _,by simp [rstate,rightCode,Turing.TM0.step]⟩

/-- Mirror field erasure clears the raw parser's real flagged archive.
The guard before the field is preserved and every right suffix is paid
and retained. It does not assert that the caller's scratch was blank. -/
def leftCode : Machine 7 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .left)
  | 1 => some (2,.move .left)
  | 2 => some (if symbol then 3 else 7,.write false)
  | 3 => some (4,.move .left)
  | 4 => some (5,.write false)
  | 5 => some (2,.move .left)
  | _ => none

def lstate (q : Fin 8) (left right : List Bool) : MachineState 7 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def leftInitial (base : List Bool) : List Bool → List Bool → MachineState 7
  | [],tail => lstate 2 base (false::tail)
  | bit::earlier,tail => lstate 2 (bit::(leftBlocks earlier++false::base)) (true::tail)

def leftTrace (base : List Bool) : List Bool → List Bool → List (MachineState 7)
  | [],tail => [leftInitial base [] tail,lstate 7 base (false::tail)]
  | bit::earlier,tail =>
      [leftInitial base (bit::earlier) tail,
       lstate 3 (bit::(leftBlocks earlier++false::base)) (false::tail),
       lstate 4 (leftBlocks earlier++false::base) (bit::false::tail),
       lstate 5 (leftBlocks earlier++false::base) (false::false::tail)] ++
      leftTrace base earlier (false::false::tail)

theorem left_head (base earlier tail : List Bool) :
    (leftTrace base earlier tail).head? = some (leftInitial base earlier tail) := by
  cases earlier <;> rfl

theorem left_last (base earlier tail : List Bool) :
    (leftTrace base earlier tail).getLast? = some
      (lstate 7 base (false::(List.replicate (2*earlier.length) false++tail))) := by
  induction earlier generalizing tail with
  | nil => rfl
  | cons bit earlier ih =>
    simp only [leftTrace,List.getLast?_append,ih,Option.some_or,List.length_cons]
    congr 3
    rw [show 2*(earlier.length+1)=2*earlier.length+2 by omega,List.replicate_add]
    simp only [List.append_assoc,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append]

theorem left_length (base earlier tail : List Bool) :
    (leftTrace base earlier tail).length = 4*earlier.length+2 := by
  induction earlier generalizing tail with
  | nil => rfl
  | cons bit earlier ih =>
    simp only [leftTrace,List.length_append,List.length_cons,List.length_nil,ih]
    omega

theorem left_chain (base earlier tail : List Bool) :
    (leftTrace base earlier tail).IsChain (fun a b => Turing.TM0.step leftCode a = some b) := by
  induction earlier generalizing tail with
  | nil => simp [leftTrace,leftInitial,List.isChain_cons_cons,lstate,leftCode,Turing.TM0.step,Turing.Tape.mk₂]
  | cons bit earlier ih =>
    apply List.IsChain.append
    · simp [leftInitial,List.isChain_cons_cons,lstate,leftCode,Turing.TM0.step,Turing.Tape.mk₂]
    · exact ih _
    · intro a ha b hb
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at ha
      rw [left_head] at hb
      have same := Option.mem_some_iff.mp hb
      subst a
      subst b
      cases earlier <;> simp [leftInitial,lstate,leftCode,Turing.TM0.step,Turing.Tape.mk₂,leftBlocks]

theorem left_loop_runsFrom (base earlier tail : List Bool) :
    PSTRTMSeq005.RunsFrom leftCode (leftInitial base earlier tail)
      (leftTrace base earlier tail)
      (lstate 7 base (false::(List.replicate (2*earlier.length) false++tail))) :=
  ⟨left_head _ _ _,left_chain _ _ _,left_last _ _ _,by simp [lstate,leftCode,Turing.TM0.step]⟩

end RootB23.Threshold.Uncapped.Erase

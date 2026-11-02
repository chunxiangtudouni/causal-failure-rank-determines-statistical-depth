module
public import Common.PSTR_TM_ThresholdCapResident_241

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCapLiteral242
open PaperProofs.Common.Native.RationalControllerComputation

/-! A narrow consumer of the actual cap TRUE branch. Its B scratch Datum
has value0,1 or2 and hence at most SIX cells. This fixed code overwrites
that scratch field and genuinely blank RIGHT with the original canonical
Rat Datum1/4, then really returns LEFT eleven cells. The left q archive
is preserved. There is NO claim for arbitrary right suffixes, a free
allocated window, or the uncapped branch. -/

def quarterBits : List Bool :=
  [true,false,true,false,true,true,true,true,false,false,false,true]

theorem quarter_codec : quarterBits = encodeDatum (.rational (1/4 : Rat)) := by
  have numerator : (1/4 : Rat).num = 1 := by
    norm_num [div_eq_mul_inv,Rat.num_mul,Rat.num_inv,Rat.den_inv]
  have denominator : (1/4 : Rat).den = 4 := by
    norm_num [div_eq_mul_inv,Rat.den_mul,Rat.den_inv]
  have positive : ¬(1/4 : Rat) < 0 := by norm_num
  calc
    quarterBits = [true,false]++encodeNat 1++encodeNat 4 := rfl
    _ = encodeDatum (.rational (1/4 : Rat)) := by
      simp only [encodeDatum,numerator,denominator,positive,decide_false,Int.natAbs_one]

/-- Twelve writes, eleven RIGHT and eleven LEFT: fixed35labels. -/
def quarterMachine : Machine 34 := fun q _ =>
  match q.val with
  | 0 => some (1,.write true)
  | 1 => some (2,.move .right)
  | 2 => some (3,.write false)
  | 3 => some (4,.move .right)
  | 4 => some (5,.write true)
  | 5 => some (6,.move .right)
  | 6 => some (7,.write false)
  | 7 => some (8,.move .right)
  | 8 => some (9,.write true)
  | 9 => some (10,.move .right)
  | 10 => some (11,.write true)
  | 11 => some (12,.move .right)
  | 12 => some (13,.write true)
  | 13 => some (14,.move .right)
  | 14 => some (15,.write true)
  | 15 => some (16,.move .right)
  | 16 => some (17,.write false)
  | 17 => some (18,.move .right)
  | 18 => some (19,.write false)
  | 19 => some (20,.move .right)
  | 20 => some (21,.write false)
  | 21 => some (22,.move .right)
  | 22 => some (23,.write true)
  | 23 => some (24,.move .left)
  | 24 => some (25,.move .left)
  | 25 => some (26,.move .left)
  | 26 => some (27,.move .left)
  | 27 => some (28,.move .left)
  | 28 => some (29,.move .left)
  | 29 => some (30,.move .left)
  | 30 => some (31,.move .left)
  | 31 => some (32,.move .left)
  | 32 => some (33,.move .left)
  | 33 => some (34,.move .left)
  | _ => none

def state (q : Fin 35) (left right : List Bool) : MachineState 34 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def quarterTrace (archive : List Bool) (n : Nat) : List (MachineState 34) :=
  [state 0 ((quarterBits.take 0).reverse++archive) ((encodeDatum (.natural n)).drop 0),
   state 1 ((quarterBits.take 0).reverse++archive)
      (quarterBits[0] :: (encodeDatum (.natural n)).drop 1),
   state 2 ((quarterBits.take 1).reverse++archive) ((encodeDatum (.natural n)).drop 1),
   state 3 ((quarterBits.take 1).reverse++archive)
      (quarterBits[1] :: (encodeDatum (.natural n)).drop 2),
   state 4 ((quarterBits.take 2).reverse++archive) ((encodeDatum (.natural n)).drop 2),
   state 5 ((quarterBits.take 2).reverse++archive)
      (quarterBits[2] :: (encodeDatum (.natural n)).drop 3),
   state 6 ((quarterBits.take 3).reverse++archive) ((encodeDatum (.natural n)).drop 3),
   state 7 ((quarterBits.take 3).reverse++archive)
      (quarterBits[3] :: (encodeDatum (.natural n)).drop 4),
   state 8 ((quarterBits.take 4).reverse++archive) ((encodeDatum (.natural n)).drop 4),
   state 9 ((quarterBits.take 4).reverse++archive)
      (quarterBits[4] :: (encodeDatum (.natural n)).drop 5),
   state 10 ((quarterBits.take 5).reverse++archive) ((encodeDatum (.natural n)).drop 5),
   state 11 ((quarterBits.take 5).reverse++archive)
      (quarterBits[5] :: (encodeDatum (.natural n)).drop 6),
   state 12 ((quarterBits.take 6).reverse++archive) ((encodeDatum (.natural n)).drop 6),
   state 13 ((quarterBits.take 6).reverse++archive)
      (quarterBits[6] :: (encodeDatum (.natural n)).drop 7),
   state 14 ((quarterBits.take 7).reverse++archive) ((encodeDatum (.natural n)).drop 7),
   state 15 ((quarterBits.take 7).reverse++archive)
      (quarterBits[7] :: (encodeDatum (.natural n)).drop 8),
   state 16 ((quarterBits.take 8).reverse++archive) ((encodeDatum (.natural n)).drop 8),
   state 17 ((quarterBits.take 8).reverse++archive)
      (quarterBits[8] :: (encodeDatum (.natural n)).drop 9),
   state 18 ((quarterBits.take 9).reverse++archive) ((encodeDatum (.natural n)).drop 9),
   state 19 ((quarterBits.take 9).reverse++archive)
      (quarterBits[9] :: (encodeDatum (.natural n)).drop 10),
   state 20 ((quarterBits.take 10).reverse++archive) ((encodeDatum (.natural n)).drop 10),
   state 21 ((quarterBits.take 10).reverse++archive)
      (quarterBits[10] :: (encodeDatum (.natural n)).drop 11),
   state 22 ((quarterBits.take 11).reverse++archive) ((encodeDatum (.natural n)).drop 11),
   state 23 ((quarterBits.take 11).reverse++archive)
      (quarterBits[11] :: (encodeDatum (.natural n)).drop 12),
   state 24 ((quarterBits.take 10).reverse++archive)
      (quarterBits.drop 10++(encodeDatum (.natural n)).drop 12),
   state 25 ((quarterBits.take 9).reverse++archive)
      (quarterBits.drop 9++(encodeDatum (.natural n)).drop 12),
   state 26 ((quarterBits.take 8).reverse++archive)
      (quarterBits.drop 8++(encodeDatum (.natural n)).drop 12),
   state 27 ((quarterBits.take 7).reverse++archive)
      (quarterBits.drop 7++(encodeDatum (.natural n)).drop 12),
   state 28 ((quarterBits.take 6).reverse++archive)
      (quarterBits.drop 6++(encodeDatum (.natural n)).drop 12),
   state 29 ((quarterBits.take 5).reverse++archive)
      (quarterBits.drop 5++(encodeDatum (.natural n)).drop 12),
   state 30 ((quarterBits.take 4).reverse++archive)
      (quarterBits.drop 4++(encodeDatum (.natural n)).drop 12),
   state 31 ((quarterBits.take 3).reverse++archive)
      (quarterBits.drop 3++(encodeDatum (.natural n)).drop 12),
   state 32 ((quarterBits.take 2).reverse++archive)
      (quarterBits.drop 2++(encodeDatum (.natural n)).drop 12),
   state 33 ((quarterBits.take 1).reverse++archive)
      (quarterBits.drop 1++(encodeDatum (.natural n)).drop 12),
   state 34 ((quarterBits.take 0).reverse++archive)
      (quarterBits.drop 0++(encodeDatum (.natural n)).drop 12)]

theorem quarter_runsFrom (archive : List Bool) (n : Nat) (small : n ≤ 2) :
    PSTRTMSeq005.RunsFrom quarterMachine
      (state 0 archive (encodeDatum (.natural n))) (quarterTrace archive n)
      (state 34 archive (encodeDatum (.rational (1/4 : Rat)))) := by
  rw [←quarter_codec]
  interval_cases n <;> refine ⟨rfl,?_,rfl,?_⟩
  all_goals simp [quarterTrace,List.isChain_cons_cons,Turing.TM0.step,
    quarterMachine,state,quarterBits,Turing.Tape.mk₂,encodeDatum,encodeNat,natBits]

theorem quarter_length (archive : List Bool) (n : Nat) : (quarterTrace archive n).length = 35 := by
  simp only [quarterTrace,List.length_cons,List.length_nil]

theorem quarter_prefix_space (archive : List Bool) (n inputLength clock : Nat) :
    visitedSpace quarterMachine inputLength ((quarterTrace archive n).take clock) ≤ inputLength+71 := by
  have hs := PSTRTMTrace002.visitedSpace_le quarterMachine inputLength ((quarterTrace archive n).take clock)
  have hl : ((quarterTrace archive n).take clock).length ≤ 35 := by
    rw [List.length_take,quarter_length]
    exact Nat.min_le_right _ _
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCapLiteral242


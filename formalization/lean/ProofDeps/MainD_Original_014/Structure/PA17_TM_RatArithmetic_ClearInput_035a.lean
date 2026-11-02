module
public import Common.PSTR_TM_Seq_005

/-! Original-input cleanup header: keep the first TRUE as an actual left
delimiter, clear the following six cells and really move to Nx. Final source
and cache cleanup are separate; no whole rational operator is claimed here. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticClearInput035

open Turing

def headerMachine : Machine 13 := fun q _symbol =>
  if active : q.val<13 then
    some (⟨q.val+1,by omega⟩,
      if q.val%2=0 then .move .right else .write false)
  else none

def headerState (q : Fin 14) (left right : List Bool) : MachineState 13 :=
  ⟨q,Tape.mk₂ left right⟩

def headerTrace (a b c d e f : Bool) (archive word : List Bool) : List (MachineState 13) :=
  [headerState 0 archive (true::a::b::c::d::e::f::word),
   headerState 1 (true::archive) (a::b::c::d::e::f::word),
   headerState 2 (true::archive) (false::b::c::d::e::f::word),
   headerState 3 (false::true::archive) (b::c::d::e::f::word),
   headerState 4 (false::true::archive) (false::c::d::e::f::word),
   headerState 5 (false::false::true::archive) (c::d::e::f::word),
   headerState 6 (false::false::true::archive) (false::d::e::f::word),
   headerState 7 (false::false::false::true::archive) (d::e::f::word),
   headerState 8 (false::false::false::true::archive) (false::e::f::word),
   headerState 9 (false::false::false::false::true::archive) (e::f::word),
   headerState 10 (false::false::false::false::true::archive) (false::f::word),
   headerState 11 (false::false::false::false::false::true::archive) (f::word),
   headerState 12 (false::false::false::false::false::true::archive) (false::word),
   headerState 13 (List.replicate 6 false++true::archive) word]

theorem header_runsFrom (a b c d e f : Bool) (archive word : List Bool) :
    PSTRTMSeq005.RunsFrom headerMachine
      (headerState 0 archive (true::a::b::c::d::e::f::word))
      (headerTrace a b c d e f archive word)
      (headerState 13 (List.replicate 6 false++true::archive) word) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [headerTrace,List.isChain_cons_cons,TM0.step,headerMachine,headerState,Tape.mk₂]
  · simp [TM0.step,headerMachine,headerState]

theorem header_length (a b c d e f : Bool) (archive word : List Bool) :
    (headerTrace a b c d e f archive word).length=14 := rfl

theorem header_prefix_space (a b c d e f : Bool) (archive word : List Bool)
    (prefixLength inputLength : Nat) :
    visitedSpace headerMachine inputLength ((headerTrace a b c d e f archive word).take prefixLength) ≤
      inputLength+29 := by
  have hs := PSTRTMTrace002.visitedSpace_le headerMachine inputLength
    ((headerTrace a b c d e f archive word).take prefixLength)
  have hp : ((headerTrace a b c d e f archive word).take prefixLength).length≤14 := by
    rw [List.length_take,header_length]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticClearInput035

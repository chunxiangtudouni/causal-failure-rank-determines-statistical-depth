module
public import Common.PSTR_TM_Seq_005
public import Common.PSTR_TM_PackFinish_039

/-! Actual constant output for the zero-denominator branch. The seven bits
belong to fixed code, not an operand-dependent answer. The caller must really
select this branch from its actual zero sensor and provide seven owned cells.
The whole four-Rat caller/selection/cleanup is not claimed here. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticLiteral027

open Turing

/-- Seven actual WRITEs, six RIGHT moves and six LEFT moves. Unlike the
mk1-only prepend codec, this preserves an arbitrary external left archive
and returns to the same first owned cell, with an arbitrary right suffix. -/
def literalMachine : Machine 19 := fun q _symbol =>
  if active : q.val < 19 then
    some (⟨q.val+1,by omega⟩,
      match q.val with
      | 0 | 6 | 10 | 12 => .write true
      | 2 | 4 | 8 => .write false
      | 1 | 3 | 5 | 7 | 9 | 11 => .move .right
      | _ => .move .left)
  else none

def literalState (q : Fin 20) (left right : List Bool) : MachineState 19 :=
  ⟨q,Tape.mk₂ left right⟩

def literalWord : List Bool := [true,false,false,true,false,true,true]

def literalTrace (a b c d e f g : Bool) (archive suffix : List Bool) :
    List (MachineState 19) :=
  [literalState 0 archive (a::b::c::d::e::f::g::suffix),
   literalState 1 archive (true::b::c::d::e::f::g::suffix),
   literalState 2 (true::archive) (b::c::d::e::f::g::suffix),
   literalState 3 (true::archive) (false::c::d::e::f::g::suffix),
   literalState 4 (false::true::archive) (c::d::e::f::g::suffix),
   literalState 5 (false::true::archive) (false::d::e::f::g::suffix),
   literalState 6 (false::false::true::archive) (d::e::f::g::suffix),
   literalState 7 (false::false::true::archive) (true::e::f::g::suffix),
   literalState 8 (true::false::false::true::archive) (e::f::g::suffix),
   literalState 9 (true::false::false::true::archive) (false::f::g::suffix),
   literalState 10 (false::true::false::false::true::archive) (f::g::suffix),
   literalState 11 (false::true::false::false::true::archive) (true::g::suffix),
   literalState 12 (true::false::true::false::false::true::archive) (g::suffix),
   literalState 13 (true::false::true::false::false::true::archive) (true::suffix),
   literalState 14 (false::true::false::false::true::archive) (true::true::suffix),
   literalState 15 (true::false::false::true::archive) (false::true::true::suffix),
   literalState 16 (false::false::true::archive) (true::false::true::true::suffix),
   literalState 17 (false::true::archive) (false::true::false::true::true::suffix),
   literalState 18 (true::archive) (false::false::true::false::true::true::suffix),
   literalState 19 archive (literalWord++suffix)]

theorem literal_runsFrom (a b c d e f g : Bool) (archive suffix : List Bool) :
    PSTRTMSeq005.RunsFrom literalMachine
      (literalState 0 archive (a::b::c::d::e::f::g::suffix))
      (literalTrace a b c d e f g archive suffix)
      (literalState 19 archive (literalWord++suffix)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [literalTrace,List.isChain_cons_cons,TM0.step,literalMachine,
      literalState,literalWord,Tape.mk₂]
  · simp [TM0.step,literalMachine,literalState]

theorem literal_word_codec : literalWord=encodeNat 0++encodeNat 1++[true] := rfl

theorem literal_length (a b c d e f g : Bool) (archive suffix : List Bool) :
    (literalTrace a b c d e f g archive suffix).length=20 := rfl

theorem literal_prefix_space (a b c d e f g : Bool) (archive suffix : List Bool)
    (prefixLength inputLength : Nat) :
    visitedSpace literalMachine inputLength
      ((literalTrace a b c d e f g archive suffix).take prefixLength) ≤ inputLength+41 := by
  have hs := PSTRTMTrace002.visitedSpace_le literalMachine inputLength
    ((literalTrace a b c d e f g archive suffix).take prefixLength)
  have hp : ((literalTrace a b c d e f g archive suffix).take prefixLength).length≤20 := by
    rw [List.length_take,literal_length]
    omega
  omega

/-- The genuine infinite blank tail supplies the seven owned cells. This
does not erase a nonblank external suffix or assert a finite blank window. -/
theorem literal_blank_runsFrom (archive : List Bool) :
    PSTRTMSeq005.RunsFrom literalMachine (literalState 0 archive [])
      (literalTrace false false false false false false false archive [])
      (literalState 19 archive (encodeNat 0++encodeNat 1++[true])) := by
  have blank : Tape.mk₂ archive (List.replicate 7 false)=Tape.mk₂ archive [] := by
    change Tape.mk₂ archive ([]++List.replicate 7 false)=Tape.mk₂ archive []
    unfold Tape.mk₂
    rw [PSTRTMPackFinish039.blank_false_suffix]
  have hr := literal_runsFrom false false false false false false false archive []
  simpa only [literalState,literal_word_codec,show
    (false::false::false::false::false::false::false::[] : List Bool)=List.replicate 7 false by rfl,
    blank,List.append_nil] using hr

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticLiteral027

module
public import Common.PSTR_TM_Seq_005

/-! Five actual prefix writes. This is a fixed local controller with two
entry ports selected by a prior REAL sign computation, not a whole Rat
arithmetic machine or an extra original input sign. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPrefix020

open Turing

def prefixLabel (negative : Bool) (q : Fin 11) : Fin 22 :=
  ⟨(if negative then 11 else 0)+q.val,by
    have h:=q.isLt
    cases negative <;> simp <;> omega⟩

def prefixMachine : Machine 21 := fun q _symbol =>
  if active : q.val%11<10 then
    some (⟨q.val+1,by have hq:=q.isLt;omega⟩,
      match q.val%11 with
      | 0 | 2 | 4 | 6 | 8 => .move .left
      | 1 => .write (decide (11≤q.val))
      | 3 | 5 | 9 => .write true
      | _ => .write false)
  else none

def prefixState (negative : Bool) (q : Fin 11) (left right : List Bool) : MachineState 21 :=
  ⟨prefixLabel negative q,Tape.mk₂ left right⟩

def prefixWord (negative : Bool) (word : List Bool) : List Bool :=
  true::false::true::true::negative::word

def prefixTrace (negative a b c d e : Bool) (archive word : List Bool) : List (MachineState 21) :=
  [prefixState negative 0 (a::b::c::d::e::archive) word,
   prefixState negative 1 (b::c::d::e::archive) (a::word),
   prefixState negative 2 (b::c::d::e::archive) (negative::word),
   prefixState negative 3 (c::d::e::archive) (b::negative::word),
   prefixState negative 4 (c::d::e::archive) (true::negative::word),
   prefixState negative 5 (d::e::archive) (c::true::negative::word),
   prefixState negative 6 (d::e::archive) (true::true::negative::word),
   prefixState negative 7 (e::archive) (d::true::true::negative::word),
   prefixState negative 8 (e::archive) (false::true::true::negative::word),
   prefixState negative 9 archive (e::false::true::true::negative::word),
   prefixState negative 10 archive (prefixWord negative word)]

/-- The five cells are actual owned cells immediately LEFT of the raw pair.
Every old bit may be arbitrary. No cell is inserted or head reset for free. -/
theorem prefix_runsFrom (negative a b c d e : Bool) (archive word : List Bool) :
    PSTRTMSeq005.RunsFrom prefixMachine
      (prefixState negative 0 (a::b::c::d::e::archive) word)
      (prefixTrace negative a b c d e archive word)
      (prefixState negative 10 archive (prefixWord negative word)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · cases negative <;> simp [prefixTrace,List.isChain_cons_cons,TM0.step,
      prefixMachine,prefixState,prefixLabel,prefixWord,Tape.mk₂]
  · cases negative <;> simp [TM0.step,prefixMachine,prefixState,prefixLabel]

theorem prefix_length (negative a b c d e : Bool) (archive word : List Bool) :
    (prefixTrace negative a b c d e archive word).length=11 := rfl

theorem prefix_prefix_space (negative a b c d e : Bool) (archive word : List Bool)
    (prefixLength inputLength : Nat) :
    visitedSpace prefixMachine inputLength
      ((prefixTrace negative a b c d e archive word).take prefixLength) ≤ inputLength+23 := by
  have hs := PSTRTMTrace002.visitedSpace_le prefixMachine inputLength
    ((prefixTrace negative a b c d e archive word).take prefixLength)
  have hp : ((prefixTrace negative a b c d e archive word).take prefixLength).length ≤ 11 := by
    rw [List.length_take,prefix_length]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPrefix020

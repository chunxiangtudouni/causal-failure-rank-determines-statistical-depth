module
public import Structure.RootB23_Threshold_NatSplice_001

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace RootB23.Threshold.PacketSteps
open PaperProofs.Common.Native.RationalControllerComputation Turing

def skipCode : Machine 3 := fun q _=>match q.val with
  | 0=>some (1,.move .right)
  | 1=>some (2,.move .right)
  | 2=>some (3,.move .right)
  | _=>none
def skipTrace (left right : List Bool) : List (MachineState 3) :=
  [⟨0,Tape.mk₂ left (true::false::true::right)⟩,
   ⟨1,Tape.mk₂ (true::left) (false::true::right)⟩,
   ⟨2,Tape.mk₂ (false::true::left) (true::right)⟩,
   ⟨3,Tape.mk₂ (true::false::true::left) right⟩]
theorem skip_runsFrom (left right : List Bool) :
    PSTRTMSeq005.RunsFrom skipCode ⟨0,Tape.mk₂ left (true::false::true::right)⟩
      (skipTrace left right) ⟨3,Tape.mk₂ (true::false::true::left) right⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [skipTrace,List.isChain_cons_cons,TM0.step,skipCode,Tape.mk₂]
  · simp [TM0.step,skipCode]

/-- Overwrite the actual old outer footer and four owned cells with
the literal Nat1 Datum and new outer footer; return by four real LEFTs. -/
def appendCode : Machine 13 := fun q _=>match q.val with
  | 0=>some (1,.write false)
  | 1=>some (2,.move .right)
  | 2=>some (3,.write true)
  | 3=>some (4,.move .right)
  | 4=>some (5,.write false)
  | 5=>some (6,.move .right)
  | 6=>some (7,.write true)
  | 7=>some (8,.move .right)
  | 8=>some (9,.write true)
  | 9=>some (10,.move .left)
  | 10=>some (11,.move .left)
  | 11=>some (12,.move .left)
  | 12=>some (13,.move .left)
  | _=>none
def appendTrace (left suffix : List Bool) : List (MachineState 13) :=
  [⟨0,Tape.mk₂ left (true::false::false::false::false::suffix)⟩,
   ⟨1,Tape.mk₂ left (false::false::false::false::false::suffix)⟩,
   ⟨2,Tape.mk₂ (false::left) (false::false::false::false::suffix)⟩,
   ⟨3,Tape.mk₂ (false::left) (true::false::false::false::suffix)⟩,
   ⟨4,Tape.mk₂ (true::false::left) (false::false::false::suffix)⟩,
   ⟨5,Tape.mk₂ (true::false::left) (false::false::false::suffix)⟩,
   ⟨6,Tape.mk₂ (false::true::false::left) (false::false::suffix)⟩,
   ⟨7,Tape.mk₂ (false::true::false::left) (true::false::suffix)⟩,
   ⟨8,Tape.mk₂ (true::false::true::false::left) (false::suffix)⟩,
   ⟨9,Tape.mk₂ (true::false::true::false::left) (true::suffix)⟩,
   ⟨10,Tape.mk₂ (false::true::false::left) (true::true::suffix)⟩,
   ⟨11,Tape.mk₂ (true::false::left) (false::true::true::suffix)⟩,
   ⟨12,Tape.mk₂ (false::left) (true::false::true::true::suffix)⟩,
   ⟨13,Tape.mk₂ left (false::true::false::true::true::suffix)⟩]
theorem append_runsFrom (left suffix : List Bool) :
    PSTRTMSeq005.RunsFrom appendCode
      ⟨0,Tape.mk₂ left (true::false::false::false::false::suffix)⟩ (appendTrace left suffix)
      ⟨13,Tape.mk₂ left (false::true::false::true::true::suffix)⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [appendTrace,List.isChain_cons_cons,TM0.step,appendCode,Tape.mk₂]
  · simp [TM0.step,appendCode]

/-- Count1's three cells and two real LEFT cells are overwritten by
the canonical count2 header. The old Rat body is never shifted/reset. -/
def headerCode : Machine 10 := fun q _=>match q.val with
  | 0=>some (1,.move .left)
  | 1=>some (2,.write true)
  | 2=>some (3,.move .left)
  | 3=>some (4,.write false)
  | 4=>some (5,.move .left)
  | 5=>some (6,.write false)
  | 6=>some (7,.move .left)
  | 7=>some (8,.write true)
  | 8=>some (9,.move .left)
  | 9=>some (10,.write true)
  | _=>none
def headerTrace (archive body : List Bool) : List (MachineState 10) :=
  [⟨0,Tape.mk₂ (true::false::true::false::false::archive) body⟩,
   ⟨1,Tape.mk₂ (false::true::false::false::archive) (true::body)⟩,
   ⟨2,Tape.mk₂ (false::true::false::false::archive) (true::body)⟩,
   ⟨3,Tape.mk₂ (true::false::false::archive) (false::true::body)⟩,
   ⟨4,Tape.mk₂ (true::false::false::archive) (false::true::body)⟩,
   ⟨5,Tape.mk₂ (false::false::archive) (true::false::true::body)⟩,
   ⟨6,Tape.mk₂ (false::false::archive) (false::false::true::body)⟩,
   ⟨7,Tape.mk₂ (false::archive) (false::false::false::true::body)⟩,
   ⟨8,Tape.mk₂ (false::archive) (true::false::false::true::body)⟩,
   ⟨9,Tape.mk₂ archive (false::true::false::false::true::body)⟩,
   ⟨10,Tape.mk₂ archive (true::true::false::false::true::body)⟩]
theorem header_runsFrom (archive body : List Bool) :
    PSTRTMSeq005.RunsFrom headerCode
      ⟨0,Tape.mk₂ (true::false::true::false::false::archive) body⟩ (headerTrace archive body)
      ⟨10,Tape.mk₂ archive (true::true::false::false::true::body)⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [headerTrace,List.isChain_cons_cons,TM0.step,headerCode,Tape.mk₂]
  · simp [TM0.step,headerCode]

end RootB23.Threshold.PacketSteps

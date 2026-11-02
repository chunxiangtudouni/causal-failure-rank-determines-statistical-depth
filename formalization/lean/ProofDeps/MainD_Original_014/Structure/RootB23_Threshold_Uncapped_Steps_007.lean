module
public import Structure.PA17_TM_RatArithmetic_Allocate_013d

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section
namespace RootB23.Threshold.Uncapped.Steps
open PaperProofs.Common.Native.RationalControllerComputation

def twoRightCode : Machine 2 := fun q _ =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (2,.move .right)
  | _ => none

def twoRightTrace (left : List Bool) (x y : Bool) (tail : List Bool) : List (MachineState 2) :=
  [⟨0,Turing.Tape.mk₂ left (x::y::tail)⟩,
   ⟨1,Turing.Tape.mk₂ (x::left) (y::tail)⟩,
   ⟨2,Turing.Tape.mk₂ (y::x::left) tail⟩]

theorem twoRight_runsFrom (left : List Bool) (x y : Bool) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom twoRightCode ⟨0,Turing.Tape.mk₂ left (x::y::tail)⟩
      (twoRightTrace left x y tail) ⟨2,Turing.Tape.mk₂ (y::x::left) tail⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [twoRightTrace,List.isChain_cons_cons,Turing.TM0.step,twoRightCode,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,twoRightCode]

def fourRightCode : Machine 4 := fun q _ =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (2,.move .right)
  | 2 => some (3,.move .right)
  | 3 => some (4,.move .right)
  | _ => none

def fourRightTrace (left : List Bool) (x y z t : Bool) (tail : List Bool) : List (MachineState 4) :=
  [⟨0,Turing.Tape.mk₂ left (x::y::z::t::tail)⟩,
   ⟨1,Turing.Tape.mk₂ (x::left) (y::z::t::tail)⟩,
   ⟨2,Turing.Tape.mk₂ (y::x::left) (z::t::tail)⟩,
   ⟨3,Turing.Tape.mk₂ (z::y::x::left) (t::tail)⟩,
   ⟨4,Turing.Tape.mk₂ (t::z::y::x::left) tail⟩]

theorem fourRight_runsFrom (left : List Bool) (x y z t : Bool) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom fourRightCode ⟨0,Turing.Tape.mk₂ left (x::y::z::t::tail)⟩
      (fourRightTrace left x y z t tail) ⟨4,Turing.Tape.mk₂ (t::z::y::x::left) tail⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [fourRightTrace,List.isChain_cons_cons,Turing.TM0.step,fourRightCode,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,fourRightCode]

/-- The original rational Datum has exactly a TRUE type tag and FALSE
positive-sign bit. Both physical preceding cells are actually written. -/
def prefixCode : Machine 4 := fun q _ =>
  match q.val with
  | 0 => some (1,.move .left)
  | 1 => some (2,.write false)
  | 2 => some (3,.move .left)
  | 3 => some (4,.write true)
  | _ => none

def prefixTrace (archive : List Bool) (oldSign oldTag : Bool) (word : List Bool) : List (MachineState 4) :=
  [⟨0,Turing.Tape.mk₂ (oldSign::oldTag::archive) word⟩,
   ⟨1,Turing.Tape.mk₂ (oldTag::archive) (oldSign::word)⟩,
   ⟨2,Turing.Tape.mk₂ (oldTag::archive) (false::word)⟩,
   ⟨3,Turing.Tape.mk₂ archive (oldTag::false::word)⟩,
   ⟨4,Turing.Tape.mk₂ archive (true::false::word)⟩]

theorem prefix_runsFrom (archive : List Bool) (oldSign oldTag : Bool) (word : List Bool) :
    PSTRTMSeq005.RunsFrom prefixCode ⟨0,Turing.Tape.mk₂ (oldSign::oldTag::archive) word⟩
      (prefixTrace archive oldSign oldTag word) ⟨4,Turing.Tape.mk₂ archive (true::false::word)⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [prefixTrace,List.isChain_cons_cons,Turing.TM0.step,prefixCode,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,prefixCode]

/-- One actual anchor at DEN EOF and three actual erasures of the old
0010 marker. The head then enters the real exhausted-DEPTH field. -/
def anchorCode : Machine 8 := fun q _ =>
  match q.val with
  | 0 => some (1,.write true)
  | 1 => some (2,.move .right)
  | 2 => some (3,.write false)
  | 3 => some (4,.move .right)
  | 4 => some (5,.write false)
  | 5 => some (6,.move .right)
  | 6 => some (7,.write false)
  | 7 => some (8,.move .right)
  | _ => none

def anchorTrace (left tail : List Bool) : List (MachineState 8) :=
  [⟨0,Turing.Tape.mk₂ left (false::false::true::false::tail)⟩,
   ⟨1,Turing.Tape.mk₂ left (true::false::true::false::tail)⟩,
   ⟨2,Turing.Tape.mk₂ (true::left) (false::true::false::tail)⟩,
   ⟨3,Turing.Tape.mk₂ (true::left) (false::true::false::tail)⟩,
   ⟨4,Turing.Tape.mk₂ (false::true::left) (true::false::tail)⟩,
   ⟨5,Turing.Tape.mk₂ (false::true::left) (false::false::tail)⟩,
   ⟨6,Turing.Tape.mk₂ (false::false::true::left) (false::tail)⟩,
   ⟨7,Turing.Tape.mk₂ (false::false::true::left) (false::tail)⟩,
   ⟨8,Turing.Tape.mk₂ (false::false::false::true::left) tail⟩]

theorem anchor_runsFrom (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom anchorCode ⟨0,Turing.Tape.mk₂ left (false::false::true::false::tail)⟩
      (anchorTrace left tail) ⟨8,Turing.Tape.mk₂ (false::false::false::true::left) tail⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [anchorTrace,List.isChain_cons_cons,Turing.TM0.step,anchorCode,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,anchorCode]

def clearCode : Machine 1 := fun q _ => if q.val=0 then some (1,.write false) else none

def clearTrace (left tail : List Bool) : List (MachineState 1) :=
  [⟨0,Turing.Tape.mk₂ left (true::tail)⟩,⟨1,Turing.Tape.mk₂ left (false::tail)⟩]

theorem clear_runsFrom (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom clearCode ⟨0,Turing.Tape.mk₂ left (true::tail)⟩
      (clearTrace left tail) ⟨1,Turing.Tape.mk₂ left (false::tail)⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [clearTrace,List.isChain_cons_cons,Turing.TM0.step,clearCode,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,clearCode]

open PA17TMRatArithmeticAllocate013

def returnTrace (head : Bool) (gap : Nat) (archive suffix : List Bool) : List (MachineState 1) :=
  seekState 0 (List.replicate gap false++true::archive) (head::suffix) ::
    seekLeftTrace gap archive (head::suffix)

theorem return_runsFrom (head : Bool) (gap : Nat) (archive suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (gapSeekMachine .left)
      (seekState 0 (List.replicate gap false++true::archive) (head::suffix))
      (returnTrace head gap archive suffix)
      (seekState 1 archive (true::(List.replicate gap false++head::suffix))) := by
  refine ⟨rfl,?_,?_,?_⟩
  · apply List.IsChain.cons (seekLeft_chain gap archive (head::suffix))
    intro next hn
    rw [seekLeft_head] at hn
    have same := Option.mem_some_iff.mp hn
    subst next
    simp [Turing.TM0.step,gapSeekMachine,seekState,Turing.Tape.mk₂]
  · change (_ :: seekLeftTrace gap archive (head::suffix)).getLast? = _
    have hn : seekLeftTrace gap archive (head::suffix) ≠ [] := by
      intro h
      have hh := seekLeft_head gap archive (head::suffix)
      simp only [h,List.head?_nil,reduceCtorEq] at hh
    rw [List.getLast?_cons_of_ne_nil hn,seekLeft_last]
  · simp [Turing.TM0.step,gapSeekMachine,seekState,Turing.Tape.mk₂]

theorem return_length (head : Bool) (gap : Nat) (archive suffix : List Bool) :
    (returnTrace head gap archive suffix).length = gap+2 := by
  simp only [returnTrace,List.length_cons,seekLeft_length]

end RootB23.Threshold.Uncapped.Steps

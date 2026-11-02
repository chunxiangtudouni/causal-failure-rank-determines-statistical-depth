module

public import PSTR_WordBool_RatBinary_Paths_002

/-! Physical output-bank and current-data resource identities for the
single instruction. Owned emptiness is discharged at the actual joins. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatBinary

open Turing PSTRWordVM RationalControllerComputation

def rawBound (coefficient : Nat) (background : RatInput.Stack→List Bool)
    (x y : Rat) (tail scratch : List Bool) : Nat:=
  coefficient*(16*RatPair.space background x y tail scratch+1)^4

def space (coefficient : Nat) (background : RatInput.Stack→List Bool)
    (x y : Rat) (tail scratch : List Bool) : Nat:=
  16*RatPair.space background x y tail scratch+rawBound coefficient background x y tail scratch+8

def time (coefficient : Nat) (background : RatInput.Stack→List Bool)
    (x y : Rat) (tail scratch : List Bool) : Nat:=
  9*RatPair.fieldSize x y+7*space coefficient background x y tail scratch+128

theorem fieldSize_eq (x y : Rat) :
    RatPair.fieldSize x y=RatInput.Encoder.fieldSize x+RatInput.Encoder.fieldSize y := by
  simp only [RatPair.fieldSize,RatPair.Collector.fieldSize,RatInput.Encoder.fieldSize]
  omega

theorem outside_native_le (contents : RatInput.Stack→List Bool) :
    IsolatedRat.outside contents≤RatInput.occupied contents := by
  simp [IsolatedRat.outside,IsolatedRat.pulled,IsolatedRat.roles,Equiv.swap_apply_def,
    RatInput.occupied,Fin.sum_univ_succ,VirtualReturn.outside]
  omega

theorem drop_mass (contents : RatInput.Stack→List Bool) (result x y : Rat) (tail : List Bool)
    (atSource : contents 15=RatDrop.source result x y tail) (empty : contents 3=[]) :
    RatDrop.budget contents result x y tail=RatInput.occupied contents := by
  have mass:=RatDrop.occupied_state contents 0 () (false,false) (RatDrop.source result x y tail) []
  change RatInput.occupied (RatDrop.cells contents (RatDrop.source result x y tail) [])=_ at mass
  rw [cells_self contents _ atSource empty] at mass
  simp only [List.length_nil,Nat.add_zero] at mass
  exact mass.symm

theorem output_source (result x y : Rat) (tail : List Bool) :
    RatInput.Encoder.packet result (RatPair.input x y tail)=RatDrop.source result x y tail := by
  apply congrArg (RatInput.Encoder.packet result)
  exact (RatPair.two_packet_format x y tail).symm

theorem result_field_bound (contents : RatInput.Stack→List Bool) (result : Rat) (tail : List Bool)
    (atSource : contents 15=RatInput.Encoder.packet result tail) :
    RatInput.Encoder.fieldSize result≤RatInput.occupied contents := by
  have mass:=RatInput.Encoder.point_mass contents 15
  rw [atSource,RatInput.Encoder.packet_length] at mass
  omega

theorem raw_input_bound (coefficient : Nat) (background contents : RatInput.Stack→List Bool)
    (x y : Rat) (tail scratch : List Bool)
    (right : contents 13=encode [.rational x,.rational y])
    (mass : RatInput.occupied contents≤16*RatPair.space background x y tail scratch) :
    coefficient*((encode [.rational x,.rational y]).length+1)^4≤rawBound coefficient background x y tail scratch := by
  have input : (encode [.rational x,.rational y]).length≤16*RatPair.space background x y tail scratch := by
    rw [←right]
    exact (RatInput.Encoder.point_mass contents 13).trans mass
  exact Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left (Nat.add_le_add_right input 1) 4)

theorem final_contents (background before after : RatInput.Stack→List Bool)
    (args scratch raw result : List Bool)
    (initial : before=RatPair.Link.finalContents background args scratch raw)
    (right : after 13=[]) (left : after 14=[])
    (frames : ∀ slot,slot≠13→slot≠14→slot≠15→after slot=before slot) :
    RatDrop.cells after result []=RatPair.Link.finalContents background result scratch [] := by
  funext slot
  fin_cases slot
  all_goals first
    | rfl
    | exact right
    | exact left
    | exact (frames _ (by decide) (by decide) (by decide)).trans (by rw [initial];rfl)

theorem nonwork (slot : RatInput.Stack) (untouched : ¬RatPair.Link.Work slot) :
    slot≠13 ∧ slot≠14 ∧ slot≠7 ∧ slot≠15 ∧ slot≠3 := by
  fin_cases slot <;> simp_all [RatPair.Link.Work,RatInput.Encoder.Work]

end PaperProofs.Common.Native.PSTRWordBool.RatBinary

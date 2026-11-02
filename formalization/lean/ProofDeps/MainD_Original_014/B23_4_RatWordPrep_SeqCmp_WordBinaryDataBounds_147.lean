module

public import B23_4_RatWordPrep_SeqCmp_WordBinaryScale_146

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

theorem actual_division_data_bounds (caller : Statement C) (high : Bool) (before : State C)
    (frame : RatInput.Stack → List Bool) (data : Data) (x y : Rat) (tail : List Rat)
    (active : before.l=some (.divide high default)) (shape : before.stk=layout frame data)
    (head : data 15=x::y::tail) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.packet (if high then .parkHigh else .parkLow) 0) ∧
      final.var.2.2.2=before.var.2.2.2 ∧ final.stk=layout frame (Function.update data 15 ((x/y)::tail)) ∧
      RunBounds caller run ((7*binaryScaleCoefficient RatMulDiv.divCoefficient+137)*(scale before)^4)
        ((binaryScaleCoefficient RatMulDiv.divCoefficient+32)*(scale before)^4)
        ((64*(binaryScaleCoefficient RatMulDiv.divCoefficient+33))*(scale before)^4) := by
  have clean : ∀ slot,Owned slot→before.stk slot=[] := by rw [shape]; exact layout_owned frame data
  have pair := pair_layout before frame data x y tail shape head
  obtain ⟨final,run,port,context,contents,bounds⟩ := actual_division_resources caller high before x y
    (PacketLists.rats tail []) active pair clean
  refine ⟨final,run,port,context,?_,bounds.mono
    (binary_time_le_mass RatMulDiv.divCoefficient before x y _ pair)
    (binary_internal_le_mass RatMulDiv.divCoefficient before x y _ pair)
    (binary_clock_le_mass RatMulDiv.divCoefficient before x y _ pair)⟩
  rw [contents,shape,binaryBank_layout]

theorem actual_subtraction_data_bounds (caller : Statement C) (before : State C)
    (frame : RatInput.Stack → List Bool) (data : Data) (x y : Rat) (tail : List Rat)
    (active : before.l=some (.subtract default)) (shape : before.stk=layout frame data)
    (head : data 15=x::y::tail) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.packet .parkComplement 0) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=layout frame (Function.update data 15 ((x-y)::tail)) ∧
      RunBounds caller run ((7*binaryScaleCoefficient RatAddSub.addSubCoefficient+137)*(scale before)^4)
        ((binaryScaleCoefficient RatAddSub.addSubCoefficient+32)*(scale before)^4)
        ((64*(binaryScaleCoefficient RatAddSub.addSubCoefficient+33))*(scale before)^4) := by
  have clean : ∀ slot,Owned slot→before.stk slot=[] := by rw [shape]; exact layout_owned frame data
  have pair := pair_layout before frame data x y tail shape head
  obtain ⟨final,run,port,context,contents,bounds⟩ := actual_subtraction_resources caller before x y
    (PacketLists.rats tail []) active pair clean
  refine ⟨final,run,port,context,?_,bounds.mono
    (binary_time_le_mass RatAddSub.addSubCoefficient before x y _ pair)
    (binary_internal_le_mass RatAddSub.addSubCoefficient before x y _ pair)
    (binary_clock_le_mass RatAddSub.addSubCoefficient before x y _ pair)⟩
  rw [contents,shape,binaryBank_layout]

end B23_4_RatWordPrep.WordFinish.Resources

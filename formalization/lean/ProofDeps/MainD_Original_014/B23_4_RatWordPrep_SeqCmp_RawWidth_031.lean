module

public import B23_4_RatWordPrep_SeqCmp_RawPublic_028

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.RawGetter

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMRatArithmeticParse002

theorem raw_datum_length (x : Rat) : (encodeDatum (.rational x)).length=2*RatInput.Encoder.fieldSize x+4 := by
  rw [rational_datum]
  simp only [List.length_append,List.length_cons,List.length_nil,rawField_length,RatInput.Encoder.fieldSize]
  omega

/-- The actual original TRUE delimiter bounds the canonical field width
by the current physical source length. No width is an added input. -/
theorem fieldSize_le_mass (background : RatInput.Stack → List Bool) (x : Rat) (suffix : List Bool)
    (right : ListBlank.mk (background 0)=ListBlank.mk (encodeDatum (.rational x)++suffix++[true])) :
    RatInput.Encoder.fieldSize x≤RatInput.occupied background := by
  obtain ⟨tail,shape⟩ := PSTRSymbolicNaturalExport.finite_marked_prefix
    (encodeDatum (.rational x)++suffix) [] (background 0) right
  have length := congrArg List.length shape
  simp only [List.length_append,List.length_cons,raw_datum_length] at length
  have point := RatInput.Encoder.point_mass background 0
  omega

theorem inputScale_le_mass (background : RatInput.Stack → List Bool) (x : Rat) (suffix : List Bool)
    (right : ListBlank.mk (background 0)=ListBlank.mk (encodeDatum (.rational x)++suffix++[true])) :
    inputScale background x≤2*(RatInput.occupied background+1) := by
  have field := fieldSize_le_mass background x suffix right
  unfold inputScale
  omega

end B23_4_RatWordPrep.RawGetter

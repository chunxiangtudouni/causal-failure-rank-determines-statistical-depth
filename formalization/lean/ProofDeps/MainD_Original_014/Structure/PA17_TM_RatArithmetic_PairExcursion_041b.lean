module
public import Structure.PA17_TM_RatArithmetic_PairExcursion_041a

/-! Actual original-source instances discharge the physical route contract.
The FIRST B bit is really copied FALSE, so it remains the A OWN delimiter.
Restoring the observed original source LSB at DEST is a later real write. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairExcursion041

open Turing PA17TMRatArithmeticWidth018

private theorem original_last : Fin.last (excursionCap 10 26)=(124 : Fin (excursionCap 10 26+1)) := by
  apply Fin.ext
  decide

theorem original_dy_first_bounded (left later first : List Bool) (gap : Nat) :
    BoundedRun
      (excursionMachine (originalRoute PA17TMRatArithmeticFarLoad031.dyRoute) false)
      (Tape.mk₂ (false::false::left)
        (PA17TMRatArithmeticFarLoad031.fieldWord [] later (workSuffix gap first []))) 124
      (Tape.mk₂ (true::false::left)
        (PA17TMRatArithmeticFarLoad031.fieldWord [] later (workSuffix gap first [false])))
      (4*later.length+2*gap+4*first.length+52) := by
  have h := excursion_bounded
    (originalRoute PA17TMRatArithmeticFarLoad031.dyRoute) []
    PA17TMRatArithmeticFarLoad031.dyFinish 5
    (original_correct _ _ _ _ PA17TMRatArithmeticFarLoad031.dy_route_correct)
    left later first [] false gap (by rfl)
  have hb := h.mono (b:=4*later.length+2*gap+4*first.length+52)
    (by simp only [List.length_nil];omega)
  rw [original_last] at hb
  simpa only [sourceWord,originalRoute,PA17TMRatArithmeticFarLoad031.fieldWord,List.nil_append] using hb

theorem original_nx_bounded (dxTail nyTail dyTail left later first copied : List Bool)
    (bit : Bool) (gap : Nat) :
    BoundedRun
      (excursionMachine (originalRoute PA17TMRatArithmeticFarLoad031.nxRoute) bit)
      (Tape.mk₂ (false::bit::left)
        (PA17TMRatArithmeticFarLoad031.fieldWord
          (PA17TMRatArithmeticFarLoad031.nxContext dxTail nyTail dyTail) later
          (workSuffix gap first (false::copied)))) 124
      (Tape.mk₂ (true::bit::left)
        (PA17TMRatArithmeticFarLoad031.fieldWord
          (PA17TMRatArithmeticFarLoad031.nxContext dxTail nyTail dyTail) later
          (workSuffix gap first ((false::copied)++[bit]))))
      (4*later.length+
        2*(2*((false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+23)+
        2*gap+4*first.length+4*(false::copied).length+42) := by
  have h := excursion_bounded
    (originalRoute PA17TMRatArithmeticFarLoad031.nxRoute)
    (PA17TMRatArithmeticFarLoad031.nxContext dxTail nyTail dyTail)
    (PA17TMRatArithmeticFarLoad031.nxFinish dxTail nyTail dyTail)
    (2*((false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+23)
    (original_correct _ _ _ _ (PA17TMRatArithmeticFarLoad031.nx_route_correct dxTail nyTail dyTail))
    left later first (false::copied) bit gap (by rfl)
  rw [original_last] at h
  simpa only [sourceWord,originalRoute,PA17TMRatArithmeticFarLoad031.fieldWord] using h

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairExcursion041

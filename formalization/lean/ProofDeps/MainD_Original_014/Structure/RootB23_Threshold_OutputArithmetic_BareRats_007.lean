module
public import Structure.RootB23_Threshold_Window_MarshalSerialize_Actual_004
public import Structure.RootB23_Threshold_OutputArithmetic_Target_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.OutputArithmetic.BareRats
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002
open RootB23.Threshold.Window RootB23.Threshold.Window.MarshalSerialize

def code : Machine 404 := MarshalSerialize.restoreBothCode

private theorem time_bound (n d m e : Nat) :
    ((((128*(n+d+1)^2+64*(n+d+1)^2)+(16*m+16*e+68))+
      128*(m+e+1)^2)+128*(n+d+1)^2) ≤ 1024*(n+d+m+e+1)^2 := by
  let w := n+d+m+e+1
  have xWidth : n+d+1 ≤ w := by dsimp only [w];omega
  have yWidth : m+e+1 ≤ w := by dsimp only [w];omega
  have positive : 1 ≤ w := by dsimp only [w];omega
  have linear : w ≤ w^2 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤2)
  have xSquare := Nat.pow_le_pow_left xWidth 2
  have ySquare := Nat.pow_le_pow_left yWidth 2
  have yLinear : m+e ≤ w^2 := by omega
  have oneSquare := positive.trans linear
  change _ ≤ 1024*w^2
  nlinarith only [xSquare,ySquare,yLinear,oneSquare]

private theorem right_zeros (left word : List Bool) (n : Nat) :
    Tape.mk₂ left (word ++ List.replicate n false) = Tape.mk₂ left word := by
  apply congrArg (Tape.mk' (ListBlank.mk left))
  apply Quotient.sound
  exact Or.inr ⟨n,by rfl⟩

/-- Only the already-frozen real two-Rat body is executed, with no count2
header. Two owned prefix FALSEs are consumed. The marked final encoder
really writes the outer TRUE footer; seven trailing FALSEs are blank only
AFTER that footer, never an internal gap. -/
theorem bounded (archive : List Bool) (x y : Rat) (hx : 0≤x) (hy : 0≤y) :
    BoundedRun code
      (Tape.mk₂ (false :: false :: archive) (MarshalSerialize.inputRight x y [])) 404
      (Tape.mk₂ archive (encodeDatum (.rational x) ++ encodeDatum (.rational y) ++ [true]))
      (1024*(MarshalSerialize.totalWidth x y+1)^2) := by
  let ny := numeratorDigits y
  let dy := denominatorDigits y
  let tail := PSTRTMIncrement009.blocks ny ++ Uncapped.Serialize.marker
    (PSTRTMIncrement009.blocks dy ++ [false,false])
  have first := RatCodec.first_bounded archive (true :: false :: tail) x hx
  have firstRight : Uncapped.Serialize.remainder (true :: false :: tail) = SlideY.inputRight ny dy [] := rfl
  rw [firstRight] at first
  have parsed := RatCodec.scan_bounded archive (SlideY.inputRight ny dy []) x
  have moved := SlideY.actual_bounded (ratLeft archive x) ny dy []
  have movedRight : SlideY.outputRight ny dy [] =
      Uncapped.Serialize.inputRight y.num.natAbs y.den (List.replicate 4 false ++ []) := rfl
  rw [movedRight] at moved
  have last := RatCodec.final_bounded (ratLeft archive x) (List.replicate 4 false ++ []) y hy
  let yTail := false :: (encodeNat y.num.natAbs ++ encodeNat y.den ++ true :: List.replicate 7 false)
  have yDatum : encodeDatum (.rational y) = true :: false :: (encodeNat y.num.natAbs ++ encodeNat y.den) := by
    have nonnegative : decide (y<0) = false := by
      simp only [decide_eq_false_iff_not]
      exact not_lt.mpr hy
    rw [encodeDatum,nonnegative]
    rfl
  have tailEq : encodeDatum (.rational y) ++ RatCodec.footerTail (List.replicate 4 false ++ []) = true :: yTail := by
    simp only [yDatum,RatCodec.footerTail,yTail,List.cons_append,List.append_assoc,List.append_nil,
      List.replicate_succ,List.replicate_zero]
  have restored := RatCodec.restore_bounded archive yTail x hx
  rw [← tailEq] at restored
  have actual := (((first.seq parsed).seq moved).seq last).seq restored
  have port : PSTRTMSeq005.rightLabel (a := 343) (60 : Fin 61) = (404 : Fin 405) := by decide
  rw [port] at actual
  have time := time_bound (natBits x.num.natAbs) (natBits x.den) (natBits y.num.natAbs) (natBits y.den)
  have fee : ((((128*(RatCodec.width x)^2+64*(RatCodec.width x)^2)+(16*ny.length+16*dy.length+68))+
      128*(RatCodec.width y)^2)+128*(RatCodec.width x)^2) ≤ 1024*(MarshalSerialize.totalWidth x y+1)^2 := by
    simpa only [RatCodec.width,MarshalSerialize.totalWidth,ny,dy,numeratorDigits_length,denominatorDigits_length] using time
  have footer : encodeDatum (.rational x) ++
      (encodeDatum (.rational y) ++ RatCodec.footerTail (List.replicate 4 false ++ [])) =
      (encodeDatum (.rational x) ++ encodeDatum (.rational y) ++ [true]) ++ List.replicate 7 false := by
    simp only [RatCodec.footerTail,List.append_assoc,List.cons_append,List.nil_append,List.append_nil,
      List.replicate_succ,List.replicate_zero]
  have outputTape := congrArg (Tape.mk₂ archive) footer
  rw [right_zeros] at outputTape
  rw [outputTape] at actual
  simpa only [code,MarshalSerialize.restoreBothCode,MarshalSerialize.lastCode,MarshalSerialize.slideCode,
    MarshalSerialize.parseCode,Uncapped.Serialize.inputRight,Uncapped.Serialize.marker,
    PA17TMRatArithmeticPairEncode017.payload,numeratorDigits,denominatorDigits,
    MarshalSerialize.inputRight,tail,ny,dy,List.append_assoc,List.cons_append,List.nil_append,List.append_nil]
    using actual.mono fee

end RootB23.Threshold.OutputArithmetic.BareRats

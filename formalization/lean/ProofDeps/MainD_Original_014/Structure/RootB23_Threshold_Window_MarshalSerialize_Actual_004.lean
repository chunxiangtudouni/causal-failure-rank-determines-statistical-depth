module
public import Structure.RootB23_Threshold_Window_MarshalSerialize_SlideY_002
public import Structure.RootB23_Threshold_Window_MarshalSerialize_Rat_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.Window.MarshalSerialize
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002

def parseCode : Machine 141 := PSTRTMSeq005.seqMachine Uncapped.Serialize.code ratMachine
def slideCode : Machine 247 := PSTRTMSeq005.seqMachine parseCode SlideY.code
def lastCode : Machine 343 := PSTRTMSeq005.seqMachine slideCode RatCodec.finalCode
def restoreBothCode : Machine 404 := PSTRTMSeq005.seqMachine lastCode RatCodec.restoreCode
def code : Machine 415 := PSTRTMSeq005.seqMachine restoreBothCode PacketSteps.headerCode

def inputRight (x y : Rat) (suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks (numeratorDigits x)++Uncapped.Serialize.marker
    (PSTRTMIncrement009.blocks (denominatorDigits x)++Uncapped.Serialize.marker
      (PSTRTMIncrement009.blocks (numeratorDigits y)++Uncapped.Serialize.marker
        (PSTRTMIncrement009.blocks (denominatorDigits y)++false::false::suffix)))

def totalWidth (x y : Rat) : ℕ :=
  natBits x.num.natAbs+natBits x.den+natBits y.num.natAbs+natBits y.den

private theorem time_bound (n d m e : ℕ) :
    (((((128*(n+d+1)^2+64*(n+d+1)^2)+(16*m+16*e+68))+
      128*(m+e+1)^2)+128*(n+d+1)^2)+11)≤1024*(n+d+m+e+1)^2 := by
  let w:=n+d+m+e+1
  have xWidth : n+d+1≤w := by dsimp only [w];omega
  have yWidth : m+e+1≤w := by dsimp only [w];omega
  have positive : 1≤w := by dsimp only [w];omega
  have linear : w≤w^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤2)
  have xSquare:=Nat.pow_le_pow_left xWidth 2
  have ySquare:=Nat.pow_le_pow_left yWidth 2
  have yLinear : m+e≤w^2 := by omega
  have oneSquare:=positive.trans linear
  change _≤1024*w^2
  nlinarith only [xSquare,ySquare,yLinear,oneSquare]

/-- The complete real Marshal ABI: four recovered original flagged
fields and three 0010 markers become the actual count2/two-Rat/list
footer packet. Exactly seven owned prefix FALSEs are consumed, and
exactly seven owned suffix FALSEs remain before the unchanged suffix.
The single finite table does not depend on x, y or any field width. -/
theorem actual_bounded (archive suffix : List Bool) (x y : Rat) (hx : 0≤x) (hy : 0≤y) :
    BoundedRun code
      (Tape.mk₂ (List.replicate 7 false++archive) (inputRight x y suffix)) 415
      (Tape.mk₂ archive (encode [.rational x,.rational y]++List.replicate 7 false++suffix))
      (1024*(totalWidth x y+1)^2) := by
  let left:=List.replicate 5 false++archive
  let ny:=numeratorDigits y
  let dy:=denominatorDigits y
  let tail:=PSTRTMIncrement009.blocks ny++Uncapped.Serialize.marker
    (PSTRTMIncrement009.blocks dy++false::false::suffix)
  have first:=RatCodec.first_bounded left (true::false::tail) x hx
  have firstRight : Uncapped.Serialize.remainder (true::false::tail)=SlideY.inputRight ny dy suffix := rfl
  rw [firstRight] at first
  have parsed:=RatCodec.scan_bounded left (SlideY.inputRight ny dy suffix) x
  have moved:=SlideY.actual_bounded (ratLeft left x) ny dy suffix
  have movedRight : SlideY.outputRight ny dy suffix=
      Uncapped.Serialize.inputRight y.num.natAbs y.den (List.replicate 4 false++suffix) := rfl
  rw [movedRight] at moved
  have last:=RatCodec.final_bounded (ratLeft left x) (List.replicate 4 false++suffix) y hy
  let yTail:=false::(encodeNat y.num.natAbs++encodeNat y.den++true::(List.replicate 7 false++suffix))
  have yDatum : encodeDatum (.rational y)=true::false::(encodeNat y.num.natAbs++encodeNat y.den) := by
    have nonnegative : decide (y<0)=false := by
      simp only [decide_eq_false_iff_not]
      exact not_lt.mpr hy
    rw [encodeDatum,nonnegative]
    rfl
  have tailEq : encodeDatum (.rational y)++RatCodec.footerTail (List.replicate 4 false++suffix)=true::yTail := by
    simp only [yDatum,RatCodec.footerTail,yTail,List.cons_append,List.append_assoc]
    rfl
  have restored:=RatCodec.restore_bounded left yTail x hx
  rw [←tailEq] at restored
  have header:=RatCodec.header_bounded archive
    (encodeDatum (.rational x)++(encodeDatum (.rational y)++RatCodec.footerTail (List.replicate 4 false++suffix)))
  have actual:=((((first.seq parsed).seq moved).seq last).seq restored).seq header
  have port : PSTRTMSeq005.rightLabel (a:=404) (10 : Fin 11)=(415 : Fin 416) := by decide
  rw [port] at actual
  have time : (((((128*(RatCodec.width x)^2+64*(RatCodec.width x)^2)+
      (16*ny.length+16*dy.length+68))+128*(RatCodec.width y)^2)+128*(RatCodec.width x)^2)+11)
      ≤1024*(totalWidth x y+1)^2 := by
    simpa only [RatCodec.width,totalWidth,ny,dy,numeratorDigits_length,denominatorDigits_length] using
      time_bound (natBits x.num.natAbs) (natBits x.den) (natBits y.num.natAbs) (natBits y.den)
  simpa only [code,restoreBothCode,lastCode,slideCode,parseCode,left,
    Uncapped.Serialize.inputRight,Uncapped.Serialize.marker,
    PA17TMRatArithmeticPairEncode017.payload,numeratorDigits,denominatorDigits,
    inputRight,tail,ny,dy,encode,RatCodec.footerTail,
    List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    Nat.reduceAdd,List.append_assoc,List.cons_append,List.nil_append,
    List.replicate_succ,List.replicate_zero] using actual.mono time

/-- The same actual trace supplies every-prefix space at the caller's
charged input length. No tape reset, additional room premise, or
standalone-only interpretation of an internal FALSE run is used. -/
theorem actual_contract (archive suffix : List Bool) (x y : Rat) (hx : 0≤x) (hy : 0≤y) :
    ∃ trace, PSTRTMSeq005.RunsFrom code
      ⟨0,Tape.mk₂ (List.replicate 7 false++archive) (inputRight x y suffix)⟩ trace
      ⟨415,Tape.mk₂ archive (encode [.rational x,.rational y]++List.replicate 7 false++suffix)⟩ ∧
      trace.length≤1024*(totalWidth x y+1)^2 ∧
      ∀ chargedLength clock, visitedSpace code chargedLength (trace.take clock)≤
        chargedLength+2048*(totalWidth x y+1)^2+1 := by
  obtain ⟨trace,actual,time⟩:=actual_bounded archive suffix x y hx hy
  refine ⟨trace,actual,time,?_⟩
  intro chargedLength clock
  have space:=PSTRTMTrace002.visitedSpace_le code chargedLength (trace.take clock)
  have taken : (trace.take clock).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
  omega

end RootB23.Threshold.Window.MarshalSerialize

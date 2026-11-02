module
public import Structure.RootB23_Threshold_ReturnNineSource_039
public import Structure.RootB23_Threshold_ReturnCompactRewind_040

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineLayout
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticParse002

/-- Physical source order, before the final reorder: badNUM,badDEN,
B,targetNUM,targetDEN,oddsNUM,oddsDEN,inverseNUM,inverseDEN. -/
structure Data where
  a : List Bool
  b : List Bool
  c : List Bool
  d : List Bool
  e : List Bool
  f : List Bool
  g : List Bool
  h : List Bool
  i : List Bool

def field (v : Data) (index : Fin 9) : List Bool := match index.val with
  | 0=>v.a | 1=>v.b | 2=>v.c | 3=>v.d | 4=>v.e | 5=>v.f | 6=>v.g | 7=>v.h | _=>v.i
def gap13 : List Bool := [false,false,true]++List.replicate 9 false++[false]
def connector (index : Fin 9) : List Bool := match index.val with
  | 1=>gap13 | 2=>[false,false,false] | 4=>[false,false,false,false] | 6=>[false,false,false] | _=>[false]
def body (v : Data) : List Bool :=
  PSTRTMIncrement009.blocks v.a++[false]++PSTRTMIncrement009.blocks v.b++gap13++
  PSTRTMIncrement009.blocks v.c++[false,false,false]++PSTRTMIncrement009.blocks v.d++[false]++
  PSTRTMIncrement009.blocks v.e++[false,false,false,false]++PSTRTMIncrement009.blocks v.f++[false]++
  PSTRTMIncrement009.blocks v.g++[false,false,false]++PSTRTMIncrement009.blocks v.h++[false]++
  PSTRTMIncrement009.blocks v.i++[false]

def left0 (base : List Bool) (_v : Data) : List Bool := false::false::base
def left1 (base : List Bool) (v : Data) : List Bool := false::(PSTRTMRawNat010.leftBlocks v.a.reverse++left0 base v)
def left2 (base : List Bool) (v : Data) : List Bool := gap13.reverse++(PSTRTMRawNat010.leftBlocks v.b.reverse++left1 base v)
def left3 (base : List Bool) (v : Data) : List Bool := [false,false,false]++(PSTRTMRawNat010.leftBlocks v.c.reverse++left2 base v)
def left4 (base : List Bool) (v : Data) : List Bool := false::(PSTRTMRawNat010.leftBlocks v.d.reverse++left3 base v)
def left5 (base : List Bool) (v : Data) : List Bool := [false,false,false,false]++(PSTRTMRawNat010.leftBlocks v.e.reverse++left4 base v)
def left6 (base : List Bool) (v : Data) : List Bool := false::(PSTRTMRawNat010.leftBlocks v.f.reverse++left5 base v)
def left7 (base : List Bool) (v : Data) : List Bool := [false,false,false]++(PSTRTMRawNat010.leftBlocks v.g.reverse++left6 base v)
def left8 (base : List Bool) (v : Data) : List Bool := false::(PSTRTMRawNat010.leftBlocks v.h.reverse++left7 base v)
def footerLeft (base : List Bool) (v : Data) : List Bool := false::(PSTRTMRawNat010.leftBlocks v.i.reverse++left8 base v)
def right8 (v : Data) : List Bool := PSTRTMIncrement009.blocks v.i++[false,false]
def right7 (v : Data) : List Bool := PSTRTMIncrement009.blocks v.h++false::right8 v
def right6 (v : Data) : List Bool := PSTRTMIncrement009.blocks v.g++[false,false,false]++right7 v
def right5 (v : Data) : List Bool := PSTRTMIncrement009.blocks v.f++false::right6 v
def right4 (v : Data) : List Bool := PSTRTMIncrement009.blocks v.e++[false,false,false,false]++right5 v
def right3 (v : Data) : List Bool := PSTRTMIncrement009.blocks v.d++false::right4 v
def right2 (v : Data) : List Bool := PSTRTMIncrement009.blocks v.c++[false,false,false]++right3 v
def right1 (v : Data) : List Bool := PSTRTMIncrement009.blocks v.b++gap13++right2 v
def right0 (v : Data) : List Bool := PSTRTMIncrement009.blocks v.a++false::right1 v
def leftAt (base : List Bool) (v : Data) (index : Fin 9) : List Bool := match index.val with
  | 0=>left0 base v | 1=>left1 base v | 2=>left2 base v | 3=>left3 base v | 4=>left4 base v
  | 5=>left5 base v | 6=>left6 base v | 7=>left7 base v | _=>left8 base v
def rightAt (v : Data) (index : Fin 9) : List Bool := match index.val with
  | 0=>right0 v | 1=>right1 v | 2=>right2 v | 3=>right3 v | 4=>right4 v
  | 5=>right5 v | 6=>right6 v | 7=>right7 v | _=>right8 v
def atData (base : List Bool) (v : Data) (index : Fin 9) : Tape Bool := Tape.mk₂ (leftAt base v index) (rightAt v index)
def atFooter (base : List Bool) (v : Data) : Tape Bool := Tape.mk₂ (footerLeft base v) [false]

def terms (bad : Rat) (n : ℕ) : Data :=
  ⟨numeratorDigits bad,denominatorDigits bad,PSTRTMNatValue017.rawPayload n,
    PSTRTMNatValue017.rawPayload 1,PSTRTMNatValue017.rawPayload (ReturnNineSource.d n),
    PSTRTMNatValue017.rawPayload (ReturnNineSource.d n-1),PSTRTMNatValue017.rawPayload 1,
    PSTRTMNatValue017.rawPayload 1,PSTRTMNatValue017.rawPayload (ReturnNineSource.d n-1)⟩

theorem footer_body (base : List Bool) (v : Data) : footerLeft base v=(body v).reverse++false::false::base := by
  simp only [footerLeft,left8,left7,left6,left5,left4,left3,left2,left1,left0,body,gap13,
    List.reverse_append,List.reverse_cons,List.reverse_nil,List.reverse_replicate,NatSplice.reverse_blocks,
    List.append_assoc,List.cons_append,List.nil_append]

theorem rawLeft_exact (base : List Bool) (bad : Rat) (nonnegative : 0≤bad) (n : ℕ) :
    ReturnNineSource.rawLeft (List.replicate 9 false++true::false::ratLeft base bad) n=
      footerLeft base (terms bad n) := by
  have positive : 0<ReturnNineSource.d n-1 := by
    have bound:=ReturnDWork.denominator_at_least_two n
    dsimp only [ReturnNineSource.d]
    omega
  have badSign : sign bad=false := by
    simp only [sign,decide_eq_false_iff_not]
    exact not_lt.mpr nonnegative
  have targetSign : sign (OutputArithmetic.Target.value n)=false := by
    simp only [sign,decide_eq_false_iff_not]
    exact not_lt.mpr (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have oddsSign : sign (ReturnNineSource.odds n)=false := by
    simp only [sign,decide_eq_false_iff_not]
    exact not_lt.mpr (Nat.cast_nonneg _)
  have inverseSign : sign (ReturnNineSource.inverse n)=false := by
    simp only [sign,decide_eq_false_iff_not]
    exact not_lt.mpr (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have targetNum : numeratorDigits (OutputArithmetic.Target.value n)=PSTRTMNatValue017.rawPayload 1 := by
    simp only [numeratorDigits,ReturnDWork.value_num,Int.natAbs_one]
  have inverseNumValue : (ReturnNineSource.inverse n).num=1 :=
    OutputArithmetic.OddsInverse.inv_num (ReturnNineSource.d n-1) positive
  have inverseDenValue : (ReturnNineSource.inverse n).den=ReturnNineSource.d n-1 :=
    OutputArithmetic.OddsInverse.inv_den (ReturnNineSource.d n-1) positive
  have inverseNum : numeratorDigits (ReturnNineSource.inverse n)=PSTRTMNatValue017.rawPayload 1 := by
    simp only [numeratorDigits,inverseNumValue,Int.natAbs_one]
  have inverseDen : denominatorDigits (ReturnNineSource.inverse n)=PSTRTMNatValue017.rawPayload (ReturnNineSource.d n-1) := by
    simp only [denominatorDigits,inverseDenValue]
  simp only [ReturnNineSource.rawLeft,ReturnNineSource.beforeOdds,ReturnDWork.denArchive,ReturnDWork.natArchive,
    ratLeft,bothLeft,firstLeft,PA17TMRatArithmeticCopy006.sourceLeft,
    footerLeft,left8,left7,left6,left5,left4,left3,left2,left1,left0,terms,gap13,
    List.append_assoc,List.cons_append,List.nil_append,List.reverse_append,List.reverse_cons,
    List.reverse_nil,List.reverse_replicate]
  simp only [badSign,targetSign,oddsSign,inverseSign,targetNum,inverseNum,inverseDen]
  simp only [ReturnNineSource.odds,numeratorDigits,denominatorDigits,Rat.num_natCast,Int.natAbs_natCast,Rat.den_natCast]

end RootB23.Threshold.ReturnNineLayout

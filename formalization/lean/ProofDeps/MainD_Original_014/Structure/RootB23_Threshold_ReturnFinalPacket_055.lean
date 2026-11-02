module
public import Structure.RootB23_Threshold_ReturnNineBounds_054
public import Structure.RootB23_Threshold_FinalSerialize_Actual_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnFinalPacket
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBookmark014

def fields (bad : Rat) (n : ℕ) : ReturnNineLayout.Data := ReturnNineLayout.terms bad n

def archive (base : List Bool) (bad : Rat) (n : ℕ) : List Bool :=
  true::false::ReturnNineLayout.footerLeft base (ReturnNineOut.mask (fields bad n))

def output (bad : Rat) (n : ℕ) : List Bool := encode
  [.natural n,.rational (OutputArithmetic.Target.value n),.rational bad,
    .rational (ReturnNineSource.odds n),.rational (ReturnNineSource.inverse n)]

def width (bad : Rat) (n : ℕ) : ℕ := FinalSerialize.totalWidth n (OutputArithmetic.Target.value n) bad
  (ReturnNineSource.odds n) (ReturnNineSource.inverse n)

def cap : ℕ := ReturnNineActual.cap+1614+1
attribute [local implicit_reducible] cap
def code : Machine cap := PSTRTMSeq005.seqMachine ReturnNineActual.code FinalSerialize.Actual.code
def finalPort : Fin (cap+1) := PSTRTMSeq005.rightLabel (a:=ReturnNineActual.cap) (1614 : Fin 1615)

theorem b_nonempty (bad : Rat) (n : ℕ) : (fields bad n).b≠[] := denominator_ne_nil bad
theorem e_nonempty (bad : Rat) (n : ℕ) : (fields bad n).e≠[] := PSTRTMThresholdUnitColumnsCost160.rawPayload_ne_nil _
theorem g_nonempty (bad : Rat) (n : ℕ) : (fields bad n).g≠[] := PSTRTMThresholdUnitColumnsCost160.rawPayload_ne_nil _
theorem i_nonempty (bad : Rat) (n : ℕ) : (fields bad n).i≠[] := PSTRTMThresholdUnitColumnsCost160.rawPayload_ne_nil _

theorem restored (bad : Rat) (n : ℕ) :
    ReturnNineCopy.fields (fields bad n) (ReturnNineActual.observed (fields bad n))=
      FinalSerialize.nineFields n (OutputArithmetic.Target.value n) bad (ReturnNineSource.odds n) (ReturnNineSource.inverse n) := by
  have gFirst : true::(fields bad n).g.tail=(fields bad n).g := by
    change true::(PSTRTMNatValue017.rawPayload 1).tail=PSTRTMNatValue017.rawPayload 1
    decide
  rw [ReturnNineActual.restored_fields _ (b_nonempty bad n) (e_nonempty bad n) (i_nonempty bad n) gFirst]
  have positive : 0<ReturnNineSource.d n-1 := by
    have bound:=ReturnDWork.denominator_at_least_two n
    dsimp only [ReturnNineSource.d]
    omega
  have targetNum : numeratorDigits (OutputArithmetic.Target.value n)=PSTRTMNatValue017.rawPayload 1 := by
    simp only [numeratorDigits,ReturnDWork.value_num,Int.natAbs_one]
  have targetDen:=ReturnDWork.denominator_digits n
  have inverseNumValue : (ReturnNineSource.inverse n).num=1 :=
    OutputArithmetic.OddsInverse.inv_num (ReturnNineSource.d n-1) positive
  have inverseDenValue : (ReturnNineSource.inverse n).den=ReturnNineSource.d n-1 :=
    OutputArithmetic.OddsInverse.inv_den (ReturnNineSource.d n-1) positive
  have inverseNum : numeratorDigits (ReturnNineSource.inverse n)=PSTRTMNatValue017.rawPayload 1 := by
    simp only [numeratorDigits,inverseNumValue,Int.natAbs_one]
  have inverseDen : denominatorDigits (ReturnNineSource.inverse n)=PSTRTMNatValue017.rawPayload (ReturnNineSource.d n-1) := by
    simp only [denominatorDigits,inverseDenValue]
  simp only [fields,ReturnNineLayout.terms,FinalSerialize.nineFields,targetNum,targetDen,inverseNum,inverseDen]
  simp only [numeratorDigits,denominatorDigits,ReturnNineSource.odds,Rat.num_natCast,Int.natAbs_natCast,Rat.den_natCast,ReturnNineSource.d]

theorem width_exact (bad : Rat) (n : ℕ) : ReturnNineRoute.width (fields bad n)=width bad n := by
  rw [←ReturnNineBounds.fields_width _ (ReturnNineActual.observed (fields bad n)),restored]
  rfl

theorem word_exact (bad : Rat) (n : ℕ) :
    ReturnNineMarshal.word (fields bad n) (ReturnNineActual.observed (fields bad n))=
      FinalSerialize.inputRight n (OutputArithmetic.Target.value n) bad (ReturnNineSource.odds n) (ReturnNineSource.inverse n) [] := by
  unfold ReturnNineMarshal.word
  rw [restored]
  simp [FinalSerialize.nineFields,FinalSerialize.inputRight,FinalSerialize.word,FinalSerialize.marker,
    ReturnNineDest.core,PA17TMRatArithmeticCopy006.workspace,List.append_assoc]

/-- Same fixed actual source->nine-copy->count5 code before ALL B/badRisk.
Only the genuine tape supplies the digits; the seven owned cells and true
footer were paid by the producer, and all first bits came from read ports. -/
theorem bounded (base : List Bool) (bad : Rat) (n : ℕ) (nonnegative : 0≤bad) :
    BoundedRun code (Tape.mk₂ (ReturnNineLayout.footerLeft base (fields bad n)) [false]) finalPort
      (Tape.mk₂ (archive base bad n) (output bad n++List.replicate 16 false))
      ((1048576+32768)*(width bad n+1)^2) := by
  have first:=ReturnNineActual.bounded base (fields bad n) (b_nonempty bad n) (e_nonempty bad n)
    (g_nonempty bad n) (i_nonempty bad n)
  have firstFee:=ReturnNineBounds.fee_le (fields bad n)
  rw [width_exact] at firstFee
  have producer:=first.mono firstFee
  rw [word_exact] at producer
  have targetPositive : 0≤OutputArithmetic.Target.value n := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have oddsPositive : 0≤ReturnNineSource.odds n := Nat.cast_nonneg _
  have inversePositive : 0≤ReturnNineSource.inverse n := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have second:=FinalSerialize.Actual.bounded (archive base bad n) [] n (OutputArithmetic.Target.value n) bad
    (ReturnNineSource.odds n) (ReturnNineSource.inverse n) targetPositive nonnegative oddsPositive inversePositive
  change BoundedRun FinalSerialize.Actual.code _ _ _ (32768*(width bad n+1)^2) at second
  have actual:=producer.seq second
  have grouped : 1048576*(width bad n+1)^2+32768*(width bad n+1)^2=(1048576+32768)*(width bad n+1)^2 :=
    (Nat.add_mul _ _ _).symm
  rw [grouped] at actual
  rw [List.append_nil] at actual
  exact actual

end RootB23.Threshold.ReturnFinalPacket

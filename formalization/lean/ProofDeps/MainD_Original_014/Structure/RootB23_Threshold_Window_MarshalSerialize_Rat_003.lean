module
public import Structure.RootB23_Threshold_Uncapped_Serialize_008
public import Structure.RootB23_Threshold_PacketSteps_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.Window.MarshalSerialize.RatCodec
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticPairEncode017

def width (q : Rat) : ℕ := natBits q.num.natAbs+natBits q.den+1

/-- The frozen 008 code also covers zero: only nonnegative sign encoding
is used, while NUM and DEN are the genuine canonical rational fields. -/
theorem first_bounded (archive suffix : List Bool) (q : Rat) (hq : 0≤q) :
    BoundedRun Uncapped.Serialize.code
      (Tape.mk₂ (false::false::archive) (Uncapped.Serialize.inputRight q.num.natAbs q.den suffix)) 95
      (Tape.mk₂ archive (encodeDatum (.rational q)++Uncapped.Serialize.remainder suffix))
      (128*(width q)^2) := by
  have actual:=Uncapped.Serialize.actual_runsFrom archive q.num.natAbs q.den suffix
  have lastEq : Uncapped.Serialize.final archive q.num.natAbs q.den suffix=
      (⟨95,Tape.mk₂ archive (encodeDatum (.rational q)++Uncapped.Serialize.remainder suffix)⟩ : MachineState 95) := by
    change (⟨PSTRTMSeq005.rightLabel (a:=90) (4 : Fin 5),_⟩ : MachineState 95)=_
    have port : PSTRTMSeq005.rightLabel (a:=90) (4 : Fin 5)=(95 : Fin 96) := by decide
    rw [port]
    have nonnegative : ¬q<0 := not_lt.mpr hq
    simp only [encodeDatum,nonnegative,decide_false,List.cons_append,List.nil_append,List.append_assoc]
  rw [lastEq] at actual
  exact ⟨_,actual,by simpa only [width,payload_length] using
    Uncapped.Serialize.actual_time_le archive q.num.natAbs q.den suffix⟩

def footerTail (suffix : List Bool) : List Bool := true::false::false::false::suffix
def finalEncodeCode : Machine 82 := PSTRTMSeq005.seqMachine Uncapped.Serialize.moveCode (pairMachine true)
def finalRawCode : Machine 90 := PSTRTMSeq005.seqMachine Uncapped.Serialize.locateCode finalEncodeCode
def finalCode : Machine 95 := PSTRTMSeq005.seqMachine finalRawCode Uncapped.Steps.prefixCode

private theorem final_cost (n d : ℕ) :
    (2*n+8)+((14*d+16)+64*(n+d+1)^2)+5≤128*(n+d+1)^2 := by
  nlinarith only [Nat.zero_le (n^2),Nat.zero_le (d^2),Nat.zero_le (n*d)]

/-- The same real 008 locate/LEFT3/pair pipeline, using the existing
marked Pair017 code at the last denominator. Its TRUE footer is the
actual outer list delimiter, followed by three real residue FALSEs. -/
theorem final_bounded (archive suffix : List Bool) (q : Rat) (hq : 0≤q) :
    BoundedRun finalCode
      (Tape.mk₂ (false::false::archive) (Uncapped.Serialize.inputRight q.num.natAbs q.den suffix)) 95
      (Tape.mk₂ archive (encodeDatum (.rational q)++footerTail suffix)) (128*(width q)^2) := by
  let a:=q.num.natAbs
  let b:=q.den
  have located : BoundedRun Uncapped.Serialize.locateCode
      (Tape.mk₂ (false::false::archive) (Uncapped.Serialize.inputRight a b suffix)) 7
      (Tape.mk₂ (Uncapped.Serialize.denominatorLeft archive a)
        (PSTRTMIncrement009.blocks (payload b)++false::false::suffix)) (2*(payload a).length+8) := by
    refine ⟨Uncapped.Serialize.locateTrace archive a b suffix,?_,?_⟩
    · have actual:=Uncapped.Serialize.locate_runsFrom archive a b suffix
      have lastEq : Uncapped.Serialize.locateFinal archive a b suffix=
          (⟨7,Tape.mk₂ (Uncapped.Serialize.denominatorLeft archive a)
            (PSTRTMIncrement009.blocks (payload b)++false::false::suffix)⟩ : MachineState 7) := by
        change (⟨PSTRTMSeq005.rightLabel (a:=2) (4 : Fin 5),_⟩ : MachineState 7)=_
        have port : PSTRTMSeq005.rightLabel (a:=2) (4 : Fin 5)=(7 : Fin 8) := by decide
        rw [port]
      rw [lastEq] at actual
      exact actual
    · simp only [Uncapped.Serialize.locateTrace,List.length_append,List.length_map,
        Uncapped.Walk.actual_length,Uncapped.Steps.fourRightTrace,List.length_cons,List.length_nil]
      omega
  have moved : BoundedRun Uncapped.Serialize.moveCode
      (Tape.mk₂ (Uncapped.Serialize.denominatorLeft archive a)
        (PSTRTMIncrement009.blocks (payload b)++false::false::suffix)) 34
      (Tape.mk₂ (false::aArchive (false::archive) a)
        (PSTRTMIncrement009.blocks (payload b)++Uncapped.Serialize.shiftSuffix suffix))
      (14*(payload b).length+16) := by
    refine ⟨Uncapped.Serialize.moveTrace archive a b suffix,?_,?_⟩
    · have actual:=Uncapped.Serialize.move_runsFrom archive a b suffix
      have lastEq : Uncapped.Serialize.moveFinal archive a b suffix=
          (⟨34,Tape.mk₂ (false::aArchive (false::archive) a)
            (PSTRTMIncrement009.blocks (payload b)++Uncapped.Serialize.shiftSuffix suffix)⟩ : MachineState 34) := by
        change (⟨PSTRTMSeq005.rightLabel (a:=30) (3 : Fin 4),_⟩ : MachineState 34)=_
        have port : PSTRTMSeq005.rightLabel (a:=30) (3 : Fin 4)=(34 : Fin 35) := by decide
        rw [port]
        rfl
      rw [lastEq] at actual
      exact actual
    · simp only [Uncapped.Serialize.moveTrace,List.length_append,List.length_map,
        Uncapped.MarkedShift.actual_length,PSTRTMPairRewind105.full_length,List.length_reverse]
      omega
  have paired : BoundedRun (pairMachine true)
      (Tape.mk₂ (false::aArchive (false::archive) a)
        (PSTRTMIncrement009.blocks (payload b)++Uncapped.Serialize.shiftSuffix suffix)) 47
      (Tape.mk₂ (false::false::archive) (encodeNat a++encodeNat b++footerTail suffix))
      (64*(width q)^2) :=
    ⟨pairTrace true (false::archive) a b (false::false::false::suffix),
      pair_explicit_runsFrom true (false::archive) a b (false::false::false::suffix),
      by simpa only [width,a,b,payload_length] using
        pair_time_le true (false::archive) a b (false::false::false::suffix)⟩
  have datum : encodeDatum (.rational q)=true::false::(encodeNat a++encodeNat b) := by
    have nonnegative : decide (q<0)=false := by
      simp only [decide_eq_false_iff_not]
      exact not_lt.mpr hq
    rw [encodeDatum,nonnegative]
    rfl
  have tagged : BoundedRun Uncapped.Steps.prefixCode
      (Tape.mk₂ (false::false::archive) (encodeNat a++encodeNat b++footerTail suffix)) 4
      (Tape.mk₂ archive (encodeDatum (.rational q)++footerTail suffix)) 5 := by
    rw [datum]
    exact ⟨Uncapped.Steps.prefixTrace archive false false (encodeNat a++encodeNat b++footerTail suffix),
      Uncapped.Steps.prefix_runsFrom _ _ _ _,by rfl⟩
  have actual:=(located.seq (moved.seq paired)).seq tagged
  have port : PSTRTMSeq005.rightLabel (a:=90) (4 : Fin 5)=(95 : Fin 96) := by decide
  rw [port] at actual
  simpa only [finalCode,finalRawCode,finalEncodeCode] using actual.mono (by
    simpa only [width,a,b,payload_length] using final_cost (natBits q.num.natAbs) (natBits q.den))

private theorem scan_cost (n d : ℕ) : n^2+d^2+9*(n+d)+11≤64*(n+d+1)^2 := by
  nlinarith only [Nat.zero_le (n^2),Nat.zero_le (d^2),Nat.zero_le (n*d)]
theorem scan_bounded (left suffix : List Bool) (q : Rat) :
    BoundedRun ratMachine (Tape.mk₂ left (encodeDatum (.rational q)++suffix)) 45
      (Tape.mk₂ (ratLeft left q) suffix) (64*(width q)^2) := by
  have lastEq : ratFinal left (sign q) (numeratorDigits q) (denominatorDigits q) suffix=
      (⟨45,Tape.mk₂ (ratLeft left q) suffix⟩ : MachineState 45) := by
    change (⟨PSTRTMSeq005.rightLabel (a:=9)
      (PSTRTMSeq005.rightLabel (a:=17) (17 : Fin 18)),_⟩ : MachineState 45)=_
    have port : PSTRTMSeq005.rightLabel (a:=9)
        (PSTRTMSeq005.rightLabel (a:=17) (17 : Fin 18))=(45 : Fin 46) := by decide
    rw [port]
    rfl
  refine ⟨ratTrace left (sign q) (numeratorDigits q) (denominatorDigits q) suffix,?_,?_⟩
  · rw [←lastEq]
    exact encodeDatum_rat_runsFrom _ _ _
  · rw [ratTrace_length,numeratorDigits_length,denominatorDigits_length]
    exact scan_cost _ _

def restoreBackCode : Machine 7 := PSTRTMSeq005.seqMachine clampHeaderMachine fieldBackMachine
def restorePairCode : Machine 55 := PSTRTMSeq005.seqMachine restoreBackCode (pairMachine true)
def restoreCode : Machine 60 := PSTRTMSeq005.seqMachine restorePairCode Uncapped.Steps.prefixCode

private theorem restore_cost (n d : ℕ) : ((2+(2*d+5))+64*(n+d+1)^2)+5≤128*(n+d+1)^2 := by
  nlinarith only [Nat.zero_le (n^2),Nat.zero_le (d^2),Nat.zero_le (n*d)]

/-- Restore the physically parsed X while retaining Y's real TRUE tag.
That tag is explicitly clamped then recreated by the marked inverse;
arbitrary Y data, footer and suffix are untouched at their true sites. -/
theorem restore_bounded (left suffix : List Bool) (q : Rat) (hq : 0≤q) :
    BoundedRun restoreCode (Tape.mk₂ (ratLeft left q) (true::suffix)) 60
      (Tape.mk₂ left (encodeDatum (.rational q)++true::suffix)) (128*(width q)^2) := by
  let a:=q.num.natAbs
  let b:=q.den
  let archive:=aArchive (false::left) a
  have zeroSign : sign q=false := by
    simp only [sign,decide_eq_false_iff_not]
    exact not_lt.mpr hq
  have geometry : ratLeft left q=false::
      (PSTRTMRawNat010.leftBlocks (denominatorDigits q).reverse++false::archive) := by
    dsimp only [ratLeft,bothLeft,firstLeft]
    rw [zeroSign]
    rfl
  have clamped : BoundedRun clampHeaderMachine (Tape.mk₂ (ratLeft left q) (true::suffix)) 1
      (Tape.mk₂ (ratLeft left q) (false::suffix)) 2 :=
    ⟨clampHeaderTrace (ratLeft left q) suffix,clampHeader_runsFrom _ _,by rfl⟩
  have backed : BoundedRun fieldBackMachine (Tape.mk₂ (ratLeft left q) (false::suffix)) 5
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (denominatorDigits q)++false::false::suffix))
      (2*natBits b+5) := by
    rw [geometry]
    refine ⟨fieldBackTrace archive (denominatorDigits q) (false::suffix),?_,?_⟩
    · have actual:=fieldBack_runsFrom archive (denominatorDigits q) (false::suffix)
      have lastEq : fieldBackFinal archive (denominatorDigits q) (false::suffix)=
          (⟨5,Tape.mk₂ (false::archive)
            (PSTRTMIncrement009.blocks (denominatorDigits q)++false::false::suffix)⟩ : MachineState 5) := by
        change (⟨PSTRTMSeq005.rightLabel (a:=1) (3 : Fin 4),_⟩ : MachineState 5)=_
        have port : PSTRTMSeq005.rightLabel (a:=1) (3 : Fin 4)=(5 : Fin 6) := by decide
        rw [port]
        rfl
      rw [lastEq] at actual
      exact actual
    · rw [fieldBackTrace_length,denominatorDigits_length]
  have paired : BoundedRun (pairMachine true)
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (denominatorDigits q)++false::false::suffix)) 47
      (Tape.mk₂ (false::false::left) (encodeNat a++encodeNat b++true::suffix)) (64*(width q)^2) :=
    ⟨pairTrace true (false::left) a b suffix,pair_explicit_runsFrom true (false::left) a b suffix,
      by simpa only [width,a,b,payload_length] using pair_time_le true (false::left) a b suffix⟩
  have datum : encodeDatum (.rational q)=true::false::(encodeNat a++encodeNat b) := by
    rw [encodeDatum,show decide (q<0)=false from zeroSign]
    rfl
  have tagged : BoundedRun Uncapped.Steps.prefixCode
      (Tape.mk₂ (false::false::left) (encodeNat a++encodeNat b++true::suffix)) 4
      (Tape.mk₂ left (encodeDatum (.rational q)++true::suffix)) 5 := by
    rw [datum]
    exact ⟨Uncapped.Steps.prefixTrace left false false (encodeNat a++encodeNat b++true::suffix),
      Uncapped.Steps.prefix_runsFrom _ _ _ _,by rfl⟩
  have actual:=((clamped.seq backed).seq paired).seq tagged
  have port : PSTRTMSeq005.rightLabel (a:=55) (4 : Fin 5)=(60 : Fin 61) := by decide
  rw [port] at actual
  simpa only [restoreCode,restorePairCode,restoreBackCode,width,b] using actual.mono (restore_cost _ _)

def headerTrace (archive word : List Bool) : List (MachineState 10) :=
  [⟨0,Tape.mk₂ (false::false::false::false::false::archive) word⟩,
   ⟨1,Tape.mk₂ (false::false::false::false::archive) (false::word)⟩,
   ⟨2,Tape.mk₂ (false::false::false::false::archive) (true::word)⟩,
   ⟨3,Tape.mk₂ (false::false::false::archive) (false::true::word)⟩,
   ⟨4,Tape.mk₂ (false::false::false::archive) (false::true::word)⟩,
   ⟨5,Tape.mk₂ (false::false::archive) (false::false::true::word)⟩,
   ⟨6,Tape.mk₂ (false::false::archive) (false::false::true::word)⟩,
   ⟨7,Tape.mk₂ (false::archive) (false::false::false::true::word)⟩,
   ⟨8,Tape.mk₂ (false::archive) (true::false::false::true::word)⟩,
   ⟨9,Tape.mk₂ archive (false::true::false::false::true::word)⟩,
   ⟨10,Tape.mk₂ archive (true::true::false::false::true::word)⟩]

/-- Reuse PacketSteps004's actual fixed header table. It writes the
five count2 bits only on these five owned FALSE cells, never on B. -/
theorem header_bounded (archive word : List Bool) :
    BoundedRun PacketSteps.headerCode (Tape.mk₂ (List.replicate 5 false++archive) word) 10
      (Tape.mk₂ archive (encodeNat 2++word)) 11 := by
  have two : encodeNat 2=[true,true,false,false,true] := by decide
  rw [two]
  refine ⟨headerTrace archive word,⟨rfl,?_,rfl,?_⟩,by rfl⟩
  · simp [headerTrace,List.isChain_cons_cons,TM0.step,PacketSteps.headerCode,Tape.mk₂]
  · simp [TM0.step,PacketSteps.headerCode]

end RootB23.Threshold.Window.MarshalSerialize.RatCodec

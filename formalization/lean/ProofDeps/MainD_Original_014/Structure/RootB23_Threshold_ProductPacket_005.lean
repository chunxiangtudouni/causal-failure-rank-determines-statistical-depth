module
public import Structure.RootB23_Threshold_PacketSteps_004
public import Structure.PA17_TM_RatArithmetic_PairEncode_017c
public import Common.PSTR_TM_ThresholdIntegerDatum_217

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ProductPacket
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002

private theorem encodeNat_one : encodeNat 1=[true,false,true] := by decide
private theorem natural_one : encodeDatum (.natural 1)=[false,true,false,true] := by
  rw [encodeDatum,encodeNat_one]
private theorem single_bits (q : Rat) : encode [.rational q]=
    [true,false,true]++encodeDatum (.rational q)++[true] := by
  simp only [encode,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,Nat.reduceAdd,encodeNat_one]
private theorem packet_bits (q : Rat) : encode [.rational q,.natural 1]=
    [true,true,false,false,true]++encodeDatum (.rational q)++[false,true,false,true,true] := by
  simp only [encode,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,Nat.reduceAdd,encodeNat_two,natural_one,List.append_assoc]
  rfl

private theorem parse_cost (n d : ℕ) : n^2+d^2+9*(n+d)+11 ≤ 64*(n+d+1)^2 := by
  nlinarith only [Nat.zero_le (n^2),Nat.zero_le (d^2),Nat.zero_le (n*d)]
private theorem total_cost (n d : ℕ) :
    (((((4+64*(n+d+1)^2)+14)+(2*d+5))+64*(n+d+1)^2)+7)+11 ≤ 256*(n+d+1)^2 := by
  nlinarith only [Nat.zero_le (n^2),Nat.zero_le (d^2),Nat.zero_le (n*d)]

def parseCode : Machine 49 := PSTRTMSeq005.seqMachine PacketSteps.skipCode ratMachine
def appendCode : Machine 63 := PSTRTMSeq005.seqMachine parseCode PacketSteps.appendCode
def backCode : Machine 69 := PSTRTMSeq005.seqMachine appendCode fieldBackMachine
def encodeCode : Machine 117 := PSTRTMSeq005.seqMachine backCode (PA17TMRatArithmeticPairEncode017.pairMachine false)
def ratCode : Machine 124 := PSTRTMSeq005.seqMachine encodeCode PSTRTMThresholdIntegerDatum217.tagMachine
def machine : Machine 135 := PSTRTMSeq005.seqMachine ratCode PacketSteps.headerCode

/-- Actual RAW-Mul result to the ORIGINAL dynamic-cap packet. The two
LEFT and four RIGHT cells are physical internal workspace, not original
input parameters. All other archive and suffix cells are preserved.
The count1 header is changed by paid writes into count2, and Nat1 plus
the final delimiter are genuinely written. No free cursor reset occurs. -/
theorem packet_bounded (q : Rat) (hq : 0<q) (archive suffix : List Bool) :
    BoundedRun machine
      (Tape.mk₂ (false::false::archive) (encode [.rational q]++false::false::false::false::suffix)) 135
      (Tape.mk₂ archive (encode [.rational q,.natural 1]++suffix))
      (256*(natBits q.num.natAbs+natBits q.den+1)^2) := by
  let base:=true::false::true::false::false::archive
  let oldTail:=true::false::false::false::false::suffix
  let newTail:=false::true::false::true::true::suffix
  let n:=q.num.natAbs
  let d:=q.den
  let w:=natBits n+natBits d+1
  have negative : sign q=false := by simp only [sign,decide_eq_false_iff_not];exact not_lt.mpr hq.le
  have skip : BoundedRun PacketSteps.skipCode
      (Tape.mk₂ (false::false::archive) (encode [.rational q]++false::false::false::false::suffix)) 3
      (Tape.mk₂ base (encodeDatum (.rational q)++oldTail)) 4 := by
    refine ⟨PacketSteps.skipTrace (false::false::archive) (encodeDatum (.rational q)++oldTail),?_,by rfl⟩
    simpa only [single_bits,List.append_assoc,List.cons_append,List.nil_append] using
      PacketSteps.skip_runsFrom (false::false::archive) (encodeDatum (.rational q)++oldTail)
  let parsed:=ratFinal base (sign q) (numeratorDigits q) (denominatorDigits q) oldTail
  have parse : BoundedRun ratMachine (Tape.mk₂ base (encodeDatum (.rational q)++oldTail)) parsed.q
      (Tape.mk₂ (ratLeft base q) oldTail) (64*w^2) := by
    refine ⟨ratTrace base (sign q) (numeratorDigits q) (denominatorDigits q) oldTail,?_,?_⟩
    · exact encodeDatum_rat_runsFrom base oldTail q
    · rw [ratTrace_length,numeratorDigits_length,denominatorDigits_length]
      change (natBits n)^2+(natBits d)^2+9*(natBits n+natBits d)+11 ≤ 64*w^2
      exact parse_cost _ _
  have append : BoundedRun PacketSteps.appendCode (Tape.mk₂ (ratLeft base q) oldTail) 13
      (Tape.mk₂ (ratLeft base q) newTail) 14 :=
    ⟨PacketSteps.appendTrace (ratLeft base q) suffix,PacketSteps.append_runsFrom _ _,by rfl⟩
  let pairArchive:=false::base
  let numArchive:=PA17TMRatArithmeticPairEncode017.aArchive pairArchive n
  have leftEq : ratLeft base q=false::(PSTRTMRawNat010.leftBlocks (denominatorDigits q).reverse++false::numArchive) := by
    dsimp only [ratLeft,bothLeft,firstLeft]
    rw [negative]
    rfl
  let backFinal:=fieldBackFinal numArchive (denominatorDigits q) newTail
  have back : BoundedRun fieldBackMachine (Tape.mk₂ (ratLeft base q) newTail) backFinal.q
      (Tape.mk₂ (false::numArchive) (PSTRTMIncrement009.blocks (denominatorDigits q)++false::newTail))
      (2*natBits d+5) := by
    rw [leftEq]
    refine ⟨fieldBackTrace numArchive (denominatorDigits q) newTail,?_,?_⟩
    · exact fieldBack_runsFrom numArchive (denominatorDigits q) newTail
    · rw [fieldBackTrace_length,denominatorDigits_length]
  have pair : BoundedRun (PA17TMRatArithmeticPairEncode017.pairMachine false)
      (Tape.mk₂ (false::numArchive) (PSTRTMIncrement009.blocks (denominatorDigits q)++false::newTail)) 47
      (Tape.mk₂ (false::pairArchive) (encodeNat n++encodeNat d++newTail)) (64*w^2) := by
    refine ⟨PA17TMRatArithmeticPairEncode017.pairTrace false pairArchive n d (true::false::true::true::suffix),?_,?_⟩
    · exact PA17TMRatArithmeticPairEncode017.pair_explicit_runsFrom false pairArchive n d _
    · simpa only [PA17TMRatArithmeticPairEncode017.payload_length] using
        PA17TMRatArithmeticPairEncode017.pair_time_le false pairArchive n d (true::false::true::true::suffix)
  have datumEq : encodeDatum (.rational q)=true::false::(encodeNat n++encodeNat d) := by
    rw [encodeDatum,show decide (q<0)=false from negative]
    rfl
  have tag : BoundedRun PSTRTMThresholdIntegerDatum217.tagMachine
      (Tape.mk₂ (false::pairArchive) (encodeNat n++encodeNat d++newTail))
      (PSTRTMThresholdIntegerDatum217.tagFinal base (encodeNat n++encodeNat d++newTail)).q
      (Tape.mk₂ base (encodeDatum (.rational q)++newTail)) 7 := by
    refine ⟨PSTRTMThresholdIntegerDatum217.tagTrace base (encodeNat n++encodeNat d++newTail),?_,?_⟩
    · rw [datumEq]
      exact PSTRTMThresholdIntegerDatum217.tag_runsFrom _ _
    · rw [PSTRTMThresholdIntegerDatum217.tag_length]
  have header : BoundedRun PacketSteps.headerCode (Tape.mk₂ base (encodeDatum (.rational q)++newTail)) 10
      (Tape.mk₂ archive (encode [.rational q,.natural 1]++suffix)) 11 := by
    refine ⟨PacketSteps.headerTrace archive (encodeDatum (.rational q)++newTail),?_,by rfl⟩
    simpa only [packet_bits,List.append_assoc,List.cons_append,List.nil_append] using
      PacketSteps.header_runsFrom archive (encodeDatum (.rational q)++newTail)
  have actual:=(((((skip.seq parse).seq append).seq back).seq pair).seq tag).seq header
  have cost : (((((4+64*w^2)+14)+(2*natBits d+5))+64*w^2)+7)+11 ≤ 256*w^2 := by
    exact total_cost _ _
  exact actual.mono cost

theorem packet_contract (q : Rat) (hq : 0<q) (archive suffix : List Bool) (inputLength : ℕ) :
    ∃ trace, PSTRTMSeq005.RunsFrom machine
      ⟨0,Tape.mk₂ (false::false::archive) (encode [.rational q]++false::false::false::false::suffix)⟩ trace
      ⟨135,Tape.mk₂ archive (encode [.rational q,.natural 1]++suffix)⟩ ∧
      trace.length ≤ 256*(natBits q.num.natAbs+natBits q.den+1)^2 ∧
      ∀ clock, visitedSpace machine inputLength (trace.take clock) ≤
        inputLength+512*(natBits q.num.natAbs+natBits q.den+1)^2+1 := by
  obtain ⟨trace,actual,time⟩:=packet_bounded q hq archive suffix
  refine ⟨trace,actual,time,?_⟩
  intro clock
  have space:=PSTRTMTrace002.visitedSpace_le machine inputLength (trace.take clock)
  have taken : (trace.take clock).length ≤ trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
  omega

end RootB23.Threshold.ProductPacket

module
public import Structure.PA17_TM_RatArithmetic_Prefix5_060a
public import Structure.PA17_TM_RatArithmetic_Parse_002g
public import Structure.PA17_TM_RatArithmetic_Unblock_004c
public import Structure.PA17_TM_RatArithmetic_FarLoad_031c
public import Common.PSTR_TM_Prepend_022

/-! Actual target-Datum prefix insertion. Parse the original width header,
write OWN zeros, shift using the fixed FIFO, rewind and inverse-encode, then
reuse the SAME frozen022 fixed literal code on five ACTUALLY new holes.
No015 metadata is mixed into Root002 and no ancestor is recompiled. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPrefix5060
open Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

def fragment : List Bool := [true,false,true,false,true]
def reserve (archive : List Bool) : List Bool := List.replicate 4 false++false::archive
def newLeft (archive : List Bool) : List Bool := false::reserve archive
def streamLeft (archive digits : List Bool) : List Bool :=
  false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)

/-- This is a far-end blank equality on the complete right word. It
does not manufacture or discard a field boundary before a nonblank suffix. -/
theorem far_false (left word : List Bool) : Tape.mk₂ left (word++[false])=Tape.mk₂ left word :=
  PA17TMRatArithmeticBankCopy024.tape_append_false left word
theorem two_blank (left : List Bool) : Tape.mk₂ left [false,false]=Tape.mk₂ left [] :=
  (far_false left [false]).trans (far_false left [])

theorem fieldBack_final (archive digits suffix : List Bool) :
    PA17TMRatArithmeticParse002.fieldBackFinal archive digits suffix=
      ⟨5,Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++false::suffix)⟩ := by
  change (⟨PSTRTMSeq005.rightLabel (a:=1) (3 : Fin 4),
    Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++false::suffix)⟩ : MachineState 5)=_
  have hq : PSTRTMSeq005.rightLabel (a:=1) (3 : Fin 4)=(5 : Fin 6) := by decide
  rw [hq]

def parseOwnMachine : Machine 22 := PSTRTMSeq005.seqMachine (a:=17) (b:=4)
  PA17TMRatArithmeticParse002.streamMachine PA17TMRatArithmeticFarLoad031.initOwnMachine
def flaggedMachine : Machine 28 := PSTRTMSeq005.seqMachine (a:=22) (b:=5)
  parseOwnMachine PA17TMRatArithmeticParse002.fieldBackMachine

theorem flagged_bounded (n : Nat) (archive : List Bool) :
    BoundedRun flaggedMachine (Tape.mk₂ (false::archive) (encodeNat n)) 28
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n)++[false,false]))
      (16*((PSTRTMNatValue017.rawPayload n).length+1)^2+2*(PSTRTMNatValue017.rawPayload n).length+10) := by
  let digits:=PSTRTMNatValue017.rawPayload n
  have hp : BoundedRun PA17TMRatArithmeticParse002.streamMachine
      (Tape.mk₂ (false::archive) (encodeNat n)) 17 (Tape.mk₂ (streamLeft archive digits) [])
      (16*(digits.length+1)^2) := by
    refine ⟨PA17TMRatArithmeticParse002.streamTrace (false::archive) [] digits [],?_,?_⟩
    · simpa only [PA17TMRatArithmeticParse002.streamState,PA17TMRatArithmeticParse002.streamFinal,
        streamLeft,List.append_nil] using PA17TMRatArithmeticParse002.encodeNat_stream_runsFrom (false::archive) [] n
    · exact PA17TMRatArithmeticParse002.stream_length_le (false::archive) digits []
  have ho : BoundedRun PA17TMRatArithmeticFarLoad031.initOwnMachine
      (Tape.mk₂ (streamLeft archive digits) []) 4 (Tape.mk₂ (streamLeft archive digits) []) 5 := by
    have h:=PA17TMRatArithmeticFarLoad031.initOwn_runsFrom (streamLeft archive digits)
    rw [two_blank] at h
    exact ⟨PA17TMRatArithmeticFarLoad031.initOwnTrace (streamLeft archive digits),h,by rfl⟩
  have hb : BoundedRun PA17TMRatArithmeticParse002.fieldBackMachine
      (Tape.mk₂ (streamLeft archive digits) []) 5
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++[false,false])) (2*digits.length+5) := by
    have h : PSTRTMSeq005.RunsFrom PA17TMRatArithmeticParse002.fieldBackMachine
        ⟨0,Tape.mk₂ (streamLeft archive digits) []⟩
        (PA17TMRatArithmeticParse002.fieldBackTrace archive digits [])
        ⟨5,Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++[false])⟩ :=
      PA17TMRatArithmeticParse002.fieldBack_runsFrom archive digits []
    have ht : Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++[false,false])=
        Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++[false]) := by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using
        far_false (false::archive) (PSTRTMIncrement009.blocks digits++[false])
    rw [←ht] at h
    exact ⟨PA17TMRatArithmeticParse002.fieldBackTrace archive digits [],h,
      by rw [PA17TMRatArithmeticParse002.fieldBackTrace_length]⟩
  have result := (hp.seq ho).seq hb
  have hq : PSTRTMSeq005.rightLabel (a:=22) (5 : Fin 6)=(28 : Fin 29) := by decide
  rw [hq] at result
  have hc : (16*(digits.length+1)^2+5)+(2*digits.length+5)≤16*(digits.length+1)^2+2*digits.length+10 := by omega
  simpa only [flaggedMachine,parseOwnMachine,digits] using result.mono hc

def shiftedMachine : Machine 509 := PSTRTMSeq005.seqMachine (a:=28) (b:=480) flaggedMachine shiftMachine
def shiftedBackMachine : Machine 511 := PSTRTMSeq005.seqMachine (a:=509) (b:=1)
  shiftedMachine PA17TMRatArithmeticParse002.backOneMachine
def relocatedMachine : Machine 517 := PSTRTMSeq005.seqMachine (a:=511) (b:=5)
  shiftedBackMachine PA17TMRatArithmeticParse002.fieldBackMachine

theorem relocated_bounded (n : Nat) (archive : List Bool) :
    BoundedRun relocatedMachine (Tape.mk₂ (false::archive) (encodeNat n)) 517
      (Tape.mk₂ (newLeft archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n)++[false,false]))
      (16*((PSTRTMNatValue017.rawPayload n).length+1)^2+8*(PSTRTMNatValue017.rawPayload n).length+32) := by
  let digits:=PSTRTMNatValue017.rawPayload n
  have hp:=flagged_bounded n archive
  have hs : BoundedRun shiftMachine
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++[false,false])) 480
      (Tape.mk₂ (false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++List.replicate 5 false++false::archive)) [])
      (4*digits.length+15) :=
    ⟨shiftTrace 0 (false::archive) digits,shift5_runsFrom digits archive,by rw [shift_length]⟩
  have hl : BoundedRun PA17TMRatArithmeticParse002.backOneMachine
      (Tape.mk₂ (false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++List.replicate 5 false++false::archive)) []) 1
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++List.replicate 5 false++false::archive)) [false]) 2 :=
    ⟨PA17TMRatArithmeticParse002.backOneTrace
        (false::(PSTRTMRawNat010.leftBlocks digits.reverse++List.replicate 5 false++false::archive)) false [],
      PA17TMRatArithmeticParse002.backOne_runsFrom
        (false::(PSTRTMRawNat010.leftBlocks digits.reverse++List.replicate 5 false++false::archive)) false [],by rfl⟩
  have hb : BoundedRun PA17TMRatArithmeticParse002.fieldBackMachine
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++List.replicate 5 false++false::archive)) [false]) 5
      (Tape.mk₂ (newLeft archive) (PSTRTMIncrement009.blocks digits++[false,false])) (2*digits.length+5) := by
    refine ⟨PA17TMRatArithmeticParse002.fieldBackTrace (reserve archive) digits [false],?_,
      by rw [PA17TMRatArithmeticParse002.fieldBackTrace_length]⟩
    simpa only [fieldBack_final,reserve,newLeft,List.replicate_succ,List.cons_append,List.nil_append,List.append_assoc] using
      PA17TMRatArithmeticParse002.fieldBack_runsFrom (reserve archive) digits [false]
  have result:=((hp.seq hs).seq hl).seq hb
  have hq : PSTRTMSeq005.rightLabel (a:=511) (5 : Fin 6)=(517 : Fin 518) := by decide
  rw [hq] at result
  have hc : ((16*(digits.length+1)^2+2*digits.length+10+(4*digits.length+15))+2)+(2*digits.length+5)≤
      16*(digits.length+1)^2+8*digits.length+32 := by omega
  simpa only [relocatedMachine,shiftedBackMachine,shiftedMachine,digits] using result.mono hc

/- The frozen022 code is reused on five proved NEW FALSE cells. The local
proof is specific to this literal; FRONT015 conflicting metadata is absent. -/
def literal0 : Machine 0 := fun _ _ => none
def literal3 : Machine 3 := PSTRTMSeq005.seqMachine (a:=0) (b:=2) literal0 (PSTRTMPrepend022.bitMachine true)
def literal6 : Machine 6 := PSTRTMSeq005.seqMachine (a:=3) (b:=2) literal3 (PSTRTMPrepend022.bitMachine false)
def literal9 : Machine 9 := PSTRTMSeq005.seqMachine (a:=6) (b:=2) literal6 (PSTRTMPrepend022.bitMachine true)
def literal12 : Machine 12 := PSTRTMSeq005.seqMachine (a:=9) (b:=2) literal9 (PSTRTMPrepend022.bitMachine false)
def literalMachine : Machine 15 := PSTRTMSeq005.seqMachine (a:=12) (b:=2) literal12 (PSTRTMPrepend022.bitMachine true)

theorem literal_same_code : literalMachine=PSTRTMPrepend022.prefixMachine fragment := by rfl

theorem literal_bit_bounded (bit : Bool) (left right : List Bool) :
    BoundedRun (PSTRTMPrepend022.bitMachine bit) (Tape.mk₂ (false::left) right) 2
      (Tape.mk₂ left (bit::right)) 3 := by
  refine ⟨[⟨0,Tape.mk₂ (false::left) right⟩,⟨1,Tape.mk₂ left (false::right)⟩,
    ⟨2,Tape.mk₂ left (bit::right)⟩],⟨rfl,?_,rfl,?_⟩,by rfl⟩
  · simp [List.isChain_cons_cons,TM0.step,PSTRTMPrepend022.bitMachine,Tape.mk₂]
  · simp [TM0.step,PSTRTMPrepend022.bitMachine]

theorem literal5_bounded (archive right : List Bool) :
    BoundedRun literalMachine (Tape.mk₂ (newLeft archive) right) 15
      (Tape.mk₂ (false::archive) (fragment++right)) 16 := by
  have hz : BoundedRun literal0
      (Tape.mk₂ (newLeft archive) right) 0 (Tape.mk₂ (newLeft archive) right) 1 := by
    refine ⟨[⟨0,Tape.mk₂ (newLeft archive) right⟩],⟨rfl,.singleton _,rfl,?_⟩,by rfl⟩
    simp [TM0.step,literal0]
  have h1:=literal_bit_bounded true (false::false::false::false::false::archive) right
  have h2:=literal_bit_bounded false (false::false::false::false::archive) (true::right)
  have h3:=literal_bit_bounded true (false::false::false::archive) (false::true::right)
  have h4:=literal_bit_bounded false (false::false::archive) (true::false::true::right)
  have h5:=literal_bit_bounded true (false::archive) (false::true::false::true::right)
  have q3 : PSTRTMSeq005.rightLabel (a:=0) (2 : Fin 3)=(3 : Fin 4) := by decide
  have q6 : PSTRTMSeq005.rightLabel (a:=3) (2 : Fin 3)=(6 : Fin 7) := by decide
  have q9 : PSTRTMSeq005.rightLabel (a:=6) (2 : Fin 3)=(9 : Fin 10) := by decide
  have q12 : PSTRTMSeq005.rightLabel (a:=9) (2 : Fin 3)=(12 : Fin 13) := by decide
  have q15 : PSTRTMSeq005.rightLabel (a:=12) (2 : Fin 3)=(15 : Fin 16) := by decide
  have h3' : BoundedRun literal3 (Tape.mk₂ (newLeft archive) right) 3
      (Tape.mk₂ (false::false::false::false::false::archive) (true::right)) 4 := by
    simpa only [literal3,q3] using hz.seq h1
  have h6' : BoundedRun literal6 (Tape.mk₂ (newLeft archive) right) 6
      (Tape.mk₂ (false::false::false::false::archive) (false::true::right)) 7 := by
    simpa only [literal6,q6] using h3'.seq h2
  have h9' : BoundedRun literal9 (Tape.mk₂ (newLeft archive) right) 9
      (Tape.mk₂ (false::false::false::archive) (true::false::true::right)) 10 := by
    simpa only [literal9,q9] using h6'.seq h3
  have h12' : BoundedRun literal12 (Tape.mk₂ (newLeft archive) right) 12
      (Tape.mk₂ (false::false::archive) (false::true::false::true::right)) 13 := by
    simpa only [literal12,q12] using h9'.seq h4
  simpa only [literalMachine,q15,fragment,List.cons_append,List.nil_append] using h12'.seq h5

def encodedMachine : Machine 537 := PSTRTMSeq005.seqMachine (a:=517) (b:=19)
  relocatedMachine PSTRTMUnblock018.unblockMachine
def prefixMachine : Machine 553 := PSTRTMSeq005.seqMachine (a:=537) (b:=15)
  encodedMachine literalMachine

theorem prefix_bounded (n : Nat) (_hn : 4≤n) (archive : List Bool) :
    BoundedRun prefixMachine (Tape.mk₂ (false::archive) (encodeNat n)) 553
      (Tape.mk₂ (false::archive) (fragment++encodeNat n)) (128*(natBits n+1)^2) := by
  let digits:=PSTRTMNatValue017.rawPayload n
  have hr:=relocated_bounded n archive
  have hi : BoundedRun PSTRTMUnblock018.unblockMachine
      (Tape.mk₂ (newLeft archive) (PSTRTMIncrement009.blocks digits++[false,false])) 19
      (Tape.mk₂ (newLeft archive) (encodeNat n++[false])) (32*(digits.length+1)^2) :=
    ⟨PA17TMRatArithmeticUnblock004.framedTrace (reserve archive) digits [],
      PA17TMRatArithmeticUnblock004.originalNat_runsFrom n (reserve archive) [],
      PA17TMRatArithmeticUnblock004.framed_time_le (reserve archive) digits []⟩
  have hp:=literal5_bounded archive (encodeNat n++[false])
  have ht : Tape.mk₂ (false::archive) (fragment++(encodeNat n++[false]))=
      Tape.mk₂ (false::archive) (fragment++encodeNat n) := by
    simpa only [List.append_assoc] using far_false (false::archive) (fragment++encodeNat n)
  rw [ht] at hp
  have result:=(hr.seq hi).seq hp
  have hq : PSTRTMSeq005.rightLabel (a:=537) (15 : Fin 16)=(553 : Fin 554) := by decide
  rw [hq] at result
  have hl : digits.length=natBits n := by simp only [digits,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have hc : (16*(digits.length+1)^2+8*digits.length+32+32*(digits.length+1)^2)+16≤128*(natBits n+1)^2 := by
    rw [hl]
    nlinarith
  simpa only [prefixMachine,encodedMachine] using result.mono hc

/-- Fixed BoolTM0 exact target-Datum prefix producer. Original guard and
EVERY archive cell are preserved; no left credit or runtime width exists. -/
theorem prefix_contract (n : Nat) (hn : 4≤n) (archive : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom prefixMachine
      ⟨0,Tape.mk₂ (false::archive) (encodeNat n)⟩ trace
      ⟨553,Tape.mk₂ (false::archive) ([true,false,true,false,true]++encodeNat n)⟩ ∧
      trace.length≤128*(natBits n+1)^2 ∧
      ∀ inputLength k, visitedSpace prefixMachine inputLength (trace.take k) ≤
        inputLength+256*(natBits n+1)^2+1 := by
  obtain ⟨trace,hr,hl⟩:=prefix_bounded n hn archive
  refine ⟨trace,hr,hl,?_⟩
  intro inputLength k
  have hs:=PSTRTMTrace002.visitedSpace_le prefixMachine inputLength (trace.take k)
  have hk : (trace.take k).length≤trace.length := by simp only [List.length_take];omega
  omega

theorem fragment_original_datum : fragment=[true,false]++encodeNat 1 := by decide

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPrefix5060

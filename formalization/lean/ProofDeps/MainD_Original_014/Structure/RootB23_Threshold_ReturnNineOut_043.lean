module
public import Structure.RootB23_Threshold_ReturnNineBack_042

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineOut
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002
open ReturnNineLayout (Data)

/-- Only the four adjacent native DEN first cells are clamped. The
actual bookmark consumer saves the three unknown bits in finite ports;
the fourth is the known numerator-one denominator. -/
def mask (v : Data) : Data := {v with b:=false::v.b.tail,e:=false::v.e.tail,g:=false::v.g.tail,i:=false::v.i.tail}

theorem scan_bounded (left digits suffix : List Bool) :
    BoundedRun PA17TMRatArithmeticWidth018.scanMachine
      (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++false::false::suffix)) 1
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (false::suffix))
      (2*digits.length+2) := by
  exact ⟨PA17TMRatArithmeticWidth018.scanTrace left digits false suffix,
    PA17TMRatArithmeticWidth018.scan_runsFrom _ _ _ _,by rw [PA17TMRatArithmeticWidth018.scanTrace_length]⟩

/-- Twelve paid RIGHTs across the fixed old badRisk/B connector. -/
def right6 : Machine 7 := PSTRTMSeq005.seqMachine ReturnTraverse.rightCode ReturnTraverse.rightCode
def right9 : Machine 11 := PSTRTMSeq005.seqMachine right6 ReturnTraverse.rightCode
def right12 : Machine 15 := PSTRTMSeq005.seqMachine right9 ReturnTraverse.rightCode

theorem right12_bounded (left suffix : List Bool) (a b c d e f g h i j k l : Bool) :
    BoundedRun right12 (Tape.mk₂ left (a::b::c::d::e::f::g::h::i::j::k::l::suffix)) 15
      (Tape.mk₂ (l::k::j::i::h::g::f::e::d::c::b::a::left) suffix) 16 := by
  have first:=ReturnTraverse.right_bounded left (d::e::f::g::h::i::j::k::l::suffix) a b c
  have second:=ReturnTraverse.right_bounded (c::b::a::left) (g::h::i::j::k::l::suffix) d e f
  have third:=ReturnTraverse.right_bounded (f::e::d::c::b::a::left) (j::k::l::suffix) g h i
  have fourth:=ReturnTraverse.right_bounded (i::h::g::f::e::d::c::b::a::left) suffix j k l
  have actual:=((first.seq second).seq third).seq fourth
  have exit : PSTRTMSeq005.rightLabel (a:=11) (3 : Fin 4)=(15 : Fin 16) := by decide
  rw [exit] at actual
  exact actual

def code8 : Machine 1 := PA17TMRatArithmeticWidth018.scanMachine
def fee8 (_v : Data) (digits : List Bool) : ℕ := 2*digits.length+2

def code7 : Machine 3 := PSTRTMSeq005.seqMachine PA17TMRatArithmeticWidth018.scanMachine code8
def fee7 (v : Data) (digits : List Bool) : ℕ := 2*digits.length+2+fee8 v (mask v).i

def prefix6 : Machine 4 := PSTRTMSeq005.seqMachine PA17TMRatArithmeticWidth018.scanMachine tagMachine

def code6 : Machine 8 := PSTRTMSeq005.seqMachine prefix6 code7
def fee6 (v : Data) (digits : List Bool) : ℕ := 2*digits.length+5+fee7 v (mask v).h

def code5 : Machine 10 := PSTRTMSeq005.seqMachine PA17TMRatArithmeticWidth018.scanMachine code6
def fee5 (v : Data) (digits : List Bool) : ℕ := 2*digits.length+2+fee6 v (mask v).g

def prefix4 : Machine 5 := PSTRTMSeq005.seqMachine PA17TMRatArithmeticWidth018.scanMachine ReturnTraverse.rightCode

def code4 : Machine 16 := PSTRTMSeq005.seqMachine prefix4 code5
def fee4 (v : Data) (digits : List Bool) : ℕ := 2*digits.length+6+fee5 v (mask v).f

def code3 : Machine 18 := PSTRTMSeq005.seqMachine PA17TMRatArithmeticWidth018.scanMachine code4
def fee3 (v : Data) (digits : List Bool) : ℕ := 2*digits.length+2+fee4 v (mask v).e

def prefix2 : Machine 4 := PSTRTMSeq005.seqMachine PA17TMRatArithmeticWidth018.scanMachine tagMachine

def code2 : Machine 23 := PSTRTMSeq005.seqMachine prefix2 code3
def fee2 (v : Data) (digits : List Bool) : ℕ := 2*digits.length+5+fee3 v (mask v).d

def prefix1 : Machine 17 := PSTRTMSeq005.seqMachine PA17TMRatArithmeticWidth018.scanMachine right12

def code1 : Machine 41 := PSTRTMSeq005.seqMachine prefix1 code2
def fee1 (v : Data) (digits : List Bool) : ℕ := 2*digits.length+18+fee2 v (mask v).c

def code0 : Machine 43 := PSTRTMSeq005.seqMachine PA17TMRatArithmeticWidth018.scanMachine code1
def fee0 (v : Data) (digits : List Bool) : ℕ := 2*digits.length+2+fee1 v (mask v).b

theorem bounded8 (v : Data) (left digits suffix : List Bool) :
    BoundedRun code8 (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++(ReturnNineBack.after8 (mask v)++false::suffix))) 1
      (Tape.mk₂ (ReturnNineBack.finish8 (mask v) left digits) (false::suffix)) (fee8 v digits) := by
  exact scan_bounded left digits suffix

theorem bounded7 (v : Data) (left digits suffix : List Bool) :
    BoundedRun code7
      (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++(ReturnNineBack.after7 (mask v)++false::suffix))) 3
      (Tape.mk₂ (ReturnNineBack.finish7 (mask v) left digits) (false::suffix)) (fee7 v digits) := by
  have scan:=scan_bounded left digits
    (true::(PSTRTMIncrement009.blocks (mask v).i.tail++(ReturnNineBack.after8 (mask v)++false::suffix)))
  have later:=bounded8 v (false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (mask v).i suffix
  have actual:=scan.seq later
  have exit : PSTRTMSeq005.rightLabel (a:=1) (1 : Fin 2)=(3 : Fin 4) := by decide
  rw [exit] at actual
  simpa [code7,fee7,ReturnNineBack.after7,ReturnNineBack.finish7,mask,
    PSTRTMIncrement009.blocks,List.append_assoc] using actual

theorem bounded6 (v : Data) (left digits suffix : List Bool) :
    BoundedRun code6
      (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++(ReturnNineBack.after6 (mask v)++false::suffix))) 8
      (Tape.mk₂ (ReturnNineBack.finish6 (mask v) left digits) (false::suffix)) (fee6 v digits) := by
  have scan:=scan_bounded left digits
    ([false]++(PSTRTMIncrement009.blocks (mask v).h++(ReturnNineBack.after7 (mask v)++false::suffix)))
  have jump : BoundedRun tagMachine
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++left))
        (false::false::(PSTRTMIncrement009.blocks (mask v).h++(ReturnNineBack.after7 (mask v)++false::suffix)))) 2
      (Tape.mk₂ (false::false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++left))
        (PSTRTMIncrement009.blocks (mask v).h++(ReturnNineBack.after7 (mask v)++false::suffix))) 3 :=
    ⟨tagTrace _ false false _,tag_runsFrom _ _ _ _,by rfl⟩
  have later:=bounded7 v (([false,false,false]).reverse++(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (mask v).h suffix
  have actual:=(scan.seq jump).seq later
  have exit : PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4)=(8 : Fin 9) := by decide
  rw [exit] at actual
  simpa [code6,prefix6,fee6,ReturnNineBack.after6,ReturnNineBack.finish6,
    ReturnNineLayout.gap13,List.append_assoc] using actual

theorem bounded5 (v : Data) (left digits suffix : List Bool) :
    BoundedRun code5
      (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++(ReturnNineBack.after5 (mask v)++false::suffix))) 10
      (Tape.mk₂ (ReturnNineBack.finish5 (mask v) left digits) (false::suffix)) (fee5 v digits) := by
  have scan:=scan_bounded left digits
    (true::(PSTRTMIncrement009.blocks (mask v).g.tail++(ReturnNineBack.after6 (mask v)++false::suffix)))
  have later:=bounded6 v (false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (mask v).g suffix
  have actual:=scan.seq later
  have exit : PSTRTMSeq005.rightLabel (a:=1) (8 : Fin 9)=(10 : Fin 11) := by decide
  rw [exit] at actual
  simpa [code5,fee5,ReturnNineBack.after5,ReturnNineBack.finish5,mask,
    PSTRTMIncrement009.blocks,List.append_assoc] using actual

theorem bounded4 (v : Data) (left digits suffix : List Bool) :
    BoundedRun code4
      (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++(ReturnNineBack.after4 (mask v)++false::suffix))) 16
      (Tape.mk₂ (ReturnNineBack.finish4 (mask v) left digits) (false::suffix)) (fee4 v digits) := by
  have scan:=scan_bounded left digits
    ([false,false]++(PSTRTMIncrement009.blocks (mask v).f++(ReturnNineBack.after5 (mask v)++false::suffix)))
  have jump:=ReturnTraverse.right_bounded (false::(PSTRTMRawNat010.leftBlocks digits.reverse++left))
    (PSTRTMIncrement009.blocks (mask v).f++(ReturnNineBack.after5 (mask v)++false::suffix)) false false false
  have later:=bounded5 v (([false,false,false,false]).reverse++(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (mask v).f suffix
  have actual:=(scan.seq jump).seq later
  have exit : PSTRTMSeq005.rightLabel (a:=5) (10 : Fin 11)=(16 : Fin 17) := by decide
  rw [exit] at actual
  simpa [code4,prefix4,fee4,ReturnNineBack.after4,ReturnNineBack.finish4,
    ReturnNineLayout.gap13,List.append_assoc] using actual

theorem bounded3 (v : Data) (left digits suffix : List Bool) :
    BoundedRun code3
      (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++(ReturnNineBack.after3 (mask v)++false::suffix))) 18
      (Tape.mk₂ (ReturnNineBack.finish3 (mask v) left digits) (false::suffix)) (fee3 v digits) := by
  have scan:=scan_bounded left digits
    (true::(PSTRTMIncrement009.blocks (mask v).e.tail++(ReturnNineBack.after4 (mask v)++false::suffix)))
  have later:=bounded4 v (false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (mask v).e suffix
  have actual:=scan.seq later
  have exit : PSTRTMSeq005.rightLabel (a:=1) (16 : Fin 17)=(18 : Fin 19) := by decide
  rw [exit] at actual
  simpa [code3,fee3,ReturnNineBack.after3,ReturnNineBack.finish3,mask,
    PSTRTMIncrement009.blocks,List.append_assoc] using actual

theorem bounded2 (v : Data) (left digits suffix : List Bool) :
    BoundedRun code2
      (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++(ReturnNineBack.after2 (mask v)++false::suffix))) 23
      (Tape.mk₂ (ReturnNineBack.finish2 (mask v) left digits) (false::suffix)) (fee2 v digits) := by
  have scan:=scan_bounded left digits
    ([false]++(PSTRTMIncrement009.blocks (mask v).d++(ReturnNineBack.after3 (mask v)++false::suffix)))
  have jump : BoundedRun tagMachine
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++left))
        (false::false::(PSTRTMIncrement009.blocks (mask v).d++(ReturnNineBack.after3 (mask v)++false::suffix)))) 2
      (Tape.mk₂ (false::false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++left))
        (PSTRTMIncrement009.blocks (mask v).d++(ReturnNineBack.after3 (mask v)++false::suffix))) 3 :=
    ⟨tagTrace _ false false _,tag_runsFrom _ _ _ _,by rfl⟩
  have later:=bounded3 v (([false,false,false]).reverse++(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (mask v).d suffix
  have actual:=(scan.seq jump).seq later
  have exit : PSTRTMSeq005.rightLabel (a:=4) (18 : Fin 19)=(23 : Fin 24) := by decide
  rw [exit] at actual
  simpa [code2,prefix2,fee2,ReturnNineBack.after2,ReturnNineBack.finish2,
    ReturnNineLayout.gap13,List.append_assoc] using actual

theorem bounded1 (v : Data) (left digits suffix : List Bool) :
    BoundedRun code1
      (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++(ReturnNineBack.after1 (mask v)++false::suffix))) 41
      (Tape.mk₂ (ReturnNineBack.finish1 (mask v) left digits) (false::suffix)) (fee1 v digits) := by
  have scan:=scan_bounded left digits
    ([true]++List.replicate 9 false++[false]++(PSTRTMIncrement009.blocks (mask v).c++(ReturnNineBack.after2 (mask v)++false::suffix)))
  have jump:=right12_bounded (false::(PSTRTMRawNat010.leftBlocks digits.reverse++left))
    (PSTRTMIncrement009.blocks (mask v).c++(ReturnNineBack.after2 (mask v)++false::suffix))
    false true false false false false false false false false false false
  have later:=bounded2 v ((ReturnNineLayout.gap13).reverse++(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (mask v).c suffix
  have actual:=(scan.seq jump).seq later
  have exit : PSTRTMSeq005.rightLabel (a:=17) (23 : Fin 24)=(41 : Fin 42) := by decide
  rw [exit] at actual
  simpa [code1,prefix1,fee1,ReturnNineBack.after1,ReturnNineBack.finish1,
    ReturnNineLayout.gap13,List.append_assoc] using actual

theorem bounded0 (v : Data) (left digits suffix : List Bool) :
    BoundedRun code0
      (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++(ReturnNineBack.after0 (mask v)++false::suffix))) 43
      (Tape.mk₂ (ReturnNineBack.finish0 (mask v) left digits) (false::suffix)) (fee0 v digits) := by
  have scan:=scan_bounded left digits
    (true::(PSTRTMIncrement009.blocks (mask v).b.tail++(ReturnNineBack.after1 (mask v)++false::suffix)))
  have later:=bounded1 v (false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (mask v).b suffix
  have actual:=scan.seq later
  have exit : PSTRTMSeq005.rightLabel (a:=1) (41 : Fin 42)=(43 : Fin 44) := by decide
  rw [exit] at actual
  simpa [code0,fee0,ReturnNineBack.after0,ReturnNineBack.finish0,mask,
    PSTRTMIncrement009.blocks,List.append_assoc] using actual

def cap (index : Fin 9) : ℕ := match index.val with
  | 0=>43 | 1=>41 | 2=>23 | 3=>18 | 4=>16 | 5=>10 | 6=>8 | 7=>3 | _=>1

def code : (index : Fin 9) → Machine (cap index)
  | ⟨0,_⟩=>code0
  | ⟨1,_⟩=>code1
  | ⟨2,_⟩=>code2
  | ⟨3,_⟩=>code3
  | ⟨4,_⟩=>code4
  | ⟨5,_⟩=>code5
  | ⟨6,_⟩=>code6
  | ⟨7,_⟩=>code7
  | ⟨8,_⟩=>code8
  | ⟨n+9,h⟩=>False.elim (by omega)

def fee (v : Data) (index : Fin 9) (digits : List Bool) : ℕ := match index.val with
  | 0=>fee0 v digits | 1=>fee1 v digits | 2=>fee2 v digits | 3=>fee3 v digits | 4=>fee4 v digits
  | 5=>fee5 v digits | 6=>fee6 v digits | 7=>fee7 v digits | _=>fee8 v digits

theorem bounded (v : Data) (index : Fin 9) (left digits suffix : List Bool) :
    BoundedRun (code index)
      (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++(ReturnNineBack.after (mask v) index++false::suffix)))
      ⟨cap index,Nat.lt_succ_self _⟩
      (Tape.mk₂ (ReturnNineBack.finish (mask v) index left digits) (false::suffix)) (fee v index digits) := by
  fin_cases index
  · exact bounded0 v left digits suffix
  · exact bounded1 v left digits suffix
  · exact bounded2 v left digits suffix
  · exact bounded3 v left digits suffix
  · exact bounded4 v left digits suffix
  · exact bounded5 v left digits suffix
  · exact bounded6 v left digits suffix
  · exact bounded7 v left digits suffix
  · exact bounded8 v left digits suffix

end RootB23.Threshold.ReturnNineOut

module
public import Structure.RootB23_Threshold_ReturnNineLayout_041

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineBack
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open ReturnNineLayout (Data)

/-- Actual backward navigation inside the nearby nine-field source bank.
Every prefix has a fixed literal length; all field widths are traversed
by the frozen pair rewind, not passed into executable control. -/

def after8 (_v : Data) : List Bool := [false]
def finish8 (_v : Data) (left digits : List Bool) : List Bool := false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)
def code8 : Machine 4 := ReturnCompactRewind.code 1
def fee8 (_v : Data) (digits : List Bool) : ℕ := 2*digits.length+4

def after7 (v : Data) : List Bool := [false]++(PSTRTMIncrement009.blocks v.i++after8 v)
def finish7 (v : Data) (left digits : List Bool) : List Bool :=
  finish8 v (([false]).reverse++(PSTRTMRawNat010.leftBlocks digits.reverse++left)) v.i
def code7 : Machine 9 := PSTRTMSeq005.seqMachine code8 (ReturnCompactRewind.code 1)
def fee7 (v : Data) (digits : List Bool) : ℕ := fee8 v v.i+(2*digits.length+4)

def after6 (v : Data) : List Bool := [false,false,false]++(PSTRTMIncrement009.blocks v.h++after7 v)
def finish6 (v : Data) (left digits : List Bool) : List Bool :=
  finish7 v (([false,false,false]).reverse++(PSTRTMRawNat010.leftBlocks digits.reverse++left)) v.h
def code6 : Machine 16 := PSTRTMSeq005.seqMachine code7 (ReturnCompactRewind.code 3)
def fee6 (v : Data) (digits : List Bool) : ℕ := fee7 v v.h+(2*digits.length+6)

def after5 (v : Data) : List Bool := [false]++(PSTRTMIncrement009.blocks v.g++after6 v)
def finish5 (v : Data) (left digits : List Bool) : List Bool :=
  finish6 v (([false]).reverse++(PSTRTMRawNat010.leftBlocks digits.reverse++left)) v.g
def code5 : Machine 21 := PSTRTMSeq005.seqMachine code6 (ReturnCompactRewind.code 1)
def fee5 (v : Data) (digits : List Bool) : ℕ := fee6 v v.g+(2*digits.length+4)

def after4 (v : Data) : List Bool := [false,false,false,false]++(PSTRTMIncrement009.blocks v.f++after5 v)
def finish4 (v : Data) (left digits : List Bool) : List Bool :=
  finish5 v (([false,false,false,false]).reverse++(PSTRTMRawNat010.leftBlocks digits.reverse++left)) v.f
def code4 : Machine 29 := PSTRTMSeq005.seqMachine code5 (ReturnCompactRewind.code 4)
def fee4 (v : Data) (digits : List Bool) : ℕ := fee5 v v.f+(2*digits.length+7)

def after3 (v : Data) : List Bool := [false]++(PSTRTMIncrement009.blocks v.e++after4 v)
def finish3 (v : Data) (left digits : List Bool) : List Bool :=
  finish4 v (([false]).reverse++(PSTRTMRawNat010.leftBlocks digits.reverse++left)) v.e
def code3 : Machine 34 := PSTRTMSeq005.seqMachine code4 (ReturnCompactRewind.code 1)
def fee3 (v : Data) (digits : List Bool) : ℕ := fee4 v v.e+(2*digits.length+4)

def after2 (v : Data) : List Bool := [false,false,false]++(PSTRTMIncrement009.blocks v.d++after3 v)
def finish2 (v : Data) (left digits : List Bool) : List Bool :=
  finish3 v (([false,false,false]).reverse++(PSTRTMRawNat010.leftBlocks digits.reverse++left)) v.d
def code2 : Machine 41 := PSTRTMSeq005.seqMachine code3 (ReturnCompactRewind.code 3)
def fee2 (v : Data) (digits : List Bool) : ℕ := fee3 v v.d+(2*digits.length+6)

def after1 (v : Data) : List Bool := ReturnNineLayout.gap13++(PSTRTMIncrement009.blocks v.c++after2 v)
def finish1 (v : Data) (left digits : List Bool) : List Bool :=
  finish2 v ((ReturnNineLayout.gap13).reverse++(PSTRTMRawNat010.leftBlocks digits.reverse++left)) v.c
def code1 : Machine 58 := PSTRTMSeq005.seqMachine code2 (ReturnCompactRewind.code 13)
def fee1 (v : Data) (digits : List Bool) : ℕ := fee2 v v.c+(2*digits.length+16)

def after0 (v : Data) : List Bool := [false]++(PSTRTMIncrement009.blocks v.b++after1 v)
def finish0 (v : Data) (left digits : List Bool) : List Bool :=
  finish1 v (([false]).reverse++(PSTRTMRawNat010.leftBlocks digits.reverse++left)) v.b
def code0 : Machine 63 := PSTRTMSeq005.seqMachine code1 (ReturnCompactRewind.code 1)
def fee0 (v : Data) (digits : List Bool) : ℕ := fee1 v v.b+(2*digits.length+4)

theorem bounded8 (v : Data) (archive digits suffix : List Bool) :
    BoundedRun code8 (Tape.mk₂ (finish8 v (false::archive) digits) (false::suffix)) 4
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++(after8 v++false::suffix)))
      (fee8 v digits) := by
  have actual:=ReturnCompactRewind.bounded [false] archive digits (false::suffix)
  exact actual.mono (by simp only [fee8,List.length_cons,List.length_nil];omega)

theorem bounded7 (v : Data) (archive digits suffix : List Bool) :
    BoundedRun code7 (Tape.mk₂ (finish7 v (false::archive) digits) (false::suffix)) 9
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++(after7 v++false::suffix)))
      (fee7 v digits) := by
  have later:=bounded8 v (([false]).reverse.tail++(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) v.i suffix
  have step:=ReturnCompactRewind.bounded ([false]).reverse archive digits
    (PSTRTMIncrement009.blocks v.i++(after8 v++false::suffix))
  have stepFee : BoundedRun (ReturnCompactRewind.code 1) _ (4 : Fin 5) _ (2*digits.length+4) := step.mono (by change 2*digits.length+1+3≤2*digits.length+4;omega :
    2*digits.length+([false]).reverse.length+3≤2*digits.length+4)
  have actual:=later.seq stepFee
  have exit : PSTRTMSeq005.rightLabel (a:=4) (4 : Fin 5)=(9 : Fin 10) := by decide
  rw [exit] at actual
  simpa [code7,finish7,after7,fee7,List.append_assoc] using actual

theorem bounded6 (v : Data) (archive digits suffix : List Bool) :
    BoundedRun code6 (Tape.mk₂ (finish6 v (false::archive) digits) (false::suffix)) 16
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++(after6 v++false::suffix)))
      (fee6 v digits) := by
  have later:=bounded7 v (([false,false,false]).reverse.tail++(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) v.h suffix
  have step:=ReturnCompactRewind.bounded ([false,false,false]).reverse archive digits
    (PSTRTMIncrement009.blocks v.h++(after7 v++false::suffix))
  have stepFee : BoundedRun (ReturnCompactRewind.code 3) _ (6 : Fin 7) _ (2*digits.length+6) := step.mono (by change 2*digits.length+3+3≤2*digits.length+6;omega :
    2*digits.length+([false,false,false]).reverse.length+3≤2*digits.length+6)
  have actual:=later.seq stepFee
  have exit : PSTRTMSeq005.rightLabel (a:=9) (6 : Fin 7)=(16 : Fin 17) := by decide
  rw [exit] at actual
  simpa [code6,finish6,after6,fee6,List.append_assoc] using actual

theorem bounded5 (v : Data) (archive digits suffix : List Bool) :
    BoundedRun code5 (Tape.mk₂ (finish5 v (false::archive) digits) (false::suffix)) 21
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++(after5 v++false::suffix)))
      (fee5 v digits) := by
  have later:=bounded6 v (([false]).reverse.tail++(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) v.g suffix
  have step:=ReturnCompactRewind.bounded ([false]).reverse archive digits
    (PSTRTMIncrement009.blocks v.g++(after6 v++false::suffix))
  have stepFee : BoundedRun (ReturnCompactRewind.code 1) _ (4 : Fin 5) _ (2*digits.length+4) := step.mono (by change 2*digits.length+1+3≤2*digits.length+4;omega :
    2*digits.length+([false]).reverse.length+3≤2*digits.length+4)
  have actual:=later.seq stepFee
  have exit : PSTRTMSeq005.rightLabel (a:=16) (4 : Fin 5)=(21 : Fin 22) := by decide
  rw [exit] at actual
  simpa [code5,finish5,after5,fee5,List.append_assoc] using actual

theorem bounded4 (v : Data) (archive digits suffix : List Bool) :
    BoundedRun code4 (Tape.mk₂ (finish4 v (false::archive) digits) (false::suffix)) 29
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++(after4 v++false::suffix)))
      (fee4 v digits) := by
  have later:=bounded5 v (([false,false,false,false]).reverse.tail++(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) v.f suffix
  have step:=ReturnCompactRewind.bounded ([false,false,false,false]).reverse archive digits
    (PSTRTMIncrement009.blocks v.f++(after5 v++false::suffix))
  have stepFee : BoundedRun (ReturnCompactRewind.code 4) _ (7 : Fin 8) _ (2*digits.length+7) := step.mono (by change 2*digits.length+4+3≤2*digits.length+7;omega :
    2*digits.length+([false,false,false,false]).reverse.length+3≤2*digits.length+7)
  have actual:=later.seq stepFee
  have exit : PSTRTMSeq005.rightLabel (a:=21) (7 : Fin 8)=(29 : Fin 30) := by decide
  rw [exit] at actual
  simpa [code4,finish4,after4,fee4,List.append_assoc] using actual

theorem bounded3 (v : Data) (archive digits suffix : List Bool) :
    BoundedRun code3 (Tape.mk₂ (finish3 v (false::archive) digits) (false::suffix)) 34
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++(after3 v++false::suffix)))
      (fee3 v digits) := by
  have later:=bounded4 v (([false]).reverse.tail++(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) v.e suffix
  have step:=ReturnCompactRewind.bounded ([false]).reverse archive digits
    (PSTRTMIncrement009.blocks v.e++(after4 v++false::suffix))
  have stepFee : BoundedRun (ReturnCompactRewind.code 1) _ (4 : Fin 5) _ (2*digits.length+4) := step.mono (by change 2*digits.length+1+3≤2*digits.length+4;omega :
    2*digits.length+([false]).reverse.length+3≤2*digits.length+4)
  have actual:=later.seq stepFee
  have exit : PSTRTMSeq005.rightLabel (a:=29) (4 : Fin 5)=(34 : Fin 35) := by decide
  rw [exit] at actual
  simpa [code3,finish3,after3,fee3,List.append_assoc] using actual

theorem bounded2 (v : Data) (archive digits suffix : List Bool) :
    BoundedRun code2 (Tape.mk₂ (finish2 v (false::archive) digits) (false::suffix)) 41
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++(after2 v++false::suffix)))
      (fee2 v digits) := by
  have later:=bounded3 v (([false,false,false]).reverse.tail++(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) v.d suffix
  have step:=ReturnCompactRewind.bounded ([false,false,false]).reverse archive digits
    (PSTRTMIncrement009.blocks v.d++(after3 v++false::suffix))
  have stepFee : BoundedRun (ReturnCompactRewind.code 3) _ (6 : Fin 7) _ (2*digits.length+6) := step.mono (by change 2*digits.length+3+3≤2*digits.length+6;omega :
    2*digits.length+([false,false,false]).reverse.length+3≤2*digits.length+6)
  have actual:=later.seq stepFee
  have exit : PSTRTMSeq005.rightLabel (a:=34) (6 : Fin 7)=(41 : Fin 42) := by decide
  rw [exit] at actual
  simpa [code2,finish2,after2,fee2,List.append_assoc] using actual

theorem bounded1 (v : Data) (archive digits suffix : List Bool) :
    BoundedRun code1 (Tape.mk₂ (finish1 v (false::archive) digits) (false::suffix)) 58
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++(after1 v++false::suffix)))
      (fee1 v digits) := by
  have later:=bounded2 v ((ReturnNineLayout.gap13).reverse.tail++(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) v.c suffix
  have step:=ReturnCompactRewind.bounded (ReturnNineLayout.gap13).reverse archive digits
    (PSTRTMIncrement009.blocks v.c++(after2 v++false::suffix))
  have stepFee : BoundedRun (ReturnCompactRewind.code 13) _ (16 : Fin 17) _ (2*digits.length+16) := step.mono (by change 2*digits.length+13+3≤2*digits.length+16;omega :
    2*digits.length+(ReturnNineLayout.gap13).reverse.length+3≤2*digits.length+16)
  have actual:=later.seq stepFee
  have exit : PSTRTMSeq005.rightLabel (a:=41) (16 : Fin 17)=(58 : Fin 59) := by decide
  rw [exit] at actual
  simpa [code1,finish1,after1,fee1,ReturnNineLayout.gap13,List.replicate_succ,List.append_assoc] using actual

theorem bounded0 (v : Data) (archive digits suffix : List Bool) :
    BoundedRun code0 (Tape.mk₂ (finish0 v (false::archive) digits) (false::suffix)) 63
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++(after0 v++false::suffix)))
      (fee0 v digits) := by
  have later:=bounded1 v (([false]).reverse.tail++(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) v.b suffix
  have step:=ReturnCompactRewind.bounded ([false]).reverse archive digits
    (PSTRTMIncrement009.blocks v.b++(after1 v++false::suffix))
  have stepFee : BoundedRun (ReturnCompactRewind.code 1) _ (4 : Fin 5) _ (2*digits.length+4) := step.mono (by change 2*digits.length+1+3≤2*digits.length+4;omega :
    2*digits.length+([false]).reverse.length+3≤2*digits.length+4)
  have actual:=later.seq stepFee
  have exit : PSTRTMSeq005.rightLabel (a:=58) (4 : Fin 5)=(63 : Fin 64) := by decide
  rw [exit] at actual
  simpa [code0,finish0,after0,fee0,List.append_assoc] using actual

def cap (index : Fin 9) : ℕ := match index.val with
  | 0=>63 | 1=>58 | 2=>41 | 3=>34 | 4=>29 | 5=>21 | 6=>16 | 7=>9 | _=>4

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

def after (v : Data) (index : Fin 9) : List Bool := match index.val with
  | 0=>after0 v | 1=>after1 v | 2=>after2 v | 3=>after3 v | 4=>after4 v
  | 5=>after5 v | 6=>after6 v | 7=>after7 v | _=>after8 v

def finish (v : Data) (index : Fin 9) (left digits : List Bool) : List Bool := match index.val with
  | 0=>finish0 v left digits | 1=>finish1 v left digits | 2=>finish2 v left digits
  | 3=>finish3 v left digits | 4=>finish4 v left digits | 5=>finish5 v left digits
  | 6=>finish6 v left digits | 7=>finish7 v left digits | _=>finish8 v left digits

def fee (v : Data) (index : Fin 9) (digits : List Bool) : ℕ := match index.val with
  | 0=>fee0 v digits | 1=>fee1 v digits | 2=>fee2 v digits | 3=>fee3 v digits | 4=>fee4 v digits
  | 5=>fee5 v digits | 6=>fee6 v digits | 7=>fee7 v digits | _=>fee8 v digits

theorem bounded (v : Data) (index : Fin 9) (archive digits suffix : List Bool) :
    BoundedRun (code index) (Tape.mk₂ (finish v index (false::archive) digits) (false::suffix))
      ⟨cap index,Nat.lt_succ_self _⟩
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++(after v index++false::suffix)))
      (fee v index digits) := by
  fin_cases index
  · exact bounded0 v archive digits suffix
  · exact bounded1 v archive digits suffix
  · exact bounded2 v archive digits suffix
  · exact bounded3 v archive digits suffix
  · exact bounded4 v archive digits suffix
  · exact bounded5 v archive digits suffix
  · exact bounded6 v archive digits suffix
  · exact bounded7 v archive digits suffix
  · exact bounded8 v archive digits suffix

/-- The exact physical footer is the same whichever source field is
selected; this equality does not move or erase any intervening cell. -/
theorem finish_at (base : List Bool) (v : Data) (index : Fin 9) :
    finish v index (ReturnNineLayout.leftAt base v index) (ReturnNineLayout.field v index)=
      ReturnNineLayout.footerLeft base v := by
  fin_cases index <;>
    simp [finish,finish0,finish1,finish2,finish3,finish4,finish5,finish6,finish7,finish8,
      ReturnNineLayout.leftAt,ReturnNineLayout.field,ReturnNineLayout.footerLeft,
      ReturnNineLayout.left0,ReturnNineLayout.left1,ReturnNineLayout.left2,ReturnNineLayout.left3,
      ReturnNineLayout.left4,ReturnNineLayout.left5,ReturnNineLayout.left6,ReturnNineLayout.left7,
      ReturnNineLayout.left8,ReturnNineLayout.gap13]

theorem right_at (v : Data) (index : Fin 9) :
    PSTRTMIncrement009.blocks (ReturnNineLayout.field v index)++after v index++[false]=
      ReturnNineLayout.rightAt v index := by
  fin_cases index <;>
    simp [after,after0,after1,after2,after3,after4,after5,after6,after7,after8,
      ReturnNineLayout.field,ReturnNineLayout.rightAt,ReturnNineLayout.right0,
      ReturnNineLayout.right1,ReturnNineLayout.right2,ReturnNineLayout.right3,
      ReturnNineLayout.right4,ReturnNineLayout.right5,ReturnNineLayout.right6,
      ReturnNineLayout.right7,ReturnNineLayout.right8,List.append_assoc]

end RootB23.Threshold.ReturnNineBack

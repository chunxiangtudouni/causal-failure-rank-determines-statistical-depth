module
public import Structure.RootB23_Threshold_ReturnNineStep_049

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineStart
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031
open ReturnNineLayout (Data)

theorem left_false (base : List Bool) (v : Data) (index : Fin 9) :
    false::(ReturnNineLayout.leftAt base v index).tail=ReturnNineLayout.leftAt base v index := by
  fin_cases index <;> rfl

theorem source_word (base : List Bool) (v : Data) (index : Fin 9) (suffix : List Bool) :
    Tape.mk₂ (ReturnNineLayout.leftAt base (ReturnNineOut.mask v) index)
      (RoutedCopy.fieldWord (ReturnNineRoute.context v index)
        (ReturnNineLayout.field (ReturnNineOut.mask v) index) suffix)=
      ReturnNineBook.tapeAt base (ReturnNineOut.mask v) index suffix := by
  rw [ReturnNineRoute.fieldWord_eq]
  have word:=congrArg
    (fun right=>Tape.mk₂ (ReturnNineLayout.leftAt base (ReturnNineOut.mask v) index) (right++suffix))
    (ReturnNineBack.right_at (ReturnNineOut.mask v) index)
  simpa only [ReturnNineBook.tapeAt,List.append_assoc,List.cons_append,List.nil_append] using word

/-- This fixed prefix stops at the original near B DATA, not a supplied
home label. All twelve cells of the old badRisk/B connector are crossed. -/
theorem toB_bounded (base : List Bool) (v : Data) (suffix : List Bool) :
    BoundedRun ReturnNineOut.prefix1 (ReturnNineBook.tapeAt base (ReturnNineOut.mask v) 1 suffix) 17
      (ReturnNineBook.tapeAt base (ReturnNineOut.mask v) 2 suffix)
      (2*(ReturnNineOut.mask v).b.length+18) := by
  let m:=ReturnNineOut.mask v
  let left:=ReturnNineLayout.left1 base m
  let tail:=ReturnNineLayout.right2 m++suffix
  have scan:=ReturnNineOut.scan_bounded left m.b ([true]++List.replicate 9 false++[false]++tail)
  have jump:=ReturnNineOut.right12_bounded
    (false::(PSTRTMRawNat010.leftBlocks m.b.reverse++left)) tail
    false true false false false false false false false false false false
  have actual:=scan.seq jump
  have exit : PSTRTMSeq005.rightLabel (a:=1) (15 : Fin 16)=(17 : Fin 18) := by decide
  rw [exit] at actual
  simpa [ReturnNineOut.prefix1,ReturnNineBook.tapeAt,ReturnNineLayout.leftAt,ReturnNineLayout.rightAt,
    ReturnNineLayout.right1,ReturnNineLayout.left2,ReturnNineLayout.gap13,List.replicate_succ,
    left,tail,m,List.append_assoc] using actual.mono (by dsimp only [m];omega)

def headroomCode : Machine 179 := PSTRTMSeq005.seqMachine ReturnHeadroom.fourCode ReturnHeadroom.twoCode

/-- Six true RIGHT1 shifts create the seven owned FALSE cells. EAST is
genuinely blank here, immediately after the first copied B field. -/
theorem headroom_bounded (archive digits : List Bool) :
    BoundedRun headroomCode (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits)) 179
      (Tape.mk₂ (List.replicate 7 false++archive) (PSTRTMIncrement009.blocks digits))
      (60*digits.length+144) := by
  have first:=ReturnHeadroom.four_bounded archive digits
  have second:=ReturnHeadroom.two_bounded (List.replicate 4 false++archive) digits
  exact (first.seq second).mono (by omega)

def copiedCode : Machine 1180 := PSTRTMSeq005.seqMachine ReturnNineOut.prefix1 (RoutedCopy.copyMachine (ReturnNineRoute.route 2))
def code : Machine 1360 := PSTRTMSeq005.seqMachine copiedCode headroomCode

def fee (v : Data) : ℕ :=
  (2*(ReturnNineOut.mask v).b.length+18)+
    (4*v.c.length^2+(2*ReturnNineRoute.cost v+41)*v.c.length+3*ReturnNineRoute.cost v+29)+
    (60*v.c.length+144)

/-- Actual observed bank -> real B copy -> paid seven-cell prefix.
No room credit is an executable or original input. -/
theorem bounded (base : List Bool) (v : Data) :
    BoundedRun code (ReturnNineBook.tapeAt base (ReturnNineOut.mask v) 1 (workSuffix 0 [])) 1360
      (Tape.mk₂ (ReturnNineDest.home (ReturnNineLayout.footerLeft base (ReturnNineOut.mask v)))
        (PA17TMRatArithmeticCopy006.workspace v.c)) (fee v) := by
  let m:=ReturnNineOut.mask v
  let footer:=ReturnNineLayout.footerLeft base m
  have first:=toB_bounded base v (workSuffix 0 [])
  have copied:=RoutedCopy.copy_bounded _ _ _ _ (ReturnNineRoute.correct v 2)
    (ReturnNineLayout.left2 base m).tail v.c 0
  have leftEq:=left_false base m (2 : Fin 9)
  change false::(ReturnNineLayout.left2 base m).tail=ReturnNineLayout.left2 base m at leftEq
  rw [leftEq] at copied
  have sourceFinish : ReturnNineRoute.finish v 2 (ReturnNineLayout.left2 base m) v.c=footer :=
    ReturnNineBack.finish_at base m 2
  rw [sourceFinish] at copied
  have word:=source_word base v (2 : Fin 9) (workSuffix 0 [])
  change Tape.mk₂ (ReturnNineLayout.left2 base m)
    (RoutedCopy.fieldWord (ReturnNineRoute.context v 2) v.c (workSuffix 0 []))=
      ReturnNineBook.tapeAt base m 2 (workSuffix 0 []) at word
  rw [word] at copied
  have paid:=headroom_bounded (true::false::footer) v.c
  have work : Tape.mk₂ (RoutedCopy.destinationLeft 0 footer) (PA17TMRatArithmeticCopy006.workspace v.c)=
      Tape.mk₂ (false::true::false::footer) (PSTRTMIncrement009.blocks v.c) :=
    PA17TMDivisionTape005.tape_owned00 _ _
  rw [work] at copied
  have actual:=(first.seq copied).seq paid
  have exit : PSTRTMSeq005.rightLabel (a:=1180) (179 : Fin 180)=(1360 : Fin 1361) := by decide
  rw [exit] at actual
  have final : Tape.mk₂ (List.replicate 7 false++true::false::footer) (PSTRTMIncrement009.blocks v.c)=
      Tape.mk₂ (ReturnNineDest.home footer) (PA17TMRatArithmeticCopy006.workspace v.c) :=
    (PA17TMDivisionTape005.tape_owned00 _ _).symm
  rw [final] at actual
  simpa only [code,copiedCode,fee,m,footer,Nat.mul_zero,Nat.add_zero] using actual

end RootB23.Threshold.ReturnNineStart

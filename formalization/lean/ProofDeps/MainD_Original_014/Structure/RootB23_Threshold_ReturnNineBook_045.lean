module
public import Structure.RootB23_Threshold_ReturnNineRoute_044

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineBook
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBookmark014 PA17TMRatArithmeticAllocate013
open ReturnNineLayout (Data)

def tapeAt (base : List Bool) (v : Data) (index : Fin 9) (suffix : List Bool) : Tape Bool :=
  Tape.mk₂ (ReturnNineLayout.leftAt base v index) (ReturnNineLayout.rightAt v index++suffix)

def clearI (v : Data) : Data := {v with i:=clampFirst v.i}
def clearG (v : Data) : Data := {v with g:=clampFirst v.g}
def clearE (v : Data) : Data := {v with e:=clampFirst v.e}
def clearB (v : Data) : Data := {v with b:=clampFirst v.b}
def clearGE (v : Data) : Data := clearE (clearG v)

theorem read_bounded (left digits suffix : List Bool) (nonempty : digits≠[]) :
    BoundedRun readClearMachine (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++suffix))
      (readPort (observedFirst digits))
      (Tape.mk₂ left (PSTRTMIncrement009.blocks (clampFirst digits)++suffix)) 2 := by
  cases digits with
  | nil=>exact False.elim (nonempty rfl)
  | cons bit later=>
    exact ⟨readClearTrace left bit (true::(PSTRTMIncrement009.blocks later++suffix)),
      readClear_runsFrom _ _ _,by rfl⟩

theorem clear_bounded (left digits suffix : List Bool) (nonempty : digits≠[]) :
    BoundedRun (setMarkerMachine false) (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++suffix)) 1
      (Tape.mk₂ left (PSTRTMIncrement009.blocks (clampFirst digits)++suffix)) 2 := by
  cases digits with
  | nil=>exact False.elim (nonempty rfl)
  | cons bit later=>
    exact ⟨setMarkerTrace bit false left (true::(PSTRTMIncrement009.blocks later++suffix)),
      setMarker_runsFrom _ _ _ _,by rfl⟩

theorem previous1 (base : List Bool) (v : Data) (suffix : List Bool) :
    BoundedRun (ReturnCompactRewind.code 1) (tapeAt base v 1 suffix) 4
      (tapeAt base v 0 suffix) (2*v.a.length+4) := by
  have actual : BoundedRun (ReturnCompactRewind.code 1) _ (4 : Fin 5) _ (2*v.a.length+4) :=
    (ReturnCompactRewind.bounded ([false]).reverse (ReturnNineLayout.leftAt base v 0).tail v.a
      (ReturnNineLayout.rightAt v 1++suffix)).mono (by
        change 2*v.a.length+1+3≤2*v.a.length+4
        omega)
  simpa [tapeAt,ReturnNineLayout.leftAt,ReturnNineLayout.rightAt,ReturnNineLayout.left0,ReturnNineLayout.left1,ReturnNineLayout.left2,ReturnNineLayout.left3,ReturnNineLayout.left4,ReturnNineLayout.left5,ReturnNineLayout.left6,ReturnNineLayout.left7,ReturnNineLayout.left8,ReturnNineLayout.right0,ReturnNineLayout.right1,ReturnNineLayout.right2,ReturnNineLayout.right3,ReturnNineLayout.right4,ReturnNineLayout.right5,ReturnNineLayout.right6,ReturnNineLayout.right7,ReturnNineLayout.right8,
    ReturnNineLayout.gap13,List.append_assoc] using actual

theorem previous2 (base : List Bool) (v : Data) (suffix : List Bool) :
    BoundedRun (ReturnCompactRewind.code 13) (tapeAt base v 2 suffix) 16
      (tapeAt base v 1 suffix) (2*v.b.length+16) := by
  have actual : BoundedRun (ReturnCompactRewind.code 13) _ (16 : Fin 17) _ (2*v.b.length+16) :=
    (ReturnCompactRewind.bounded (ReturnNineLayout.gap13).reverse (ReturnNineLayout.leftAt base v 1).tail v.b
      (ReturnNineLayout.rightAt v 2++suffix)).mono (by
        change 2*v.b.length+13+3≤2*v.b.length+16
        omega)
  simpa [tapeAt,ReturnNineLayout.leftAt,ReturnNineLayout.rightAt,ReturnNineLayout.left0,ReturnNineLayout.left1,ReturnNineLayout.left2,ReturnNineLayout.left3,ReturnNineLayout.left4,ReturnNineLayout.left5,ReturnNineLayout.left6,ReturnNineLayout.left7,ReturnNineLayout.left8,ReturnNineLayout.right0,ReturnNineLayout.right1,ReturnNineLayout.right2,ReturnNineLayout.right3,ReturnNineLayout.right4,ReturnNineLayout.right5,ReturnNineLayout.right6,ReturnNineLayout.right7,ReturnNineLayout.right8,
    ReturnNineLayout.gap13,List.append_assoc] using actual

theorem previous3 (base : List Bool) (v : Data) (suffix : List Bool) :
    BoundedRun (ReturnCompactRewind.code 3) (tapeAt base v 3 suffix) 6
      (tapeAt base v 2 suffix) (2*v.c.length+6) := by
  have actual : BoundedRun (ReturnCompactRewind.code 3) _ (6 : Fin 7) _ (2*v.c.length+6) :=
    (ReturnCompactRewind.bounded ([false,false,false]).reverse (ReturnNineLayout.leftAt base v 2).tail v.c
      (ReturnNineLayout.rightAt v 3++suffix)).mono (by
        change 2*v.c.length+3+3≤2*v.c.length+6
        omega)
  simpa [tapeAt,ReturnNineLayout.leftAt,ReturnNineLayout.rightAt,ReturnNineLayout.left0,ReturnNineLayout.left1,ReturnNineLayout.left2,ReturnNineLayout.left3,ReturnNineLayout.left4,ReturnNineLayout.left5,ReturnNineLayout.left6,ReturnNineLayout.left7,ReturnNineLayout.left8,ReturnNineLayout.right0,ReturnNineLayout.right1,ReturnNineLayout.right2,ReturnNineLayout.right3,ReturnNineLayout.right4,ReturnNineLayout.right5,ReturnNineLayout.right6,ReturnNineLayout.right7,ReturnNineLayout.right8,
    ReturnNineLayout.gap13,List.append_assoc] using actual

theorem previous4 (base : List Bool) (v : Data) (suffix : List Bool) :
    BoundedRun (ReturnCompactRewind.code 1) (tapeAt base v 4 suffix) 4
      (tapeAt base v 3 suffix) (2*v.d.length+4) := by
  have actual : BoundedRun (ReturnCompactRewind.code 1) _ (4 : Fin 5) _ (2*v.d.length+4) :=
    (ReturnCompactRewind.bounded ([false]).reverse (ReturnNineLayout.leftAt base v 3).tail v.d
      (ReturnNineLayout.rightAt v 4++suffix)).mono (by
        change 2*v.d.length+1+3≤2*v.d.length+4
        omega)
  simpa [tapeAt,ReturnNineLayout.leftAt,ReturnNineLayout.rightAt,ReturnNineLayout.left0,ReturnNineLayout.left1,ReturnNineLayout.left2,ReturnNineLayout.left3,ReturnNineLayout.left4,ReturnNineLayout.left5,ReturnNineLayout.left6,ReturnNineLayout.left7,ReturnNineLayout.left8,ReturnNineLayout.right0,ReturnNineLayout.right1,ReturnNineLayout.right2,ReturnNineLayout.right3,ReturnNineLayout.right4,ReturnNineLayout.right5,ReturnNineLayout.right6,ReturnNineLayout.right7,ReturnNineLayout.right8,
    ReturnNineLayout.gap13,List.append_assoc] using actual

theorem previous5 (base : List Bool) (v : Data) (suffix : List Bool) :
    BoundedRun (ReturnCompactRewind.code 4) (tapeAt base v 5 suffix) 7
      (tapeAt base v 4 suffix) (2*v.e.length+7) := by
  have actual : BoundedRun (ReturnCompactRewind.code 4) _ (7 : Fin 8) _ (2*v.e.length+7) :=
    (ReturnCompactRewind.bounded ([false,false,false,false]).reverse (ReturnNineLayout.leftAt base v 4).tail v.e
      (ReturnNineLayout.rightAt v 5++suffix)).mono (by
        change 2*v.e.length+4+3≤2*v.e.length+7
        omega)
  simpa [tapeAt,ReturnNineLayout.leftAt,ReturnNineLayout.rightAt,ReturnNineLayout.left0,ReturnNineLayout.left1,ReturnNineLayout.left2,ReturnNineLayout.left3,ReturnNineLayout.left4,ReturnNineLayout.left5,ReturnNineLayout.left6,ReturnNineLayout.left7,ReturnNineLayout.left8,ReturnNineLayout.right0,ReturnNineLayout.right1,ReturnNineLayout.right2,ReturnNineLayout.right3,ReturnNineLayout.right4,ReturnNineLayout.right5,ReturnNineLayout.right6,ReturnNineLayout.right7,ReturnNineLayout.right8,
    ReturnNineLayout.gap13,List.append_assoc] using actual

theorem previous6 (base : List Bool) (v : Data) (suffix : List Bool) :
    BoundedRun (ReturnCompactRewind.code 1) (tapeAt base v 6 suffix) 4
      (tapeAt base v 5 suffix) (2*v.f.length+4) := by
  have actual : BoundedRun (ReturnCompactRewind.code 1) _ (4 : Fin 5) _ (2*v.f.length+4) :=
    (ReturnCompactRewind.bounded ([false]).reverse (ReturnNineLayout.leftAt base v 5).tail v.f
      (ReturnNineLayout.rightAt v 6++suffix)).mono (by
        change 2*v.f.length+1+3≤2*v.f.length+4
        omega)
  simpa [tapeAt,ReturnNineLayout.leftAt,ReturnNineLayout.rightAt,ReturnNineLayout.left0,ReturnNineLayout.left1,ReturnNineLayout.left2,ReturnNineLayout.left3,ReturnNineLayout.left4,ReturnNineLayout.left5,ReturnNineLayout.left6,ReturnNineLayout.left7,ReturnNineLayout.left8,ReturnNineLayout.right0,ReturnNineLayout.right1,ReturnNineLayout.right2,ReturnNineLayout.right3,ReturnNineLayout.right4,ReturnNineLayout.right5,ReturnNineLayout.right6,ReturnNineLayout.right7,ReturnNineLayout.right8,
    ReturnNineLayout.gap13,List.append_assoc] using actual

theorem previous7 (base : List Bool) (v : Data) (suffix : List Bool) :
    BoundedRun (ReturnCompactRewind.code 3) (tapeAt base v 7 suffix) 6
      (tapeAt base v 6 suffix) (2*v.g.length+6) := by
  have actual : BoundedRun (ReturnCompactRewind.code 3) _ (6 : Fin 7) _ (2*v.g.length+6) :=
    (ReturnCompactRewind.bounded ([false,false,false]).reverse (ReturnNineLayout.leftAt base v 6).tail v.g
      (ReturnNineLayout.rightAt v 7++suffix)).mono (by
        change 2*v.g.length+3+3≤2*v.g.length+6
        omega)
  simpa [tapeAt,ReturnNineLayout.leftAt,ReturnNineLayout.rightAt,ReturnNineLayout.left0,ReturnNineLayout.left1,ReturnNineLayout.left2,ReturnNineLayout.left3,ReturnNineLayout.left4,ReturnNineLayout.left5,ReturnNineLayout.left6,ReturnNineLayout.left7,ReturnNineLayout.left8,ReturnNineLayout.right0,ReturnNineLayout.right1,ReturnNineLayout.right2,ReturnNineLayout.right3,ReturnNineLayout.right4,ReturnNineLayout.right5,ReturnNineLayout.right6,ReturnNineLayout.right7,ReturnNineLayout.right8,
    ReturnNineLayout.gap13,List.append_assoc] using actual

theorem previous8 (base : List Bool) (v : Data) (suffix : List Bool) :
    BoundedRun (ReturnCompactRewind.code 1) (tapeAt base v 8 suffix) 4
      (tapeAt base v 7 suffix) (2*v.h.length+4) := by
  have actual : BoundedRun (ReturnCompactRewind.code 1) _ (4 : Fin 5) _ (2*v.h.length+4) :=
    (ReturnCompactRewind.bounded ([false]).reverse (ReturnNineLayout.leftAt base v 7).tail v.h
      (ReturnNineLayout.rightAt v 8++suffix)).mono (by
        change 2*v.h.length+1+3≤2*v.h.length+4
        omega)
  simpa [tapeAt,ReturnNineLayout.leftAt,ReturnNineLayout.rightAt,ReturnNineLayout.left0,ReturnNineLayout.left1,ReturnNineLayout.left2,ReturnNineLayout.left3,ReturnNineLayout.left4,ReturnNineLayout.left5,ReturnNineLayout.left6,ReturnNineLayout.left7,ReturnNineLayout.left8,ReturnNineLayout.right0,ReturnNineLayout.right1,ReturnNineLayout.right2,ReturnNineLayout.right3,ReturnNineLayout.right4,ReturnNineLayout.right5,ReturnNineLayout.right6,ReturnNineLayout.right7,ReturnNineLayout.right8,
    ReturnNineLayout.gap13,List.append_assoc] using actual

def stage0 : Machine 7 := PSTRTMSeq005.seqMachine ReturnNineBack.code8 readClearMachine
def port0 (bit : Bool) : Fin 8 := if bit then 7 else 6

theorem stage0_bounded (base : List Bool) (v : Data) (suffix : List Bool) (nonempty : v.i≠[]) :
    BoundedRun stage0 (Tape.mk₂ (ReturnNineLayout.footerLeft base v) (false::suffix))
      (port0 (observedFirst v.i)) (tapeAt base (clearI v) 8 suffix) (2*v.i.length+6) := by
  have back:=ReturnNineBack.bounded8 v (ReturnNineLayout.left8 base v).tail v.i suffix
  have read:=read_bounded (ReturnNineLayout.left8 base v) v.i ([false,false]++suffix) nonempty
  have actual:=back.seq read
  have exit : PSTRTMSeq005.rightLabel (a:=4) (readPort (observedFirst v.i))=port0 (observedFirst v.i) := by
    cases observedFirst v.i <;> decide
  rw [exit] at actual
  simpa [stage0,tapeAt,clearI,ReturnNineBack.finish8,ReturnNineBack.after8,ReturnNineBack.fee8,
    ReturnNineLayout.footerLeft,ReturnNineLayout.leftAt,ReturnNineLayout.rightAt,
    ReturnNineLayout.left8,ReturnNineLayout.left7,ReturnNineLayout.left6,ReturnNineLayout.left5,
    ReturnNineLayout.left4,ReturnNineLayout.left3,ReturnNineLayout.left2,ReturnNineLayout.left1,
    ReturnNineLayout.left0,ReturnNineLayout.right8,List.append_assoc]
    using actual.mono (by dsimp only [ReturnNineBack.fee8];omega)

def toG : Machine 11 := PSTRTMSeq005.seqMachine (ReturnCompactRewind.code 1) (ReturnCompactRewind.code 3)
def clearGCode : Machine 13 := PSTRTMSeq005.seqMachine toG (setMarkerMachine false)
def toF : Machine 18 := PSTRTMSeq005.seqMachine clearGCode (ReturnCompactRewind.code 1)
def toE : Machine 26 := PSTRTMSeq005.seqMachine toF (ReturnCompactRewind.code 4)
def stage1 : Machine 29 := PSTRTMSeq005.seqMachine toE readClearMachine
def port1 (bit : Bool) : Fin 30 := if bit then 29 else 28

theorem stage1_bounded (base : List Bool) (v : Data) (suffix : List Bool)
    (gNonempty : v.g≠[]) (eNonempty : v.e≠[]) :
    BoundedRun stage1 (tapeAt base v 8 suffix) (port1 (observedFirst v.e))
      (tapeAt base (clearGE v) 4 suffix) (2*(v.h.length+v.g.length+v.f.length+v.e.length)+25) := by
  have first:=previous8 base v suffix
  have second:=previous7 base v suffix
  have clear : BoundedRun (setMarkerMachine false) (tapeAt base v 6 suffix) 1 (tapeAt base (clearG v) 6 suffix) 2 := by
    have actual:=clear_bounded (ReturnNineLayout.left6 base v) v.g
      ([false,false,false]++(ReturnNineLayout.right7 v++suffix)) gNonempty
    simpa [tapeAt,clearG,ReturnNineLayout.leftAt,ReturnNineLayout.rightAt,
      ReturnNineLayout.left6,ReturnNineLayout.left5,ReturnNineLayout.left4,ReturnNineLayout.left3,
      ReturnNineLayout.left2,ReturnNineLayout.left1,ReturnNineLayout.left0,
      ReturnNineLayout.right6,ReturnNineLayout.right7,ReturnNineLayout.right8,List.append_assoc] using actual
  have fourth:=previous6 base (clearG v) suffix
  have fifth:=previous5 base (clearG v) suffix
  have read : BoundedRun readClearMachine (tapeAt base (clearG v) 4 suffix) (readPort (observedFirst v.e))
      (tapeAt base (clearGE v) 4 suffix) 2 := by
    have actual:=read_bounded (ReturnNineLayout.left4 base (clearG v)) v.e
      ([false,false,false,false]++(ReturnNineLayout.right5 (clearG v)++suffix)) eNonempty
    simpa [tapeAt,clearGE,clearE,clearG,ReturnNineLayout.leftAt,ReturnNineLayout.rightAt,
      ReturnNineLayout.left4,ReturnNineLayout.left3,ReturnNineLayout.left2,ReturnNineLayout.left1,
      ReturnNineLayout.left0,ReturnNineLayout.right4,ReturnNineLayout.right5,
      ReturnNineLayout.right6,ReturnNineLayout.right7,ReturnNineLayout.right8,List.append_assoc] using actual
  have actual:=((((first.seq second).seq clear).seq fourth).seq fifth).seq read
  have exit : PSTRTMSeq005.rightLabel (a:=26) (readPort (observedFirst v.e))=port1 (observedFirst v.e) := by
    cases observedFirst v.e <;> decide
  rw [exit] at actual
  exact actual.mono (by dsimp only [clearG];omega)

def beforeB : Machine 11 := PSTRTMSeq005.seqMachine (ReturnCompactRewind.code 1) (ReturnCompactRewind.code 3)
def toB : Machine 28 := PSTRTMSeq005.seqMachine beforeB (ReturnCompactRewind.code 13)
def stage2 : Machine 31 := PSTRTMSeq005.seqMachine toB readClearMachine
def port2 (bit : Bool) : Fin 32 := if bit then 31 else 30

theorem stage2_bounded (base : List Bool) (v : Data) (suffix : List Bool) (nonempty : v.b≠[]) :
    BoundedRun stage2 (tapeAt base v 4 suffix) (port2 (observedFirst v.b))
      (tapeAt base (clearB v) 1 suffix) (2*(v.d.length+v.c.length+v.b.length)+28) := by
  have first:=previous4 base v suffix
  have second:=previous3 base v suffix
  have third:=previous2 base v suffix
  have read : BoundedRun readClearMachine (tapeAt base v 1 suffix) (readPort (observedFirst v.b))
      (tapeAt base (clearB v) 1 suffix) 2 := by
    have actual:=read_bounded (ReturnNineLayout.left1 base v) v.b
      (ReturnNineLayout.gap13++(ReturnNineLayout.right2 v++suffix)) nonempty
    simpa [tapeAt,clearB,ReturnNineLayout.leftAt,ReturnNineLayout.rightAt,
      ReturnNineLayout.left1,ReturnNineLayout.left0,ReturnNineLayout.right1,
      ReturnNineLayout.right2,ReturnNineLayout.right3,ReturnNineLayout.right4,
      ReturnNineLayout.right5,ReturnNineLayout.right6,ReturnNineLayout.right7,
      ReturnNineLayout.right8,List.append_assoc] using actual
  have actual:=((first.seq second).seq third).seq read
  have exit : PSTRTMSeq005.rightLabel (a:=28) (readPort (observedFirst v.b))=port2 (observedFirst v.b) := by
    cases observedFirst v.b <;> decide
  rw [exit] at actual
  exact actual.mono (by omega)

end RootB23.Threshold.ReturnNineBook

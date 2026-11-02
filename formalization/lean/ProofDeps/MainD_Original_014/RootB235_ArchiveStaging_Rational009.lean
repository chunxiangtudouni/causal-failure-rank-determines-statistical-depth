module
public import RootB235_ArchiveStaging_Control006
public import RootB235_ArchiveStaging_Navigation008

/-! Actual rational-record preparation and serialization on the fixed
whole control graph: denominator, numerator, sign, and kind. Temporary
TRUE flags are real cell writes; each is removed before digit export. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
open Turing RationalControllerComputation

namespace Rational
open Control

def numberWord (digits : List Bool) : List Bool := List.replicate digits.length true++false::digits

def tape (left num laterDen higher output : List Bool) (boundary sign firstDen : Bool) (gap : Nat) : Tape Bool :=
  Macro.source (Restore.reversePairs laterDen.reverse++firstDen::true::
    (Restore.reversePairs num.reverse++sign::false::boundary::true::left)) higher output true true gap

noncomputable def denEntry (left older laterDen higher output : List Bool)
    (boundary sign near firstDen : Bool) (gap : Nat) :
    Segment Control.code (Control.state 0 (tape left (near::older).reverse laterDen higher output boundary sign firstDen gap))
      (Control.state 40 (NumberField.input
        (Restore.reversePairs older++sign::false::boundary::true::left) higher output near gap (firstDen::laterDen)).Tape)
      (12*laterDen.length+60) := by
  let west := Restore.reversePairs older++sign::false::boundary::true::left
  let leftNum := near::false::west
  let suffix := true::true::Macro.suffix higher output gap
  let a := Control.state 0 (tape left (near::older).reverse laterDen higher output boundary sign firstDen gap)
  let b := embed Control.Label.control (Navigation.leftStart (23 : Fin 98) leftNum firstDen laterDen.reverse suffix)
  have front : Segment Control.code a b 9 := by
    apply follow_actual Control.code 4
    cases shape : laterDen.reverse with
    | nil =>
      simp [a,b,tape,follow,Control.state,Control.code,call,Macro.code,Control.program,
        Navigation.leftStart,Navigation.state,leftNum,west,suffix,Macro.source,
        Restore.reversePairs,shape,TM0.step,Tape.mk₂,embed]
    | cons bit rest =>
      simp [a,b,tape,follow,Control.state,Control.code,call,Macro.code,Control.program,
        Navigation.leftStart,Navigation.state,leftNum,west,suffix,Macro.source,
        Restore.reversePairs,shape,TM0.step,Tape.mk₂,embed]
  have scanned := Control.liftControl (Navigation.left Control.program 23 24 25 26 rfl rfl rfl
    leftNum laterDen.reverse suffix firstDen)
  let c := Control.state 26 (Tape.mk₂ leftNum (true::firstDen::(MarkSeek.pairs laterDen++suffix)))
  have scanned' : Segment Control.code b c (6*laterDen.length+2) := by
    simpa only [b,c,Navigation.state,Control.state,embed,List.reverse_reverse,List.length_reverse] using scanned
  let d := Control.state 32 (Tape.mk₂ (near::true::west)
    (MarkSeek.pairs (firstDen::laterDen)++true::true::Macro.suffix higher output gap))
  have mark : Segment Control.code c d 13 := by
    apply follow_actual Control.code 6
    simp [c,d,follow,Control.state,Control.code,call,Macro.code,Control.program,
      leftNum,suffix,MarkSeek.pairs,TM0.step,Tape.mk₂]
  have right := Control.liftControl (Navigation.right Control.program 32 33 34 35 rfl rfl rfl
    (near::true::west) (firstDen::laterDen) (true::Macro.suffix higher output gap))
  let e := Control.state 35 (Tape.mk₂
    ((MarkSeek.pairs (firstDen::laterDen)).reverse++near::true::west)
    (true::true::Macro.suffix higher output gap))
  have right' : Segment Control.code d e (6*(firstDen::laterDen).length+2) := right
  let f := Control.state 40 (NumberField.input west higher output near gap (firstDen::laterDen)).Tape
  have close : Segment Control.code e f 11 := by
    dsimp only [e]
    rw [Restore.pairs_reverse]
    apply follow_actual Control.code 5
    cases shape : (firstDen::laterDen).reverse with
    | nil => have size := congrArg List.length shape; simp at size
    | cons bit rest =>
      simp [f,follow,Control.state,Control.code,call,Macro.code,Control.program,
        NumberField.input,NumberField.loopCfg,NumberField.cfg,Macro.cfg,Macro.source,Macro.suffix,
        Restore.reversePairs,shape,MarkSeek.pairs,TM0.step,Tape.mk₂]
  exact ((((front.trans scanned').trans mark).trans right').trans close).weaken
    (by simp only [List.length_cons];omega)

noncomputable def numEntry (left older laterDen higher output : List Bool)
    (boundary sign near firstDen : Bool) (gap : Nat) :
    Segment Control.code
      (Control.state 41 (NumberField.finish
        (Restore.reversePairs older++sign::false::boundary::true::left) higher output near gap (firstDen::laterDen)).Tape)
      (Control.state 57 (NumberField.input (boundary::true::left)
        (List.replicate (firstDen::laterDen).length false++higher)
        (numberWord (firstDen::laterDen)++output) sign gap (near::older).reverse).Tape)
      (12*older.length+60) := by
  let den := firstDen::laterDen
  let east := List.replicate (den.length+1) false++higher
  let out := numberWord den++output
  let west := Restore.reversePairs older++sign::false::boundary::true::left
  let suffix := true::near::Macro.suffix east out gap
  let a := Control.state 41 (NumberField.finish west higher output near gap den).Tape
  let b := embed Control.Label.control (Navigation.leftStart (44 : Fin 98) left boundary (older++[sign]) suffix)
  have front : Segment Control.code a b 7 := by
    apply follow_actual Control.code 3
    cases older with
    | nil =>
      simp [a,b,follow,Control.state,Control.code,call,Macro.code,Control.program,NumberField.finish,
        NumberField.cfg,Macro.cfg,Macro.source,Macro.suffix,Navigation.leftStart,Navigation.state,
        west,east,out,numberWord,suffix,Restore.reversePairs,TM0.step,Tape.mk₂,embed,List.append_assoc]
    | cons bit rest =>
      simp [a,b,follow,Control.state,Control.code,call,Macro.code,Control.program,NumberField.finish,
        NumberField.cfg,Macro.cfg,Macro.source,Macro.suffix,Navigation.leftStart,Navigation.state,
        west,east,out,numberWord,suffix,Restore.reversePairs,TM0.step,Tape.mk₂,embed,List.flatMap_append,List.append_assoc]
  have scanned := Control.liftControl (Navigation.left Control.program 44 45 46 47 rfl rfl rfl
    left (older++[sign]) suffix boundary)
  let c := Control.state 47 (Tape.mk₂ left
    (true::boundary::(MarkSeek.pairs (older++[sign]).reverse++suffix)))
  have scanned' : Segment Control.code b c (6*(older++[sign]).length+2) := scanned
  let d := Control.state 52 (Tape.mk₂ (sign::true::boundary::true::left)
    (MarkSeek.pairs older.reverse++true::near::Macro.suffix east out gap))
  have mark : Segment Control.code c d 11 := by
    apply follow_actual Control.code 5
    simp [c,d,follow,Control.state,Control.code,call,Macro.code,Control.program,suffix,
      MarkSeek.pairs,List.reverse_append,TM0.step,Tape.mk₂]
  have right := Control.liftControl (Navigation.right Control.program 52 53 54 55 rfl rfl rfl
    (sign::true::boundary::true::left) older.reverse (near::Macro.suffix east out gap))
  let e := Control.state 55 (Tape.mk₂
    ((MarkSeek.pairs older.reverse).reverse++sign::true::boundary::true::left)
    (true::near::Macro.suffix east out gap))
  have right' : Segment Control.code d e (6*older.length+2) := by
    simpa only [d,e,Navigation.state,Control.state,embed,List.length_reverse] using right
  let f := Control.state 57 (NumberField.input (boundary::true::left)
    (List.replicate den.length false++higher) out sign gap (near::older).reverse).Tape
  have close : Segment Control.code e f 5 := by
    dsimp only [e]
    rw [Restore.pairs_reverse,List.reverse_reverse]
    apply follow_actual Control.code 2
    simp [f,follow,Control.state,Control.code,call,Macro.code,Control.program,
      NumberField.input,NumberField.loopCfg,NumberField.cfg,Macro.cfg,Macro.source,Macro.suffix,
      east,Restore.reversePairs,List.replicate_succ,MarkSeek.pairs,TM0.step,Tape.mk₂]
  exact ((((front.trans scanned').trans mark).trans right').trans close).weaken
    (by simp only [List.length_append,List.length_singleton];omega)

noncomputable def actual (left older laterDen higher output : List Bool)
    (boundary sign near firstDen : Bool) (gap : Nat) :
    let num := (near::older).reverse
    let den := firstDen::laterDen
    Segment Control.code (Control.state 0 (tape left num laterDen higher output boundary sign firstDen gap))
      (Control.cfg 0 left (sign::(List.replicate (num.length+den.length+1) false++higher))
        (true::sign::(numberWord num++numberWord den++output)) true boundary gap)
      (100000*(num.length+den.length+higher.length+output.length+gap+1)^2) := by
  dsimp only
  let num := (near::older).reverse
  let den := firstDen::laterDen
  let west := Restore.reversePairs older++sign::false::boundary::true::left
  let outDen := numberWord den++output
  let middleHigher := List.replicate den.length false++higher
  let outNum := numberWord num++outDen
  let clean := List.replicate (num.length+den.length+1) false++higher
  have a := denEntry left older laterDen higher output boundary sign near firstDen gap
  have b := Control.fieldRun 40 1 rfl rfl west higher output near gap den
  have c := numEntry left older laterDen higher output boundary sign near firstDen gap
  have d := Control.fieldRun 57 2 rfl rfl (boundary::true::left) middleHigher outDen sign gap num
  have doneTape : (NumberField.finish (boundary::true::left) middleHigher outDen sign gap num).Tape=
      Macro.source (boundary::true::left) clean outNum true sign gap := by
    have highEq : List.replicate (num.length+1) false++(List.replicate den.length false++higher)=clean := by
      dsimp only [clean]
      rw [←List.append_assoc,←List.replicate_add]
      congr 2
      omega
    change Macro.source (boundary::true::left)
      (List.replicate (num.length+1) false++(List.replicate den.length false++higher))
      (List.replicate num.length true++false::(num++outDen)) true sign gap=_
    rw [highEq]
    simp only [outNum,numberWord,List.append_assoc,List.cons_append]
  rw [doneTape] at d
  let e := Control.cfg 58 (boundary::true::left) clean outNum true sign gap
  let f := Control.cfg 66 (boundary::true::left) clean outNum false sign gap
  have clear : Segment Control.code e f 7 := by
    apply follow_actual Control.code 3
    simp [e,f,Control.cfg,Control.state,follow,Control.code,call,Macro.code,Control.program,
      Macro.source,TM0.step,Tape.mk₂]
  have signPath := Control.liftControl (Macro.export_actual Control.program 66 67 .preserve rfl
    (boundary::true::left) clean outNum false sign gap)
  have tagPath := Control.liftControl (Macro.export_actual Control.program 67 68 .emitTrue rfl
    (boundary::true::left) clean (sign::outNum) false sign gap)
  let g := Control.cfg 68 (boundary::true::left) clean (true::sign::outNum) false sign gap
  let h := Control.cfg 0 left (sign::clean) (true::sign::outNum) true boundary gap
  have returnPath : Segment Control.code g h 5 := by
    apply follow_actual Control.code 2
    simp [g,h,Control.cfg,Control.state,follow,Control.code,call,Macro.code,Control.program,
      Macro.source,Macro.suffix,MarkSeek.pairs,TM0.step,Tape.mk₂]
  have result := ((((((((a.trans b).trans c).trans d).trans clear).trans signPath).trans tagPath).trans returnPath))
  have bounded := result.weaken (t:=100000*(num.length+den.length+higher.length+output.length+gap+1)^2) (by
    simp only [num,den,middleHigher,outDen,outNum,clean,numberWord,List.length_append,
      List.length_replicate,List.length_cons,List.length_reverse]
    nlinarith [Nat.zero_le (older.length^2),Nat.zero_le (laterDen.length^2),
      Nat.zero_le (higher.length^2),Nat.zero_le (output.length^2),Nat.zero_le (gap^2)])
  simpa only [h,clean,outNum,outDen,num,den,List.append_assoc] using bounded

end Rational
end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging

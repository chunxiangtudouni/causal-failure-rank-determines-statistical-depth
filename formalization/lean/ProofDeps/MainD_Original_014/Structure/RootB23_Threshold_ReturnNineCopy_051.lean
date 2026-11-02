module
public import Structure.RootB23_Threshold_ReturnNineStart_050

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineCopy
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow
open ReturnNineLayout (Data)

def fields (v : Data) (memory : Fin 8) : List (List Bool) :=
  [v.c,ReturnNineStep.output v 0 memory,ReturnNineStep.output v 1 memory,
    ReturnNineStep.output v 2 memory,ReturnNineStep.output v 3 memory,
    ReturnNineStep.output v 4 memory,ReturnNineStep.output v 5 memory,
    ReturnNineStep.output v 6 memory,ReturnNineStep.output v 7 memory]

def home (base : List Bool) (v : Data) : List Bool :=
  ReturnNineDest.home (ReturnNineLayout.footerLeft base (ReturnNineOut.mask v))

def stepCode (slot : Fin 8) (memory : Fin 8) : Machine 1271 :=
  PSTRTMSeq005.seqMachine (PayloadSteps.nextMachine (ReturnNineRouted.route slot)) (ReturnNineStep.copyCode slot memory)

def stepPort (slot : Fin 8) : Fin 1272 := PSTRTMSeq005.rightLabel (a:=106) (ReturnNineStep.copyPort slot)

def stepFee (v : Data) (slot : Fin 8) (previous : List (List Bool)) (last : List Bool) : ℕ :=
  (2*last.length+2*(ReturnNineStep.source v slot).length+ReturnNineRouted.cost v (previous++[last])+6)+
    ReturnNineStep.copyFee v slot (previous++[last])

/-- One full next-anchor/return/copy/restore step, including the actual
destination footer boundary required by the frozen marshaller. -/
theorem step_bounded (base : List Bool) (v : Data) (slot : Fin 8) (memory : Fin 8)
    (previous : List (List Bool)) (last : List Bool) (lengthEq : (previous++[last]).length=slot.val+1) :
    BoundedRun (stepCode slot memory)
      (Tape.mk₂ (ReturnNineStep.cursor (home base v) previous) (PA17TMRatArithmeticCopy006.workspace last))
      (stepPort slot)
      (Tape.mk₂ (ReturnNineStep.cursor (home base v) (previous++[last]))
        (PA17TMRatArithmeticCopy006.workspace (ReturnNineStep.output v slot memory)))
      (stepFee v slot previous last) := by
  let currentLeft:=ReturnNineLayout.leftAt base (ReturnNineOut.mask v) (ReturnNineRouted.index slot)
  let source:=ReturnNineStep.source v slot
  let previousAll:=previous++[last]
  have leftEq:=ReturnNineStart.left_false base (ReturnNineOut.mask v) (ReturnNineRouted.index slot)
  have boundary:=ReturnNineStep.boundary base v slot previous last
  have boundaryTail : ReturnNineRouted.finish v slot previousAll (false::currentLeft.tail) source=
      PA17TMRatArithmeticAllocatePass023.pushField (ReturnNineStep.cursor (home base v) previous) last := by
    rw [leftEq]
    exact boundary
  have correct:=ReturnNineRouted.correct v slot previousAll lengthEq
  have next:=PayloadSteps.next_bounded _ _ _ _ correct currentLeft.tail source
    (ReturnNineStep.cursor (home base v) previous) last boundaryTail
  have copied:=ReturnNineStep.copy_bounded v slot memory previousAll lengthEq currentLeft.tail
  rw [boundaryTail] at copied
  have actual:=next.seq copied
  have cursorEq : RoutedCopy.destinationLeft 0
      (PA17TMRatArithmeticAllocatePass023.pushField (ReturnNineStep.cursor (home base v) previous) last)=
      ReturnNineStep.cursor (home base v) (previous++[last]) := by
    simp [RoutedCopy.destinationLeft,ReturnNineStep.cursor,List.foldl_append,PayloadNav.nextLeft]
  rw [cursorEq] at actual
  exact actual

def slot (n : ℕ) : Fin 8 := ⟨n%8,Nat.mod_lt _ (by decide)⟩

theorem slot_val (n : ℕ) (small : n<8) : (slot n).val=n := Nat.mod_eq_of_lt small

theorem fields_take (v : Data) (memory : Fin 8) (slot : Fin 8) :
    (fields v memory).take slot.val++[(fields v memory).getD slot.val []]=(fields v memory).take (slot.val+1) := by
  fin_cases slot <;> rfl

theorem fields_next (v : Data) (memory : Fin 8) (slot : Fin 8) :
    (fields v memory).getD (slot.val+1) []=ReturnNineStep.output v slot memory := by
  fin_cases slot <;> rfl

theorem fields_take_length (v : Data) (memory : Fin 8) (slot : Fin 8) :
    ((fields v memory).take slot.val).length=slot.val := by fin_cases slot <;> rfl

def cap : ℕ→ℕ | 0=>1360 | n+1=>cap n+1271+1

def code (memory : Fin 8) : (n : ℕ)→Machine (cap n)
  | 0=>ReturnNineStart.code
  | n+1=>PSTRTMSeq005.seqMachine (code memory n) (stepCode (slot n) memory)

def port : (n : ℕ)→Fin (cap n+1)
  | 0=>1360
  | n+1=>PSTRTMSeq005.rightLabel (a:=cap n) (stepPort (slot n))

def fee (v : Data) (memory : Fin 8) : ℕ→ℕ
  | 0=>ReturnNineStart.fee v
  | n+1=>fee v memory n+stepFee v (slot n) ((fields v memory).take n) ((fields v memory).getD n [])

/-- Fixed nine-copy program; all seven prefix zeros and every0010 marker
are written by its real constituent traces. No field list enters code. -/
theorem bounded_prefix (base : List Bool) (v : Data) (memory : Fin 8) (n : ℕ) (small : n≤8) :
    BoundedRun (code memory n)
      (ReturnNineBook.tapeAt base (ReturnNineOut.mask v) 1 (workSuffix 0 [])) (port n)
      (Tape.mk₂ (ReturnNineStep.cursor (home base v) ((fields v memory).take n))
        (PA17TMRatArithmeticCopy006.workspace ((fields v memory).getD n []))) (fee v memory n) := by
  induction n with
  | zero=>exact ReturnNineStart.bounded base v
  | succ n ih=>
    have bound : n<8 := by omega
    have slotEq:=slot_val n bound
    have lengthEq : (((fields v memory).take n)++[(fields v memory).getD n []]).length=(slot n).val+1 := by
      have previous:=fields_take_length v memory (slot n)
      rw [slotEq] at previous
      simp only [List.length_append,List.length_cons,List.length_nil,previous,slotEq]
    have first:=ih (by omega)
    have next:=step_bounded base v (slot n) memory ((fields v memory).take n) ((fields v memory).getD n []) lengthEq
    have actual:=first.seq next
    have takeEq:=fields_take v memory (slot n)
    have valueEq:=fields_next v memory (slot n)
    rw [slotEq] at takeEq valueEq
    rw [takeEq,←valueEq] at actual
    exact actual

def machine (memory : Fin 8) : Machine 11536 := code memory 8

theorem final_port : port 8=(11536 : Fin 11537) := by apply Fin.ext;rfl

theorem bounded (base : List Bool) (v : Data) (memory : Fin 8) :
    BoundedRun (machine memory)
      (ReturnNineBook.tapeAt base (ReturnNineOut.mask v) 1 (workSuffix 0 [])) 11536
      (Tape.mk₂ (ReturnNineStep.cursor (home base v) ((fields v memory).take 8))
        (PA17TMRatArithmeticCopy006.workspace (ReturnNineStep.output v 7 memory))) (fee v memory 8) := by
  have actual:=bounded_prefix base v memory 8 (by decide)
  rw [final_port] at actual
  exact actual

end RootB23.Threshold.ReturnNineCopy

module
public import Structure.RootB23_Threshold_ReturnNineRouted_048

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineStep
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow
open ReturnNineLayout (Data)

def source (v : Data) (slot : Fin 8) : List Bool := ReturnNineLayout.field (ReturnNineOut.mask v) (ReturnNineRouted.index slot)

def output (v : Data) (slot : Fin 8) (memory : Fin 8) : List Bool := match slot.val with
  | 0=>v.d
  | 1=>memory.val.testBit 1::v.e.tail
  | 2=>v.a
  | 3=>memory.val.testBit 0::v.b.tail
  | 4=>v.f
  | 5=>true::v.g.tail
  | 6=>v.h
  | _=>memory.val.testBit 2::v.i.tail

/-- These eight choices are fixed control rows. In the whole producer
memory is dispatched from ReturnNineObserved's actual read ports. -/
def copyCode (slot : Fin 8) (memory : Fin 8) : Machine 1164 := match slot.val with
  | 1=>PayloadSteps.copyMachine (ReturnNineRouted.route slot) 1 memory.val
  | 3=>PayloadSteps.copyMachine (ReturnNineRouted.route slot) 0 memory.val
  | 5=>PayloadSteps.copyMachine (ReturnNineRouted.route slot) 0 1
  | 7=>PayloadSteps.copyMachine (ReturnNineRouted.route slot) 2 memory.val
  | _=>padMachine (by decide : 1162≤1164) (RoutedCopy.copyMachine (ReturnNineRouted.route slot))

def copyPort (slot : Fin 8) : Fin 1165 := match slot.val with | 1|3|5|7=>1164 | _=>1162

def copyFee (v : Data) (slot : Fin 8) (previous : List (List Bool)) : ℕ :=
  4*(source v slot).length^2+(2*ReturnNineRouted.cost v previous+41)*(source v slot).length+
    3*ReturnNineRouted.cost v previous+31

/-- Genuine copying and paid restoration of the observed first bit.
Source cells, earlier destination fields and markers remain in WEST. -/
theorem copy_bounded (v : Data) (slot : Fin 8) (memory : Fin 8) (previous : List (List Bool))
    (lengthEq : previous.length=slot.val+1) (archive : List Bool) :
    BoundedRun (copyCode slot memory)
      (Tape.mk₂ (false::archive) (RoutedCopy.fieldWord (ReturnNineRouted.context v slot previous)
        (source v slot) (PA17TMRatArithmeticFarLoad031.workSuffix 0 []))) (copyPort slot)
      (Tape.mk₂ (RoutedCopy.destinationLeft 0 (ReturnNineRouted.finish v slot previous (false::archive) (source v slot)))
        (PA17TMRatArithmeticCopy006.workspace (output v slot memory))) (copyFee v slot previous) := by
  have correct:=ReturnNineRouted.correct v slot previous lengthEq
  fin_cases slot
  · have actual:=bounded_pad (by decide : 1162≤1164)
      (RoutedCopy.copy_bounded _ _ _ _ correct archive (source v 0) 0)
    simpa [copyCode,copyPort,copyFee,output,source,ReturnNineRouted.index,
      ReturnNineLayout.field,ReturnNineOut.mask,padLabel,Nat.mul_zero,Nat.add_zero] using actual.mono (b:=copyFee v (0 : Fin 8) previous) (by dsimp only [copyFee];simp only [Nat.mul_zero,Nat.add_zero];omega)
  · have actual:=PayloadSteps.copy_bounded _ _ _ _ correct 1 memory.val archive v.e.tail
    simpa [copyCode,copyPort,copyFee,source,output,ReturnNineRouted.index,
      ReturnNineLayout.field,ReturnNineOut.mask,PayloadSteps.copyFee] using actual
  · have actual:=bounded_pad (by decide : 1162≤1164)
      (RoutedCopy.copy_bounded _ _ _ _ correct archive (source v 2) 0)
    simpa [copyCode,copyPort,copyFee,output,source,ReturnNineRouted.index,
      ReturnNineLayout.field,ReturnNineOut.mask,padLabel,Nat.mul_zero,Nat.add_zero] using actual.mono (b:=copyFee v (2 : Fin 8) previous) (by dsimp only [copyFee];simp only [Nat.mul_zero,Nat.add_zero];omega)
  · have actual:=PayloadSteps.copy_bounded _ _ _ _ correct 0 memory.val archive v.b.tail
    simpa [copyCode,copyPort,copyFee,source,output,ReturnNineRouted.index,
      ReturnNineLayout.field,ReturnNineOut.mask,PayloadSteps.copyFee] using actual
  · have actual:=bounded_pad (by decide : 1162≤1164)
      (RoutedCopy.copy_bounded _ _ _ _ correct archive (source v 4) 0)
    simpa [copyCode,copyPort,copyFee,output,source,ReturnNineRouted.index,
      ReturnNineLayout.field,ReturnNineOut.mask,padLabel,Nat.mul_zero,Nat.add_zero] using actual.mono (b:=copyFee v (4 : Fin 8) previous) (by dsimp only [copyFee];simp only [Nat.mul_zero,Nat.add_zero];omega)
  · have actual:=PayloadSteps.copy_bounded _ _ _ _ correct 0 1 archive v.g.tail
    simpa [copyCode,copyPort,copyFee,source,output,ReturnNineRouted.index,
      ReturnNineLayout.field,ReturnNineOut.mask,PayloadSteps.copyFee] using actual
  · have actual:=bounded_pad (by decide : 1162≤1164)
      (RoutedCopy.copy_bounded _ _ _ _ correct archive (source v 6) 0)
    simpa [copyCode,copyPort,copyFee,output,source,ReturnNineRouted.index,
      ReturnNineLayout.field,ReturnNineOut.mask,padLabel,Nat.mul_zero,Nat.add_zero] using actual.mono (b:=copyFee v (6 : Fin 8) previous) (by dsimp only [copyFee];simp only [Nat.mul_zero,Nat.add_zero];omega)
  · have actual:=PayloadSteps.copy_bounded _ _ _ _ correct 2 memory.val archive v.i.tail
    simpa [copyCode,copyPort,copyFee,source,output,ReturnNineRouted.index,
      ReturnNineLayout.field,ReturnNineOut.mask,PayloadSteps.copyFee] using actual

theorem source_length (v : Data) (slot : Fin 8) : (source v slot).length≤ReturnNineRoute.width v := by
  fin_cases slot <;> simp [source,ReturnNineLayout.field,ReturnNineRouted.index,ReturnNineRoute.width] <;> omega

private theorem copy_fee_bound (n w p : ℕ) (small : n≤w) :
    4*n^2+(2*(2*w+128+2*p+128)+41)*n+3*(2*w+128+2*p+128)+31≤4096*(w+p+1)^2 := by
  have bound : n≤w+p := by omega
  have square:=Nat.pow_le_pow_left bound 2
  have product:=Nat.mul_le_mul_left (w+p) bound
  nlinarith only [square,product,bound,Nat.zero_le n,Nat.zero_le w,Nat.zero_le p]

theorem copy_fee_le (v : Data) (slot : Fin 8) (previous : List (List Bool)) :
    copyFee v slot previous≤4096*(ReturnNineRoute.width v+ReturnNineDest.width previous+1)^2 := by
  exact copy_fee_bound _ _ _ (source_length v slot)

/-- Actual cursor on a destination DATA cell after all previous fields. -/
def cursor (left : List Bool) (previous : List (List Bool)) : List Bool := previous.foldl PayloadNav.nextLeft left

theorem finish_cons (left a : List Bool) (later : List (List Bool)) (nonempty : later≠[]) :
    ReturnNineDest.finish left (a::later)=ReturnNineDest.finish (PayloadNav.nextLeft left a) later := by
  cases later with
  | nil=>exact False.elim (nonempty rfl)
  | cons b rest=>rfl

theorem finish_append (left : List Bool) (previous : List (List Bool)) (last : List Bool) :
    ReturnNineDest.finish left (previous++[last])=PA17TMRatArithmeticAllocatePass023.pushField (cursor left previous) last := by
  induction previous generalizing left with
  | nil=>rfl
  | cons a rest ih=>
    have nonempty : rest++[last]≠[] := List.append_ne_nil_of_right_ne_nil rest (by simp)
    rw [List.cons_append,finish_cons _ _ _ nonempty,ih]
    rfl

theorem source_finish (base : List Bool) (v : Data) (slot : Fin 8) :
    ReturnNineRoute.finish v (ReturnNineRouted.index slot)
      (ReturnNineLayout.leftAt base (ReturnNineOut.mask v) (ReturnNineRouted.index slot)) (source v slot)=
      ReturnNineLayout.footerLeft base (ReturnNineOut.mask v) :=
  ReturnNineBack.finish_at base (ReturnNineOut.mask v) (ReturnNineRouted.index slot)

/-- The old destination footer is physically the return point used by
nextMachine; every source and destination cell is retained. -/
theorem boundary (base : List Bool) (v : Data) (slot : Fin 8) (previous : List (List Bool)) (last : List Bool) :
    ReturnNineRouted.finish v slot (previous++[last])
      (ReturnNineLayout.leftAt base (ReturnNineOut.mask v) (ReturnNineRouted.index slot)) (source v slot)=
      PA17TMRatArithmeticAllocatePass023.pushField
        (cursor (ReturnNineDest.home (ReturnNineLayout.footerLeft base (ReturnNineOut.mask v))) previous) last := by
  unfold ReturnNineRouted.finish
  rw [source_finish,finish_append]

end RootB23.Threshold.ReturnNineStep

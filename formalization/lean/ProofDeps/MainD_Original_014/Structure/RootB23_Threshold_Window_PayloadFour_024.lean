module

public import Structure.RootB23_Threshold_Window_PayloadSteps_023

/-! Four real far copies with actual first-bit restoration in a fixed memory
row. All RouteCorrect and cursor-boundary inputs are discharged below. This
produces the exact four-block serializer input out of the actual source bank. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadFour
open Turing PSTRTMSeq005
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticAllocatePass023

def a (memory : Nat) (nx : List Bool) : List Bool := memory.testBit 4 :: nx
def b (memory : Nat) (dx : List Bool) : List Bool := memory.testBit 3 :: dx
def c (memory : Nat) (ny : List Bool) : List Bool := memory.testBit 1 :: ny
def d (memory : Nat) (dy : List Bool) : List Bool := memory.testBit 0 :: dy

def firstRoute : RootB23.Threshold.RoutedCopy.Route := GapRoute.route nxRoute
def secondRoute : RootB23.Threshold.RoutedCopy.Route := PayloadRoute.route dxRoute 0
def thirdRoute : RootB23.Threshold.RoutedCopy.Route := PayloadRoute.route nyRoute 1
def fourthRoute : RootB23.Threshold.RoutedCopy.Route := PayloadRoute.route dyRoute 2

def firstMachine (memory : Nat) : Machine 1303 :=
  seqMachine PayloadInit.machine (PayloadSteps.copyMachine firstRoute 4 memory)
def secondStartMachine (memory : Nat) : Machine 1410 :=
  seqMachine (firstMachine memory) (PayloadSteps.nextMachine secondRoute)
def secondMachine (memory : Nat) : Machine 2575 :=
  seqMachine (secondStartMachine memory) (PayloadSteps.copyMachine secondRoute 3 memory)
def thirdStartMachine (memory : Nat) : Machine 2682 :=
  seqMachine (secondMachine memory) (PayloadSteps.nextMachine thirdRoute)
def thirdMachine (memory : Nat) : Machine 3847 :=
  seqMachine (thirdStartMachine memory) (PayloadSteps.copyMachine thirdRoute 1 memory)
def fourthStartMachine (memory : Nat) : Machine 3954 :=
  seqMachine (thirdMachine memory) (PayloadSteps.nextMachine fourthRoute)
def fourthMachine (memory : Nat) : Machine 5119 :=
  seqMachine (fourthStartMachine memory) (PayloadSteps.copyMachine fourthRoute 0 memory)
def rewindMachine (memory : Nat) : Machine 5149 := seqMachine (fourthMachine memory) PayloadSteps.returnFirstMachine
def machine (memory : Nat) : Machine 5160 := seqMachine (rewindMachine memory) PayloadSteps.clearPrefixMachine

def retainedArchive (archive nx dx ny dy : List Bool) (n : Nat) : List Bool :=
  true :: false :: counterArchive (PhysicalReserve.preservedArchive archive nx dx ny dy) (List.replicate n false) 4

def firstCost (n gap : Nat) (dx ny dy : List Bool) : Nat := TotalWidth.numCost dx ny dy + 8 * n + gap + 40
def secondCost (n gap memory : Nat) (nx ny dy : List Bool) : Nat :=
  TotalWidth.denCost ny dy + 8 * n + gap + 2 * (a memory nx).length + 100
def thirdCost (n gap memory : Nat) (nx dx dy : List Bool) : Nat :=
  TotalWidth.riskNumCost dy + 8 * n + gap + 2 * ((a memory nx).length + (b memory dx).length) + 100
def fourthCost (n gap memory : Nat) (nx dx ny : List Bool) : Nat :=
  5 + 8 * n + gap + 2 * ((a memory nx).length + (b memory dx).length + (c memory ny).length) + 100

def fee (n gap memory : Nat) (nx dx ny dy : List Bool) : Nat :=
  (32 * n + 2 * gap + 2 * (false :: nx).length + TotalWidth.numCost dx ny dy + 104) +
    PayloadSteps.copyFee nx (firstCost n gap dx ny dy) +
    (2 * (a memory nx).length + 2 * (false :: dx).length + secondCost n gap memory nx ny dy + 6) +
    PayloadSteps.copyFee dx (secondCost n gap memory nx ny dy) +
    (2 * (b memory dx).length + 2 * (false :: ny).length + thirdCost n gap memory nx dx dy + 6) +
    PayloadSteps.copyFee ny (thirdCost n gap memory nx dx dy) +
    (2 * (c memory ny).length + 2 * (false :: dy).length + fourthCost n gap memory nx dx ny + 6) +
    PayloadSteps.copyFee dy (fourthCost n gap memory nx dx ny) +
    (2 * ((a memory nx).length + (b memory dx).length + (c memory ny).length) + 27) + 11

theorem four_bounded (memory : Nat) (archive nx dx ny dy : List Bool) (n gap : Nat) :
    BoundedRun (machine memory)
      (Tape.mk₂ (false :: PhysicalReserve.preservedArchive archive nx dx ny dy) (powerWord n 4 gap)) 5160
      (Tape.mk₂ (List.replicate (gap + 4) false ++ retainedArchive archive nx dx ny dy n)
        (PayloadSteps.word4 (a memory nx) (b memory dx) (c memory ny) (d memory dy) []))
      (fee n gap memory nx dx ny dy) := by
  let p := a memory nx
  let q := b memory dx
  let r := c memory ny
  let s := d memory dy
  let gapFinish := GapRoute.finish (nxFinish dx ny dy) n gap (false :: archive) (false :: nx)
  let payloadLeft := RootB23.Threshold.RoutedCopy.destinationLeft 0 gapFinish
  let payloadArchive := true :: false :: gapFinish
  have r0 := GapRoute.correct nxRoute (nxContext dx ny dy) (nxFinish dx ny dy)
    (TotalWidth.numCost dx ny dy) (nx_route_correct dx ny dy) n gap
  have r1 := PayloadRoute.correct dxRoute (dxContext ny dy) (dxFinish ny dy)
    (TotalWidth.denCost ny dy) (dx_route_correct ny dy) n gap 0 p [] []
  have r2 := PayloadRoute.correct nyRoute (nyContext dy) (nyFinish dy)
    (TotalWidth.riskNumCost dy) (ny_route_correct dy) n gap 1 p q []
  have r3 := PayloadRoute.correct dyRoute [] dyFinish 5 dy_route_correct n gap 2 p q r
  simp only [PayloadPorts.width, Fin.val_zero, ite_true] at r1
  simp [PayloadPorts.width] at r2 r3
  have boundary1 : PayloadRoute.finish (dxFinish ny dy) n gap 0 p [] []
      (false :: TotalWidth.dxArchive archive nx) (false :: dx) = pushField payloadLeft p := by
    simp [PayloadRoute.finish, PayloadPorts.finish, GapRoute.finish, payloadLeft, gapFinish,
      TotalWidth.dxArchive, nxFinish, dxFinish, pushField, yHeaderLeft,
      RootB23.Threshold.RoutedCopy.destinationLeft]
  have boundary2 : PayloadRoute.finish (nyFinish dy) n gap 1 p q []
      (false :: TotalWidth.nyArchive archive nx dx) (false :: ny) =
        pushField (PayloadNav.nextLeft payloadLeft p) q := by
    simp [PayloadRoute.finish, PayloadPorts.finish, GapRoute.finish, payloadLeft, gapFinish,
      TotalWidth.nyArchive, nxFinish, nyFinish, pushField, yHeaderLeft,
      PayloadNav.nextLeft, RootB23.Threshold.RoutedCopy.destinationLeft]
  have boundary3 : PayloadRoute.finish dyFinish n gap 2 p q r
      (false :: TotalWidth.dyArchive archive nx dx ny) (false :: dy) =
        pushField (PayloadNav.nextLeft (PayloadNav.nextLeft payloadLeft p) q) r := by
    simp [PayloadRoute.finish, PayloadPorts.finish, GapRoute.finish, payloadLeft, gapFinish,
      TotalWidth.dyArchive, TotalWidth.nyArchive, nxFinish, dyFinish,
      pushField, yHeaderLeft, PayloadNav.nextLeft, RootB23.Threshold.RoutedCopy.destinationLeft]
  have init := PayloadInit.init_bounded archive nx dx ny dy n gap
  have first := PayloadSteps.copy_bounded firstRoute (GapRoute.context (nxContext dx ny dy) n gap)
    (GapRoute.finish (nxFinish dx ny dy) n gap) (firstCost n gap dx ny dy) r0 4 memory archive nx
  have next1 := PayloadSteps.next_bounded secondRoute (PayloadRoute.context (dxContext ny dy) n gap 0 p [] [])
    (PayloadRoute.finish (dxFinish ny dy) n gap 0 p [] []) (secondCost n gap memory nx ny dy)
    r1 (TotalWidth.dxArchive archive nx) (false :: dx) payloadLeft p boundary1
  have second := PayloadSteps.copy_bounded secondRoute (PayloadRoute.context (dxContext ny dy) n gap 0 p [] [])
    (PayloadRoute.finish (dxFinish ny dy) n gap 0 p [] []) (secondCost n gap memory nx ny dy)
    r1 3 memory (TotalWidth.dxArchive archive nx) dx
  have next2 := PayloadSteps.next_bounded thirdRoute (PayloadRoute.context (nyContext dy) n gap 1 p q [])
    (PayloadRoute.finish (nyFinish dy) n gap 1 p q []) (thirdCost n gap memory nx dx dy)
    r2 (TotalWidth.nyArchive archive nx dx) (false :: ny) (PayloadNav.nextLeft payloadLeft p) q boundary2
  have third := PayloadSteps.copy_bounded thirdRoute (PayloadRoute.context (nyContext dy) n gap 1 p q [])
    (PayloadRoute.finish (nyFinish dy) n gap 1 p q []) (thirdCost n gap memory nx dx dy)
    r2 1 memory (TotalWidth.nyArchive archive nx dx) ny
  have next3 := PayloadSteps.next_bounded fourthRoute (PayloadRoute.context [] n gap 2 p q r)
    (PayloadRoute.finish dyFinish n gap 2 p q r) (fourthCost n gap memory nx dx ny)
    r3 (TotalWidth.dyArchive archive nx dx ny) (false :: dy)
    (PayloadNav.nextLeft (PayloadNav.nextLeft payloadLeft p) q) r boundary3
  have fourth := PayloadSteps.copy_bounded fourthRoute (PayloadRoute.context [] n gap 2 p q r)
    (PayloadRoute.finish dyFinish n gap 2 p q r) (fourthCost n gap memory nx dx ny)
    r3 0 memory (TotalWidth.dyArchive archive nx dx ny) dy
  rw [boundary1] at second
  rw [boundary2] at third
  rw [boundary3] at fourth
  have back := PayloadSteps.returnFirst_bounded payloadArchive p q r s []
  have clear : BoundedRun PayloadSteps.clearPrefixMachine
      (Tape.mk₂ (false :: true :: false :: gapFinish) (PayloadSteps.word4 p q r s [])) 10
      (Tape.mk₂ (false :: false :: false :: false ::
        (List.replicate gap false ++ retainedArchive archive nx dx ny dy n))
        (PayloadSteps.word4 p q r s [])) 11 := by
    simpa only [gapFinish, GapRoute.finish, retainedArchive,
      PhysicalReserve.preservedArchive, TotalWidth.bankLeft] using PayloadSteps.clearPrefix_bounded
        (List.replicate gap false ++ retainedArchive archive nx dx ny dy n) (PayloadSteps.word4 p q r s [])
  dsimp only [p, q, r, s, payloadLeft, payloadArchive, gapFinish] at first next1 second next2 third next3 fourth back
  simp only [fieldWord, RootB23.Threshold.RoutedCopy.fieldWord,
    RootB23.Threshold.RoutedCopy.destinationLeft, List.replicate_zero, List.nil_append, List.append_nil,
    PayloadNav.nextLeft] at init first next1 second next2 third next3 fourth back
  have actual := ((((((((init.seq first).seq next1).seq second).seq next2).seq third).seq next3).seq fourth).seq back).seq clear
  have exit : rightLabel (a := 5149) (10 : Fin 11) = (5160 : Fin 5161) := by decide
  rw [exit] at actual
  have prefixShape : false :: false :: false :: false ::
      (List.replicate gap false ++ retainedArchive archive nx dx ny dy n) =
        List.replicate (gap + 4) false ++ retainedArchive archive nx dx ny dy n := by
    rw [show gap + 4 = 4 + gap by omega, List.replicate_add, List.append_assoc]
    rfl
  rw [prefixShape] at actual
  simpa only [machine, rewindMachine, fourthMachine, fourthStartMachine, thirdMachine,
    thirdStartMachine, secondMachine, secondStartMachine, firstMachine, fee,
    p, q, r, s, Nat.add_assoc] using actual

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadFour

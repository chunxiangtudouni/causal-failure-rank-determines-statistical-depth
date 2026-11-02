module

public import Structure.RootB23_Threshold_Window_PayloadNav_018

/-! The exact three finite payload-navigation choices used by the remaining
three copies. Widths/fields occur only in these tape equations, never code. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadPorts
open Turing PSTRTMSeq005 PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticAllocatePass023

def core (slot : Fin 3) (a b c : List Bool) : List Bool :=
  if slot.val = 0 then PSTRTMIncrement009.blocks a ++ [false]
  else if slot.val = 1 then PA17TMRatArithmeticCopy006.workspace a ++ true :: false :: (PSTRTMIncrement009.blocks b ++ [false])
  else PA17TMRatArithmeticCopy006.workspace a ++ true :: false ::
    (PA17TMRatArithmeticCopy006.workspace b ++ true :: false :: (PSTRTMIncrement009.blocks c ++ [false]))

def finish (slot : Fin 3) (left a b c : List Bool) : List Bool :=
  if slot.val = 0 then pushField left a
  else if slot.val = 1 then pushField (PayloadNav.nextLeft left a) b
  else pushField (PayloadNav.nextLeft (PayloadNav.nextLeft left a) b) c

def width (slot : Fin 3) (a b c : List Bool) : Nat :=
  if slot.val = 0 then a.length else if slot.val = 1 then a.length + b.length else a.length + b.length + c.length

def outMachine (slot : Fin 3) : Machine 13 :=
  if slot.val = 0 then padMachine (by decide : 1 ≤ 13) outDyMachine
  else if slot.val = 1 then padMachine (by decide : 7 ≤ 13) PayloadNav.skip2Machine
  else PayloadNav.skip3Machine

def outPort (slot : Fin 3) : Fin 14 := if slot.val = 0 then 1 else if slot.val = 1 then 7 else 13

def backMachine (slot : Fin 3) : Machine 25 :=
  if slot.val = 0 then padMachine (by decide : 5 ≤ 25) PA17TMRatArithmeticParse002.fieldBackMachine
  else if slot.val = 1 then padMachine (by decide : 15 ≤ 25) PayloadNav.back2Machine
  else PayloadNav.back3Machine

def backPort (slot : Fin 3) : Fin 26 := if slot.val = 0 then 5 else if slot.val = 1 then 15 else 25

theorem out_bounded (slot : Fin 3) (left a b c suffix : List Bool) :
    BoundedRun (outMachine slot) (Tape.mk₂ left (core slot a b c ++ false :: suffix)) (outPort slot)
      (Tape.mk₂ (finish slot left a b c) (false :: suffix)) (2 * width slot a b c + 14) := by
  fin_cases slot
  · have actual := bounded_pad (by decide : 1 ≤ 13) (PayloadNav.scan_bounded left a suffix)
    simpa [outMachine, outPort, core, finish, width, padLabel,
      PA17TMRatArithmeticCopy006.workspace, List.append_assoc]
      using actual.mono (by omega : 2 * a.length + 2 ≤ 2 * a.length + 14)
  · have actual := bounded_pad (by decide : 7 ≤ 13) (PayloadNav.skip2_bounded left a b suffix)
    simpa [outMachine, outPort, core, finish, width, padLabel, PayloadNav.word2,
      PA17TMRatArithmeticCopy006.workspace, List.append_assoc]
      using actual.mono (by omega : 2 * (a.length + b.length) + 8 ≤ 2 * (a.length + b.length) + 14)
  · have actual := PayloadNav.skip3_bounded left a b c suffix
    simpa [outMachine, outPort, core, finish, width, PayloadNav.word3, PayloadNav.word2,
      PA17TMRatArithmeticCopy006.workspace, List.append_assoc] using actual

theorem back_bounded (slot : Fin 3) (archive a b c suffix : List Bool) :
    BoundedRun (backMachine slot)
      (Tape.mk₂ (finish slot (false :: archive) a b c) (false :: suffix)) (backPort slot)
      (Tape.mk₂ (false :: archive) (core slot a b c ++ false :: suffix))
      (2 * width slot a b c + 23) := by
  fin_cases slot
  · have actual := bounded_pad (by decide : 5 ≤ 25) (PayloadNav.rewind_bounded archive a suffix)
    simpa [backMachine, backPort, core, finish, width, padLabel,
      PA17TMRatArithmeticCopy006.workspace, List.append_assoc]
      using actual.mono (by omega : 2 * a.length + 5 ≤ 2 * a.length + 23)
  · have actual := bounded_pad (by decide : 15 ≤ 25) (PayloadNav.back2_bounded archive a b suffix)
    simpa [backMachine, backPort, core, finish, width, padLabel, PayloadNav.word2,
      PA17TMRatArithmeticCopy006.workspace, List.append_assoc]
      using actual.mono (by omega : 2 * (a.length + b.length) + 14 ≤ 2 * (a.length + b.length) + 23)
  · have actual := PayloadNav.back3_bounded archive a b c suffix
    simpa [backMachine, backPort, core, finish, width, PayloadNav.word3, PayloadNav.word2,
      PA17TMRatArithmeticCopy006.workspace, List.append_assoc] using actual

def fourMachine (direction : Dir) : Machine 4 := fun q _ =>
  if h : q.val < 4 then some (⟨q.val + 1, by omega⟩, .move direction) else none

theorem fourRight_bounded (left suffix : List Bool) :
    BoundedRun (fourMachine .right)
      (Tape.mk₂ left (true :: false :: true :: false :: suffix)) 4
      (Tape.mk₂ (false :: true :: false :: true :: left) suffix) 5 := by
  let state := fun (q : Fin 5) (west east : List Bool) => (⟨q, Tape.mk₂ west east⟩ : MachineState 4)
  refine ⟨[state 0 left (true::false::true::false::suffix),
    state 1 (true::left) (false::true::false::suffix),
    state 2 (false::true::left) (true::false::suffix),
    state 3 (true::false::true::left) (false::suffix),
    state 4 (false::true::false::true::left) suffix], ?_, by rfl⟩
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [state, List.isChain_cons_cons, TM0.step, fourMachine, Tape.mk₂]
  · simp [TM0.step, fourMachine]

theorem fourLeft_bounded (left suffix : List Bool) :
    BoundedRun (fourMachine .left)
      (Tape.mk₂ (false :: true :: false :: true :: left) suffix) 4
      (Tape.mk₂ left (true :: false :: true :: false :: suffix)) 5 := by
  let state := fun (q : Fin 5) (west east : List Bool) => (⟨q, Tape.mk₂ west east⟩ : MachineState 4)
  refine ⟨[state 0 (false::true::false::true::left) suffix,
    state 1 (true::false::true::left) (false::suffix),
    state 2 (false::true::left) (true::false::suffix),
    state 3 (true::left) (false::true::false::suffix),
    state 4 left (true::false::true::false::suffix)], ?_, by rfl⟩
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [state, List.isChain_cons_cons, TM0.step, fourMachine, Tape.mk₂]
  · simp [TM0.step, fourMachine]

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadPorts

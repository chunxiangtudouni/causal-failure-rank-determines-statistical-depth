module

public import Structure.RootB23_Threshold_BarePacket_017
public import Structure.RootB23_Threshold_Window_FixedConsumer_030
public import Structure.RootB23_Threshold_ReturnActual_022

/-! The fixed original-input bridge. The only new finite table dispatches
the two actual Window HALT labels to the two existing return entries.
Both transfers retain the real head/tape and perform a paid write-self. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace RootB23.Threshold.OriginalBridge
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PSTRTMSeq005 PA17TMDivisionCompose006
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

attribute [local implicit_reducible] FixedConsumer.cap ProtectedConsumer.cap
  ProtectedConsumer.prefixCap Producer.cap

def prefixCap : Nat := ProtectedConsumer.prefixCap 32 512

def rowCap : Nat := FixedConsumer.cap + 219

attribute [local implicit_reducible] prefixCap rowCap

theorem window_le : FixedConsumer.cap ≤ rowCap := by unfold rowCap; omega

theorem return_le : 219 ≤ rowCap := by unfold rowCap; omega

def rows (phase : Fin 2) : Machine rowCap :=
  if phase.val = 0 then padMachine window_le FixedConsumer.code
  else padMachine return_le ReturnDispatch.code

def ports (phase : Fin 2) (q : Fin (rowCap + 1)) : Option (Fin 2 × Fin (rowCap + 1)) :=
  if phase.val = 0 then
    if small : q.val < FixedConsumer.cap + 1 then
      (ReturnDispatch.dispatch prefixCap ⟨q.val, small⟩).map
        (fun destination => (1, padLabel return_le destination))
    else none
  else none

def tailCap : Nat := totalStates 1 rowCap

def tailCode : Machine tailCap := blockMachine rows ports

def cap : Nat := 4405 + tailCap + 1

attribute [local implicit_reducible] tailCap cap

def code : Machine cap := seqMachine BarePacket.machine tailCode

def tailPort (capped : Bool) : Fin (tailCap + 1) :=
  label (p := 1) (s := rowCap) (1 : Fin 2) (padLabel return_le (ReturnDispatch.exitPort capped))

def finalPort (capped : Bool) : Fin (cap + 1) := rightLabel (a := 4405) (tailPort capped)

def truePort : Fin (cap + 1) := finalPort true

def falsePort : Fin (cap + 1) := finalPort false

theorem rows_start : rows (0 : Fin 2) = padMachine window_le FixedConsumer.code := by
  simp only [rows, Fin.val_zero, ite_true]

theorem rows_return : rows (1 : Fin 2) = padMachine return_le ReturnDispatch.code := by
  simp only [rows, show (1 : Fin 2).val = 1 by rfl, Nat.one_ne_zero, ite_false]

theorem ports_return (q : Fin (rowCap + 1)) : ports (1 : Fin 2) q = none := by
  simp only [ports, show (1 : Fin 2).val = 1 by rfl, Nat.one_ne_zero, ite_false]

theorem ports_observed (q : Fin (FixedConsumer.cap + 1)) (destination : Fin 220)
    (observed : ReturnDispatch.dispatch prefixCap q = some destination) :
    ports (0 : Fin 2) (padLabel window_le q) = some (1, padLabel return_le destination) := by
  dsimp only [ports, padLabel]
  simp only [Fin.val_zero, ite_true, dite_eq_left q.isLt]
  change (ReturnDispatch.dispatch prefixCap q).map
    (fun destination => (1, padLabel return_le destination)) = _
  rw [observed]
  rfl

theorem true_port_value : truePort.val = 4406 + (rowCap + 1) + 219 := by
  change 4405 + 1 + (1 * (rowCap + 1) + 219) = _
  rw [Nat.one_mul]
  omega

theorem false_port_value : falsePort.val = 4406 + (rowCap + 1) + 72 := by
  change 4405 + 1 + (1 * (rowCap + 1) + 72) = _
  rw [Nat.one_mul]
  omega

theorem distinct_ports : truePort ≠ falsePort := by
  intro same
  have values := congrArg Fin.val same
  rw [true_port_value, false_port_value] at values
  omega

end RootB23.Threshold.OriginalBridge

module

public import Common.PSTR_WordVM_VirtualBool_025
public import Common.PSTR_TM_NativeMul_112

/-! Direct consumer of the mature actual original two-Nat multiplier.
The complete old terminal head push and its real return step survive.
Whole-Tape correctness gives a ListBlank R0 contract for the real reader;
it never gives an exact canonical finite R0 or a free input packet/init.
This is an internal port; the next joint caller must pay initialization. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.NativeMulPort

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

abbrev OldStore := BoolOnStacks.Store 982
abbrev Statement (C : Type*) := PSTRWordVM.VirtualReturn.Statement C OldStore
abbrev State (C : Type*) := PSTRWordVM.VirtualReturn.State C OldStore

variable {C : Type*}

def source : Unit → PSTRWordVM.VirtualReturn.SmallStatement OldStore :=
  PSTRWordVM.VirtualBool.source PSTRTMNativeMul112.nativeMulMachine

def program (caller : Statement C) : PSTRWordVM.VirtualReturn.Label → Statement C :=
  PSTRWordVM.VirtualReturn.program source caller

def entry (context : C) (background : Fin 16 → List Bool) (a b : Nat) : State C :=
  PSTRWordVM.VirtualReturn.configuration context background
    (TM2.init (Γ := PushPop.Alphabet) (Λ := Unit) (σ := OldStore) 0 (encodeNat a ++ encodeNat b))

theorem actual_product_port (caller : Statement C) (context : C)
    (background : Fin 16 → List Bool) (a b : Nat) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head? = some (entry context background a b) ∧
      trace.IsChain (fun before after => TM2.step (program caller) before = some after) ∧
      trace.getLast? = some final ∧ final.l = some 1 ∧
      ListBlank.mk (final.stk 0) = ListBlank.mk (encodeNat (a * b)) ∧
      PSTRWordVM.VirtualBool.representedState final = PSTRTMNativeMul112.nativeFinal a b ∧
      trace.map PSTRWordVM.VirtualBool.representedState =
        PSTRTMNativeMul112.nativeTrace a b ++ [PSTRTMNativeMul112.nativeFinal a b] ∧
      trace.length ≤ 16384 * (natBits a + natBits b + 1) ^ 2 + 1 ∧
      final.var.1 = context ∧
      (∀ current ∈ trace, current.var.1 = context ∧
        ∀ slot, slot ≠ 0 → slot ≠ 1 → current.stk slot = background slot) ∧
      ∀ current ∈ trace, PSTRWordVM.VirtualReturn.occupiedSlots current.stk ≤
        PSTRWordVM.VirtualReturn.outside background + 65536 * (natBits a + natBits b + 1) ^ 2 := by
  have oldRun := PSTRTMNativeMul112.native_runs a b
  obtain ⟨trace, final, first, chain, last, returned, represented, order, length, contextFinal, frames, space⟩ :=
    PSTRWordVM.VirtualBool.same_old_run PSTRTMNativeMul112.nativeMulMachine caller context background
      (encodeNat a ++ encodeNat b) (PSTRTMNativeMul112.nativeTrace a b)
      (PSTRTMNativeMul112.nativeFinal a b) oldRun.1 oldRun.2.1 oldRun.2.2.1 oldRun.2.2.2.1
  have wholeTape := congrArg (fun cfg : MachineState 982 => cfg.Tape) represented
  have rightTape := congrArg Tape.right₀
    (wholeTape.trans (PSTRTMNativeMul112.native_final_tape_canonical a b))
  have rightResult : ListBlank.mk (final.stk 0) = ListBlank.mk (encodeNat (a * b)) := by
    simpa only [PSTRWordVM.VirtualBool.representedState, Tape.mk₁, Tape.mk₂, Tape.mk'_right₀] using rightTape
  refine ⟨trace, final, first, chain, last, returned, rightResult, represented, order, ?_,
    contextFinal, frames, ?_⟩
  · have oldTime := PSTRTMNativeMul112.native_length_le a b
    omega
  · intro current present
    have occupied := space current present
    have oldSpace := PSTRTMNativeMul112.native_visitedSpace_le a b
    omega

theorem body_actions : ScannerClock.actions
    (PSTRWordVM.VirtualReturn.statement (C := C) (source ())) = 4 :=
  PSTRWordVM.VirtualBool.actions PSTRTMNativeMul112.nativeMulMachine

theorem body_pushes : AuxWorkspace.pushes
    (PSTRWordVM.VirtualReturn.statement (C := C) (source ())) = 2 :=
  PSTRWordVM.VirtualBool.pushes PSTRTMNativeMul112.nativeMulMachine

end PaperProofs.Common.Native.PSTRWordBool.NativeMulPort

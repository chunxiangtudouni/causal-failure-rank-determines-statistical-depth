module

public import Common.PSTR_WordVM_VirtualReturn_024
public import Common.PSTR_WordBool_BoolStackSpace_019

/-! Actual old Bool machine -> reusable real two-stack callee, for the
parent NativeMul consumer. The SAME old run/order/geometry is retained.
Final source HALT's head-bit push and its whole paid step are translated
to ACTIVE return1. No finite-right-list equality is inferred from Tape.
Caller context/control must be fixed finite before all data for native040. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.VirtualBool

open Turing VirtualReturn

variable {C : Type*} {states : Nat}

abbrev OldStore := PSTRWordBool.BoolOnStacks.Store states
abbrev OldState := PSTRWordBool.BoolOnStacks.State states

def source (machine : TM0.Machine Bool (Fin (states + 1))) : Unit → SmallStatement (OldStore (states := states)) :=
  PSTRWordBool.BoolOnStacks.program machine

def representedState (before : VirtualReturn.State C (OldStore (states := states))) : TM0.Cfg Bool (Fin (states + 1)) :=
  ⟨before.var.2.1, Tape.mk' (ListBlank.mk (before.stk 1)) (ListBlank.mk (before.stk 0))⟩

theorem represented_configuration (context : C) (background : Stack → List Bool) (small : OldState (states := states)) :
    representedState (configuration context background small) = PSTRWordBool.BoolOnStacks.representedState small := rfl

/-- This exposes the exact terminal data and REAL source step. With R=[]
the output really contains one FALSE; it is not silently reset to[]. -/
theorem paid_terminal (machine : TM0.Machine Bool (Fin (states + 1)))
    (caller : Statement C (OldStore (states := states))) (context : C) (background : Stack → List Bool)
    (control : Fin (states + 1)) (scratch : Bool) (left right : List Bool)
    (actual : machine control (PSTRWordBool.BoolStackStep.headBit right) = none) :
    TM2.step (program (source machine) caller)
      (configuration context background (PSTRWordBool.BoolStackStep.cfg (some ()) control scratch left right)) =
      some (configuration context background (PSTRWordBool.BoolStackStep.cfg none control
        (PSTRWordBool.BoolStackStep.headBit right) left (PSTRWordBool.BoolStackStep.headBit right :: right.tail))) :=
  step_configuration (source machine) caller context background _ _
    (PSTRWordBool.BoolStackStep.halt_step machine control scratch left right actual)

theorem pushes (machine : TM0.Machine Bool (Fin (states + 1))) :
    PSTRWordBool.AuxWorkspace.pushes (statement (C := C) (source machine ())) = 2 := by
  rw [statement_pushes]
  rfl

theorem actions (machine : TM0.Machine Bool (Fin (states + 1))) :
    PSTRWordBool.ScannerClock.actions (statement (C := C) (source machine ())) = 4 := by
  rw [statement_actions]
  rfl

/-- Both short-lived source stacks are bounded from the OLD macro input
and fixed push allowance2, not from old/new elapsed time. All14 other
physical stacks and caller C are unchanged at EVERY internal snapshot. -/
theorem internal_resources (machine : TM0.Machine Bool (Fin (states + 1)))
    (context : C) (memory : OldStore (states := states)) (small : SmallStack → List Bool)
    (background : Stack → List Bool) :
    ∀ current ∈ PSTRWordBool.AuxWorkspace.nodes (statement (C := C) (source machine ()))
        (context, memory) (slots background small),
      current.1.1 = context ∧
      (∀ point, point ≠ 0 → point ≠ 1 → current.2 point = background point) ∧
      occupiedSlots current.2 ≤ outside background + 2 * ((small 0).length + (small 1).length + 2) := by
  intro current present
  have frame := internal_frame (source machine ()) context memory small background current present
  have mass := internal_occupied (source machine ()) context memory small background current present
  have fixedPushes : PSTRWordBool.AuxWorkspace.pushes (source machine ()) = 2 := rfl
  rw [fixedPushes] at mass
  exact ⟨frame.1, frame.2, mass⟩

/-- Internal callee theorem. The real old trace is supplied by the proved
NativeMul112 Runs consumer, never by an original caller as a new oracle.
It retains exact source<->old order and genuine old visitedSpace. -/
theorem same_old_run (machine : TM0.Machine Bool (Fin (states + 1)))
    (caller : Statement C (OldStore (states := states))) (context : C) (background : Stack → List Bool)
    (input : List Bool) (oldTrace : List (TM0.Cfg Bool (Fin (states + 1))))
    (oldFinal : TM0.Cfg Bool (Fin (states + 1)))
    (first : oldTrace.head? = some (TM0.init input))
    (chain : oldTrace.IsChain (fun before after => TM0.step machine before = some after))
    (last : oldTrace.getLast? = some oldFinal) (halt : TM0.step machine oldFinal = none) :
    ∃ (path : List (VirtualReturn.State C (OldStore (states := states)))) (final : VirtualReturn.State C (OldStore (states := states))),
      path.head? = some (configuration context background
        (TM2.init (Γ := PSTRWordBool.PushPop.Alphabet) (Λ := Unit) (σ := OldStore (states := states)) 0 input)) ∧
      path.IsChain (fun before after => TM2.step (program (source machine) caller) before = some after) ∧
      path.getLast? = some final ∧ final.l = some 1 ∧
      representedState final = oldFinal ∧ path.map representedState = oldTrace ++ [oldFinal] ∧
      path.length = oldTrace.length + 1 ∧ final.var.1 = context ∧
      (∀ current ∈ path, current.var.1 = context ∧
        ∀ point, point ≠ 0 → point ≠ 1 → current.stk point = background point) ∧
      ∀ current ∈ path, occupiedSlots current.stk ≤ outside background +
        PaperProofs.Common.Native.RationalControllerComputation.visitedSpace machine input.length oldTrace := by
  obtain ⟨smallTrace, smallFinal, smallHead, smallChain, smallLast, smallStop, smallRepresented,
      smallOrder, smallLength, smallSpace⟩ :=
    PSTRWordBool.BoolStackSpace.same_old_run machine input oldTrace oldFinal first chain last halt
  obtain ⟨head, liftedChain, liftedLast, liftedLength, frame⟩ :=
    path_configuration (source machine) caller context background smallTrace _ _ smallHead smallChain smallLast
  refine ⟨smallTrace.map (configuration context background), configuration context background smallFinal,
    head, liftedChain, liftedLast, ?_, ?_, ?_, liftedLength.trans smallLength, rfl, frame, ?_⟩
  · exact returned context background smallFinal (none_of_stopped (source machine) smallFinal smallStop)
  · exact (represented_configuration context background smallFinal).trans smallRepresented
  · simpa only [List.map_map, Function.comp_def, represented_configuration] using smallOrder
  · intro current present
    obtain ⟨small, member, rfl⟩ := List.mem_map.mp present
    change occupiedSlots (slots background small.stk) ≤ _
    rw [occupied_slots]
    have space := smallSpace small member
    omega

/-- Every actual body invocation, including the terminal one, is the same
new finite statement with actions4/pushes2; no unchanged-native-time claim. -/
theorem body_at_entry (machine : TM0.Machine Bool (Fin (states + 1)))
    (caller : Statement C (OldStore (states := states))) :
    program (source machine) caller 0 = statement (source machine ()) := rfl

end PaperProofs.Common.Native.PSTRWordVM.VirtualBool

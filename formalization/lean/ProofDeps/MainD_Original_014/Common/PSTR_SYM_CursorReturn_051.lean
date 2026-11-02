module

public import Common.PSTR_SYM_CursorCounter_050

/-! Actual END00→RIGHT1→marker scan→restore→true HALT in the same concrete
048 table. The finite zero bit is part of the incoming control label; its
producer is the actual counter port in050, not a new original input field. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorReturn

open Turing PSTRTMSeq005 PSTRSymbolicPairedCursor PSTRSymbolicCarry
open PSTRSymbolicLaneScan PSTRSymbolicLaneArchive PSTRSymbolicLaneReturn PSTRSymbolicMarkedReturn
open PSTRSymbolicZeroTail PSTRSymbolicCursorPorts PSTRSymbolicCursorCode PSTRSymbolicCursorStages

theorem restore_from_carrier (tag first second : Bool) :
    restoreLabel 0
      (savedTag (carryLabel (6 : Fin 7) (markerCarry tag first second)).val)
      (savedFirst (carryLabel (6 : Fin 7) (markerCarry tag first second)).val)
      (savedSecond (carryLabel (6 : Fin 7) (markerCarry tag first second)).val) =
      restoreLabel 0 tag first second := by
  cases tag <;> cases first <;> cases second <;> decide

theorem actual_return_halt (data : List Datum) (earlier later : List (Bool × Bool))
    (shape : allDatumPairs data = earlier ++ later) (header suffix : List Bool)
    (near middle first far second tag zero : Bool) :
    ∃ (trace : List (TM0.Cfg Bool Label)) (final : TM0.Cfg Bool Label),
      trace.head? = some
        ⟨.one zero (carryLabel (18 : Fin 20) (markerCarry tag first second)),Tape.mk₂ header
          (false :: (navigationCells earlier ++ false :: far :: true :: middle :: true :: near :: true :: suffix))⟩ ∧
      trace.IsChain (fun before after => TM0.step machine before = some after) ∧
      trace.getLast? = some final ∧ final.q = .halt zero ∧
      final.Tape = Tape.mk₂
        (near :: true :: middle :: first :: far :: second :: ((navigationCells earlier).reverse ++ false :: header))
        (tag :: suffix) ∧ TM0.step machine final = none ∧
      trace.length = 2 * earlier.length + 27 := by
  let carry := markerCarry tag first second
  let marked := navigationCells earlier ++ false :: far :: true :: middle :: true :: near :: true :: suffix
  let initialTape := Tape.mk₂ header (false :: marked)
  let markedLeft := near :: true :: middle :: true :: far :: false ::
    ((navigationCells earlier).reverse ++ false :: header)
  let restoredLeft := near :: true :: middle :: first :: far :: second ::
    ((navigationCells earlier).reverse ++ false :: header)
  let oneTrace := (rightOneTrace initialTape).map (carryCfg carry)
  let oneEnd := carryCfg carry (rightState 19 (by decide) (Tape.mk₂ (false :: header) marked))
  let scanTrace := (rightScanTrace 0 (false :: header) (rightPrefix earlier far) middle near suffix).map (carryCfg carry)
  let scanEnd := carryCfg carry (scanState 6 markedLeft (true :: suffix))
  let restoreNativeTrace := restoreTrace near middle first far second
    ((navigationCells earlier).reverse ++ false :: header) tag suffix
  let restoreEnd := restoreState 15 tag first second restoredLeft (tag :: suffix)
  have moved := right_one_runsFrom initialTape
  have shifted : initialTape.move .right = Tape.mk₂ (false :: header) marked := by
    simp [initialTape, Tape.mk₂]
  rw [shifted] at moved
  have oneActual := carry_runsFrom right19Machine carry _ _ _ moved
  have scanNative : RunsFrom (flagWalkMachine true)
      (scanState 0 (false :: header) marked)
      (rightScanTrace 0 (false :: header) (rightPrefix earlier far) middle near suffix)
      (scanState 6 markedLeft (true :: suffix)) :=
    actual_right_return data earlier later (false :: header) suffix far middle near shape
  have scanActual := carry_runsFrom (flagWalkMachine true) carry _ _ _ scanNative
  have restored : RunsFrom markerRestoreMachine
      (restoreState 0 tag first second markedLeft (true :: suffix)) restoreNativeTrace restoreEnd :=
    restore_runsFrom near middle first far second ((navigationCells earlier).reverse ++ false :: header) tag suffix
  let oneFinish : Fin 160 → Label := fun current =>
    .scanRight zero (carryLabel (0 : Fin 7) (savedLabel (states := 19) current))
  let scanFinish : Fin 56 → Label := fun current => .restore zero
    (restoreLabel 0 (savedTag current.val) (savedFirst current.val) (savedSecond current.val))
  have onePart := called_endpoints machine (carryMachine right19Machine) (Label.one zero) oneFinish
    (by intro q bit; rfl) _ _ _ oneActual
  have scanPart := called_endpoints machine (carryMachine (flagWalkMachine true)) (Label.scanRight zero) scanFinish
    (by intro q bit; rfl) _ _ _ scanActual
  have restorePart := called_endpoints machine markerRestoreMachine (Label.restore zero) (fun _ => .halt zero)
    (by intro q bit; rfl) _ _ _ restored
  have oneHead : (oneTrace.map (tagCfg (Label.one zero))).head? = some
      (tagCfg (Label.one zero) (carryCfg carry (rightState 18 (by decide) initialTape))) := onePart.1
  have scanLast : (scanTrace.map (tagCfg (Label.scanRight zero))).getLast? =
      some (tagCfg (Label.scanRight zero) scanEnd) := scanPart.2.2.1
  have restoreLast : (restoreNativeTrace.map (tagCfg (Label.restore zero))).getLast? =
      some (tagCfg (Label.restore zero) restoreEnd) := restorePart.2.2.1
  have firstBridge : TM0.step machine (tagCfg (Label.one zero) oneEnd) = some
      (tagCfg (Label.scanRight zero) (carryCfg carry (scanState 0 (false :: header) marked))) := by
    have edge := onePart.2.2.2.1
    change TM0.step machine (tagCfg (Label.one zero) oneEnd) = some
      ⟨.scanRight zero (carryLabel (0 : Fin 7) (savedLabel (carryLabel (19 : Fin 20) carry))),
        Tape.mk₂ (false :: header) marked⟩ at edge
    rw [saved_carry] at edge
    exact edge
  have secondBridge : TM0.step machine (tagCfg (Label.scanRight zero) scanEnd) = some
      (tagCfg (Label.restore zero) (restoreState 0 tag first second markedLeft (true :: suffix))) := by
    have edge := scanPart.2.2.2.1
    change TM0.step machine (tagCfg (Label.scanRight zero) scanEnd) = some
      ⟨.restore zero (restoreLabel 0
        (savedTag (carryLabel (6 : Fin 7) (markerCarry tag first second)).val)
        (savedFirst (carryLabel (6 : Fin 7) (markerCarry tag first second)).val)
        (savedSecond (carryLabel (6 : Fin 7) (markerCarry tag first second)).val)),scanEnd.Tape⟩ at edge
    rw [restore_from_carrier] at edge
    exact edge
  let firstTrace := oneTrace.map (tagCfg (Label.one zero)) ++ scanTrace.map (tagCfg (Label.scanRight zero))
  have firstChain : firstTrace.IsChain (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append onePart.2.1 scanPart.2.1
    intro before beforeLast after afterHead
    simp only [onePart.2.2.1, Option.mem_some_iff] at beforeLast
    simp only [scanPart.1, Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact firstBridge
  have firstLast : firstTrace.getLast? = some (tagCfg (Label.scanRight zero) scanEnd) := by
    simp only [firstTrace, List.getLast?_append, scanLast, Option.some_or]
  let throughRestore := firstTrace ++ restoreNativeTrace.map (tagCfg (Label.restore zero))
  have throughChain : throughRestore.IsChain (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append firstChain restorePart.2.1
    intro before beforeLast after afterHead
    simp only [firstLast, Option.mem_some_iff] at beforeLast
    simp only [restorePart.1, Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact secondBridge
  have throughLast : throughRestore.getLast? = some (tagCfg (Label.restore zero) restoreEnd) := by
    simp only [throughRestore, List.getLast?_append, restoreLast, Option.some_or]
  let final : TM0.Cfg Bool Label := ⟨.halt zero,Tape.mk₂ restoredLeft (tag :: suffix)⟩
  let trace := throughRestore ++ [final]
  have chain : trace.IsChain (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append throughChain (.singleton _)
    intro before beforeLast after afterHead
    simp only [throughLast, Option.mem_some_iff] at beforeLast
    simp only [List.head?_cons, Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact restorePart.2.2.2.1
  refine ⟨trace, final, ?_, chain, ?_, rfl, rfl, terminal zero _, ?_⟩
  · change trace.head? = some (tagCfg (Label.one zero)
      (carryCfg carry (rightState 18 (by decide) initialTape)))
    simp only [trace, throughRestore, firstTrace, List.head?_append, oneHead, Option.some_or]
  · simp only [trace, List.getLast?_append, List.getLast?_singleton, Option.some_or]
  · simp only [trace, throughRestore, firstTrace, List.length_append, List.length_cons, List.length_nil,
      List.length_map, oneTrace, right_one_length, scanTrace, right_scan_length,
      rightPrefix, restoreNativeTrace, restore_length]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorReturn

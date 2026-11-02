module

public import Common.PSTR_SYM_CursorCode_048

/-! Actual same-whole stage transport for048. A local HALT is replaced by
a charged WRITE-current-symbol return edge in the concrete whole table.
Its displacement remains zero, so the original scan/fold space is exactly
preserved on each mapped callee prefix. Whole-macro assembly follows. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorStages

open Turing PSTRTMSeq005 PSTRSymbolicRelabel PSTRSymbolicCursorCode

theorem called_chain {states : Nat} {Target : Type} [Inhabited Target]
    (whole : TM0.Machine Bool Target) (callee : Machine states)
    (tag finish : Fin (states + 1) → Target)
    (code : ∀ q bit, whole (tag q) bit = calledCode callee tag finish q bit)
    (trace : List (MachineState states))
    (actual : trace.IsChain (fun before after => TM0.step callee before = some after)) :
    (trace.map (tagCfg tag)).IsChain (fun before after => TM0.step whole before = some after) := by
  apply (List.isChain_map _).mpr
  exact actual.imp (fun before after edge => called_step_some whole callee tag finish code before after edge)

theorem called_endpoints {states : Nat} {Target : Type} [Inhabited Target]
    (whole : TM0.Machine Bool Target) (callee : Machine states)
    (tag finish : Fin (states + 1) → Target)
    (code : ∀ q bit, whole (tag q) bit = calledCode callee tag finish q bit)
    (entry final : MachineState states) (trace : List (MachineState states))
    (actual : RunsFrom callee entry trace final) :
    (trace.map (tagCfg tag)).head? = some (tagCfg tag entry) ∧
    (trace.map (tagCfg tag)).IsChain (fun before after => TM0.step whole before = some after) ∧
    (trace.map (tagCfg tag)).getLast? = some (tagCfg tag final) ∧
    TM0.step whole (tagCfg tag final) = some ⟨finish final.q,final.Tape⟩ ∧
    (trace.map (tagCfg tag)).length = trace.length := by
  refine ⟨?_, called_chain whole callee tag finish code trace actual.2.1, ?_, ?_, ?_⟩
  · simp only [List.head?_map, actual.1, Option.map_some]
  · simp only [List.getLast?_map, actual.2.2.1, Option.map_some]
  · exact called_step_none whole callee tag finish code final actual.2.2.2
  · exact List.length_map _

theorem called_displacement {states : Nat} {Target : Type} [Inhabited Target]
    (whole : TM0.Machine Bool Target) (callee : Machine states)
    (tag finish : Fin (states + 1) → Target)
    (code : ∀ q bit, whole (tag q) bit = calledCode callee tag finish q bit)
    (cfg : MachineState states) :
    sourceDisplacement whole (tagCfg tag cfg) = displacement callee cfg := by
  cases cfg with
  | mk q tape =>
    unfold sourceDisplacement displacement tagCfg
    rw [code]
    unfold calledCode
    cases callee q tape.head with
    | none => rfl
    | some action =>
      obtain ⟨next,op⟩ := action
      cases op with
      | write bit => rfl
      | move direction => cases direction <;> rfl

theorem called_space {states : Nat} {Target : Type} [Inhabited Target]
    (whole : TM0.Machine Bool Target) (callee : Machine states)
    (tag finish : Fin (states + 1) → Target)
    (code : ∀ q bit, whole (tag q) bit = calledCode callee tag finish q bit)
    (inputLength : Nat) (trace : List (MachineState states)) :
    sourceVisitedSpace whole inputLength (trace.map (tagCfg tag)) = visitedSpace callee inputLength trace := by
  have movements : (trace.map (tagCfg tag)).map (sourceDisplacement whole) = trace.map (displacement callee) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro cfg _
    exact called_displacement whole callee tag finish code cfg
  unfold sourceVisitedSpace visitedSpace
  rw [movements]

/-! The first two actual stages of the concrete whole table. Physical
root cells are parameters of this internal entry; the original header
producer still has to establish them and the counter width. -/

open PSTRSymbolicPairedCursor PSTRSymbolicCarry PSTRSymbolicLaneScan
open PSTRSymbolicLaneArchive PSTRSymbolicLaneReturn PSTRSymbolicMarkedReturn

def markerCarry (tag first second : Bool) : Fin 8 :=
  savedLabel (states := 9) (markLabel 9 tag first second)

theorem rePair_length (current : Bool) (pairs : List (Bool × Bool)) (last : Bool) :
    (rePair current pairs last).length = pairs.length + 1 := by
  induction pairs generalizing current with
  | nil => rfl
  | cons pair earlier ih =>
    obtain ⟨flag,bit⟩ := pair
    simp only [rePair, List.length_cons, ih]

theorem leftPrefix_length (earlier : List (Bool × Bool)) :
    (leftPrefix earlier).length = earlier.length + 1 := by
  simp only [leftPrefix, rePair_length, List.length_reverse]

theorem actual_mark_left (data : List Datum) (earlier later : List (Bool × Bool))
    (shape : allDatumPairs data = earlier ++ later)
    (rootOlder suffix : List Bool) (rootFirst rootSecond near middle first far second tag : Bool) :
    ∃ (trace : List (TM0.Cfg Bool Label)) (final : TM0.Cfg Bool Label),
      trace.head? = some ⟨.mark 0, Tape.mk₂
        (near :: true :: middle :: first :: far :: second :: ((navigationCells earlier).reverse ++
          false :: true :: rootFirst :: true :: rootSecond :: true :: rootOlder)) (tag :: suffix)⟩ ∧
      trace.IsChain (fun before after => TM0.step machine before = some after) ∧
      trace.getLast? = some final ∧
      final.q = .scanLeft (carryLabel (6 : Fin 7) (markerCarry tag first second)) ∧
      final.Tape = Tape.mk₂ rootOlder (true :: rootSecond :: true :: rootFirst :: true ::
        ((navigationCells (leftPrefix earlier)).reverse ++ far :: true :: middle :: true :: near :: true :: suffix)) ∧
      TM0.step machine final = some ⟨.six (carryLabel (13 : Fin 20) (markerCarry tag first second)),final.Tape⟩ ∧
      trace.length = 2 * earlier.length + 18 := by
  let tail := far :: true :: middle :: true :: near :: true :: suffix
  let archive := (navigationCells earlier).reverse ++
    false :: true :: rootFirst :: true :: rootSecond :: true :: rootOlder
  let carry := markerCarry tag first second
  let firstTrace := markerTrace near middle first far second archive tag suffix
  let firstEnd := markState 9 tag first second archive (false :: tail)
  let secondTrace := leftScanTrace 0 rootOlder (leftPrefix earlier) rootFirst rootSecond tail
  let secondEnd := scanState 6 rootOlder (true :: rootSecond :: true :: rootFirst :: true ::
    ((navigationCells (leftPrefix earlier)).reverse ++ tail))
  have installed : RunsFrom markerSetupMachine
      ⟨0,Tape.mk₂ (near :: true :: middle :: first :: far :: second :: archive) (tag :: suffix)⟩
      firstTrace firstEnd := marker_runsFrom near middle first far second archive tag suffix
  have scanned : RunsFrom (flagWalkMachine false) (scanState 0 archive (false :: tail))
      secondTrace secondEnd := actual_left_root data earlier later rootOlder tail rootFirst rootSecond shape
  let markFinish : Fin 80 → Label := fun current =>
    .scanLeft (carryLabel (0 : Fin 7) (savedLabel (states := 9) current))
  let leftFinish : Fin 56 → Label := fun current =>
    .six (carryLabel (13 : Fin 20) (savedLabel (states := 6) current))
  have firstPart := called_endpoints machine markerSetupMachine Label.mark markFinish
    (by intro q bit; rfl) _ _ _ installed
  have secondCarried := carry_runsFrom (flagWalkMachine false) carry _ _ _ scanned
  have secondPart := called_endpoints machine (carryMachine (flagWalkMachine false)) Label.scanLeft leftFinish
    (by intro q bit; rfl) _ _ _ secondCarried
  let trace := firstTrace.map (tagCfg Label.mark) ++
    (secondTrace.map (carryCfg carry)).map (tagCfg Label.scanLeft)
  let final := tagCfg Label.scanLeft (carryCfg carry secondEnd)
  have chain : trace.IsChain (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append firstPart.2.1 secondPart.2.1
    intro before beforeLast after afterHead
    simp only [firstPart.2.2.1, Option.mem_some_iff] at beforeLast
    simp only [secondPart.1, Option.mem_some_iff] at afterHead
    subst before
    subst after
    change TM0.step machine (tagCfg Label.mark firstEnd) =
      some ⟨.scanLeft (carryLabel (0 : Fin 7) carry),firstEnd.Tape⟩
    exact firstPart.2.2.2.1
  have returnStep : TM0.step machine final =
      some ⟨.six (carryLabel (13 : Fin 20) carry),final.Tape⟩ := by
    have step := secondPart.2.2.2.1
    change TM0.step machine final =
      some ⟨.six (carryLabel (13 : Fin 20) (savedLabel (carryLabel (6 : Fin 7) carry))),final.Tape⟩ at step
    rw [saved_carry] at step
    exact step
  refine ⟨trace, final, ?_, chain, ?_, rfl, rfl, returnStep, ?_⟩
  · change trace.head? = some (tagCfg Label.mark
      ⟨0,Tape.mk₂ (near :: true :: middle :: first :: far :: second :: archive) (tag :: suffix)⟩)
    simp only [trace, List.head?_append, firstPart.1, Option.some_or]
  · simp only [trace, List.getLast?_append, secondPart.2.2.1, Option.some_or, final]
  · simp only [trace, List.length_append, List.length_map, firstTrace, marker_length,
      secondTrace, left_scan_length, leftPrefix_length]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorStages

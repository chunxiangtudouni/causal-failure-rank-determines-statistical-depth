module

public import Common.PSTR_SYM_RawLoopSuffix_067
public import Common.PSTR_SYM_FiniteRelabel_007

/-! A real finite entry0 for the frozen generic remaining-Datum loop.
The entry is one charged head-preserving WRITE to .datum0, not .boot0;
the counted TRUE-footer return is followed by its actual final step and
true HALT. All layout/count qualifications are internal producer ABI. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.Remaining

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMSeq005 PSTRSymbolicRawLoop PSTRSymbolicLaneArchive PSTRSymbolicCursorArchive
open PSTRTMIncrement009 PSTRSymbolicRelabel

inductive Label where
  | entry
  | body : LoopLabel → Label
  deriving DecidableEq,Fintype

instance : Inhabited Label := ⟨.entry⟩

noncomputable def code : TM0.Machine Bool Label
  | .entry, symbol => some (.body (.datum 0),.write symbol)
  | .body q, symbol => (loopCode q symbol).map (fun action => (.body action.1,action.2))

noncomputable def support : Finset Label := Finset.univ
noncomputable def machine : Machine support.card := finiteMachine code support
noncomputable def labels : PointedMap Label (Fin (support.card+1)) := finiteLabels support
noncomputable def haltPort : Fin (support.card+1) := labels (.body (.done true))

def bodyCfg (cfg : TM0.Cfg Bool LoopLabel) : TM0.Cfg Bool Label := ⟨.body cfg.q,cfg.Tape⟩
noncomputable def liftCfg (cfg : TM0.Cfg Bool Label) : MachineState support.card := relabelCfg labels cfg

theorem body_step (cfg : TM0.Cfg Bool LoopLabel) :
    TM0.step code (bodyCfg cfg) = (TM0.step loopCode cfg).map bodyCfg := by
  cases cfg with
  | mk q tape =>
    simp only [TM0.step,bodyCfg,code]
    cases action : loopCode q tape.head with
    | none => rfl
    | some pair => obtain ⟨next,op⟩ := pair; cases op <;> rfl

theorem lift_step (cfg : TM0.Cfg Bool Label) :
    TM0.step machine (liftCfg cfg) = (TM0.step code cfg).map liftCfg := by
  exact (relabel_step code (support : Set Label) labels (finiteDecode support)
    (fun q present => finite_inverse support q present) cfg (Finset.mem_univ _)).symm

theorem actual (data remaining : List Datum) (base digits unread : List Bool) (bytes inputLength : Nat)
    (nonempty : remaining ≠ []) (archiveRoom : 3 ≤ (allDatumPairs data).length)
    (headerRoom : 3 ≤ digits.length) (countValue : valueDigits digits = remaining.length)
    (sized : ∀ value ∈ remaining, (encodeDatum value).length ≤ bytes) :
    ∃ (endDigits : List Bool) (path : List (MachineState support.card)) (final : MachineState support.card),
      RunsFrom machine ⟨0,pendingSuffix data base digits remaining unread⟩ path final ∧
      final.q = haltPort ∧
      final.Tape = archiveTape (data ++ remaining) base endDigits unread true ∧
      valueDigits endDigits = 0 ∧ endDigits.length = digits.length ∧
      path.length ≤ remaining.length * cycleBudget (allDatumPairs (data ++ remaining)).length digits.length bytes + 2 ∧
      ∀ clock, visitedSpace machine inputLength (path.take clock) ≤ inputLength+
        2*(remaining.length * cycleBudget (allDatumPairs (data ++ remaining)).length digits.length bytes)+5 := by
  classical
  obtain ⟨endDigits,oldTrace,oldFinal,oldHead,oldChain,oldLast,_oldPort,oldTape,oldNext,
    endValue,endWidth,oldTime⟩ :=
    actual_remaining_suffix data remaining base digits unread bytes nonempty archiveRoom headerRoom countValue sized
  let initial : TM0.Cfg Bool Label := ⟨.entry,pendingSuffix data base digits remaining unread⟩
  let finalSource : TM0.Cfg Bool Label := ⟨.body (.done true),oldFinal.Tape⟩
  let sourceTrace := [initial] ++ oldTrace.map bodyCfg ++ [finalSource]
  have firstStep : TM0.step code initial =
      some (bodyCfg ⟨.datum 0,pendingSuffix data base digits remaining unread⟩) := by
    simp only [TM0.step,initial,code,Option.map_some,Tape.write_self]
    rfl
  have prefixChain : ([initial] ++ oldTrace.map bodyCfg).IsChain
      (fun before after => TM0.step code before = some after) := by
    apply List.IsChain.append (.singleton _)
    · apply (List.isChain_map _).mpr
      exact oldChain.imp (fun before after edge => by simp only [body_step,edge,Option.map_some])
    · intro before beforeLast after afterHead
      simp only [List.getLast?_singleton,Option.mem_some_iff] at beforeLast
      simp only [List.head?_map,oldHead,Option.map_some,Option.mem_some_iff] at afterHead
      subst before
      subst after
      exact firstStep
  have sourceChain : sourceTrace.IsChain (fun before after => TM0.step code before = some after) := by
    apply List.IsChain.append prefixChain (.singleton _)
    intro before beforeLast after afterHead
    simp only [List.getLast?_append,List.getLast?_map,oldLast,Option.map_some,Option.some_or,
      Option.mem_some_iff] at beforeLast
    simp only [List.head?_singleton,Option.mem_some_iff] at afterHead
    subst before
    subst after
    simp only [body_step,oldNext,Option.map_some]
    rfl
  have sourceHalt : TM0.step code finalSource = none := by
    change TM0.step code (bodyCfg ⟨.done true,oldFinal.Tape⟩) = none
    rw [body_step,loop_halt]
    rfl
  let path := sourceTrace.map liftCfg
  let final := liftCfg finalSource
  have run : RunsFrom machine ⟨0,pendingSuffix data base digits remaining unread⟩ path final := by
    refine ⟨?_,?_,?_,?_⟩
    · simp only [path,sourceTrace,List.head?_map,List.head?_append,List.head?_singleton,Option.some_or,
        Option.map_some]
      have hentry : labels (.entry) = (0 : Fin (support.card + 1)) := by
        have entry_default : (.entry : Label) = default := rfl
        simp only [labels, finiteLabels, entry_default, ↓reduceIte]
      change some (⟨labels (.entry),pendingSuffix data base digits remaining unread⟩ : MachineState support.card) =
        some (⟨0,pendingSuffix data base digits remaining unread⟩ : MachineState support.card)
      rw [hentry]
    · apply (List.isChain_map _).mpr
      exact sourceChain.imp (fun before after edge => by simp only [lift_step,edge,Option.map_some])
    · simp only [path,final,sourceTrace,List.getLast?_map,List.getLast?_append,List.getLast?_singleton,
        Option.some_or,Option.map_some]
    · simp only [final,lift_step,sourceHalt,Option.map_none]
  have time : path.length ≤ remaining.length * cycleBudget
      (allDatumPairs (data ++ remaining)).length digits.length bytes + 2 := by
    simp only [path,sourceTrace,List.length_map,List.length_append,List.length_cons,List.length_nil]
    omega
  refine ⟨endDigits,path,final,run,rfl,?_,endValue,endWidth,time,?_⟩
  · exact oldTape
  · intro clock
    have space := PSTRTMTrace002.visitedSpace_le machine inputLength (path.take clock)
    have short := List.length_take_le' clock path
    omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.Remaining

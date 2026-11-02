module

public import PaperProofs.Paid.PDROC_Simulator_018
public import PaperProofs.Paid.PDROC_SimulatorHandles_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

def simulatorMarkAt (writes : I.Stage → Option (Bool × ℕ)) : VisibleEvent I → Option (HistoryMark I)
  | .report stage truth serial => match writes stage with
      | none => none
      | some (bit, writtenSerial) => if writtenSerial = serial then some (.writeError stage (bit != truth)) else none
  | .committed handle tool => some (.reserve handle.stage tool)
  | .executed handle tool => some (.correction handle.stage tool)
  | .advanced stage => some (.advance stage)
  | .abandoned => some (.terminate true)
  | .stopped => some (.terminate false)
  | _ => none

theorem markedHistory_eq_simulatorMarkAt (history : List (VisibleEvent I)) :
    markedHistory history = history.filterMap (simulatorMarkAt (historyWrite history)) := by
  unfold markedHistory
  apply List.filterMap_congr
  intro event _he
  cases event with
  | report stage truth serial =>
    cases hw : historyWrite history stage with
    | none => simp only [simulatorMarkAt, hw]
    | some pair => cases pair; simp only [simulatorMarkAt, hw]
  | observation | wrote | committed | executed | advanced | stopped | abandoned => rfl

theorem markedHistory_append_frame (before packet : List (VisibleEvent I))
    (hf : ∀ stage : I.Stage, historyWrite (before ++ packet) stage = historyWrite before stage) :
    markedHistory (before ++ packet) = markedHistory before ++
      packet.filterMap (simulatorMarkAt (historyWrite before)) := by
  have hfun := congrArg (simulatorMarkAt (I := I)) (funext hf)
  rw [markedHistory_eq_simulatorMarkAt, hfun, List.filterMap_append, ← markedHistory_eq_simulatorMarkAt]

theorem markedHistory_append_simulatorReviews (before : List (VisibleEvent I))
    (stage : I.Stage) (record : AuxiliaryRecord) :
    markedHistory (before ++ simulatorReviewPacket stage record) = markedHistory before := by
  rw [markedHistory_append_frame before (simulatorReviewPacket stage record)
    (fun other => historyWrite_append_simulatorReviews before stage other record)]
  simp [simulatorReviewPacket, List.filterMap_map, Function.comp_def, simulatorMarkAt]

theorem markedHistory_append_writeReport (before : List (VisibleEvent I))
    (stage : I.Stage) (bit truth : Bool) (serial : ℕ) (hnoreport : historyReport before stage = none) :
    markedHistory ((before ++ [.wrote stage bit serial]) ++ [.report stage truth serial]) =
      markedHistory before ++ [.writeError stage (bit != truth)] := by
  let after := (before ++ [.wrote stage bit serial]) ++ [.report stage truth serial]
  have hn : before.filterMap (eventReport stage) = [] := List.getLast?_eq_none_iff.mp hnoreport
  have hno := List.filterMap_eq_nil_iff.mp hn
  have hself : historyWrite after stage = some (bit, serial) := by
    rw [historyWrite_append_report, historyWrite_append_wrote_same]
  have hold : before.filterMap (simulatorMarkAt (historyWrite after)) = markedHistory before := by
    rw [markedHistory_eq_simulatorMarkAt]
    apply List.filterMap_congr
    intro event he
    cases event with
    | report other value previousSerial =>
      have hne : stage ≠ other := by
        intro h
        subst other
        have hh := hno (.report stage value previousSerial) he
        simp only [eventReport, ↓reduceIte, reduceCtorEq] at hh
      have hw : historyWrite after other = historyWrite before other := by
        rw [historyWrite_append_report, historyWrite_append_wrote_other before stage other hne]
      simp only [simulatorMarkAt, hw]
    | observation | wrote | committed | executed | advanced | stopped | abandoned => rfl
  rw [markedHistory_eq_simulatorMarkAt]
  change ((before ++ [VisibleEvent.wrote stage bit serial]) ++ [VisibleEvent.report stage truth serial]).filterMap
    (simulatorMarkAt (historyWrite after)) = _
  rw [List.filterMap_append, List.filterMap_append, hold]
  simp only [List.filterMap_cons, List.filterMap_nil, simulatorMarkAt, hself, ↓reduceIte,
    List.append_nil]

end PDROC

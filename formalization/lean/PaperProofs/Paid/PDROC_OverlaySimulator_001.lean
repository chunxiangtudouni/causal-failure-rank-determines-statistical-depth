module

public import PaperProofs.Paid.PDROC_CoordinateCoupling_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- Evaluated only after the real report. A false positive can change the
virtual truth, but never erases a genuine physical error. -/
def overlayReportTruth (actualWrite virtualWrite actualTruth mark : Bool) : Bool :=
  Bool.xor virtualWrite ((actualWrite != actualTruth) || mark)

theorem overlayReportTruth_error (actualWrite virtualWrite actualTruth mark : Bool) :
    (virtualWrite != overlayReportTruth actualWrite virtualWrite actualTruth mark) =
      ((actualWrite != actualTruth) || mark) := by
  cases actualWrite <;> cases virtualWrite <;> cases actualTruth <;> cases mark <;> decide

theorem overlayReportTruth_dominates (actualWrite virtualWrite actualTruth mark : Bool)
    (h : (actualWrite != actualTruth) = true) :
    (virtualWrite != overlayReportTruth actualWrite virtualWrite actualTruth mark) = true := by
  rw [overlayReportTruth_error, h]
  rfl

theorem overlayReportTruth_zeroMark (actualWrite virtualWrite actualTruth : Bool) :
    overlayReportTruth actualWrite virtualWrite actualTruth false =
      Bool.xor actualTruth (Bool.xor virtualWrite actualWrite) := by
  cases actualWrite <;> cases virtualWrite <;> cases actualTruth <;> decide

/-- Full Option-valued report identity with the actual and virtual serials.
The mark affects the report packet only after a genuine report is supplied. -/
theorem reportedWriteError_append_overlayReport
    (actual virtual : List (VisibleEvent I)) (stage : I.Stage)
    (actualWrite virtualWrite actualTruth mark : Bool) (actualSerial virtualSerial : ℕ)
    (ha : historyWrite actual stage = some (actualWrite, actualSerial))
    (hv : historyWrite virtual stage = some (virtualWrite, virtualSerial)) :
    reportedWriteError (virtual ++ [.report stage
      (overlayReportTruth actualWrite virtualWrite actualTruth mark) virtualSerial]) stage =
      (reportedWriteError (actual ++ [.report stage actualTruth actualSerial]) stage).map
        (fun error => error || mark) := by
  simp only [reportedWriteError, historyWrite_append_report_self,
    historyReport_append_report_self, hv, ha]
  change (if virtualSerial = virtualSerial then
    some (virtualWrite != overlayReportTruth actualWrite virtualWrite actualTruth mark) else none) =
      (if actualSerial = actualSerial then some (actualWrite != actualTruth) else none).map _
  rw [ite_eq_left rfl, ite_eq_left rfl, Option.map_some, overlayReportTruth_error]

/-- A real mismatch gives a valid virtual mismatch, with the virtual serial.
The converse is deliberately unavailable on false-positive branches. -/
theorem historyValidHandle_append_overlayReport
    (actual virtual : List (VisibleEvent I)) (stage : I.Stage)
    (actualWrite virtualWrite actualTruth mark : Bool) (actualSerial virtualSerial : ℕ)
    (ha : historyWrite actual stage = some (actualWrite, actualSerial))
    (hv : historyWrite virtual stage = some (virtualWrite, virtualSerial))
    (hactual : historyValidHandle (actual ++ [.report stage actualTruth actualSerial])
      ⟨stage, actualSerial⟩) :
    historyValidHandle (virtual ++ [.report stage
      (overlayReportTruth actualWrite virtualWrite actualTruth mark) virtualSerial])
      ⟨stage, virtualSerial⟩ := by
  cases actualWrite <;> cases virtualWrite <;> cases actualTruth <;> cases mark <;>
    simp_all [historyValidHandle, historyWritten, historyWriteSerial,
      historyWrite_append_report_self, historyReport_append_report_self, overlayReportTruth]

theorem historyUsed_subset_of_reservedPairs_sublist
    (actual virtual : List (VisibleEvent I))
    (h : (reservedPairs actual).Sublist (reservedPairs virtual)) :
    historyUsed actual ⊆ historyUsed virtual := by
  intro tool ht
  obtain ⟨pair, hp, he⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
  have hm : (pair.1.stage, pair.2) ∈ reservedPairs actual := List.mem_map.mpr ⟨pair, hp, rfl⟩
  obtain ⟨pair', hp', hpair⟩ := List.mem_map.mp (h.subset hm)
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨pair', hp', ?_⟩
  exact (congrArg Prod.snd hpair).trans he

/-- Permission transport for a physical allocation uses a REAL actual handle.
Virtual-only marks never satisfy this premise. Tool freshness is inherited
from the virtual ledger because physical reservations form a sublist. -/
theorem overlay_allocation_permission
    (actual virtual : List (VisibleEvent I)) (handle : MismatchHandle I) (tool : I.Tool)
    (hcursor : historyCursor actual = historyCursor virtual)
    (hreserved : (reservedPairs actual).Sublist (reservedPairs virtual))
    (hactual : historyValidHandle actual (reserialHandle actual handle))
    (hvirtual : historyAllowsAction virtual (.allocate handle tool)) :
    historyAllowsAction actual (.allocate (reserialHandle actual handle) tool) := by
  rcases hvirtual with ⟨hc, _, he, hf, hu⟩
  refine ⟨hcursor.trans hc, hactual, he, ?_, ?_⟩
  · exact fun ht => hf (historyUsed_subset_of_reservedPairs_sublist actual virtual hreserved ht)
  · intro pair hp
    have hm : (pair.1.stage, pair.2) ∈ reservedPairs actual := List.mem_map.mpr ⟨pair, hp, rfl⟩
    obtain ⟨pair', hp', heq⟩ := List.mem_map.mp (hreserved.subset hm)
    have hstage : pair'.1.stage = pair.1.stage := congrArg Prod.fst heq
    exact hstage ▸ hu pair' hp'

/-- A physical execute additionally needs the genuine physical reservation;
virtual membership alone cannot authorize a payment. -/
theorem overlay_execution_permission
    (actual virtual : List (VisibleEvent I)) (handle : MismatchHandle I) (tool : I.Tool)
    (hcursor : historyCursor actual = historyCursor virtual)
    (hexecuted : (executedPairs actual).Sublist (executedPairs virtual))
    (hactual : historyValidHandle actual (reserialHandle actual handle))
    (hreserved : (reserialHandle actual handle, tool) ∈ historyCommitments actual)
    (hvirtual : historyAllowsAction virtual (.execute handle tool)) :
    historyAllowsAction actual (.execute (reserialHandle actual handle) tool) := by
  rcases hvirtual with ⟨hc, _, he, _, hf, hu⟩
  refine ⟨hcursor.trans hc, hactual, he, hreserved, ?_, ?_⟩
  · intro pair hp
    have hm : (pair.1.stage, pair.2) ∈ executedPairs actual := List.mem_map.mpr ⟨pair, hp, rfl⟩
    obtain ⟨pair', hp', heq⟩ := List.mem_map.mp (hexecuted.subset hm)
    have ht : pair'.2 = pair.2 := congrArg (fun pair : I.Stage × I.Tool => pair.2) heq
    exact ht ▸ hf pair' hp'
  · intro pair hp
    have hm : (pair.1.stage, pair.2) ∈ executedPairs actual := List.mem_map.mpr ⟨pair, hp, rfl⟩
    obtain ⟨pair', hp', heq⟩ := List.mem_map.mp (hexecuted.subset hm)
    have hs : pair'.1.stage = pair.1.stage := congrArg Prod.fst heq
    exact hs ▸ hu pair' hp'

end PDROC

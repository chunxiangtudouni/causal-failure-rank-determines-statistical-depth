module

public import PaperProofs.Paid.RepresentationClaims
public import PaperProofs.Common.ReferenceController

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- Transport only the serial, reading the target's actual visible write. -/
def reserialHandle (target : List (VisibleEvent I)) (handle : MismatchHandle I) : MismatchHandle I :=
  ⟨handle.stage, historyWriteSerial target handle.stage⟩

@[simp] theorem reserialHandle_stage (target : List (VisibleEvent I)) (handle : MismatchHandle I) :
    (reserialHandle target handle).stage = handle.stage := rfl

@[simp] theorem reserialHandle_serial (target : List (VisibleEvent I)) (handle : MismatchHandle I) :
    (reserialHandle target handle).writeSerial = historyWriteSerial target handle.stage := rfl

theorem reserialHandle_roundtrip (original target : List (VisibleEvent I)) (handle : MismatchHandle I)
    (hserial : handle.writeSerial = historyWriteSerial original handle.stage) :
    reserialHandle original (reserialHandle target handle) = handle := by
  cases handle with
  | mk stage serial =>
    simp only [reserialHandle]
    congr
    exact hserial.symm

/-- Reports and guessed writes are handled by the simulator's own fold;
physical commitment/execution events only need their target serial changed. -/
def reserialHandleEvent (target : List (VisibleEvent I)) : VisibleEvent I → VisibleEvent I
  | .committed handle tool => .committed (reserialHandle target handle) tool
  | .executed handle tool => .executed (reserialHandle target handle) tool
  | event => event

theorem reservedPairs_reserial_singleton (target : List (VisibleEvent I)) (event : VisibleEvent I) :
    reservedPairs [reserialHandleEvent target event] = reservedPairs [event] := by
  cases event <;> rfl

theorem executedPairs_reserial_singleton (target : List (VisibleEvent I)) (event : VisibleEvent I) :
    executedPairs [reserialHandleEvent target event] = executedPairs [event] := by
  cases event <;> rfl

theorem reservedPairs_append (before after : List (VisibleEvent I)) :
    reservedPairs (before ++ after) = reservedPairs before ++ reservedPairs after := by
  simp only [reservedPairs, historyCommitments, List.filterMap_append, List.map_append]

theorem executedPairs_append (before after : List (VisibleEvent I)) :
    executedPairs (before ++ after) = executedPairs before ++ executedPairs after := by
  simp only [executedPairs, historyExecutions, List.filterMap_append, List.map_append]

theorem reservedPairs_reserial_map (target history : List (VisibleEvent I)) :
    reservedPairs (history.map (reserialHandleEvent target)) = reservedPairs history := by
  induction history with
  | nil => rfl
  | cons event history ih =>
    change reservedPairs ([reserialHandleEvent target event] ++ history.map (reserialHandleEvent target)) =
      reservedPairs ([event] ++ history)
    rw [reservedPairs_append, reservedPairs_append, reservedPairs_reserial_singleton, ih]

theorem executedPairs_reserial_map (target history : List (VisibleEvent I)) :
    executedPairs (history.map (reserialHandleEvent target)) = executedPairs history := by
  induction history with
  | nil => rfl
  | cons event history ih =>
    change executedPairs ([reserialHandleEvent target event] ++ history.map (reserialHandleEvent target)) =
      executedPairs ([event] ++ history)
    rw [executedPairs_append, executedPairs_append, executedPairs_reserial_singleton, ih]

theorem pairAlignment_append_reserial (actual virtual target : List (VisibleEvent I)) (event : VisibleEvent I)
    (hr : reservedPairs actual = reservedPairs virtual) (he : executedPairs actual = executedPairs virtual) :
    reservedPairs (actual ++ [event]) = reservedPairs (virtual ++ [reserialHandleEvent target event]) ∧
      executedPairs (actual ++ [event]) = executedPairs (virtual ++ [reserialHandleEvent target event]) := by
  constructor
  · rw [reservedPairs_append, reservedPairs_append, reservedPairs_reserial_singleton, hr]
  · rw [executedPairs_append, executedPairs_append, executedPairs_reserial_singleton, he]

/-- The fold's flip is virtualWrite xor actualWrite, determined before the
real report; only reported actualTruth is used to reconstruct virtualTruth. -/
theorem coordinateFlip_error_flag (actualWrite virtualWrite actualTruth : Bool) :
    (actualWrite != actualTruth) =
      (virtualWrite != Bool.xor actualTruth (Bool.xor virtualWrite actualWrite)) := by
  cases actualWrite <;> cases virtualWrite <;> cases actualTruth <;> decide

theorem historyWrite_append_report_self (history : List (VisibleEvent I)) (stage : I.Stage)
    (truth : Bool) (serial : ℕ) :
    historyWrite (history ++ [.report stage truth serial]) stage = historyWrite history stage := by
  simp only [historyWrite, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, eventWrite,
    List.append_nil]

theorem historyReport_append_report_self (history : List (VisibleEvent I)) (stage : I.Stage)
    (truth : Bool) (serial : ℕ) :
    historyReport (history ++ [.report stage truth serial]) stage = some (truth, serial) := by
  simp [historyReport, List.filterMap_append, eventReport]

/-- Exact original Option-valued reported error after the REAL report. It
allows different real/virtual write serials and retains each matching serial. -/
theorem reportedWriteError_append_coordinateReport
    (actual virtual : List (VisibleEvent I)) (stage : I.Stage)
    (actualWrite virtualWrite actualTruth : Bool) (actualSerial virtualSerial : ℕ)
    (ha : historyWrite actual stage = some (actualWrite, actualSerial))
    (hv : historyWrite virtual stage = some (virtualWrite, virtualSerial)) :
    reportedWriteError (actual ++ [.report stage actualTruth actualSerial]) stage =
      reportedWriteError (virtual ++ [.report stage
        (Bool.xor actualTruth (Bool.xor virtualWrite actualWrite)) virtualSerial]) stage := by
  simp only [reportedWriteError, historyWrite_append_report_self, historyReport_append_report_self, ha, hv]
  change (if actualSerial = actualSerial then some (actualWrite != actualTruth) else none) =
    (if virtualSerial = virtualSerial then some (virtualWrite != Bool.xor actualTruth (Bool.xor virtualWrite actualWrite)) else none)
  rw [ite_eq_left rfl, ite_eq_left rfl]
  exact congrArg some (coordinateFlip_error_flag actualWrite virtualWrite actualTruth)



/-- The actual genuine report-bound handle and its virtual counterpart have
identical observable validity, even though their write serials can differ. -/
theorem historyValidHandle_append_coordinateReport
    (actual virtual : List (VisibleEvent I)) (stage : I.Stage)
    (actualWrite virtualWrite actualTruth : Bool) (actualSerial virtualSerial : ℕ)
    (ha : historyWrite actual stage = some (actualWrite, actualSerial))
    (hv : historyWrite virtual stage = some (virtualWrite, virtualSerial)) :
    historyValidHandle (actual ++ [.report stage actualTruth actualSerial]) ⟨stage, actualSerial⟩ ↔
      historyValidHandle (virtual ++ [.report stage
        (Bool.xor actualTruth (Bool.xor virtualWrite actualWrite)) virtualSerial]) ⟨stage, virtualSerial⟩ := by
  cases actualWrite <;> cases virtualWrite <;> cases actualTruth <;>
    simp [historyValidHandle, historyWritten, historyWriteSerial, historyWrite_append_report_self,
      historyReport_append_report_self, ha, hv]

end PDROC

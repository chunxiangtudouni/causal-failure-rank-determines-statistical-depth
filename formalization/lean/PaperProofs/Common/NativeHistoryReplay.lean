module

public import PaperProofs.Common.NativeRelaxation

/-!
Public history queries for the actual Native reference controller. These are
finite list computations on existing VisibleEvent histories, not a new ledger,
world, or policy-performance record. Prefix alignment is proved from Step.
The controller rule and the identification with the posterior-test kernel are
not supplied by this module.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

def eventAction : VisibleEvent I → Option (Action I)
  | .observation i _ => some (.review i)
  | .wrote i bit _ => some (.write i bit)
  | .report _ _ _ => none
  | .committed handle tool => some (.allocate handle tool)
  | .executed handle tool => some (.execute handle tool)
  | .advanced i => some (.advance i)
  | .stopped => some .stop
  | .abandoned => some .abandon

def eventAdvance : VisibleEvent I → Option I.Stage
  | .advanced i => some i
  | _ => none

def eventObservation (i : I.Stage) : VisibleEvent I → Option ℕ
  | .observation j symbol => if j = i then some symbol else none
  | _ => none

def eventWrite (i : I.Stage) : VisibleEvent I → Option (Bool × ℕ)
  | .wrote j bit serial => if j = i then some (bit, serial) else none
  | _ => none

def eventReport (i : I.Stage) : VisibleEvent I → Option (Bool × ℕ)
  | .report j truth serial => if j = i then some (truth, serial) else none
  | _ => none

def eventCommitment : VisibleEvent I → Option (MismatchHandle I × I.Tool)
  | .committed handle tool => some (handle, tool)
  | _ => none

def eventExecution : VisibleEvent I → Option (MismatchHandle I × I.Tool)
  | .executed handle tool => some (handle, tool)
  | _ => none

def historyActions (history : List (VisibleEvent I)) : List (Action I) := history.filterMap eventAction
def historyCursor (history : List (VisibleEvent I)) : ℕ := (history.filterMap eventAdvance).length
def historyObservations (history : List (VisibleEvent I)) (i : I.Stage) : List ℕ :=
  history.filterMap (eventObservation i)
def historyWrite (history : List (VisibleEvent I)) (i : I.Stage) : Option (Bool × ℕ) :=
  (history.filterMap (eventWrite i)).getLast?
def historyWritten (history : List (VisibleEvent I)) (i : I.Stage) : Option Bool :=
  (historyWrite history i).map Prod.fst
def historyWriteSerial (history : List (VisibleEvent I)) (i : I.Stage) : ℕ :=
  ((historyWrite history i).map Prod.snd).getD 0
def historyReport (history : List (VisibleEvent I)) (i : I.Stage) : Option (Bool × ℕ) :=
  (history.filterMap (eventReport i)).getLast?
def historyCommitments (history : List (VisibleEvent I)) : List (MismatchHandle I × I.Tool) :=
  history.filterMap eventCommitment
def historyExecutions (history : List (VisibleEvent I)) : List (MismatchHandle I × I.Tool) :=
  history.filterMap eventExecution
def historyUsed (history : List (VisibleEvent I)) : Finset I.Tool :=
  ((historyCommitments history).map Prod.snd).toFinset
def historyHalted (history : List (VisibleEvent I)) : Bool :=
  (historyActions history).any fun action => match action with
    | .stop | .abandon => true
    | _ => false

private theorem filterMap_reportAll {A : Type*} (f : VisibleEvent I → Option A)
    (hreport : ∀ i truth serial, f (.report i truth serial) = none) (L : Ledger I) :
    (reportAll L).filterMap f = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro event hevent
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hevent
  exact hreport i (L.truth i) (L.writeSerial i)

private theorem filterMap_writeResponses {A : Type*} (f : VisibleEvent I → Option A)
    (hreport : ∀ i truth serial, f (.report i truth serial) = none)
    (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (writeResponses C s i bit).filterMap f = ([.wrote i bit s.clock]).filterMap f := by
  classical
  unfold writeResponses
  rw [List.filterMap_append]
  suffices htail : (if C.reporting = .early then
      [.report i ((writeLedger s i bit).truth i) s.clock]
    else if allWritten (writeLedger s i bit) then reportAll (writeLedger s i bit) else []).filterMap f = [] by
    rw [htail, List.append_nil]
  split_ifs
  · simp only [List.filterMap_cons, hreport, List.filterMap_nil]
  · exact filterMap_reportAll f hreport _
  · rfl

@[simp] private theorem reportedWrite_commitments (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s i bit).commitments = s.ledger.commitments := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

@[simp] private theorem reportedWrite_executions (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s i bit).executions = s.ledger.executions := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

@[simp] private theorem actions_writeResponses (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (writeResponses C s i bit).filterMap eventAction = [.write i bit] := by
  rw [filterMap_writeResponses eventAction (by intros; rfl)]
  rfl

@[simp] private theorem advances_writeResponses (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (writeResponses C s i bit).filterMap eventAdvance = [] := by
  rw [filterMap_writeResponses eventAdvance (by intros; rfl)]
  rfl

@[simp] private theorem commitments_writeResponses (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (writeResponses C s i bit).filterMap eventCommitment = [] := by
  rw [filterMap_writeResponses eventCommitment (by intros; rfl)]
  rfl

@[simp] private theorem executions_writeResponses (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (writeResponses C s i bit).filterMap eventExecution = [] := by
  rw [filterMap_writeResponses eventExecution (by intros; rfl)]
  rfl

@[simp] private theorem observations_writeResponses (C : Contract I) (s : State I)
    (i j : I.Stage) (bit : Bool) :
    (writeResponses C s i bit).filterMap (eventObservation j) = [] := by
  rw [filterMap_writeResponses (eventObservation j) (by intros; rfl)]
  rfl

@[simp] private theorem reportedWrite_written (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s i bit).written = Function.update s.ledger.written i (some bit) := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

@[simp] private theorem reportedWrite_serial (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s i bit).writeSerial = Function.update s.ledger.writeSerial i s.clock := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

@[simp] private theorem reportedWrite_reviews (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s i bit).reviews = s.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

theorem historyWrite_append_writeResponses (history : List (VisibleEvent I))
    (C : Contract I) (s : State I) (i j : I.Stage) (bit : Bool) :
    historyWrite (history ++ writeResponses C s i bit) j =
      if i = j then some (bit, s.clock) else historyWrite history j := by
  unfold historyWrite
  rw [List.filterMap_append, filterMap_writeResponses (eventWrite j) (by intros; rfl)]
  by_cases hij : i = j <;> simp [eventWrite, hij]

theorem prefix_historyActions_length (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    (historyActions s.history).length = s.clock := by
  induction hp with
  | initial => rfl
  | @next n s s' _ step ih =>
    simp only [historyActions] at ih ⊢
    generalize haction : policy seed s.history = action at step
    cases step <;>
      simp [record, stopState, List.filterMap_append, eventAction, ih]

theorem prefix_historyCursor (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    historyCursor s.history = s.cursor := by
  induction hp with
  | initial => rfl
  | @next n s s' _ step ih =>
    simp only [historyCursor] at ih ⊢
    generalize haction : policy seed s.history = action at step
    cases step <;>
      simp [record, stopState, List.filterMap_append, eventAdvance, ih]

theorem prefix_historyCommitments (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    historyCommitments s.history = s.ledger.commitments.map (fun a => (a.handle, a.tool)) := by
  induction hp with
  | initial => rfl
  | @next n s s' _ step ih =>
    simp only [historyCommitments] at ih ⊢
    generalize haction : policy seed s.history = action at step
    cases step <;>
      simp [record, stopState, List.filterMap_append, eventCommitment,
        reviewLedger, allocateLedger, executeLedger,
        advanceLedger, List.map_append, ih]

theorem prefix_historyExecutions (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    historyExecutions s.history = s.ledger.executions.map (fun e => (e.handle, e.tool)) := by
  induction hp with
  | initial => rfl
  | @next n s s' _ step ih =>
    simp only [historyExecutions] at ih ⊢
    generalize haction : policy seed s.history = action at step
    cases step <;>
      simp [record, stopState, List.filterMap_append, eventExecution,
        reviewLedger, allocateLedger, executeLedger,
        advanceLedger, List.map_append, ih]

theorem prefix_historyUsed (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    historyUsed s.history = (s.ledger.commitments.map (fun a => a.tool)).toFinset := by
  unfold historyUsed
  rw [prefix_historyCommitments input C mode accounting policy seed truth tapes hp, List.map_map]
  rfl

theorem prefix_historyWrite (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    ∀ i : I.Stage, historyWrite s.history i = (s.ledger.written i).map (fun bit => (bit, s.ledger.writeSerial i)) := by
  induction hp with
  | initial => intro i; rfl
  | @next n s s' _ step ih =>
    generalize haction : policy seed s.history = action at step
    cases step with
    | write i bit live port resources =>
      intro j
      change historyWrite (s.history ++ writeResponses C s i bit) j = _
      rw [historyWrite_append_writeResponses]
      by_cases hij : i = j
      · subst j
        simp [record]
      · have hji := Ne.symm hij
        simpa [record, hij, Function.update_of_ne hji] using ih j
    | review | allocate | execute | advance | stop | abandon =>
      intro i
      simpa [record, stopState, historyWrite, List.filterMap_append,
        eventWrite, reviewLedger, allocateLedger, executeLedger, advanceLedger] using ih i

theorem prefix_historyWritten (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) (i : I.Stage) :
    historyWritten s.history i = s.ledger.written i := by
  unfold historyWritten
  rw [prefix_historyWrite input C mode accounting policy seed truth tapes hp i]
  cases s.ledger.written i <;> rfl

theorem prefix_historyObservations_length (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    ∀ i : I.Stage, ((historyObservations s.history i).length : ℕ∞) = s.ledger.reviews i := by
  induction hp with
  | initial => intro i; rfl
  | @next n s s' _ step ih =>
    generalize haction : policy seed s.history = action at step
    cases step with
    | review j live port resources =>
      intro i
      by_cases hji : j = i
      · subst i
        simp [record, historyObservations, List.filterMap_append, eventObservation, reviewLedger,
          ← ih j]
      · have hij := Ne.symm hji
        simpa [record, historyObservations, List.filterMap_append, eventObservation, hji,
          reviewLedger, Function.update_of_ne hij] using ih i
    | write | allocate | execute | advance | stop | abandon =>
      intro i
      simpa [record, stopState, historyObservations, List.filterMap_append, List.filterMap_cons,
        eventObservation, allocateLedger, executeLedger, advanceLedger] using ih i

theorem prefix_historyWriteSerial (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    ∀ i : I.Stage, historyWriteSerial s.history i = s.ledger.writeSerial i := by
  induction hp with
  | initial => intro i; rfl
  | @next n s s' _ step ih =>
    generalize haction : policy seed s.history = action at step
    cases step with
    | write i bit live port resources =>
      intro j
      change ((historyWrite (s.history ++ writeResponses C s i bit) j).map Prod.snd).getD 0 = _
      rw [historyWrite_append_writeResponses]
      by_cases hij : i = j
      · subst j
        simp [record]
      · have hji := Ne.symm hij
        simpa [record, historyWriteSerial, hij, Function.update_of_ne hji] using ih j
    | review | allocate | execute | advance | stop | abandon =>
      intro i
      simpa [record, stopState, historyWriteSerial, historyWrite, List.filterMap_append,
        eventWrite, reviewLedger, allocateLedger, executeLedger, advanceLedger] using ih i

theorem prefix_historyHalted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    historyHalted s.history = s.halted := by
  induction hp with
  | initial => rfl
  | @next n s s' _ step ih =>
    have hactive := step_source_active input C mode accounting tapes step
    simp only [historyHalted, historyActions] at ih ⊢
    generalize haction : policy seed s.history = action at step
    cases step <;>
      simp [record, stopState, List.filterMap_append, eventAction, ih, hactive]

/-- This controller needs early reports. The query preserves the report's old
write serial; its timestamp is not reconstructed from that serial. -/
theorem prefix_historyReport_early (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    ∀ i : I.Stage, historyReport s.history i =
      (s.ledger.reportTime i).map (fun _ => (s.ledger.truth i, s.ledger.writeSerial i)) := by
  induction hp with
  | initial => intro i; rfl
  | @next n s s' _ step ih =>
    generalize haction : policy seed s.history = action at step
    cases step with
    | write j bit live port resources =>
      intro i
      by_cases hji : j = i
      · subst i
        simp [record, historyReport, List.filterMap_append, List.filterMap_cons, eventReport,
          writeResponses, reportedWriteLedger, hearly, writeLedger]
      · have hij := Ne.symm hji
        simpa [record, historyReport, List.filterMap_append, List.filterMap_cons, eventReport,
          writeResponses, reportedWriteLedger, hearly, writeLedger, hji,
          Function.update_of_ne hij] using ih i
    | review | allocate | execute | advance | stop | abandon =>
      intro i
      simpa [record, stopState, historyReport, List.filterMap_append, List.filterMap_cons,
        eventReport, reviewLedger, allocateLedger, executeLedger, advanceLedger] using ih i

/-- The visible used-tool set supplies exactly the Native unused-allocation
guard. Its definition only reads committed responses in the history. -/
theorem prefix_historyUnused_iff (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) (tool : I.Tool) :
    tool ∉ historyUsed s.history ↔ ∀ a ∈ s.ledger.commitments, a.tool ≠ tool := by
  rw [prefix_historyUsed input C mode accounting policy seed truth tapes hp]
  simp only [List.mem_toFinset, List.mem_map, not_exists, not_and]

end PaperProofs.Common.Native

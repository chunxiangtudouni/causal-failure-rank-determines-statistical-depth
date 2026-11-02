module

public import PaperProofs.Paid.PA17_D31Witness_001
public import PaperProofs.Paid.PA17_D31Witness_Guard_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Paid.PA17D31WitnessNonbinding006

open Common Common.Native MeasureTheory
open PA17D31Witness001 PA17D31WitnessGuard002

theorem currentBranch_allows (P : Parameters)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (hcursor : historyCursor history = stage.val) :
    mixedAllows history (match historyWrite history stage with
    | none => .write stage false
    | some _ =>
        if historyValidHandle history ⟨stage, historyWriteSerial history stage⟩ ∧
            ¬ (historyCommitments history).any (fun pair => pair.1.stage == stage) then
          match blindUnusedTool P history with
          | some tool => .allocate ⟨stage, historyWriteSerial history stage⟩ tool
          | none => .advance stage
        else .advance stage) := by
  cases hw : historyWrite history stage with
  | none => exact ⟨hcursor, by simp only [historyWritten, hw, Option.map_none]⟩
  | some pair =>
    have hwritten : historyWritten history stage ≠ none := by
      intro hnone
      have hnone' : some pair.1 = (none : Option Bool) := by
        simpa only [historyWritten, hw, Option.map_some] using hnone
      cases hnone'
    change mixedAllows history (if
      historyValidHandle history ⟨stage, historyWriteSerial history stage⟩ ∧
        ¬ (historyCommitments history).any (fun pair => pair.1.stage == stage) then
      match blindUnusedTool P history with
      | some tool => .allocate ⟨stage, historyWriteSerial history stage⟩ tool
      | none => .advance stage
      else .advance stage)
    by_cases hrepair : historyValidHandle history ⟨stage, historyWriteSerial history stage⟩ ∧
        ¬ (historyCommitments history).any (fun pair => pair.1.stage == stage)
    · rw [ite_eq_left hrepair]
      cases htool : blindUnusedTool P history with
      | some tool =>
        change historyCursor history = stage.val ∧
          historyValidHandle history ⟨stage, historyWriteSerial history stage⟩ ∧
          tool ∈ P.sharedInstance.eligible stage ∧ tool ∉ historyUsed history ∧
          ∀ pair ∈ historyCommitments history, pair.1.stage ≠ stage
        refine ⟨hcursor, hrepair.1, ?_, ?_, ?_⟩
        · rw [P.eligible_eq_univ]
          exact Finset.mem_univ tool
        · change (List.finRange P.tools).find?
            (fun selected : P.sharedInstance.Tool => decide (selected ∉ historyUsed history)) = some tool at htool
          have hfound : decide (tool ∉ historyUsed history) = true :=
            List.find?_some (p := fun selected : P.sharedInstance.Tool =>
              decide (selected ∉ historyUsed history)) htool
          exact of_decide_eq_true hfound
        · intro pair hpair heq
          apply hrepair.2
          exact List.any_eq_true.mpr ⟨pair, hpair, by simpa only [beq_iff_eq] using heq⟩
      | none => exact ⟨hcursor, hwritten⟩
    · rw [ite_eq_right hrepair]
      exact ⟨hcursor, hwritten⟩

theorem pendingExecution_allows (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*}
    (rule : PolicyRule P.sharedInstance Seed) (seed : Seed)
    (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C .uncapped accounting rule seed truth tapes n s)
    (pair : MismatchHandle P.sharedInstance × P.sharedInstance.Tool)
    (hfind : (historyCommitments s.history).find? (fun pair =>
      !(historyExecutions s.history).any (fun e => e.1.stage == pair.1.stage)) = some pair) :
    mixedAllows s.history (.execute pair.1 pair.2) := by
  have hmem := List.mem_of_find?_eq_some hfind
  have hkeep := List.find?_some hfind
  have hnotstage : ∀ e ∈ historyExecutions s.history, e.1.stage ≠ pair.1.stage := by
    intro e he heq
    have hany : (historyExecutions s.history).any
        (fun e => e.1.stage == pair.1.stage) = true :=
      List.any_eq_true.mpr ⟨e, he, by simpa only [beq_iff_eq] using heq⟩
    simp only [hany, Bool.not_true, Bool.false_eq_true] at hkeep
  rw [prefix_historyCommitments (P.input fee hfee) C .uncapped accounting
    rule seed truth tapes hp] at hmem
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmem
  have hinv := prefix_invariant (P.input fee hfee) C .uncapped accounting
    rule seed truth tapes hp
  have hv : validHandle s a.handle := by
    refine ⟨(hinv.commitment_genuine a ha).1, (hinv.commitment_genuine a ha).2, ?_⟩
    obtain ⟨time, ht, _⟩ := hinv.wellFormed.reported a ha
    exact ⟨time, ht⟩
  refine ⟨Retained.PRetRetainedGuard007.historyValidHandle_complete
    (P.input fee hfee) C hearly .uncapped accounting rule seed truth tapes hp a.handle hv,
    ?_, ?_, ?_, hnotstage⟩
  · rw [P.eligible_eq_univ]
    exact Finset.mem_univ a.tool
  · rw [prefix_historyCommitments (P.input fee hfee) C .uncapped accounting
      rule seed truth tapes hp]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  · intro pair hpair htool
    rw [prefix_historyExecutions (P.input fee hfee) C .uncapped accounting
      rule seed truth tapes hp] at hpair
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpair
    obtain ⟨b, hb, hhandle, htool', _⟩ := hinv.wellFormed.backed e he
    have hba : b = a := List.inj_on_of_nodup_map hinv.wellFormed.commitment_tools
      hb ha (htool'.trans htool)
    apply hnotstage (e.handle, e.tool)
    · rw [prefix_historyExecutions (P.input fee hfee) C .uncapped accounting
        rule seed truth tapes hp]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    · exact (congrArg (fun handle : MismatchHandle P.sharedInstance => handle.stage)
        hhandle.symm).trans (congrArg (fun c : Commitment P.sharedInstance => c.handle.stage) hba)

theorem blindCandidate_allows (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*}
    (rule : PolicyRule P.sharedInstance Seed) (seed : Seed)
    (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C .uncapped accounting rule seed truth tapes n s) :
    mixedAllows s.history (blindCandidate P () s.history) := by
  unfold blindCandidate
  split
  · trivial
  · split
    · rename_i hstage
      exact currentBranch_allows P s.history
        ⟨historyCursor s.history, by simpa only [Parameters.sharedInstance,
          List.length_replicate] using hstage⟩ rfl
    · split
      · split
        · trivial
        · split
          · rename_i pair hfind
            exact pendingExecution_allows P fee hfee C hearly accounting
              rule seed truth tapes hp pair hfind
          · trivial
      · trivial

theorem blindCandidate_ne_abandon_of_cursor_le (P : Parameters) (seed : Unit)
    (history : List (VisibleEvent P.sharedInstance))
    (hcursor : historyCursor history ≤ P.certificate.stages) :
    blindCandidate P seed history ≠ .abandon := by
  unfold blindCandidate
  split
  · simp
  · split
    · dsimp only
      split
      · simp
      · split
        · split <;> simp
        · simp
    · split
      · split
        · simp
        · split <;> simp
      · omega

theorem blindCandidate_ne_abandon (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract P.sharedInstance) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} (rule : PolicyRule P.sharedInstance Seed) (seed : Seed)
    (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C .uncapped accounting rule seed truth tapes n s) :
    blindCandidate P () s.history ≠ .abandon := by
  apply blindCandidate_ne_abandon_of_cursor_le
  rw [prefix_historyCursor (P.input fee hfee) C .uncapped accounting rule seed truth tapes hp]
  simpa only [P.stageCount_eq] using
    (prefix_cursorInvariant (P.input fee hfee) C .uncapped accounting rule seed truth tapes hp).bound

theorem blindCandidate_guard_nonbinding (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*}
    (rule : PolicyRule P.sharedInstance Seed) (seed : Seed)
    (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C .uncapped accounting rule seed truth tapes n s) :
    mixedGuarded (blindCandidate P) () s.history = blindCandidate P () s.history := by
  exact ite_eq_left (blindCandidate_allows P fee hfee C hearly accounting
    rule seed truth tapes hp)

theorem blindCandidate_allowed (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) {Seed : Type*} (rule : PolicyRule P.sharedInstance Seed)
    (seed : Seed) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .uncapped
      (blindCallAccounting P.sharedInstance) rule seed truth tapes n s) (rawSeed : Unit) :
    mixedAllows s.history (blindCandidate P rawSeed s.history) := by
  cases rawSeed
  exact blindCandidate_allows P fee hfee (P.retainedPaymentExampleContract allocation)
    rfl (blindCallAccounting P.sharedInstance) rule seed truth tapes hp

end PaperProofs.Paid.PA17D31WitnessNonbinding006

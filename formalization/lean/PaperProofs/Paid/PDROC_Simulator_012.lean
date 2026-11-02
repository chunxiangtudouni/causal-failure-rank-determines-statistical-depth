module

public import PaperProofs.Paid.PDROC_Simulator_011

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance}

def simulatorReviewStateFrom (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (tape : (input.experiment stage).Tape) (s : State I) : ℕ → State I
  | 0 => s
  | n + 1 =>
      let before := simulatorReviewStateFrom input accounting stage tape s n
      record accounting before (.review stage) [.observation stage (tape n).val]
        (reviewLedger before stage) before.cursor false

theorem simulatorReviewStateFrom_cursor (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (tape : (input.experiment stage).Tape) (s : State I) (n : ℕ) :
    (simulatorReviewStateFrom input accounting stage tape s n).cursor = s.cursor := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem simulatorReviewStateFrom_active (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (tape : (input.experiment stage).Tape) (s : State I) (n : ℕ) (ha : s.halted = false) :
    (simulatorReviewStateFrom input accounting stage tape s n).halted = false := by
  cases n with
  | zero => exact ha
  | succ => rfl

theorem simulatorReviewStateFrom_written (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (tape : (input.experiment stage).Tape) (s : State I) (n : ℕ) :
    (simulatorReviewStateFrom input accounting stage tape s n).ledger.written = s.ledger.written := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem simulatorReviewStateFrom_reviews (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (tape : (input.experiment stage).Tape) (s : State I) (n : ℕ)
    (hz : s.ledger.reviews stage = 0) :
    (simulatorReviewStateFrom input accounting stage tape s n).ledger.reviews stage = (n : ℕ∞) := by
  induction n with
  | zero => exact hz
  | succ n ih => simp only [simulatorReviewStateFrom, record, reviewLedger, Function.update_self,
      ih, Nat.cast_add, Nat.cast_one]

theorem simulatorReviewStateFrom_history (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (tape : (input.experiment stage).Tape) (s : State I) (n : ℕ) :
    (simulatorReviewStateFrom input accounting stage tape s n).history =
      s.history ++ headReviewHistory input stage tape n := by
  induction n with
  | zero => simp only [simulatorReviewStateFrom, headReviewHistory, List.ofFn_zero, List.append_nil]
  | succ n ih => simp only [simulatorReviewStateFrom, record, ih, headReviewHistory_succ, List.append_assoc]

variable {Seed : Type u}

/-- The actual Native interpreter, at every prewrite clock, executes the
same physical reviews as the original endpoint experiment. Conditions are
the concrete fresh-entry fields and selected record, not a performance field. -/
theorem simulator_run_eq_reviewStateFrom (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (stage : P.sharedInstance.Stage) (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (ha : (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start).halted = false)
    (hc : (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start).cursor = stage.val)
    (hw : (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start).ledger.written stage = none)
    (hr : (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start).ledger.reviews stage = 0)
    (ho : historyObservations (run (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) (seed, world) start).history stage = [])
    (hdraw : simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed (run (P.input fee hfee) C.val .uncapped accounting
        (simulatorRule P fee hfee source) (seed, world) start).history) = some draw)
    (hd : draw.record.decision = some decision) (n : ℕ)
    (hn : (n : ℕ∞) ≤ (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage)
      (worldTapes (P.input fee hfee) world stage)) :
    run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) (start + n) =
      simulatorReviewStateFrom (P.input fee hfee) accounting stage (worldTapes (P.input fee hfee) world stage)
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start) n := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let s := run input C.val .uncapped accounting actual (seed, world) start
  let tape := worldTapes input world stage
  obtain ⟨k, _hk, hprefix⟩ := run_has_prefix input C.val .uncapped accounting actual
    (simulatorRule_legal P fee hfee C accounting source) (seed, world) start
  have hhh : historyHalted s.history = false :=
    (prefix_historyHalted input C.val .uncapped accounting actual seed _ _ hprefix).trans ha
  have hhc : historyCursor s.history = stage.val :=
    (prefix_historyCursor input C.val .uncapped accounting actual seed _ _ hprefix).trans hc
  have hhw : historyWritten s.history stage = none :=
    (prefix_historyWritten input C.val .uncapped accounting actual seed _ _ hprefix stage).trans hw
  induction n with
  | zero => rfl
  | succ n ih =>
    have hle : (n : ℕ∞) ≤ (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage) tape :=
      (show (n : ℕ∞) ≤ (n + 1 : ℕ∞) from by exact_mod_cast Nat.le_succ n).trans hn
    have hbefore : (n : ℕ∞) < (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage) tape :=
      (show (n : ℕ∞) < (n + 1 : ℕ∞) from by exact_mod_cast Nat.lt_succ_self n).trans_le hn
    have heq := ih hle
    let before := simulatorReviewStateFrom input accounting stage tape s n
    have heq' : run input C.val .uncapped accounting actual (seed, world) (start + n) = before := heq
    have hbactive : before.halted = false := simulatorReviewStateFrom_active input accounting stage tape s n ha
    have haction : actual seed before.history = .review stage := by
      rw [simulatorReviewStateFrom_history]
      exact simulatorRule_on_endpoint_word_before P fee hfee source seed s.history stage draw decision
        hhh hhc hhw ho hdraw hd tape n hbefore
    have hstep : Step input C.val .uncapped accounting (worldTapes input world) before (.review stage)
        (simulatorReviewStateFrom input accounting stage tape s (n + 1)) := by
      have hwb : before.ledger.written stage = none :=
        (congrFun (simulatorReviewStateFrom_written input accounting stage tape s n) stage).trans hw
      have h := Step.review (input := input) (C := C.val) (mode := ResourceMode.uncapped)
        (accounting := accounting) (tapes := worldTapes input world) before stage
        ⟨hbactive, (simulatorReviewStateFrom_cursor input accounting stage tape s n).trans hc⟩
        hwb (Or.inl rfl)
      have hcount : before.ledger.reviews stage = (n : ℕ∞) :=
        simulatorReviewStateFrom_reviews input accounting stage tape s n hr
      change Step input C.val .uncapped accounting (worldTapes input world) before (.review stage)
        (record accounting before (.review stage) [.observation stage (tape n).val]
          (reviewLedger before stage) before.cursor false)
      simpa only [hcount, ENat.toNat_natCast] using h
    rw [Nat.add_succ]
    apply run_succ_of_step input C.val .uncapped accounting actual (seed, world) (start + n) _
    · exact (congrArg State.halted heq').trans hbactive
    · rw [heq', haction]
      exact hstep

end PDROC

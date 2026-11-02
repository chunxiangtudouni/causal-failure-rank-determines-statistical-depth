module

public import PaperProofs.Common.NativeHistoryReplay
public import PaperProofs.Statistics.PosteriorSPRT

/-!
The word actually observed by an arbitrary Native prefix. The parser continues
to read only VisibleEvent histories. Tapes occur in the correctness theorem as
the existing system input, never as an additional policy argument. No success
condition or resource relaxation is used in the word correspondence.
-/

@[expose] public section

open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

private theorem observations_reportAll (L : Ledger I) (i : I.Stage) :
    (reportAll L).filterMap (eventObservation i) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro event hevent
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hevent
  rfl

private theorem observations_writeResponses (C : Contract I) (s : State I)
    (i j : I.Stage) (bit : Bool) :
    (writeResponses C s i bit).filterMap (eventObservation j) = [] := by
  classical
  simp only [writeResponses, List.filterMap_append]
  split_ifs
  · simp only [List.filterMap_cons, eventObservation, List.filterMap_nil, List.nil_append]
  · simp only [List.filterMap_cons, eventObservation, List.filterMap_nil, List.nil_append,
      observations_reportAll]
  · rfl

private theorem reportedWrite_reviews (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s i bit).reviews = s.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

theorem prefix_reviews_ne_top (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) (i : I.Stage) :
    s.ledger.reviews i ≠ ⊤ := by
  rw [← prefix_historyObservations_length input C mode accounting policy seed truth tapes hp i]
  exact ENat.natCast_ne_top _

theorem prefix_historyObservations_length_toNat (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) (i : I.Stage) :
    (historyObservations s.history i).length = (s.ledger.reviews i).toNat := by
  rw [← prefix_historyObservations_length input C mode accounting policy seed truth tapes hp i,
    ENat.toNat_natCast]

theorem prefix_historyObservations_eq_rangeMap (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    ∀ i : I.Stage, historyObservations s.history i =
      (List.range (s.ledger.reviews i).toNat).map (fun k => (tapes i k).val) := by
  induction hp with
  | initial => intro i; rfl
  | @next n s s' earlier step ih =>
    generalize haction : policy seed s.history = action at step
    cases step with
    | review j live port resources =>
      intro i
      by_cases hji : j = i
      · subst i
        have hfinite := prefix_reviews_ne_top input C mode accounting policy seed truth tapes earlier j
        have hsucc : (s.ledger.reviews j + 1).toNat = (s.ledger.reviews j).toNat + 1 := by
          rw [ENat.toNat_add hfinite (by simp)]
          rfl
        simp only [record, reviewLedger, Function.update_self]
        change historyObservations
          (s.history ++ [.observation j (tapes j (s.ledger.reviews j).toNat).val]) j =
          (List.range (s.ledger.reviews j + 1).toNat).map (fun k => (tapes j k).val)
        simp only [historyObservations, List.filterMap_append]
        rw [show ([.observation j (tapes j (s.ledger.reviews j).toNat).val] : List (VisibleEvent I)).filterMap
          (eventObservation j) = [(tapes j (s.ledger.reviews j).toNat).val] by simp [eventObservation]]
        rw [hsucc, List.range_succ, List.map_append, List.map_singleton]
        simpa only [historyObservations] using
          congrArg (fun word => word ++ [(tapes j (s.ledger.reviews j).toNat).val]) (ih j)
      · have hij := Ne.symm hji
        simpa [record, historyObservations, List.filterMap_append, eventObservation, hji,
          reviewLedger, Function.update_of_ne hij] using ih i
    | write =>
      intro i
      simpa only [record, historyObservations, List.filterMap_append, observations_writeResponses,
        List.append_nil, reportedWrite_reviews] using ih i
    | allocate | execute | advance | stop | abandon =>
      intro i
      simpa [record, stopState, historyObservations, List.filterMap_append, List.filterMap_cons,
        eventObservation, allocateLedger, executeLedger, advanceLedger] using ih i

private theorem map_range_eq_ofFn {A : Type*} (f : ℕ → A) (r : ℕ) :
    (List.range r).map f = List.ofFn (fun k : Fin r => f k.val) := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    simp

/-- All observations, including those charged on subsequently failing paths,
are exactly the original tape prefix. The finite count is proved before toNat. -/
theorem prefix_historyObservations_eq_tapeWord (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) (i : I.Stage) :
    historyObservations s.history i =
      List.ofFn (fun k : Fin (s.ledger.reviews i).toNat => (tapes i k.val).val) := by
  rw [prefix_historyObservations_eq_rangeMap input C mode accounting policy seed truth tapes hp i]
  exact map_range_eq_ofFn _ _

theorem prefix_historyObservation_getElem (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (i : I.Stage) (k : ℕ) (hk : k < (historyObservations s.history i).length) :
    (historyObservations s.history i)[k] = (tapes i k).val := by
  have hword := prefix_historyObservations_eq_tapeWord input C mode accounting policy seed truth tapes hp i
  have hget := congrArg (fun word : List ℕ => word[k]?) hword
  have hk' : k < (s.ledger.reviews i).toNat := by
    simpa only [hword, List.length_ofFn] using hk
  have hright : (List.ofFn (fun k : Fin (s.ledger.reviews i).toNat => (tapes i k.val).val))[k]? =
      some (tapes i k).val := by simp [hk']
  rw [List.getElem?_eq_getElem hk, hright] at hget
  exact Option.some.inj hget

theorem prefix_historyObservation_alphabet (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (i : I.Stage) (symbol : ℕ) (hmem : symbol ∈ historyObservations s.history i) :
    symbol < (input.experiment i).alphabetSize := by
  rw [prefix_historyObservations_eq_tapeWord input C mode accounting policy seed truth tapes hp i] at hmem
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hmem
  exact (tapes i k.val).isLt

/-- A validated finite history word. Validation concerns only the finite
visible list and the known alphabet size; the proof is erased at execution. -/
def historyObservationWord (input : StatisticalInput I) (history : List (VisibleEvent I)) (i : I.Stage)
    (hvalid : ∀ symbol ∈ historyObservations history i, symbol < (input.experiment i).alphabetSize) :
    (input.experiment i).StoppedWord :=
  ⟨(historyObservations history i).length, fun k =>
    ⟨(historyObservations history i)[k.val], hvalid _ (List.getElem_mem k.isLt)⟩⟩

theorem prefix_historyObservationWord_apply (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) (i : I.Stage)
    (hvalid : ∀ symbol ∈ historyObservations s.history i, symbol < (input.experiment i).alphabetSize)
    (k : Fin (historyObservations s.history i).length) :
    (historyObservationWord input s.history i hvalid).2 k = tapes i k.val := by
  apply Fin.ext
  exact prefix_historyObservation_getElem input C mode accounting policy seed truth tapes hp i k.val k.isLt

end PaperProofs.Common.Native

namespace PaperProofs.Statistics.BinaryExperiment

open scoped BigOperators

/-- Executable finite-word posterior odds. This uses rational products only. -/
def rationalWordOdds (E : BinaryExperiment) (word : E.StoppedWord) : ℚ :=
  E.prior true * (∏ k : Fin word.1, E.channel true (word.2 k) / E.channel false (word.2 k)) /
    E.prior false

theorem rationalWordOdds_pos (E : BinaryExperiment) (word : E.StoppedWord) :
    0 < E.rationalWordOdds word := by
  exact div_pos (mul_pos (E.prior_pos' true) (Finset.prod_pos fun k _ =>
    div_pos (E.channel_pos true (word.2 k)) (E.channel_pos false (word.2 k)))) (E.prior_pos' false)

theorem rationalWordOdds_cast (E : BinaryExperiment) (word : E.StoppedWord) :
    (E.rationalWordOdds word : ℝ) =
      E.priorReal true * E.wordLikelihood true word / E.priorReal false := by
  simp [rationalWordOdds, priorReal, wordLikelihood, channelReal]

theorem log_rationalWordOdds (E : BinaryExperiment) (word : E.StoppedWord) :
    Real.log (E.rationalWordOdds word : ℝ) = E.stoppedWordScore word := by
  rw [E.rationalWordOdds_cast, E.stoppedWordScore_eq_log_odds]

/-- Inclusive boundary comparisons, including a hit with no observations. -/
def rationalWordHits (E : BinaryExperiment) (p : ℚ) (word : E.StoppedWord) : Bool :=
  decide (E.rationalWordOdds word ≤ p / (1 - p) ∨ (1 - p) / p ≤ E.rationalWordOdds word)

def rationalWordMAP (E : BinaryExperiment) (word : E.StoppedWord) : Bool :=
  decide (1 ≤ E.rationalWordOdds word)

theorem rationalWordHits_iff (E : BinaryExperiment) (p : ℚ) (hp : 0 < p) (hpone : p < 1)
    (word : E.StoppedWord) :
    E.rationalWordHits p word = true ↔
      Real.log ((1 - (p : ℝ)) / (p : ℝ)) ≤ |E.stoppedWordScore word| := by
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
  have honeReal : (p : ℝ) < 1 := by exact_mod_cast hpone
  have hboundary : 0 < (1 - (p : ℝ)) / (p : ℝ) := div_pos (sub_pos.mpr honeReal) hpReal
  have hodds : 0 < (E.rationalWordOdds word : ℝ) := by exact_mod_cast E.rationalWordOdds_pos word
  rw [rationalWordHits, decide_eq_true_eq, ← E.log_rationalWordOdds, le_abs',
    ← Real.log_inv ((1 - (p : ℝ)) / (p : ℝ)),
    Real.log_le_log_iff hodds (inv_pos.mpr hboundary), Real.log_le_log_iff hboundary hodds]
  rw [inv_div]
  norm_cast

theorem rationalWordMAP_eq_recordDecision (E : BinaryExperiment) (word : E.StoppedWord) :
    E.rationalWordMAP word = E.posteriorRecordDecision ((), word) := by
  have hodds : 0 < (E.rationalWordOdds word : ℝ) := by exact_mod_cast E.rationalWordOdds_pos word
  have hmap : (1 ≤ E.rationalWordOdds word) ↔ 0 ≤ E.stoppedWordScore word := by
    rw [← E.log_rationalWordOdds, Real.log_nonneg_iff hodds]
    norm_cast
  change decide (1 ≤ E.rationalWordOdds word) = decide (0 ≤ E.stoppedWordScore word)
  exact decide_eq_decide.mpr hmap

theorem stoppedWordScore_prefix (E : BinaryExperiment) (tape : E.Tape) (n : ℕ) :
    E.stoppedWordScore ⟨n, fun k => tape k.val⟩ = E.logOddsScore tape n := by
  unfold stoppedWordScore wordLogLikelihood logOddsScore
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun k => Real.log (E.channelReal true (tape k) / E.channelReal false (tape k))) n

theorem stoppedWordScore_eq_of_word_prefix (E : BinaryExperiment) (word : E.StoppedWord) (tape : E.Tape)
    (hword : ∀ k : Fin word.1, word.2 k = tape k.val) :
    E.stoppedWordScore word = E.logOddsScore tape word.1 := by
  unfold stoppedWordScore wordLogLikelihood logOddsScore
  congr 1
  calc
    _ = ∑ k : Fin word.1, Real.log (E.channelReal true (tape k.val) / E.channelReal false (tape k.val)) :=
      Finset.sum_congr rfl (fun k _ => by simp only [hword k, Bool.not_true])
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun k => Real.log (E.channelReal true (tape k) / E.channelReal false (tape k))) word.1

/-- The real first-exit test is exactly the executable rational test on one
of the finite prefixes, with the endpoint n included. -/
theorem posteriorThresholdStop_le_iff_rationalHit (E : BinaryExperiment) (p : ℚ)
    (hp : 0 < p) (hpone : p < 1) (tape : E.Tape) (n : ℕ) :
    E.posteriorThresholdStop p tape ≤ n ↔
      ∃ k ≤ n, E.rationalWordHits p ⟨k, fun j => tape j.val⟩ = true := by
  rw [E.posteriorThresholdStop_le_iff]
  constructor <;> rintro ⟨k, hkn, hhit⟩ <;> refine ⟨k, hkn, ?_⟩
  · exact (E.rationalWordHits_iff p hp hpone _).mpr ((E.stoppedWordScore_prefix tape k).symm ▸ hhit)
  · simpa only [E.stoppedWordScore_prefix] using (E.rationalWordHits_iff p hp hpone _).mp hhit

theorem posteriorThresholdStop_zero_iff_rationalHit (E : BinaryExperiment) (p : ℚ)
    (hp : 0 < p) (hpone : p < 1) (tape : E.Tape) :
    E.posteriorThresholdStop p tape = 0 ↔
      E.rationalWordHits p ⟨0, fun j => tape j.val⟩ = true := by
  rw [← nonpos_iff_eq_zero, ← Nat.cast_zero, E.posteriorThresholdStop_le_iff_rationalHit p hp hpone]
  simp

/-- Hitting at the quota is a permitted stop; overflow uses the strict event Q<T. -/
theorem rationalHit_at_quota (E : BinaryExperiment) (p : ℚ) (hp : 0 < p) (hpone : p < 1)
    (tape : E.Tape) (quota : ℕ) (hstop : E.posteriorThresholdStop p tape = quota) :
    E.rationalWordHits p ⟨quota, fun j => tape j.val⟩ = true := by
  apply (E.rationalWordHits_iff p hp hpone _).mpr
  rw [E.stoppedWordScore_prefix]
  exact E.posteriorThresholdStop_hits p tape quota hstop

theorem rationalWordMAP_at_stop (E : BinaryExperiment) (p : ℚ) (tape : E.Tape)
    (n : ℕ) (hstop : E.posteriorThresholdStop p tape = n) :
    E.rationalWordMAP ⟨n, fun k => tape k.val⟩ = (E.posteriorSPRT p).rule.decision () tape := by
  rw [E.rationalWordMAP_eq_recordDecision]
  change decide (0 ≤ E.stoppedWordScore ⟨n, fun k => tape k.val⟩) =
    decide (0 ≤ E.logOddsScore tape (E.posteriorThresholdStop p tape).toNat)
  rw [E.stoppedWordScore_prefix, hstop, ENat.toNat_natCast]

end PaperProofs.Statistics.BinaryExperiment

namespace PaperProofs.Common.Native

variable {I : Instance}

theorem prefix_historyObservationWord_score (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) (i : I.Stage)
    (hvalid : ∀ symbol ∈ historyObservations s.history i, symbol < (input.experiment i).alphabetSize) :
    (input.experiment i).stoppedWordScore (historyObservationWord input s.history i hvalid) =
      (input.experiment i).logOddsScore (tapes i) (s.ledger.reviews i).toNat := by
  rw [(input.experiment i).stoppedWordScore_eq_of_word_prefix _ (tapes i)
    (prefix_historyObservationWord_apply input C mode accounting policy seed truth tapes hp i hvalid)]
  exact congrArg ((input.experiment i).logOddsScore (tapes i))
    (prefix_historyObservations_length_toNat input C mode accounting policy seed truth tapes hp i)

/-- The executable comparison on the actual observed word is the same real
posterior boundary test. Alphabet validity follows above for every prefix. -/
theorem prefix_historyObservationWord_hits_iff (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) (i : I.Stage)
    (hvalid : ∀ symbol ∈ historyObservations s.history i, symbol < (input.experiment i).alphabetSize)
    (p : ℚ) (hpTarget : 0 < p) (hpone : p < 1) :
    (input.experiment i).rationalWordHits p (historyObservationWord input s.history i hvalid) = true ↔
      Real.log ((1 - (p : ℝ)) / (p : ℝ)) ≤
        |(input.experiment i).logOddsScore (tapes i) (s.ledger.reviews i).toNat| := by
  rw [(input.experiment i).rationalWordHits_iff p hpTarget hpone,
    prefix_historyObservationWord_score input C mode accounting policy seed truth tapes hp i hvalid]

theorem prefix_historyObservationWord_MAP_at_stop (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) (i : I.Stage)
    (hvalid : ∀ symbol ∈ historyObservations s.history i, symbol < (input.experiment i).alphabetSize)
    (p : ℚ) (hstop : (input.experiment i).posteriorThresholdStop p (tapes i) =
      ((s.ledger.reviews i).toNat : ℕ∞)) :
    (input.experiment i).rationalWordMAP (historyObservationWord input s.history i hvalid) =
      ((input.experiment i).posteriorSPRT p).rule.decision () (tapes i) := by
  rw [(input.experiment i).rationalWordMAP_eq_recordDecision]
  change decide (0 ≤ (input.experiment i).stoppedWordScore (historyObservationWord input s.history i hvalid)) =
    decide (0 ≤ (input.experiment i).logOddsScore (tapes i)
      ((input.experiment i).posteriorThresholdStop p (tapes i)).toNat)
  rw [prefix_historyObservationWord_score input C mode accounting policy seed truth tapes hp i hvalid,
    hstop, ENat.toNat_natCast]

end PaperProofs.Common.Native

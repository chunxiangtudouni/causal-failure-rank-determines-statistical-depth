module

public import PaperProofs.Paid.ComputationalClaims
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.BitVec
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Uniform

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open PaperProofs.Paid PaperProofs.Paid.Computation
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

theorem sampler_measurable_comp {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] {f : A → B} {g : B → C} (hg : Measurable g) (hf : Measurable f) :
    Measurable (fun x => g (f x)) := by
  simpa only [Function.comp_def] using hg.comp hf

theorem sampler_map_map {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] {f : A → B} {g : B → C} {μ : Measure A}
    (hg : Measurable g) (hf : Measurable f) :
    (μ.map f).map g = μ.map (fun x => g (f x)) := by
  simpa only [Function.comp_def] using Measure.map_map hg hf


/- Unchanged mathematical body from initial draft 001. -/

instance samplerCoinState_countable : Countable CoinState :=
  Function.Injective.countable
    (f := fun s : CoinState => (s.accumulator, s.filled, s.bitsRead, s.result)) (by
      intro a b h
      cases a
      cases b
      simpa only [Prod.mk.injEq, CoinState.mk.injEq] using h)

instance samplerCoinState_measurableSpace : MeasurableSpace CoinState := ⊤

instance samplerCoinState_measurableSingleton : MeasurableSingletonClass CoinState :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The total update used by the original run, including its absorbing return. -/
def samplerCoinAdvance (p : Set.Icc (0 : ℚ) 1) (tape : FairTape) (state : CoinState) : CoinState :=
  (coinStep p tape state).getD state

theorem samplerCoinAdvance_of_returned (p : Set.Icc (0 : ℚ) 1) (tape : FairTape)
    (state : CoinState) (h : state.result.isSome = true) :
    samplerCoinAdvance p tape state = state := by
  simp [samplerCoinAdvance, coinStep, h]

theorem samplerCoinAdvance_bits_mono (p : Set.Icc (0 : ℚ) 1) (tape : FairTape)
    (state : CoinState) : state.bitsRead ≤ (samplerCoinAdvance p tape state).bitsRead := by
  unfold samplerCoinAdvance coinStep
  split_ifs <;> simp

theorem samplerCoinRun_bits_mono (p : Set.Icc (0 : ℚ) 1) (tape : FairTape) :
    Monotone (fun n => (coinRun p tape n).bitsRead) := by
  apply monotone_nat_of_le_succ
  intro n
  exact samplerCoinAdvance_bits_mono p tape (coinRun p tape n)

theorem samplerCoinRun_absorbing (p : Set.Icc (0 : ℚ) 1) (tape : FairTape)
    (n : ℕ) (h : (coinRun p tape n).result.isSome = true) (k : ℕ) :
    coinRun p tape (n + k) = coinRun p tape n := by
  induction k with
  | zero => simp
  | succ k ih =>
      change samplerCoinAdvance p tape (coinRun p tape (n + k)) = _
      rw [ih, samplerCoinAdvance_of_returned p tape _ h]

theorem samplerCoinResult_of_run (p : Set.Icc (0 : ℚ) 1) (tape : FairTape)
    (n : ℕ) (h : (coinRun p tape n).result.isSome = true) :
    coinResult p tape = (coinRun p tape n).result := by
  classical
  let hx : ∃ k, (coinRun p tape k).result.isSome = true := ⟨n, h⟩
  have hn : Nat.find hx ≤ n := Nat.find_min' hx h
  have heq := samplerCoinRun_absorbing p tape (Nat.find hx) (Nat.find_spec hx)
    (n - Nat.find hx)
  rw [Nat.add_sub_of_le hn] at heq
  simp only [coinResult, dite_eq_left hx]
  exact congrArg CoinState.result heq.symm

theorem samplerCoinResult_none_iff (p : Set.Icc (0 : ℚ) 1) (tape : FairTape) :
    coinResult p tape = none ↔ ∀ n, (coinRun p tape n).result = none := by
  classical
  constructor
  · intro h n
    cases hr : (coinRun p tape n).result with
    | none => rfl
    | some b =>
        have hs : (coinRun p tape n).result.isSome = true := by simp [hr]
        have := samplerCoinResult_of_run p tape n hs
        simp [h, hr] at this
  · intro h
    have hn : ¬ ∃ n, (coinRun p tape n).result.isSome = true := by simp [h]
    simp [coinResult, hn]

theorem samplerCoinAdvance_prefix (p : Set.Icc (0 : ℚ) 1) (tape tape' : FairTape)
    (state : CoinState) (count : ℕ) (hprefix : ∀ k < count, tape k = tape' k)
    (hbound : (samplerCoinAdvance p tape state).bitsRead ≤ count) :
    samplerCoinAdvance p tape' state = samplerCoinAdvance p tape state := by
  by_cases hr : state.result.isSome = true
  · simp [samplerCoinAdvance, coinStep, hr]
  by_cases hzero : p.val = 0
  · simp [samplerCoinAdvance, coinStep, hr, hzero]
  by_cases hone : p.val = 1
  · simp [samplerCoinAdvance, coinStep, hr, hone]
  by_cases hfill : state.filled < coinWidth p
  · have hk : state.bitsRead < count := by
      simpa [samplerCoinAdvance, coinStep, hr, hzero, hone, hfill] using hbound
    simp only [samplerCoinAdvance, coinStep, hr, hzero, hone, hfill, ↓reduceIte]
    rw [hprefix state.bitsRead hk]
  · simp [samplerCoinAdvance, coinStep, hr, hzero, hone, hfill]

theorem samplerCoinRun_prefix (p : Set.Icc (0 : ℚ) 1) (tape tape' : FairTape)
    (count n : ℕ) (hprefix : ∀ k < count, tape k = tape' k)
    (hbound : (coinRun p tape n).bitsRead ≤ count) :
    coinRun p tape' n = coinRun p tape n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn : (coinRun p tape n).bitsRead ≤ count :=
        (samplerCoinRun_bits_mono p tape (Nat.le_succ n)).trans hbound
      change samplerCoinAdvance p tape' (coinRun p tape' n) =
        samplerCoinAdvance p tape (coinRun p tape n)
      rw [ih hn]
      exact samplerCoinAdvance_prefix p tape tape' _ count hprefix hbound

theorem samplerCoin_causal (p : Set.Icc (0 : ℚ) 1) (tape tape' : FairTape)
    (count : ℕ) (hprefix : ∀ k < count, tape k = tape' k)
    (hbits : coinBits p tape ≤ (count : ℕ∞)) :
    coinResult p tape' = coinResult p tape := by
  classical
  by_cases hx : ∃ n, (coinRun p tape n).result.isSome = true
  · have hbound : (coinRun p tape (Nat.find hx)).bitsRead ≤ count := by
      simpa [coinBits, hx] using hbits
    have heq := samplerCoinRun_prefix p tape tape' count (Nat.find hx) hprefix hbound
    have hreturn : (coinRun p tape' (Nat.find hx)).result.isSome = true := by
      rw [heq]
      exact Nat.find_spec hx
    rw [samplerCoinResult_of_run p tape' _ hreturn,
      samplerCoinResult_of_run p tape _ (Nat.find_spec hx), heq]
  · simp [coinBits, hx] at hbits

theorem measurable_samplerCoinAdvance (p : Set.Icc (0 : ℚ) 1) :
    Measurable (fun pair : FairTape × CoinState => samplerCoinAdvance p pair.1 pair.2) := by
  apply measurable_from_prod_countable_left
  intro state
  change Measurable (fun tape : FairTape => samplerCoinAdvance p tape state)
  by_cases hr : state.result.isSome = true
  · simp [samplerCoinAdvance, coinStep, hr]
  by_cases hzero : p.val = 0
  · simp [samplerCoinAdvance, coinStep, hr, hzero]
  by_cases hone : p.val = 1
  · simp [samplerCoinAdvance, coinStep, hr, hone]
  by_cases hfill : state.filled < coinWidth p
  · have hfun : (fun tape : FairTape => samplerCoinAdvance p tape state) =
        (fun bit : Bool => (⟨2 * state.accumulator + bit.toNat,
          state.filled + 1, state.bitsRead + 1, state.result⟩ : CoinState)) ∘
          (fun tape : FairTape => tape state.bitsRead) := by
      funext tape
      cases hb : tape state.bitsRead <;>
        simp [samplerCoinAdvance, coinStep, hr, hzero, hone, hfill, hb]
    rw [hfun]
    exact (measurable_of_countable (fun bit : Bool =>
      (⟨2 * state.accumulator + bit.toNat,
        state.filled + 1, state.bitsRead + 1, state.result⟩ : CoinState))).comp
        (measurable_pi_apply state.bitsRead)
  · simp [samplerCoinAdvance, coinStep, hr, hzero, hone, hfill]

theorem measurable_samplerCoinRun (p : Set.Icc (0 : ℚ) 1) (n : ℕ) :
    Measurable (coinRun p · n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (measurable_samplerCoinAdvance p).comp (measurable_id.prodMk ih)

theorem measurable_samplerCoinResult (p : Set.Icc (0 : ℚ) 1) :
    Measurable (coinResult p) := by
  classical
  have hr (n : ℕ) : Measurable (fun tape : FairTape => (coinRun p tape n).result) :=
    (measurable_of_countable CoinState.result).comp (measurable_samplerCoinRun p n)
  have hsome (b : Bool) : {tape | coinResult p tape = some b} =
      ⋃ n : ℕ, {tape | (coinRun p tape n).result = some b} := by
    ext tape
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      by_cases hx : ∃ n, (coinRun p tape n).result.isSome = true
      · exact ⟨Nat.find hx, by simpa [coinResult, hx] using h⟩
      · simp [coinResult, hx] at h
    · rintro ⟨n, h⟩
      rw [samplerCoinResult_of_run p tape n (by simp [h]), h]
  apply measurable_to_countable'
  intro result
  cases result with
  | none =>
      have hnone : {tape | coinResult p tape = none} =
          ⋂ n : ℕ, {tape | (coinRun p tape n).result = none} := by
        ext tape
        simp [samplerCoinResult_none_iff]
      change MeasurableSet {tape | coinResult p tape = none}
      rw [hnone]
      exact MeasurableSet.iInter (fun n => (hr n) (measurableSet_singleton none))
  | some b =>
      change MeasurableSet {tape | coinResult p tape = some b}
      rw [hsome b]
      exact MeasurableSet.iUnion (fun n => (hr n) (measurableSet_singleton (some b)))


/- Unchanged mathematical body from initial draft 002. -/

def samplerCoinIter (p : Set.Icc (0 : ℚ) 1) (tape : FairTape) : CoinState → ℕ → CoinState
  | state, 0 => state
  | state, n + 1 => samplerCoinAdvance p tape (samplerCoinIter p tape state n)

theorem samplerCoinIter_initial (p : Set.Icc (0 : ℚ) 1) (tape : FairTape) (n : ℕ) :
    samplerCoinIter p tape coinInitial n = coinRun p tape n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (samplerCoinAdvance p tape) ih

theorem samplerCoinIter_add (p : Set.Icc (0 : ℚ) 1) (tape : FairTape)
    (state : CoinState) (n k : ℕ) :
    samplerCoinIter p tape state (n + k) =
      samplerCoinIter p tape (samplerCoinIter p tape state n) k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (samplerCoinAdvance p tape) ih

def samplerTapeTail (count : ℕ) (tape : FairTape) : FairTape := fun k => tape (count + k)

theorem samplerTapeTail_eq (count : ℕ) :
    samplerTapeTail count = (fun tape : FairTape => fun k => tape (count + k)) := rfl

def samplerShiftState (count : ℕ) (state : CoinState) : CoinState :=
  {state with bitsRead := count + state.bitsRead}

theorem samplerCoinAdvance_shift (p : Set.Icc (0 : ℚ) 1) (tape : FairTape)
    (count : ℕ) (state : CoinState) :
    samplerCoinAdvance p tape (samplerShiftState count state) =
      samplerShiftState count (samplerCoinAdvance p (samplerTapeTail count tape) state) := by
  unfold samplerCoinAdvance coinStep samplerShiftState samplerTapeTail
  split_ifs <;> rfl

theorem samplerCoinIter_shift (p : Set.Icc (0 : ℚ) 1) (tape : FairTape)
    (count : ℕ) (state : CoinState) (n : ℕ) :
    samplerCoinIter p tape (samplerShiftState count state) n =
      samplerShiftState count (samplerCoinIter p (samplerTapeTail count tape) state n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change samplerCoinAdvance p tape
        (samplerCoinIter p tape (samplerShiftState count state) n) = _
      rw [ih, samplerCoinAdvance_shift]
      rfl

def samplerWordValue (word : List Bool) : ℕ :=
  (BitVec.ofBoolListBE word).toNat

theorem samplerWordValue_lt (word : List Bool) : samplerWordValue word < 2 ^ word.length :=
  (BitVec.ofBoolListBE word).isLt

theorem samplerWordValue_cons (b : Bool) (word : List Bool) :
    samplerWordValue (b :: word) = b.toNat * 2 ^ word.length + samplerWordValue word := by
  simp only [samplerWordValue, BitVec.ofBoolListBE, BitVec.toNat_cons', Nat.shiftLeft_eq]

theorem samplerWord_fold (word : List Bool) (a : ℕ) :
    word.foldl (fun v b => 2 * v + b.toNat) a =
      a * 2 ^ word.length + samplerWordValue word := by
  induction word generalizing a with
  | nil => simp [samplerWordValue, BitVec.ofBoolListBE]
  | cons b word ih =>
      rw [List.foldl_cons, ih, List.length_cons, pow_succ, samplerWordValue_cons]
      ring

/-- Exact finite fill of the original state machine, with all consumed bits retained. -/
theorem samplerCoinIter_fill (p : Set.Icc (0 : ℚ) 1) (hp0 : p.val ≠ 0) (hp1 : p.val ≠ 1)
    (tape : FairTape) (state : CoinState) (hr : state.result = none)
    (n : ℕ) (hn : state.filled + n ≤ coinWidth p) :
    samplerCoinIter p tape state n =
      {state with
        accumulator := (List.ofFn (fun i : Fin n => tape (state.bitsRead + i.val))).foldl
          (fun v b => 2 * v + b.toNat) state.accumulator
        filled := state.filled + n
        bitsRead := state.bitsRead + n} := by
  induction n with
  | zero => simp [samplerCoinIter]
  | succ n ih =>
      have hn' : state.filled + n ≤ coinWidth p := by omega
      have hfill : state.filled + n < coinWidth p := by omega
      change samplerCoinAdvance p tape (samplerCoinIter p tape state n) = _
      rw [ih hn']
      simp only [samplerCoinAdvance, coinStep, hr, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte, hp0, hp1, hfill, Option.getD_some, List.ofFn_succ', List.concat_eq_append, List.foldl_concat]
      congr 1
      cases hb : tape (state.bitsRead + n) <;> simp [Fin.val_castSucc, Fin.val_last, hb]

def samplerBlockValue (count : ℕ) (tape : FairTape) : ℕ :=
  samplerWordValue (List.ofFn (fun i : Fin count => tape i.val))

theorem samplerCoinRun_block (p : Set.Icc (0 : ℚ) 1) (hp0 : p.val ≠ 0) (hp1 : p.val ≠ 1)
    (tape : FairTape) :
    coinRun p tape (coinWidth p) =
      ⟨samplerBlockValue (coinWidth p) tape, coinWidth p, coinWidth p, none⟩ := by
  rw [← samplerCoinIter_initial,
    samplerCoinIter_fill p hp0 hp1 tape coinInitial rfl _ (by simp [coinInitial])]
  simp [coinInitial, samplerWord_fold, samplerBlockValue]

theorem samplerCoinResult_exists (p : Set.Icc (0 : ℚ) 1) (tape : FairTape) (b : Bool) :
    coinResult p tape = some b ↔ ∃ n, (coinRun p tape n).result = some b := by
  classical
  constructor
  · intro h
    by_cases hx : ∃ n, (coinRun p tape n).result.isSome = true
    · exact ⟨Nat.find hx, by simpa [coinResult, hx] using h⟩
    · simp [coinResult, hx] at h
  · rintro ⟨n, h⟩
    rw [samplerCoinResult_of_run p tape n (by simp [h]), h]

theorem samplerCoinResult_suffix (p : Set.Icc (0 : ℚ) 1) (tape tape' : FairTape)
    (count : ℕ) (h : ∀ n, (coinRun p tape (count + n)).result = (coinRun p tape' n).result) :
    coinResult p tape = coinResult p tape' := by
  classical
  apply Option.ext
  intro b
  rw [samplerCoinResult_exists, samplerCoinResult_exists]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← h]
    have heq := samplerCoinRun_absorbing p tape n (by simp [hn]) count
    rw [Nat.add_comm] at heq
    exact (congrArg CoinState.result heq).trans hn
  · rintro ⟨n, hn⟩
    exact ⟨count + n, (h n).trans hn⟩

/-- One exact rejection block: acceptance compares with the original numerator;
rejection restarts on the remaining private tape. -/
theorem samplerCoinResult_block (p : Set.Icc (0 : ℚ) 1) (hp0 : p.val ≠ 0) (hp1 : p.val ≠ 1)
    (tape : FairTape) :
    coinResult p tape =
      if samplerBlockValue (coinWidth p) tape < p.val.den then
        some (decide (samplerBlockValue (coinWidth p) tape < p.val.num.toNat))
      else coinResult p (samplerTapeTail (coinWidth p) tape) := by
  let value := samplerBlockValue (coinWidth p) tape
  have hrun := samplerCoinRun_block p hp0 hp1 tape
  have hstep : coinRun p tape (coinWidth p + 1) =
      if value < p.val.den then
        ⟨value, coinWidth p, coinWidth p, some (decide (value < p.val.num.toNat))⟩
      else samplerShiftState (coinWidth p) coinInitial := by
    change samplerCoinAdvance p tape (coinRun p tape (coinWidth p)) = _
    rw [hrun]
    simp [samplerCoinAdvance, coinStep, hp0, hp1, value, samplerShiftState, coinInitial]
    split <;> rfl
  by_cases ha : value < p.val.den
  · rw [ite_eq_left ha] at hstep ⊢
    exact (samplerCoinResult_of_run p tape (coinWidth p + 1) (by simp [hstep])).trans
      (congrArg CoinState.result hstep)
  · rw [ite_eq_right ha] at hstep ⊢
    apply samplerCoinResult_suffix p tape (samplerTapeTail (coinWidth p) tape) (coinWidth p + 1)
    intro n
    rw [← samplerCoinIter_initial, samplerCoinIter_add, samplerCoinIter_initial, hstep,
      samplerCoinIter_shift, samplerCoinIter_initial]
    rfl


/- Unchanged mathematical body from initial draft 003. -/

theorem samplerFairGuess_singleton (b : Bool) : fairGuessLaw {b} = (2 : ℝ≥0∞)⁻¹ := by
  cases b <;> norm_num [fairGuessLaw, rocCoinLaw, ENNReal.ofReal_div_of_pos]

def samplerWordFin (count : ℕ) (word : Fin count → Bool) : Fin (2 ^ count) :=
  ⟨samplerWordValue (List.ofFn word), by simpa using samplerWordValue_lt (List.ofFn word)⟩

theorem samplerWordFin_injective (count : ℕ) : Function.Injective (samplerWordFin count) := by
  intro a b h
  have hv : (BitVec.ofBoolListBE (List.ofFn a)).cast (by simp : (List.ofFn a).length = count) =
      (BitVec.ofBoolListBE (List.ofFn b)).cast (by simp : (List.ofFn b).length = count) := by
    apply BitVec.eq_of_toNat_eq
    exact congrArg Fin.val h
  funext i
  have hi := congrArg (fun v : BitVec count => v.getMsbD i.val) hv
  simpa [List.getD_eq_getElem?_getD, i.isLt] using hi

theorem samplerWordFin_bijective (count : ℕ) : Function.Bijective (samplerWordFin count) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨samplerWordFin_injective count, by simp⟩

def samplerTapePrefix (count : ℕ) (tape : FairTape) : Fin count → Bool := fun i => tape i.val

theorem samplerTapePrefix_eq (count : ℕ) :
    samplerTapePrefix count = (fun tape : FairTape => fun i : Fin count => tape i.val) := rfl

@[fun_prop] theorem measurable_samplerTapePrefix (count : ℕ) : Measurable (samplerTapePrefix count) := by
  exact Measurable.of_eval (fun i => measurable_pi_apply i.val)

@[fun_prop] theorem measurable_samplerTapeTail (count : ℕ) : Measurable (samplerTapeTail count) := by
  exact Measurable.of_eval (fun i => measurable_pi_apply (count + i))

theorem samplerTapePrefix_law (count : ℕ) :
    fairTapeLaw.map (samplerTapePrefix count) = Measure.pi (fun _ : Fin count => fairGuessLaw) := by
  have h := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => fairGuessLaw) (f := fun i : Fin count => i.val)
    (fun _ _ h => Fin.ext h)
  simpa only [fairTapeLaw, samplerTapePrefix_eq, Measure.infinitePi_eq_pi] using h

theorem samplerTapeTail_law (count : ℕ) :
    fairTapeLaw.map (samplerTapeTail count) = fairTapeLaw := by
  have h := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => fairGuessLaw) (f := fun n : ℕ => count + n)
    (fun _ _ h => Nat.add_left_cancel h)
  simpa only [fairTapeLaw, samplerTapeTail_eq] using h

/-- The complete unused tape remains independent of the entire consumed block. -/
theorem samplerTapePrefix_tail_law (count : ℕ) :
    fairTapeLaw.map (fun tape => (samplerTapePrefix count tape, samplerTapeTail count tape)) =
      (Measure.pi (fun _ : Fin count => fairGuessLaw)).prod fairTapeLaw := by
  have hind : iIndepFun (fun k (tape : FairTape) => tape k) fairTapeLaw :=
    iIndepFun_infinitePi (X := fun _ b => b) (fun _ => measurable_id)
  have hd : Disjoint {k : ℕ | k < count} {k : ℕ | count ≤ k} := by
    exact Set.disjoint_left.mpr (fun _ hlt hle => (Nat.not_le.mpr hlt) hle)
  have hi := hind.indepFun_set {k : ℕ | k < count} {k : ℕ | count ≤ k} hd
    (fun k => measurable_pi_apply k)
  have hj := hi.comp
    (φ := fun pre : {k : ℕ // k < count} → Bool => fun i : Fin count => pre ⟨i.val, i.isLt⟩)
    (ψ := fun post : {k : ℕ // count ≤ k} → Bool => fun k : ℕ => post ⟨count + k, by omega⟩)
    (Measurable.of_eval (fun i : Fin count =>
      measurable_pi_apply (⟨i.val, i.isLt⟩ : {k : ℕ // k < count})))
    (Measurable.of_eval (fun k : ℕ =>
      measurable_pi_apply (⟨count + k, by omega⟩ : {k : ℕ // count ≤ k})))
  have hbase : IndepFun (samplerTapePrefix count) (samplerTapeTail count) fairTapeLaw := by
    simpa only [Function.comp_def, samplerTapePrefix_eq, samplerTapeTail_eq] using hj
  have hm := hbase.map_prod_eq_prod_map_map
    (measurable_samplerTapePrefix count).aemeasurable (measurable_samplerTapeTail count).aemeasurable
  exact hm.trans (by rw [samplerTapePrefix_law, samplerTapeTail_law])

theorem samplerWordFin_law (count : ℕ) :
    (Measure.pi (fun _ : Fin count => fairGuessLaw)).map (samplerWordFin count) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin (2 ^ count))) := by
  classical
  apply Measure.ext_of_singleton
  intro value
  obtain ⟨word, hw⟩ := (samplerWordFin_bijective count).2 value
  have hpre : samplerWordFin count ⁻¹' {value} = {word} := by
    ext other
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hw]
    exact (samplerWordFin_injective count).eq_iff
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), hpre,
    Measure.pi_singleton, Measure.uniformOfFinset_apply_singleton]
  simp [samplerFairGuess_singleton, ENNReal.inv_pow]

@[fun_prop] theorem measurable_samplerBlockValue (count : ℕ) : Measurable (samplerBlockValue count) :=
  (measurable_of_countable (fun word : Fin count → Bool =>
    samplerWordValue (List.ofFn word))).comp (measurable_samplerTapePrefix count)

theorem samplerBlockValue_lt (count : ℕ) (tape : FairTape) :
    samplerBlockValue count tape < 2 ^ count := by
  simpa [samplerBlockValue] using samplerWordValue_lt
    (List.ofFn (fun i : Fin count => tape i.val))

theorem samplerBlockValue_law (count : ℕ) :
    fairTapeLaw.map (samplerBlockValue count) = Measure.uniformOfFinset (Finset.range (2 ^ count)) := by
  classical
  have hfin : fairTapeLaw.map (fun tape => samplerWordFin count (samplerTapePrefix count tape)) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin (2 ^ count))) := by
    rw [← sampler_map_map (measurable_of_countable _) (measurable_samplerTapePrefix count),
      samplerTapePrefix_law, samplerWordFin_law]
  have hnat := congrArg (fun μ : Measure (Fin (2 ^ count)) => μ.map Fin.val) hfin
  rw [sampler_map_map (measurable_of_countable _)
    (sampler_measurable_comp (measurable_of_countable (samplerWordFin count))
      (measurable_samplerTapePrefix count))] at hnat
  refine hnat.trans ?_
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  by_cases hk : k < 2 ^ count
  · have hpre : (Fin.val : Fin (2 ^ count) → ℕ) ⁻¹' {k} = {⟨k, hk⟩} := by
      ext i
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    rw [hpre]
    simp [hk]
  · have hpre : (Fin.val : Fin (2 ^ count) → ℕ) ⁻¹' {k} = ∅ := by
      ext i
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hi
      exact hk (hi ▸ i.isLt)
    simp [hpre, hk]

theorem samplerBlockValue_lt_mass (count limit : ℕ) (hlimit : limit ≤ 2 ^ count) :
    fairTapeLaw {tape | samplerBlockValue count tape < limit} =
      (limit : ℝ≥0∞) / (2 ^ count : ℕ) := by
  change fairTapeLaw (samplerBlockValue count ⁻¹' {k | k < limit}) = _
  rw [← Measure.map_apply (measurable_samplerBlockValue count) (by measurability), samplerBlockValue_law,
    Measure.uniformOfFinset_apply]
  have hfilter : @Finset.filter ℕ (fun k => k ∈ {k : ℕ | k < limit})
      (fun k => Classical.propDecidable (k ∈ {k : ℕ | k < limit}))
      (Finset.range (2 ^ count)) = Finset.range limit := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq]
    omega
  rw [hfilter]
  simp

theorem samplerBlockValue_tail_law (count : ℕ) :
    fairTapeLaw.map (fun tape => (samplerBlockValue count tape, samplerTapeTail count tape)) =
      (Measure.uniformOfFinset (Finset.range (2 ^ count))).prod fairTapeLaw := by
  let value := fun word : Fin count → Bool => samplerWordValue (List.ofFn word)
  have hvalue : Measurable value := measurable_of_countable _
  have hm := congrArg (fun μ : Measure ((Fin count → Bool) × FairTape) =>
    μ.map (Prod.map value id)) (samplerTapePrefix_tail_law count)
  rw [sampler_map_map (hvalue.prodMap measurable_id)
    ((measurable_samplerTapePrefix count).prodMk (measurable_samplerTapeTail count)),
    ← Measure.map_prod_map _ _ (measurable_of_countable _) measurable_id] at hm
  have hv : (Measure.pi (fun _ : Fin count => fairGuessLaw)).map value =
      Measure.uniformOfFinset (Finset.range (2 ^ count)) := by
    rw [← samplerTapePrefix_law count,
      sampler_map_map (measurable_of_countable _) (measurable_samplerTapePrefix count)]
    exact samplerBlockValue_law count
  simpa only [hv, Measure.map_id, Prod.map, id_eq, value, samplerBlockValue, samplerTapePrefix_eq] using hm


/- Unchanged mathematical body from initial draft 004. -/

theorem samplerCoinWidth_den_lt (p : Set.Icc (0 : ℚ) 1) : p.val.den < 2 ^ coinWidth p := by
  exact Nat.lt_log2_self

theorem samplerCoin_num_le_den (p : Set.Icc (0 : ℚ) 1) : p.val.num.toNat ≤ p.val.den := by
  have hn : 0 ≤ p.val.num := Rat.num_nonneg.mpr p.property.1
  have hq : (p.val.num : ℚ) ≤ p.val.den := by
    have := p.property.2
    rw [← Rat.num_div_den p.val] at this
    exact (div_le_one (by exact_mod_cast p.val.den_pos)).mp this
  have hc : (p.val.num.toNat : ℚ) = p.val.num := by
    exact_mod_cast Int.toNat_of_nonneg hn
  exact_mod_cast hc.trans_le hq

theorem samplerCoin_cast (p : Set.Icc (0 : ℚ) 1) :
    (p.val : ℝ) = (p.val.num.toNat : ℝ) / (p.val.den : ℝ) := by
  rw [Rat.cast_def]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg (Rat.num_nonneg.mpr p.property.1)).symm

/-- Exact one-block equation for each actual returned value, including nonreturn. -/
theorem samplerCoinResult_mass_block (p : Set.Icc (0 : ℚ) 1) (hp0 : p.val ≠ 0)
    (hp1 : p.val ≠ 1) (b : Option Bool) :
    fairTapeLaw {tape | coinResult p tape = b} =
      (Measure.uniformOfFinset (Finset.range (2 ^ coinWidth p)))
        {k | k < p.val.den ∧ some (decide (k < p.val.num.toNat)) = b} +
      (Measure.uniformOfFinset (Finset.range (2 ^ coinWidth p))) {k | p.val.den ≤ k} *
        fairTapeLaw {tape | coinResult p tape = b} := by
  classical
  let U := Measure.uniformOfFinset (Finset.range (2 ^ coinWidth p))
  let : IsProbabilityMeasure U := by
    dsimp only [U]
    rw [← samplerBlockValue_law (coinWidth p)]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_samplerBlockValue _).aemeasurable).mpr inferInstance
  let A : Set ℕ := {k | k < p.val.den ∧ some (decide (k < p.val.num.toNat)) = b}
  let R : Set ℕ := {k | p.val.den ≤ k}
  let B : Set FairTape := {tape | coinResult p tape = b}
  have hB : MeasurableSet B := (measurable_samplerCoinResult p) (measurableSet_singleton b)
  have hA : MeasurableSet A := Set.to_countable _ |>.measurableSet
  have hR : MeasurableSet R := Set.to_countable _ |>.measurableSet
  have hset : {tape | coinResult p tape = b} =
      (fun tape => (samplerBlockValue (coinWidth p) tape, samplerTapeTail (coinWidth p) tape)) ⁻¹'
        ((A ×ˢ Set.univ) ∪ (R ×ˢ B)) := by
    ext tape
    change coinResult p tape = b ↔ _
    rw [samplerCoinResult_block p hp0 hp1 tape]
    by_cases hk : samplerBlockValue (coinWidth p) tape < p.val.den
    · simp [A, R, B, hk, Nat.not_le.mpr hk]
    · simp [A, R, B, hk, Nat.le_of_not_gt hk]
  have hd : Disjoint (A ×ˢ Set.univ) (R ×ˢ B) := by
    apply Set.disjoint_left.mpr
    rintro pair ⟨ha, _⟩ ⟨hr, _⟩
    exact (Nat.not_le.mpr ha.1) hr
  conv_lhs =>
    rw [hset, ← Measure.map_apply
      ((measurable_samplerBlockValue _).prodMk (measurable_samplerTapeTail _))
      ((hA.prod MeasurableSet.univ).union (hR.prod hB)),
      samplerBlockValue_tail_law, measure_union hd (hR.prod hB), Measure.prod_prod, Measure.prod_prod]
    simp only [measure_univ, mul_one]

theorem samplerCoinResult_none_mass (p : Set.Icc (0 : ℚ) 1) (hp0 : p.val ≠ 0)
    (hp1 : p.val ≠ 1) :
    fairTapeLaw {tape | coinResult p tape = none} = 0 := by
  classical
  let U := Measure.uniformOfFinset (Finset.range (2 ^ coinWidth p))
  let : IsProbabilityMeasure U := by
    dsimp only [U]
    rw [← samplerBlockValue_law (coinWidth p)]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_samplerBlockValue _).aemeasurable).mpr inferInstance
  have hrec := samplerCoinResult_mass_block p hp0 hp1 none
  simp only [Option.some_ne_none, and_false, Set.ofPred_false, measure_empty, zero_add] at hrec
  have hcut : U {k | k < p.val.den} = (p.val.den : ℝ≥0∞) / (2 ^ coinWidth p : ℕ) := by
    dsimp only [U]
    rw [← samplerBlockValue_law (coinWidth p)]
    rw [Measure.map_apply (measurable_samplerBlockValue _) (by measurability)]
    change fairTapeLaw {tape | samplerBlockValue (coinWidth p) tape < p.val.den} = _
    exact samplerBlockValue_lt_mass _ _ (samplerCoinWidth_den_lt p).le
  have hcomp : U {k | p.val.den ≤ k} = 1 - (p.val.den : ℝ≥0∞) / (2 ^ coinWidth p : ℕ) := by
    have hs : {k : ℕ | p.val.den ≤ k} = {k : ℕ | k < p.val.den}ᶜ := by ext k; simp
    rw [hs, measure_compl (by measurability) (measure_ne_top U _), measure_univ, hcut]
  have hd : (0 : ℝ) < p.val.den := by exact_mod_cast p.val.den_pos
  have hpow : (0 : ℝ) < (2 ^ coinWidth p : ℕ) := by positivity
  have hratio : (p.val.den : ℝ≥0∞) / (2 ^ coinWidth p : ℕ) ≤ 1 := by
    rw [ENNReal.div_le_iff (by positivity) (by simp)]
    simpa using (show (p.val.den : ℝ≥0∞) ≤ (2 ^ coinWidth p : ℕ) by
      exact_mod_cast (samplerCoinWidth_den_lt p).le)
  have heq := congrArg ENNReal.toReal hrec
  rw [hcomp, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hratio (by simp)] at heq
  simp only [ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_natCast] at heq
  have hz : (fairTapeLaw {tape | coinResult p tape = none}).toReal = 0 := by
    have hprod : ((p.val.den : ℝ) / (2 ^ coinWidth p : ℕ)) *
        (fairTapeLaw {tape | coinResult p tape = none}).toReal = 0 := by nlinarith [heq]
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (div_pos hd hpow))
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top fairTapeLaw _)

theorem samplerCoinResult_true_mass (p : Set.Icc (0 : ℚ) 1) (hp0 : p.val ≠ 0)
    (hp1 : p.val ≠ 1) :
    fairTapeLaw {tape | coinResult p tape = some true} = ENNReal.ofReal (p.val : ℝ) := by
  classical
  let U := Measure.uniformOfFinset (Finset.range (2 ^ coinWidth p))
  let : IsProbabilityMeasure U := by
    dsimp only [U]
    rw [← samplerBlockValue_law (coinWidth p)]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_samplerBlockValue _).aemeasurable).mpr inferInstance
  have hn := samplerCoin_num_le_den p
  have hset : {k : ℕ | k < p.val.den ∧ some (decide (k < p.val.num.toNat)) = some true} =
      {k | k < p.val.num.toNat} := by
    ext k
    simp only [Set.mem_ofPred_eq, Option.some.injEq, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨h.trans_le hn, h⟩⟩
  have hmass (limit : ℕ) (hl : limit ≤ 2 ^ coinWidth p) :
      U {k | k < limit} = (limit : ℝ≥0∞) / (2 ^ coinWidth p : ℕ) := by
    dsimp only [U]
    rw [← samplerBlockValue_law (coinWidth p), Measure.map_apply (measurable_samplerBlockValue _) (by measurability)]
    change fairTapeLaw {tape | samplerBlockValue (coinWidth p) tape < limit} = _
    exact samplerBlockValue_lt_mass _ _ hl
  have hcomp : U {k | p.val.den ≤ k} = 1 - (p.val.den : ℝ≥0∞) / (2 ^ coinWidth p : ℕ) := by
    have hs : {k : ℕ | p.val.den ≤ k} = {k : ℕ | k < p.val.den}ᶜ := by ext k; simp
    rw [hs, measure_compl (by measurability) (measure_ne_top U _), measure_univ,
      hmass _ (samplerCoinWidth_den_lt p).le]
  have hrec := samplerCoinResult_mass_block p hp0 hp1 (some true)
  rw [hset, hmass _ (hn.trans (samplerCoinWidth_den_lt p).le), hcomp] at hrec
  have hratio : (p.val.den : ℝ≥0∞) / (2 ^ coinWidth p : ℕ) ≤ 1 := by
    rw [ENNReal.div_le_iff (by positivity) (by simp)]
    simpa using (show (p.val.den : ℝ≥0∞) ≤ (2 ^ coinWidth p : ℕ) by
      exact_mod_cast (samplerCoinWidth_den_lt p).le)
  have heq := congrArg ENNReal.toReal hrec
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le hratio (by simp)] at heq
  simp only [ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_natCast] at heq
  have hd : (0 : ℝ) < p.val.den := by exact_mod_cast p.val.den_pos
  have hb : (0 : ℝ) < (2 ^ coinWidth p : ℕ) := by positivity
  have hx : (fairTapeLaw {tape | coinResult p tape = some true}).toReal =
      (p.val.num.toNat : ℝ) / (p.val.den : ℝ) := by
    apply (eq_div_iff hd.ne').mpr
    have hdiv : (fairTapeLaw {tape | coinResult p tape = some true}).toReal *
        ((p.val.den : ℝ) / (2 ^ coinWidth p : ℕ)) =
        (p.val.num.toNat : ℝ) / (2 ^ coinWidth p : ℕ) := by nlinarith [heq]
    have heq' := congrArg (fun z : ℝ => z * (2 ^ coinWidth p : ℕ)) hdiv
    have hD : ((p.val.den : ℝ) / (2 ^ coinWidth p : ℕ)) * (2 ^ coinWidth p : ℕ) = p.val.den :=
      div_mul_cancel₀ _ hb.ne'
    have hN : ((p.val.num.toNat : ℝ) / (2 ^ coinWidth p : ℕ)) * (2 ^ coinWidth p : ℕ) = p.val.num.toNat :=
      div_mul_cancel₀ _ hb.ne'
    simpa only [mul_assoc, hD, hN] using heq'
  rw [← samplerCoin_cast p] at hx
  exact (ENNReal.ofReal_toReal (measure_ne_top fairTapeLaw _)).symm.trans (congrArg ENNReal.ofReal hx)


/- Unchanged mathematical body from initial draft 005. -/

theorem samplerCoinResult_zero (p : Set.Icc (0 : ℚ) 1) (hp : p.val = 0) (tape : FairTape) :
    coinResult p tape = some false := by
  have hr : coinRun p tape 1 = ⟨0, 0, 0, some false⟩ := by
    simp [coinRun, coinInitial, coinStep, hp]
  exact (samplerCoinResult_of_run p tape 1 (by simp [hr])).trans (congrArg CoinState.result hr)

theorem samplerCoinResult_one (p : Set.Icc (0 : ℚ) 1) (hp : p.val = 1) (tape : FairTape) :
    coinResult p tape = some true := by
  have hr : coinRun p tape 1 = ⟨0, 0, 0, some true⟩ := by
    simp [coinRun, coinInitial, coinStep, hp]
  exact (samplerCoinResult_of_run p tape 1 (by simp [hr])).trans (congrArg CoinState.result hr)

theorem samplerCoinResult_nonreturn_null (p : Set.Icc (0 : ℚ) 1) :
    fairTapeLaw {tape | coinResult p tape = none} = 0 := by
  by_cases h0 : p.val = 0
  · simp [samplerCoinResult_zero p h0]
  by_cases h1 : p.val = 1
  · simp [samplerCoinResult_one p h1]
  exact samplerCoinResult_none_mass p h0 h1

theorem samplerCoinResult_law (p : Set.Icc (0 : ℚ) 1) :
    fairTapeLaw.map (coinResult p) = (rocCoinLaw (realProbability p)).map some := by
  classical
  by_cases h0 : p.val = 0
  · have heq : coinResult p = fun _ => some false := funext (samplerCoinResult_zero p h0)
    rw [heq]
    simp [realProbability, h0, rocCoinLaw, Measure.map_const]
  by_cases h1 : p.val = 1
  · have heq : coinResult p = fun _ => some true := funext (samplerCoinResult_one p h1)
    rw [heq]
    simp [realProbability, h1, rocCoinLaw, Measure.map_const]
  let μ := fairTapeLaw.map (coinResult p)
  have hnone : μ {none} = 0 := by
    rw [Measure.map_apply (measurable_samplerCoinResult p) (measurableSet_singleton _)]
    exact samplerCoinResult_nonreturn_null p
  have htrue : μ {some true} = ENNReal.ofReal (p.val : ℝ) := by
    rw [Measure.map_apply (measurable_samplerCoinResult p) (measurableSet_singleton _)]
    exact samplerCoinResult_true_mass p h0 h1
  have hfalse : μ {some false} = ENNReal.ofReal (1 - (p.val : ℝ)) := by
    let : IsProbabilityMeasure μ :=
      (Measure.isProbabilityMeasure_map_iff (measurable_samplerCoinResult p).aemeasurable).mpr inferInstance
    have hset : ({some false} : Set (Option Bool)) = ({none} ∪ {some true})ᶜ := by
      ext b
      cases b with
      | none => simp
      | some b => cases b <;> simp
    rw [hset, measure_compl (by measurability) (measure_ne_top μ _), measure_univ,
      measure_union (by simp) (by measurability), hnone, htrue, zero_add]
    have hp0 : (0 : ℝ) ≤ p.val := by exact_mod_cast p.property.1
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hp0]
  apply Measure.ext_of_singleton
  intro b
  cases b with
  | none =>
      change μ {none} = _
      rw [hnone, Measure.map_apply (measurable_of_countable (some : Bool → Option Bool))
        (measurableSet_singleton _)]
      have hpre : (some : Bool → Option Bool) ⁻¹' {none} = ∅ := by ext k; simp
      rw [hpre, measure_empty]
  | some b =>
      change μ {some b} = _
      rw [Measure.map_apply (measurable_of_countable (some : Bool → Option Bool))
        (measurableSet_singleton _)]
      have hpre : (some : Bool → Option Bool) ⁻¹' {some b} = {b} := by ext k; simp
      rw [hpre]
      cases b
      · simpa [rocCoinLaw, realProbability] using hfalse
      · simpa [rocCoinLaw, realProbability] using htrue

/-- Original D27 rational-coin target, for the literal sampler and its actual bit count. -/
theorem exactRationalCoinClaims : ExactRationalCoinClaims := by
  intro p
  exact ⟨measurable_samplerCoinResult p, samplerCoinResult_nonreturn_null p,
    samplerCoinResult_law p, samplerCoin_causal p⟩

theorem samplerCoin_getD_law (p : Set.Icc (0 : ℚ) 1) :
    fairTapeLaw.map (fun tape => (coinResult p tape).getD false) = rocCoinLaw (realProbability p) := by
  rw [← sampler_map_map (measurable_of_countable (fun b : Option Bool => b.getD false))
    (measurable_samplerCoinResult p), samplerCoinResult_law,
    sampler_map_map (measurable_of_countable _) (measurable_of_countable _)]
  exact Measure.map_id


/- Unchanged mathematical body from initial draft 006. -/

def samplerIndexProbability (P : Parameters) (fee : ℚ) : CoinIndex P → Set.Icc (0 : ℚ) 1
  | .inl _ => selectorProbability P fee
  | .inr (.inl _) => rationalProbability (1 / 2)
  | .inr (.inr (_, level)) => calibrationProbability P fee level

def samplerIndexUnpack (P : Parameters) (bits : CoinIndex P → Bool) : P.CalibratedSearchSeed :=
  (bits (.inl ()), (fun stage => bits (.inr (.inl stage))),
    fun stage level => bits (.inr (.inr (stage, level))))

theorem samplerPi_curry_law {A B : Type} [Fintype A] [Fintype B]
    (μ : A → B → Measure Bool) [∀ a b, IsProbabilityMeasure (μ a b)] :
    (Measure.pi (fun pair : A × B => μ pair.1 pair.2)).map
      (fun bits a b => bits (a, b)) = Measure.pi (fun a => Measure.pi (μ a)) := by
  have h := Measure.infinitePi_map_curry μ
  have hc : (MeasurableEquiv.curry A B Bool : (A × B → Bool) → A → B → Bool) =
      (fun bits a b => bits (a, b)) := rfl
  rw [hc] at h
  simpa only [Measure.infinitePi_eq_pi] using h

/-- Reindex the complete finite family; both nested products and the selector
are retained, so this is stronger than separate marginal identities. -/
theorem samplerIndexUnpack_law (P : Parameters) (μ : CoinIndex P → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.pi μ).map (samplerIndexUnpack P) =
      (μ (.inl ())).prod
        ((Measure.pi (fun stage => μ (.inr (.inl stage)))).prod
          (Measure.pi (fun stage => Measure.pi (fun level => μ (.inr (.inr (stage, level))))))) := by
  let split := (MeasurableEquiv.sumPiEquivProdPi (fun _ : CoinIndex P => Bool))
  let splitRest := (MeasurableEquiv.sumPiEquivProdPi
    (fun _ : P.sharedInstance.Stage ⊕ (P.sharedInstance.Stage × Fin (P.certificate.M + 1)) => Bool))
  let restLaw := Measure.pi (fun rest => μ (.inr rest))
  have hsplit : (Measure.pi μ).map split =
      (Measure.pi (fun _ : Unit => μ (.inl ()))).prod restLaw :=
    (measurePreserving_sumPiEquivProdPi μ).map_eq
  have hrest : restLaw.map splitRest =
      (Measure.pi (fun stage => μ (.inr (.inl stage)))).prod
        (Measure.pi (fun pair => μ (.inr (.inr pair)))) :=
    (measurePreserving_sumPiEquivProdPi (fun rest => μ (.inr rest))).map_eq
  have hunit : (Measure.pi (fun _ : Unit => μ (.inl ()))).map (fun bits => bits ()) = μ (.inl ()) :=
    (measurePreserving_eval (fun _ : Unit => μ (.inl ())) ()).map_eq
  have hfirst := congrArg (fun ρ => ρ.map (Prod.map (fun bits : Unit → Bool => bits ()) splitRest)) hsplit
  rw [Measure.map_map (by fun_prop) split.measurable,
    ← Measure.map_prod_map _ _ (measurable_pi_apply ()) splitRest.measurable,
    hunit, hrest] at hfirst
  let curry := fun bits : (P.sharedInstance.Stage × Fin (P.certificate.M + 1)) → Bool =>
    fun stage level => bits (stage, level)
  have hcurry : Measurable curry := by fun_prop
  have hsecond := congrArg (fun ρ => ρ.map (Prod.map id (Prod.map id curry))) hfirst
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ measurable_id (measurable_id.prodMap hcurry),
    ← Measure.map_prod_map _ _ measurable_id hcurry, Measure.map_id, Measure.map_id,
    samplerPi_curry_law (fun stage level => μ (.inr (.inr (stage, level))))] at hsecond
  exact hsecond

theorem sampler_realProbability_clip (value : ℚ) :
    (realProbability (rationalProbability value)).val = max 0 (min 1 (value : ℝ)) := by
  simp only [realProbability, rationalProbability, clipRat, Rat.cast_max, Rat.cast_min,
    Rat.cast_zero, Rat.cast_one]

theorem sampler_clipRat_idempotent (value : ℚ) : clipRat (clipRat value) = clipRat value := by
  have h0 : 0 ≤ clipRat value := le_max_left _ _
  have h1 : clipRat value ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  change max 0 (min 1 (clipRat value)) = _
  rw [min_eq_right h1, max_eq_right h0]

theorem sampler_calibration_probability (P : Parameters) (fee : ℚ)
    (level : Fin (P.certificate.M + 1)) :
    realProbability (calibrationProbability P fee level) =
      P.cachedClippedWeight (P.buildCachedFrontend fee) level.val := by
  apply Subtype.ext
  exact sampler_realProbability_clip _

theorem sampler_selector_probability (P : Parameters) (fee : ℚ) :
    rocCoinLaw (realProbability (selectorProbability P fee)) =
      if P.zeroChargeRisk fee ≤ P.certificate.risk then Measure.dirac false
      else rocCoinLaw (P.stateWeight (P.buildCachedFrontend fee).state) := by
  classical
  by_cases h : P.zeroChargeRisk fee ≤ P.certificate.risk
  · simp [selectorProbability, buildArtifact, selectorWeightRat, h,
      realProbability, rationalProbability, clipRat, rocCoinLaw]
  · rw [ite_eq_right h]
    have hsel : (buildArtifact P fee).selectorWeight =
        match (P.buildCachedFrontend fee).state with
        | .exact _ => 0
        | .bracket lower upper => clipRat (P.mixtureWeight lower upper) := by
      simp only [buildArtifact, selectorWeightRat, ite_eq_right h]
      cases (P.buildCachedFrontend fee).state <;> rfl
    unfold selectorProbability
    rw [hsel]
    generalize hs : (P.buildCachedFrontend fee).state = state
    cases state with
    | exact _ =>
        simp [realProbability, rationalProbability, clipRat,
          PaperProofs.Paid.Parameters.stateWeight, rocCoinLaw]
    | bracket lower upper =>
        congr 1
        apply Subtype.ext
        change ((clipRat (clipRat (P.mixtureWeight lower upper)) : ℚ) : ℝ) =
          max 0 (min 1 (P.mixtureWeight lower upper : ℝ))
        rw [sampler_clipRat_idempotent]
        simp only [clipRat, Rat.cast_max, Rat.cast_min, Rat.cast_zero, Rat.cast_one]

theorem measurable_sampledSeed (P : Parameters) (fee : ℚ) : Measurable (sampledSeed P fee) := by
  have hbit (i : CoinIndex P) :
      Measurable (fun streams : PrivateStreams P =>
        (coinResult (samplerIndexProbability P fee i) (streams i)).getD false) :=
    (measurable_of_countable (fun b : Option Bool => b.getD false)).comp
      ((measurable_samplerCoinResult _).comp (measurable_pi_apply i))
  exact (measurable_of_countable (samplerIndexUnpack P)).comp (Measurable.of_eval hbit)

theorem sampledSeed_nonreturn_null (P : Parameters) (fee : ℚ) :
    privateStreamsLaw P {streams | ¬ seedSamplerReturns P fee streams} = 0 := by
  have hsingle (i : CoinIndex P) :
      privateStreamsLaw P {streams | coinResult (samplerIndexProbability P fee i) (streams i) = none} = 0 := by
    change (privateStreamsLaw P) ((fun streams : PrivateStreams P => streams i) ⁻¹'
      {tape | coinResult (samplerIndexProbability P fee i) tape = none}) = 0
    have heval : (privateStreamsLaw P).map (fun streams : PrivateStreams P => streams i) = fairTapeLaw := by
      have hh := (measurePreserving_eval (fun _ : CoinIndex P => fairTapeLaw) i).map_eq
      have he : (Function.eval i : PrivateStreams P → FairTape) = (fun streams => streams i) := rfl
      simpa only [privateStreamsLaw, he] using hh
    rw [← Measure.map_apply (measurable_pi_apply i)
      ((measurable_samplerCoinResult (samplerIndexProbability P fee i)) (measurableSet_singleton none)),
      heval]
    exact samplerCoinResult_nonreturn_null _
  have hall : ∀ᵐ streams ∂privateStreamsLaw P, ∀ i : CoinIndex P,
      (coinResult (samplerIndexProbability P fee i) (streams i)).isSome = true := by
    apply ae_all_iff.mpr
    intro i
    simpa only [ae_iff, Option.isSome_iff_ne_none, not_not] using hsingle i
  apply ae_iff.mp
  filter_upwards [hall] with streams hs
  exact ⟨hs (.inl ()), fun stage => hs (.inr (.inl stage)),
    fun stage level => hs (.inr (.inr (stage, level)))⟩

set_option pp.explicit true in
theorem sampledSeed_law (P : Parameters) (fee : ℚ) :
    (privateStreamsLaw P).map (sampledSeed P fee) = P.cachedAlgorithmSeedLaw fee := by
  let μ : CoinIndex P → Measure Bool := fun i => rocCoinLaw (realProbability (samplerIndexProbability P fee i))
  have hmaps : Measurable (fun streams : PrivateStreams P => fun i =>
      (coinResult (samplerIndexProbability P fee i) (streams i)).getD false) :=
    Measurable.of_eval (fun i =>
      ((measurable_of_countable (fun b : Option Bool => b.getD false)).comp
        (measurable_samplerCoinResult _)).comp (measurable_pi_apply i))
  have hcoins : (privateStreamsLaw P).map
      (fun streams i => (coinResult (samplerIndexProbability P fee i) (streams i)).getD false) = Measure.pi μ := by
    rw [privateStreamsLaw, Measure.pi_map_pi
      (f := fun i tape => (coinResult (samplerIndexProbability P fee i) tape).getD false)
      (fun i => (sampler_measurable_comp
        (measurable_of_countable (fun b : Option Bool => b.getD false))
        (measurable_samplerCoinResult (samplerIndexProbability P fee i))).aemeasurable)]
    congr 1
    funext i
    exact samplerCoin_getD_law _
  have hm := congrArg (fun ρ => ρ.map (samplerIndexUnpack P)) hcoins
  rw [sampler_map_map (measurable_of_countable _) hmaps, samplerIndexUnpack_law] at hm
  have hfair : rocCoinLaw (realProbability (rationalProbability (1 / 2))) = fairGuessLaw := by
    congr 1
    apply Subtype.ext
    norm_num [realProbability, rationalProbability, clipRat]
  have hseed : sampledSeed P fee = (fun streams : PrivateStreams P =>
      ((coinResult (selectorProbability P fee) (streams (.inl ()))).getD false,
        (fun stage => (coinResult (rationalProbability (1 / 2)) (streams (.inr (.inl stage)))).getD false),
        fun stage level => (coinResult (calibrationProbability P fee level)
          (streams (.inr (.inr (stage, level))))).getD false)) := rfl
  by_cases hzero : P.zeroChargeRisk fee ≤ P.certificate.risk
  · simp only [samplerIndexProbability, μ, sampler_calibration_probability, hfair,
      sampler_selector_probability, PaperProofs.Paid.Parameters.cachedAlgorithmSeedLaw,
      PaperProofs.Paid.Parameters.cachedSeedLawFrom, menuSeedLaw,
      hseed, samplerIndexUnpack, ite_eq_left hzero] at hm ⊢
    dsimp only [PaperProofs.Paid.Parameters.sharedInstance, freshInstance] at hm ⊢
    exact hm
  · simp only [samplerIndexProbability, μ, sampler_calibration_probability, hfair,
      sampler_selector_probability, PaperProofs.Paid.Parameters.cachedAlgorithmSeedLaw,
      PaperProofs.Paid.Parameters.cachedSeedLawFrom, menuSeedLaw,
      hseed, samplerIndexUnpack, ite_eq_right hzero] at hm ⊢
    dsimp only [PaperProofs.Paid.Parameters.sharedInstance, freshInstance] at hm ⊢
    exact hm

/-- Original full cached-backend private-seed target, with no sampling oracle
and no assumption about observation/correction worlds. -/
theorem privateSeedSamplingClaims : PrivateSeedSamplingClaims := by
  intro P fee _
  exact ⟨measurable_sampledSeed P fee, sampledSeed_nonreturn_null P fee, sampledSeed_law P fee⟩


end PDROC

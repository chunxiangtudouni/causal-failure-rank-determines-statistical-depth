module

public import PaperProofs.Structure.PSTR_HD_ZeroLiveSafety_012

/-! Original A19 CallClaims for the actual q=0 persistent-heap live program.
No used set, stage or reply is supplied in the public call input. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PSTRZeroLive

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine RawIncidenceLaminarRAM RawTreePreprocessingClaims

variable {bits : Nat}

theorem word_ne (left right : Nat) (hl : Fits bits left) (hr : Fits bits right) (hne : left ≠ right) :
    BitVec.ofNat bits left ≠ BitVec.ofNat bits right := by
  intro he
  have h := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] at h
  exact hne h

theorem stage_word (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (heap : BitVec bits → BitVec bits) (hr : HeapRepresents 0 full 0 configuration heap) :
    heap (BitVec.ofNat bits 4) = BitVec.ofNat bits configuration.stage := by
  have hs : (heap (BitVec.ofNat bits 4)).toNat = configuration.stage := by
    simpa [logicalHeap, dataHeap, physicalHeaderWords] using hr.2.2.2.2.1
  simpa using congrArg (BitVec.ofNat bits) hs

theorem represents_update (full : List (Finset (Fin 0))) (before after : Configuration 0)
    (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits)
    (hstage : Fits bits after.stage) (hr : HeapRepresents 0 full 0 before heap) :
    HeapRepresents 0 full 0 after
      (Function.update (Function.update heap (BitVec.ofNat bits 5) (BitVec.ofNat bits (bit after.failed)))
        (BitVec.ofNat bits 4) (BitVec.ofNat bits after.stage)) := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  have hsmall (value : Nat) (hv : value ≤ 128) : Fits bits value := by unfold Fits; omega
  have hfailed : Fits bits (bit after.failed) := by
    cases after.failed <;> apply hsmall <;> decide
  have h54 : BitVec.ofNat bits 5 ≠ BitVec.ofNat bits 4 := word_ne 5 4 (hsmall 5 (by decide)) (hsmall 4 (by decide)) (by decide)
  have hframe (address : Nat) (ha : address < 4) :
      (Function.update (Function.update heap (BitVec.ofNat bits 5) (BitVec.ofNat bits (bit after.failed)))
        (BitVec.ofNat bits 4) (BitVec.ofNat bits after.stage)) (BitVec.ofNat bits address) =
        heap (BitVec.ofNat bits address) := by
    have h4 : BitVec.ofNat bits address ≠ BitVec.ofNat bits 4 :=
      word_ne address 4 (hsmall address (by omega)) (hsmall 4 (by decide)) (by omega)
    have h5 : BitVec.ofNat bits address ≠ BitVec.ofNat bits 5 :=
      word_ne address 5 (hsmall address (by omega)) (hsmall 5 (by decide)) (by omega)
    simp only [Function.update_of_ne h4, Function.update_of_ne h5]
  rcases hr with ⟨h0, h1, h2, h3, _hs, _hf, _hm, _hu, _hc⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hframe 0 (by decide)]; exact h0
  · rw [hframe 1 (by decide)]; exact h1
  · rw [hframe 2 (by decide)]; exact h2
  · rw [hframe 3 (by decide)]; exact h3
  · simp only [logicalHeap, ↓reduceIte, dataHeap, physicalHeaderWords,
      BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero, Function.update_self,
      Nat.mod_eq_of_lt hstage]
  · simp only [logicalHeap, ↓reduceIte, dataHeap, physicalHeaderWords,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hsmall 1 (by decide)),
      Function.update_of_ne h54, Function.update_self, Nat.mod_eq_of_lt hfailed]
  · intro position hp
    simp [staticMetadata] at hp
  · intro tool
    exact Fin.elim0 tool
  · intro hq
    omega

theorem allowed_fields (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (command : Command) (ha : Allowed full configuration command) :
    configuration.failed = false ∧ configuration.stage ≤ full.length := by
  cases command with
  | query => exact ha
  | correct | error => exact ⟨ha.1, ha.2.le⟩

theorem next_numbers (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (command : Command) (ha : Allowed full configuration command) :
    (nextConfiguration 0 full configuration command).stage = configuration.stage + increment command ∧
    bit (nextConfiguration 0 full configuration command).failed = failedWord command := by
  cases command with
  | query => simp [nextConfiguration, increment, failedWord, ha.1, bit]
  | correct => simp [nextConfiguration, increment, failedWord, ha.1, bit]
  | error =>
    have hs : configuration.stage < full.length + 1 := by have hh := ha.2; omega
    simp [nextConfiguration, hs, callback, increment, failedWord, bit]

theorem encode_rank_word (N stage : Nat) :
    encodeRank 0 (if stage < N then 1 else ⊤) = rankWord N stage := by
  by_cases hs : stage < N
  · have hd : N - stage ≠ 0 := Nat.sub_ne_zero_of_lt hs
    simp [encodeRank, rankWord, hs, hd]
  · have hd : N - stage = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp [encodeRank, rankWord, hs, hd]

theorem callback_words (full : List (Finset (Fin 0))) (stage : Fin (full.length + 1))
    (used : Finset (Fin 0)) :
    encodeRank 0 (callback 0 full stage used).rank = rankWord full.length stage.val ∧
    encodeRank 0 (callback 0 full stage used).good = goodWord full.length stage.val ∧
    encodeRank 0 (callback 0 full stage used).bad = 0 ∧ (callback 0 full stage used).tool = none := by
  simp only [callback, Nat.lt_irrefl, ↓reduceDIte]
  refine ⟨encode_rank_word full.length stage.val, ?_, ?_, True.intro⟩
  · simpa only [rankWord, goodWord] using encode_rank_word full.length (stage.val + 1)
  · simp [encodeRank]

theorem callClaims (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (command : Command) (heapWords : Nat) (heap : BitVec bits → BitVec bits)
    (hb : 8 ≤ bits) (hfit : Fits bits (full.length + 128)) (hh : 6 ≤ heapWords)
    (hfoot : Fits bits ((callInput 0 full command).size + heapWords + (packingCode program).length))
    (hr : HeapRepresents 0 full 0 configuration heap) (ha : Allowed full configuration command) :
    CallClaims 512 0 full 0 heapWords program configuration command 24 heap := by
  have hs := (allowed_fields full configuration command ha).2
  have hsmall (value : Nat) (hv : value ≤ full.length + 128) : Fits bits value := hv.trans_lt hfit
  have hN := hsmall full.length (by omega)
  have hstage := hsmall configuration.stage (by omega)
  have hstage1 := hsmall (configuration.stage + 1) (by omega)
  have vals := actual_values full command configuration.stage heap hb hN hstage hstage1
    (stage_word full configuration heap hr)
  have nums := next_numbers full configuration command ha
  have hnextFit : Fits bits (nextConfiguration 0 full configuration command).stage := by
    rw [nums.1]
    cases command <;> simp only [increment, Nat.add_zero] <;> assumption
  refine ⟨dynamic_correct full command heapWords heap hb hN hh hfoot,
    actual_call_cost full command heap, ?_, ?_, ?_, ?_⟩
  · rw [vals.2.2.2.2.2]
    have hr' := represents_update full configuration (nextConfiguration 0 full configuration command) heap hb hnextFit hr
    simpa only [nums.1, nums.2] using hr'
  · intro address _hq positive
    omega
  · intro count _hc positive
    omega
  · intro hcursor
    have cr := callback_words full ⟨configuration.stage, hcursor⟩ configuration.used
    have hrankFit : Fits bits (rankWord full.length configuration.stage) := by
      unfold rankWord
      split <;> apply hsmall <;> omega
    have hgoodFit : Fits bits (goodWord full.length configuration.stage) := by
      unfold goodWord
      split <;> apply hsmall <;> omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [cr.1]
      change ((packingRun (callInput 0 full command) program 24 (packingInitial heap)).register .value).toNat = _
      rw [vals.2.1, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hrankFit
    · rw [cr.2.1]
      change ((packingRun (callInput 0 full command) program 24 (packingInitial heap)).register .old).toNat = _
      rw [vals.2.2.1, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hgoodFit
    · rw [cr.2.2.1]
      change ((packingRun (callInput 0 full command) program 24 (packingInitial heap)).register .fresh).toNat = _
      rw [vals.2.2.2.1]
      simp
    · rw [cr.2.2.2]
      change ((packingRun (callInput 0 full command) program 24 (packingInitial heap)).register .index).toNat = 0
      rw [vals.2.2.2.2.1]
      simp

/-- One common original preprocessing/live constant may absorb this bound. -/
theorem callClaims_of_constant (constant : Nat) (hconstant : 512 ≤ constant)
    (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (command : Command) (heapWords : Nat) (heap : BitVec bits → BitVec bits)
    (hb : 8 ≤ bits) (hfit : Fits bits (full.length + 128)) (hh : 6 ≤ heapWords)
    (hfoot : Fits bits ((callInput 0 full command).size + heapWords + (packingCode program).length))
    (hr : HeapRepresents 0 full 0 configuration heap) (ha : Allowed full configuration command) :
    CallClaims constant 0 full 0 heapWords program configuration command 24 heap := by
  obtain ⟨hd, hc, hn, hf, hp, hrp⟩ := callClaims full configuration command heapWords heap hb hfit hh hfoot hr ha
  exact ⟨hd, hc.trans (Nat.mul_le_mul_right _ hconstant), hn, hf, hp, hrp⟩
end PaperProofs.Structure.LaminarTree.PSTRZeroLive



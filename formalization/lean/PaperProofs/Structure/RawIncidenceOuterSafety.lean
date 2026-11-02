module

public import PaperProofs.Structure.RawIncidenceLaminarFullRAM
public import PaperProofs.Structure.RawIncidenceScanSafety
public import PaperProofs.Structure.PackingWordRefinement
public import PaperProofs.Structure.RawIncidenceCostBounds

/-! Actual-prefix safety and physical word execution of the fixed raw
incidence checker. Generic prefix composition below concerns only the
existing encoded machine run; it introduces no instruction or input data. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine
open RawIncidenceScanSafety

def PrefixSafe (P : NatState → Prop) (rom : PhysicalROM) (program : List PackingOp)
    (state : NatState) (steps : Nat) : Prop :=
  ∀ count < steps, P (natRun rom program count state)

theorem PrefixSafe.add (P : NatState → Prop) (rom : PhysicalROM) (program : List PackingOp)
    (state : NatState) (left right : Nat)
    (hleft : PrefixSafe P rom program state left)
    (hright : PrefixSafe P rom program (natRun rom program left state) right) :
    PrefixSafe P rom program state (left + right) := by
  intro count hc
  by_cases hl : count < left
  · exact hleft count hl
  · have heq : count = left + (count - left) := by omega
    rw [heq, natRun_add]
    exact hright (count - left) (by omega)

theorem PrefixSafe.mono (P : NatState → Prop) (rom : PhysicalROM) (program : List PackingOp)
    (state : NatState) {less more : Nat} (hle : less ≤ more)
    (hmore : PrefixSafe P rom program state more) : PrefixSafe P rom program state less := by
  intro count hc
  exact hmore count (hc.trans_le hle)

theorem natRun_of_halted (rom : PhysicalROM) (program : List PackingOp)
    (state : NatState) (halted : state.halted = true) (count : Nat) :
    natRun rom program count state = state := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [natRun, natStep, halted, ite_true] using ih

theorem natRun_after_halt (rom : PhysicalROM) (program : List PackingOp)
    (state : NatState) (start : Nat) (halted : (natRun rom program start state).halted = true)
    (more : Nat) : natRun rom program (start + more) state = natRun rom program start state := by
  rw [natRun_add, natRun_of_halted rom program _ halted more]

theorem natRun_halted_eq (rom : PhysicalROM) (program : List PackingOp) (state : NatState)
    (left right : Nat) (hleft : (natRun rom program left state).halted = true)
    (hright : (natRun rom program right state).halted = true) :
    natRun rom program left state = natRun rom program right state := by
  rcases le_total left right with hle | hle
  · have heq : right = left + (right - left) := by omega
    rw [heq, natRun_after_halt rom program state left hleft]
  · have heq : left = right + (left - right) := by omega
    rw [heq, natRun_after_halt rom program state right hright]

/-- A proved halting run supplies its first real HALT clock. Later halted
clocks have identical registers and heap, so the flag and cost bound transfer
without assuming an uncharged early stop is a valid implementation. -/
theorem exists_first_halt (rom : PhysicalROM) (program : List PackingOp)
    (state : NatState) (steps : Nat) (halted : (natRun rom program steps state).halted = true) :
    ∃ first : Nat, first ≤ steps ∧
      natRun rom program first state = natRun rom program steps state ∧
      (natRun rom program first state).halted = true ∧
      ∀ count < first, (natRun rom program count state).halted = false := by
  classical
  have hex : ∃ count : Nat, (natRun rom program count state).halted = true := ⟨steps, halted⟩
  let first := Nat.find hex
  have hfirst : (natRun rom program first state).halted = true := Nat.find_spec hex
  have hle : first ≤ steps := Nat.find_min' hex halted
  refine ⟨first, hle, ?_, hfirst, ?_⟩
  · have heq : steps = first + (steps - first) := by omega
    rw [heq, natRun_after_halt rom program state first hfirst]
  · intro count hc
    apply Bool.eq_false_iff.mpr
    exact Nat.find_min hex hc

def ThroughSafe (P : NatState → Prop) (rom : PhysicalROM) (program : List PackingOp)
    (state : NatState) (steps : Nat) : Prop :=
  ∀ count ≤ steps, P (natRun rom program count state)

theorem ThroughSafe.add (P : NatState → Prop) (rom : PhysicalROM) (program : List PackingOp)
    (state : NatState) (left right : Nat)
    (hleft : ThroughSafe P rom program state left)
    (hright : ThroughSafe P rom program (natRun rom program left state) right) :
    ThroughSafe P rom program state (left + right) := by
  intro count hc
  by_cases hl : count ≤ left
  · exact hleft count hl
  · have heq : count = left + (count - left) := by omega
    rw [heq, natRun_add]
    exact hright (count - left) (by omega)

theorem ThroughSafe.prefix (P : NatState → Prop) (rom : PhysicalROM) (program : List PackingOp)
    (state : NatState) (steps : Nat) (h : ThroughSafe P rom program state steps) :
    PrefixSafe P rom program state steps := fun count hc => h count hc.le

theorem checker_code_le : ∀ value ∈ packingCode checker, value ≤ 630 := by decide

theorem checker_code_wordsFit (N q : Nat) : WordsFit (indexWidth 16 N q) (packingCode checker) := by
  intro value hv
  exact fits_checker_code_word N q value (checker_code_le value hv)

theorem incidence_words_le_one (q : Nat) (full : List (Finset (Fin q))) :
    ∀ value ∈ incidence full, value ≤ 1 := by
  intro value hv
  obtain ⟨eligible, _he, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨tool, _ht, rfl⟩ := List.mem_map.mp hv
  simp only [bit]
  split_ifs <;> omega

theorem raw_rom_wordsFit (q : Nat) (full : List (Finset (Fin q))) :
    ∀ region, WordsFit (indexWidth 16 full.length q) ((rawIncidenceROM q full).words region) := by
  intro region value hv
  cases region with
  | internal | children => cases hv
  | input =>
    change value ∈ [full.length, q] ++ incidence full at hv
    rcases List.mem_append.mp hv with hheader | hbit
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hheader
      rcases hheader with hN | hQ
      · rw [hN]
        exact lt_of_le_of_lt (show full.length ≤ registerBound full.length q from by dsimp [registerBound]; omega)
          (fits_checker_register_bound full.length q)
      · rw [hQ]
        exact lt_of_le_of_lt (show q ≤ registerBound full.length q from by dsimp [registerBound]; omega)
          (fits_checker_register_bound full.length q)
    · exact lt_of_le_of_lt ((incidence_words_le_one q full value hbit).trans
        (show 1 ≤ registerBound full.length q from by dsimp [registerBound]; omega))
        (fits_checker_register_bound full.length q)

theorem safePoint_registersFit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hs : SafePoint q full state) : RegistersFit (indexWidth 16 full.length q) state := by
  intro reg
  exact lt_of_le_of_lt (hs.1 reg) (fits_checker_register_bound full.length q)

theorem safePoint_pcFit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hs : SafePoint q full state) : Fits (indexWidth 16 full.length q) state.pc :=
  fits_checker_code_word full.length q state.pc hs.2.1

theorem physical_access_of_nat {bits : Nat} (rom : PhysicalROM) (heapWords : Nat)
    (state : NatState) (op : PackingOp) (hfit : RegistersFit bits state)
    (haccess : NatAccessFits rom heapWords state op) :
    packingAccessFits rom heapWords (state.toWord bits) op := by
  have hr := toWord_register_toNat bits state hfit
  cases op with
  | base op =>
    cases op with
    | base instruction =>
      cases instruction <;> simp only [NatAccessFits, packingAccessFits, AccessFits, hr] at haccess ⊢
      all_goals exact haccess
    | subtract target left right => exact trivial
  | arithmetic operation target left right => exact trivial
  | jumpIfZero condition target => exact trivial

theorem checker_physical_fetch (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hs : SafePoint q full state) :
    fetch checker (state.toWord (indexWidth 16 full.length q)) = natFetch checker state.pc := by
  change physicalFetch (indexWidth 16 full.length q) (packingCode checker)
    (BitVec.ofNat (indexWidth 16 full.length q) state.pc).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (safePoint_pcFit q full state hs),
    physicalFetch_eq _ _ _ (checker_code_wordsFit full.length q)]
  rfl

theorem checker_pair_scan_bounds {q : Nat} (full : List (Finset (Fin q))) (i j : Nat)
    (hi : i < full.length) (hj : j < full.length) (state : NatState)
    (ready : Ready full.length q i j 100 state) :
    let result := natRun (rawIncidenceROM q full) checker (53 * q + 26) state
    result.heap 5 ≤ q ∧ result.heap 6 ≤ q ∧ result.heap 7 ≤ q := by
  let rom := rawIncidenceROM q full
  have hsetup := checker_pair_setup rom ready hj
  let scanning := natRun rom checker 19 state
  have hs := natRun_checker_pairScan_raw q full ⟨i, hi⟩ ⟨j, hj⟩ scanning
    hsetup.1.pc hsetup.1.active hsetup.1.tools hsetup.1.left hsetup.1.right
    hsetup.2.1 hsetup.2.2.1 hsetup.2.2.2.1 hsetup.2.2.2.2
  dsimp only at hs
  have hrun : natRun rom checker (53 * q + 26) state = natRun rom checker (53 * q + 7) scanning := by
    rw [show 53 * q + 26 = 19 + (53 * q + 7) from by omega, natRun_add]
  dsimp only
  rw [hrun, hs.2.1, hs.2.2.1, hs.2.2.2.1]
  exact ⟨by simpa only [Fintype.card_fin] using Finset.card_le_univ (full[i] ∩ full[j]),
    by simpa only [Fintype.card_fin] using Finset.card_le_univ (full[i] \ full[j]),
    by simpa only [Fintype.card_fin] using Finset.card_le_univ (full[j] \ full[i])⟩

/-- Physical assembly consumes actual prefix bounds of the fixed checker;
the final phase theorem below must supply those bounds from the code itself.
No safety condition is added to the raw-input eligibility class. -/
theorem checker_word_of_prefix_safety (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (steps : Nat) (hsteps : steps ≤ checkerSteps full.length q)
    (hhalt : (natRun (rawIncidenceROM q full) checker steps natInitial).halted = true)
    (hflag : (natRun (rawIncidenceROM q full) checker steps natInitial).register .value ≤ 1)
    (hcorrect : (natRun (rawIncidenceROM q full) checker steps natInitial).register .value = 1 ↔ LaminarSchedule full)
    (hsafe : PrefixSafe (SafePoint q full) (rawIncidenceROM q full) checker natInitial steps) :
    let bits := indexWidth 16 full.length q
    let heap := fun _ => BitVec.ofNat bits 0
    ∃ first : Nat, DynamicRunCorrect 8 (rawIncidenceROM q full) checker first heap ∧
      totalCost 8 (rawIncidenceROM q full) checker first heap ≤ 4096 * treeWork full.length q ∧
      (((packingRun (rawIncidenceROM q full) checker first (packingInitial heap)).register .value).toNat ≤ 1) ∧
      (((packingRun (rawIncidenceROM q full) checker first (packingInitial heap)).register .value).toNat = 1 ↔ LaminarSchedule full) := by
  let bits := indexWidth 16 full.length q
  let rom := rawIncidenceROM q full
  let heap : BitVec bits → BitVec bits := fun _ => BitVec.ofNat bits 0
  have hflag' : (natRun rom checker steps natInitial).register .value ≤ 1 := hflag
  have hword (count : Nat) (hc : count ≤ steps) :
      packingRun rom checker count (packingInitial heap) = (natRun rom checker count natInitial).toWord bits := by
    change packingRun rom checker count (natInitial.toWord bits) = _
    apply natRun_toWord rom checker natInitial count (checker_code_wordsFit full.length q)
    intro k hk
    have hs := hsafe k (hk.trans_le hc)
    exact ⟨safePoint_registersFit q full _ hs, safePoint_pcFit q full _ hs⟩
  obtain ⟨first, hfirstLe, hsame, hh, hbefore⟩ := exists_first_halt rom checker natInitial steps hhalt
  refine ⟨first, ?_, checker_totalCost_le q full hq first heap (hfirstLe.trans hsteps), ?_, ?_⟩
  · refine ⟨checker_code_wordsFit full.length q, raw_rom_wordsFit q full,
      checker_footprint_fits q full, ?_, ?_⟩
    · rw [hword first hfirstLe]
      exact hh
    · intro count hc
      have hs := hsafe count (hc.trans_le hfirstLe)
      dsimp only
      rw [hword count (hc.le.trans hfirstLe)]
      refine ⟨hbefore count hc, ?_, ?_⟩
      · change (BitVec.ofNat bits (natRun rom checker count natInitial).pc).toNat + 4 < (packingCode checker).length
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (safePoint_pcFit q full _ hs), packingCode_length, checker_length]
        have hp := hs.2.1
        omega
      · rw [checker_physical_fetch q full _ hs]
        obtain ⟨_index, _hi, _hp, ha⟩ := hs.2.2
        have ha' := ha (hbefore count hc)
        cases hd : PackingOp.decode (natFetch checker (natRun rom checker count natInitial).pc) with
        | none =>
          dsimp only [rom] at hd
          simpa only [hd] using ha'
        | some op =>
          apply physical_access_of_nat rom 8 _ op (safePoint_registersFit q full _ hs)
          dsimp only [rom] at hd
          simpa only [hd] using ha'
  · rw [hword first hfirstLe]
    change (BitVec.ofNat bits ((natRun rom checker first natInitial).register .value)).toNat ≤ 1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_le_of_lt
      (show (natRun rom checker first natInitial).register .value ≤ 630 from by rw [hsame]; exact hflag'.trans (by decide))
      (fits_checker_code_word full.length q 630 le_rfl))]
    simpa only [hsame] using hflag
  · rw [hword first hfirstLe]
    change (BitVec.ofNat bits ((natRun rom checker first natInitial).register .value)).toNat = 1 ↔ _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_le_of_lt
      (show (natRun rom checker first natInitial).register .value ≤ 630 from by rw [hsame]; exact hflag'.trans (by decide))
      (fits_checker_code_word full.length q 630 le_rfl)), hsame]
    exact hcorrect

end PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM

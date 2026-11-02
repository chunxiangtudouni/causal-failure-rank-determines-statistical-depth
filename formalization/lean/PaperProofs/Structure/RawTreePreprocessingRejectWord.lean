module

public import PaperProofs.Structure.RawTreePreprocessingStartWord

/-! Nonlaminar raw inputs execute the same whole program's rejection
branch on the physical word machine.  Its actual terminal HALT is charged.
The accepted constructor remains a separate unfinished A06 obligation. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.RawTreePreprocessingRejectWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM
open RawTreePreprocessingNat (program)
open RawTreePreprocessingCostBounds (heapWords)
open RawTreePreprocessingWordInterface (SafePoint)
open RawTreePreprocessingStartWord (prefix_word_eq)

/-- A generic adapter for the already fixed whole program.  The invariant
and first-HALT conditions are supplied below by the actual rejection path. -/
theorem dynamicCorrect_of_safe_prefix (q : Nat) (full : List (Finset (Fin q))) (steps : Nat)
    (hsafe : PrefixSafe (SafePoint q full) (rawIncidenceROM q full) program natInitial steps)
    (hhalt : (natRun (rawIncidenceROM q full) program steps natInitial).halted = true)
    (hbefore : ∀ count < steps, (natRun (rawIncidenceROM q full) program count natInitial).halted = false) :
    DynamicRunCorrect (heapWords full.length q) (rawIncidenceROM q full) program steps
      (fun _ => BitVec.ofNat (indexWidth 16 full.length q) 0) := by
  have hword (count : Nat) (hc : count ≤ steps) := prefix_word_eq q full count
    (PrefixSafe.mono _ _ _ _ hc hsafe)
  refine ⟨RawTreePreprocessingCostBounds.code_wordsFit full.length q, raw_rom_wordsFit q full,
    RawTreePreprocessingCostBounds.footprint_fits q full, ?_, ?_⟩
  · rw [hword steps le_rfl]
    exact hhalt
  · intro count hc
    dsimp only
    rw [hword count hc.le]
    have hs := hsafe count hc
    refine ⟨hbefore count hc, ?_, ?_⟩
    · change (BitVec.ofNat (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) program count natInitial).pc).toNat + 4 < _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (RawTreePreprocessingWordInterface.safePoint_pcFit q full _ hs)]
      exact RawTreePreprocessingWordInterface.safePoint_fetchWindow q full _ hs
    · rw [RawTreePreprocessingWordInterface.safePoint_physicalFetch q full _ hs]
      obtain ⟨hr, _index, _hi, _hp, ha⟩ := hs
      have ha' := ha (hbefore count hc)
      cases hd : PackingOp.decode (natFetch program
          (natRun (rawIncidenceROM q full) program count natInitial).pc) with
      | none => simpa only [hd] using ha'
      | some op =>
        apply physical_access_of_nat _ (heapWords full.length q) _ op hr
        simpa only [hd] using ha'

theorem safePoint_halt (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hp : state.pc = 5 * program.length) (hr : RegistersFit (indexWidth 16 full.length q) state) :
    SafePoint q full state := by
  refine ⟨hr, program.length, le_rfl, hp, ?_⟩
  intro _
  rw [hp, natFetch_halt, decode_halt]

/-- No prefix-safety hypothesis is added to nonlaminar input eligibility. -/
theorem rejects (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : ¬ LaminarSchedule full) :
    ∃ steps ≤ checkerSteps full.length q + 2,
      DynamicRunCorrect (heapWords full.length q) (rawIncidenceROM q full) program steps
        (fun _ => BitVec.ofNat (indexWidth 16 full.length q) 0) ∧
      totalCost (heapWords full.length q) (rawIncidenceROM q full) program steps
        (fun _ => BitVec.ofNat (indexWidth 16 full.length q) 0) ≤ 262144 * treeWork full.length q ∧
      ((packingRun (rawIncidenceROM q full) program steps
        (packingInitial (fun _ => BitVec.ofNat (indexWidth 16 full.length q) 0))).register .value).toNat = 0 := by
  obtain ⟨clock, hclock, entry⟩ := RawTreePreprocessingStartWord.gate_entry q full
  let before := natRun (rawIncidenceROM q full) program clock natInitial
  have hp : before.pc = 5 * program.length := (entry.rejects hl).1
  have hv : before.register .value = 0 := (entry.rejects hl).2
  have hh : natRun (rawIncidenceROM q full) program (clock + 1) natInitial =
      { before with halted := true } := by
    rw [natRun_succ]
    exact natStep_halt _ program before hp entry.active
  have hlast : PrefixSafe (SafePoint q full) (rawIncidenceROM q full) program before 1 := by
    intro count hc
    have hz : count = 0 := by omega
    rw [hz]
    exact safePoint_halt q full before hp entry.fit
  have hsafe := PrefixSafe.add _ _ _ _ clock 1 entry.safe hlast
  have hhalt : (natRun (rawIncidenceROM q full) program (clock + 1) natInitial).halted = true := by rw [hh]
  have hfirst : ∀ count < clock + 1,
      (natRun (rawIncidenceROM q full) program count natInitial).halted = false := by
    intro count hc
    exact natRun_active_of_le _ program natInitial count clock (by omega) entry.active
  have hcostSteps : clock + 1 ≤ 16384 * treeWork full.length q := by
    have hchecker := checkerSteps_le full.length q hq
    have hunit : 1 ≤ treeWork full.length q := by
      unfold treeWork
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega : 1 ≤ full.length + q + 1) 2) hq
    omega
  refine ⟨clock + 1, by omega, dynamicCorrect_of_safe_prefix q full (clock + 1) hsafe hhalt hfirst,
    RawTreePreprocessingCostBounds.totalCost_le q full hq (clock + 1) _ hcostSteps, ?_⟩
  rw [prefix_word_eq q full (clock + 1) hsafe, hh]
  change (BitVec.ofNat (indexWidth 16 full.length q) (before.register .value)).toNat = 0
  rw [hv]
  exact Nat.mod_eq_of_lt (RawTreePreprocessingCodeBounds.constant_fits full.length q 0 (by decide))

end PaperProofs.Structure.LaminarTree.RawTreePreprocessingRejectWord

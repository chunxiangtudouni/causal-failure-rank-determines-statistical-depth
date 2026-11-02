module

public import PaperProofs.Structure.RawIncidenceCheckerPhase
public import PaperProofs.Structure.PackingProgramPrefix

/-! The actual active boundary immediately before the fixed checker's
first encoded HALT. Appending code preserves every prefix through this
boundary, so no halted state needs to be restarted. This component neither
implements a dispatcher nor constructs or serializes the inclusion tree. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine
  RawIncidenceScanSafety

theorem checker_before_first_halt (q : Nat) (full : List (Finset (Fin q))) :
    ∃ count : Nat, count + 1 ≤ checkerSteps full.length q ∧
      (natRun (rawIncidenceROM q full) checker count natInitial).halted = false ∧
      (natRun (rawIncidenceROM q full) checker count natInitial).pc = 5 * checker.length ∧
      (natRun (rawIncidenceROM q full) checker count natInitial).register .value ≤ 1 ∧
      ((natRun (rawIncidenceROM q full) checker count natInitial).register .value = 1 ↔ LaminarSchedule full) ∧
      natRun (rawIncidenceROM q full) checker (count + 1) natInitial =
        { natRun (rawIncidenceROM q full) checker count natInitial with halted := true } ∧
      (∀ clock < count,
        (natRun (rawIncidenceROM q full) checker clock natInitial).halted = false ∧
        (natRun (rawIncidenceROM q full) checker clock natInitial).pc < 5 * checker.length ∧
        ∃ index < checker.length,
          (natRun (rawIncidenceROM q full) checker clock natInitial).pc = 5 * index) ∧
      ∀ suffix : List PackingOp, ∀ clock ≤ count,
        natRun (rawIncidenceROM q full) (checker ++ suffix) clock natInitial =
          natRun (rawIncidenceROM q full) checker clock natInitial := by
  let rom := rawIncidenceROM q full
  obtain ⟨steps, hsteps, hsafe, hhalt⟩ := checker_has_safe_halt q full
  obtain ⟨first, hfirstLe, _hsame, hfirstHalt, hbefore⟩ :=
    exists_first_halt rom checker natInitial steps hhalt
  have hfirstPos : 0 < first := by
    have hne : first ≠ 0 := by
      intro hz
      have hh := hfirstHalt
      rw [hz] at hh
      change false = true at hh
      cases hh
    exact Nat.pos_of_ne_zero hne
  let count := first - 1
  have hfirstEq : count + 1 = first := by dsimp [count]; omega
  have hcountLt : count < first := by omega
  let boundary := natRun rom checker count natInitial
  have hactive : boundary.halted = false := hbefore count hcountLt
  have hpoint : SafePoint q full boundary := hsafe count (hcountLt.le.trans hfirstLe)
  obtain ⟨index, hindex, hpc, _haccess⟩ := hpoint.2.2
  have hnextHalt : (natStep rom checker boundary).halted = true := by
    have hh := hfirstHalt
    rw [← hfirstEq, natRun_succ] at hh
    exact hh
  have hindexEq : index = checker.length := by
    by_contra hne
    have hi : index < checker.length := lt_of_le_of_ne hindex hne
    have hs := natStep_of_index rom checker boundary index hi hpc hactive
    have hh := hnextHalt
    rw [hs, natExecuteOp_halted, hactive] at hh
    cases hh
  have hboundaryPc : boundary.pc = 5 * checker.length := by simpa only [hindexEq] using hpc
  have hterminal : natRun rom checker (count + 1) natInitial = { boundary with halted := true } := by
    rw [natRun_succ]
    exact natStep_halt rom checker boundary hboundaryPc hactive
  obtain ⟨semanticSteps, _hsemanticBound, hsemanticHalt, hsemanticFlag, hsemanticCorrect⟩ :=
    nat_checker_correct q full
  have hsemanticSame := natRun_halted_eq rom checker natInitial first semanticSteps hfirstHalt hsemanticHalt
  have hvalue : boundary.register .value = (natRun rom checker semanticSteps natInitial).register .value := by
    have hv := congrArg (fun state : NatState => state.register .value) hterminal
    rw [hfirstEq, hsemanticSame] at hv
    exact hv.symm
  have hbody : ∀ clock < count,
      (natRun rom checker clock natInitial).halted = false ∧
        ∃ index < checker.length, (natRun rom checker clock natInitial).pc = 5 * index := by
    intro clock hc
    have hclockFirst : clock < first := hc.trans hcountLt
    have ha := hbefore clock hclockFirst
    have hp := hsafe clock (hclockFirst.le.trans hfirstLe)
    obtain ⟨earlierIndex, hi, hpc, _hguard⟩ := hp.2.2
    have hstrict : earlierIndex < checker.length := by
      by_contra hnot
      have heq : earlierIndex = checker.length := by omega
      have hpHalt : (natRun rom checker clock natInitial).pc = 5 * checker.length := by
        simpa only [heq] using hpc
      have hnextFalse := hbefore (clock + 1) (by omega)
      have hnextTrue : (natRun rom checker (clock + 1) natInitial).halted = true := by
        rw [natRun_succ, natStep_halt rom checker _ hpHalt ha]
      rw [hnextTrue] at hnextFalse
      cases hnextFalse
    exact ⟨ha, earlierIndex, hstrict, hpc⟩
  refine ⟨count, hfirstEq.le.trans (hfirstLe.trans hsteps), hactive, hboundaryPc, ?_, ?_, hterminal, ?_, ?_⟩
  · rw [hvalue]
    exact hsemanticFlag
  · rw [hvalue]
    exact hsemanticCorrect
  · intro clock hc
    obtain ⟨ha, earlierIndex, hi, hpc⟩ := hbody clock hc
    refine ⟨ha, ?_, earlierIndex, hi, hpc⟩
    rw [hpc]
    omega
  · intro suffix
    exact ProgramPrefix.natRun_append_all_prefixes rom checker suffix count natInitial
      (fun clock hc => (hbody clock hc).2)

end PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM

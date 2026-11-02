module

public import PaperProofs.Structure.RawTreePreprocessingA06Closure
public import PaperProofs.Structure.PackingProgramPrefix

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePreHalt001

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawTreePreprocessingWordInterface
open RawTreePreprocessingNat (program)

/-- A true instruction boundary of the same A06 raw run, before encoded HALT.
The serialized output is already present; no stopped state is restarted. -/
structure Ready (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop where
  pc : state.pc = 5 * program.length
  active : state.halted = false
  accepted : state.register .value = 1
  nodes : state.register .old = (prepareNormalization q full).indexed.nodes.size
  length : state.register .fresh = (serializeROM (givenTreeROM q full)).length
  words : ∀ position < (serializeROM (givenTreeROM q full)).length,
    state.heap position = (serializeROM (givenTreeROM q full)).getD position 0

/-- Original positive-q/laminar inputs alone produce the ACTIVE serialized
output boundary. Every previous clock executes a real body instruction. -/
theorem active_output (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) :
    ∃ clock ≤ 16384 * treeWork full.length q,
      let state := natRun (rawIncidenceROM q full) program clock natInitial
      Ready q full state ∧
      PrefixSafe (SafePoint q full) (rawIncidenceROM q full) program natInitial clock ∧
      (∀ count < clock, ∃ index < program.length,
        (natRun (rawIncidenceROM q full) program count natInitial).pc = 5 * index) := by
  obtain ⟨steps, hsteps, hhalt, _hflag, _hiff, houtput⟩ :=
    RawTreePreprocessingNat.raw_preprocessing q full hq
  have output := houtput hl
  obtain ⟨first, hfirst, hsame, hh, hbefore⟩ :=
    exists_first_halt (rawIncidenceROM q full) program natInitial steps hhalt
  have hp : 0 < first := by
    by_contra hn
    have hz : first = 0 := by omega
    subst first
    change false = true at hh
    contradiction
  let clock := first - 1
  have hc : clock + 1 = first := by dsimp only [clock]; omega
  have ha : (natRun (rawIncidenceROM q full) program clock natInitial).halted = false :=
    hbefore clock (by omega)
  have hs : SafePoint q full (natRun (rawIncidenceROM q full) program clock natInitial) :=
    RawTreePreprocessingA06Closure.all_prefix_safe q full hq first clock (by omega)
  obtain ⟨_hr, index, hi, hpc, _access⟩ := hs
  have hd : PackingOp.decode (natFetch program
      (natRun (rawIncidenceROM q full) program clock natInitial).pc) = none := by
    have hlast : (natStep (rawIncidenceROM q full) program
        (natRun (rawIncidenceROM q full) program clock natInitial)).halted = true := by
      rw [← natRun_succ, hc]
      exact hh
    cases he : PackingOp.decode (natFetch program
        (natRun (rawIncidenceROM q full) program clock natInitial).pc) with
    | none => rfl
    | some op =>
      simp only [natStep, ha, Bool.false_eq_true, ite_false, he,
        natExecuteOp_halted] at hlast
  have hend : index = program.length := by
    by_contra hn
    have hlt : index < program.length := by omega
    rw [hpc, natFetch_body program index hlt, decode_encode] at hd
    contradiction
  have hboundary : (natRun (rawIncidenceROM q full) program clock natInitial).pc =
      5 * program.length := by simpa only [hend] using hpc
  have hlast : natRun (rawIncidenceROM q full) program first natInitial =
      { natRun (rawIncidenceROM q full) program clock natInitial with halted := true } := by
    rw [← hc, natRun_succ]
    exact natStep_halt _ _ _ hboundary ha
  have hfinal : natRun (rawIncidenceROM q full) program steps natInitial =
      { natRun (rawIncidenceROM q full) program clock natInitial with halted := true } :=
    hsame.symm.trans hlast
  refine ⟨clock, by omega, ?_⟩
  refine ⟨?_, RawTreePreprocessingA06Closure.all_prefix_safe q full hq clock, ?_⟩
  · refine ⟨hboundary, ha, ?_, ?_, ?_, ?_⟩
    · have h := output.accepted
      rw [hfinal] at h
      exact h
    · have h := output.nodes
      rw [hfinal] at h
      exact h
    · have h := output.length
      rw [hfinal] at h
      exact h
    · intro position hposition
      have h := output.words position hposition
      rw [hfinal] at h
      exact h
  · intro count hcount
    have hs' := RawTreePreprocessingA06Closure.all_prefix_safe q full hq first count (by omega)
    obtain ⟨_hr', index', hi', hp', _access'⟩ := hs'
    refine ⟨index', ?_, hp'⟩
    by_contra hn
    have he : index' = program.length := by omega
    have hpc' : (natRun (rawIncidenceROM q full) program count natInitial).pc =
        5 * program.length := by simpa only [he] using hp'
    have halt : (natRun (rawIncidenceROM q full) program (count + 1) natInitial).halted = true := by
      rw [natRun_succ, natStep_halt _ _ _ hpc' (hbefore count (by omega))]
    have active := hbefore (count + 1) (by omega)
    rw [halt] at active
    contradiction

/-- Arbitrary appended body keeps the entire real pre-HALT computation,
including the endpoint. This does not assert safety of the appended code. -/
theorem append_active_output (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) (later : List PackingOp) :
    ∃ clock ≤ 16384 * treeWork full.length q,
      Ready q full (natRun (rawIncidenceROM q full) (program ++ later) clock natInitial) ∧
      ∀ count ≤ clock,
        natRun (rawIncidenceROM q full) (program ++ later) count natInitial =
          natRun (rawIncidenceROM q full) program count natInitial := by
  obtain ⟨clock, hbound, ready, _safe, hbody⟩ := active_output q full hq hl
  have heq := ProgramPrefix.natRun_append_all_prefixes (rawIncidenceROM q full)
    program later clock natInitial hbody
  refine ⟨clock, hbound, ?_, heq⟩
  rw [heq clock le_rfl]
  exact ready

end PaperProofs.Structure.LaminarTree.PA06A19PreparePreHalt001

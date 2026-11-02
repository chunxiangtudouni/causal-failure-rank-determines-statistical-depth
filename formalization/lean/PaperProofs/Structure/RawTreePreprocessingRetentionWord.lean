module

public import PaperProofs.Structure.RawTreePreprocessingStartWord
public import PaperProofs.Structure.RawCandidateRetentionWordSafety
public import PaperProofs.Structure.RawCandidateRetentionWordLoop

/-! The original raw-input program's actual retention handoff.  The
retention phase may overwrite the value register; only the final footer
restores the success flag.  The next phase receives actual tables. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.RawTreePreprocessingRetentionWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM
open RawTreePreprocessingNat (program)
open RawCandidateWorkspaceInit (workspaceBase candidateCount workspaceBase_ge)

def afterRetention : List PackingOp :=
  RawCandidateOrderingRAM.programAt RawCandidateMetadataPrefix.orderingStart ++
    (RawCandidateParentRAM.programAt RawCandidateTreePrefix.parentStart ++
      RawCandidateSerializedInputRAM.programAt RawCandidateTreePrefix.inputStart ++ RawTreePreprocessingNat.tail)

def front : List PackingOp := RawCandidateMetadataPrefix.front afterRetention

theorem program_eq : program = RawCandidateMetadataPrefix.program afterRetention := rfl

theorem front_length : front.length = 144 := by
  simp only [front, RawCandidateMetadataPrefix.front_length,
    RawCandidateMetadataPrefix.retentionStart, checker_length]

theorem front_program : front ++ RawCandidateRetentionRAM.programAt front.length ++ afterRetention = program := by
  exact (RawCandidateMetadataPrefix.program_eq afterRetention).trans program_eq.symm

theorem retention_slice : 144 + 398 ≤ program.length ∧
    ∀ position < 398, program.getD (144 + position) RawCandidateRetentionRAM.paddingOp =
      (RawCandidateRetentionRAM.programAt 144).getD position RawCandidateRetentionRAM.paddingOp := by
  have h := RawCandidateRetentionRAM.append_slice front afterRetention
  rw [front_program, front_length] at h
  exact h

theorem retention_point (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hs : RawCandidateRetentionWordSafety.SafePoint q full program 144 state) :
    RawTreePreprocessingWordInterface.SafePoint q full state := by
  obtain ⟨hr, offset, hoff, hp, _ha, op, hd, hx⟩ := hs
  refine ⟨hr, 144 + offset, by have h := retention_slice.1; omega, hp, ?_⟩
  intro _
  rw [hd]
  exact hx

structure Ready (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop where
  fit : RegistersFit (indexWidth 16 full.length q) state
  ptr : state.heap 8 = workspaceBase full.length q
  header : state.heap (workspaceBase full.length q) = candidateCount full.length q
  tables : RawCandidateOrderingRAM.InputTables (workspaceBase full.length q) (candidateCount full.length q)
    (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state
  high_zero : ∀ address, workspaceBase full.length q + 4 + 2 * candidateCount full.length q ≤ address → state.heap address = 0
  pc : state.pc = 5 * 542
  active : state.halted = false

def clockBound (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  checkerSteps full.length q + 17 + RawCandidateRetentionRAM.totalSteps full.length q

/-- Original raw input establishes the actual candidate tables and every
prefix's word/access safety up to the sorting entry. No cached result,
pointer/header, safe execution or private scratch value is an input. -/
theorem retained_entry (q : Nat) (full : List (Finset (Fin q))) (hl : LaminarSchedule full) :
    ∃ clock ≤ clockBound q full,
      PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full)
        (rawIncidenceROM q full) program natInitial clock ∧
      Ready q full (natRun (rawIncidenceROM q full) program clock natInitial) ∧
      packingRun (rawIncidenceROM q full) program clock
        (packingInitial (fun _ => BitVec.ofNat (indexWidth 16 full.length q) 0)) =
          (natRun (rawIncidenceROM q full) program clock natInitial).toWord (indexWidth 16 full.length q) := by
  obtain ⟨first, hfirst, hsafePrefix, entry, _word⟩ := RawTreePreprocessingStartWord.initialized_entry q full hl
  let before := natRun (rawIncidenceROM q full) program first natInitial
  let steps := RawCandidateRetentionRAM.totalSteps full.length q
  let after := natRun (rawIncidenceROM q full) program steps before
  have hend : Fits (indexWidth 16 full.length q) (5 * (144 + 398)) :=
    RawTreePreprocessingCodeBounds.constant_fits _ _ _ (by decide)
  have hs := RawCandidateRetentionWordLoop.retention_nat_safe q full program 144
    retention_slice.1 retention_slice.2 before entry.base entry.count entry.pc entry.active entry.fit hend
  have sem := RawCandidateRetentionRAM.retention q full program 144 retention_slice.1 retention_slice.2
    (workspaceBase full.length q) (workspaceBase_ge full.length q) before
    entry.base entry.count entry.pc entry.active
  dsimp only at sem
  rcases sem with ⟨ptr, header, _index, arrays, frame, pc, active⟩
  have hout : Ready q full after := by
    refine ⟨hs.2.1, ptr, header, ?_, ?_, pc, active⟩
    · constructor
      · intro index hi
        simpa only [RawCandidateOrderingRAM.arraySlot, Nat.mul_zero, Nat.add_zero,
          RawCandidateStableOrder.candidateCard, RawCandidateRetentionRAM.cardAddress] using (arrays index hi).1
      · intro index hi
        have heq : RawCandidateOrderingRAM.arraySlot (workspaceBase full.length q) (candidateCount full.length q) 1 index =
            RawCandidateRetentionRAM.keepAddress (workspaceBase full.length q) (candidateCount full.length q) index := by
          unfold RawCandidateOrderingRAM.arraySlot RawCandidateRetentionRAM.keepAddress
          omega
        rw [heq]
        exact (arrays index hi).2
    · intro address hadr
      have hb := workspaceBase_ge full.length q
      have ha : 8 ≤ address := by omega
      change after.heap address = 0
      rw [frame address ⟨ha, by omega, by omega, by omega, Or.inr hadr⟩]
      exact entry.untouched address ha (by omega) (by omega)
  have lifted : PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full)
      (rawIncidenceROM q full) program before steps :=
    fun count hc => retention_point q full _ (hs.1 count hc)
  have allSafe : PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full)
      (rawIncidenceROM q full) program natInitial (first + steps) :=
    PrefixSafe.add _ _ _ _ first steps hsafePrefix lifted
  refine ⟨first + steps, by unfold clockBound; dsimp only [steps]; omega, allSafe, ?_,
    RawTreePreprocessingStartWord.prefix_word_eq q full (first + steps) allSafe⟩
  rw [natRun_add]
  exact hout

end PaperProofs.Structure.LaminarTree.RawTreePreprocessingRetentionWord

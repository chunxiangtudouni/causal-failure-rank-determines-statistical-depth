module

public import PaperProofs.Structure.RawTreePreprocessingRetentionWord
public import PaperProofs.Structure.RawCandidateOrderingWord

/-! The same original raw-input program reaches the actual sorting output.
Its initial ord words are derived from the retained run's untouched zero
region; neither a sorted answer nor a safety certificate is an input. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.RawTreePreprocessingOrderingWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM
open RawTreePreprocessingNat (program)
open RawCandidateWorkspaceInit (workspaceBase candidateCount workspaceBase_ge)

def afterOrdering : List PackingOp :=
  RawCandidateParentRAM.programAt RawCandidateTreePrefix.parentStart ++
    RawCandidateSerializedInputRAM.programAt RawCandidateTreePrefix.inputStart ++ RawTreePreprocessingNat.tail

def front : List PackingOp := RawCandidateMetadataPrefix.orderingFront afterOrdering

theorem front_length : front.length = 542 := by
  simp only [front, RawCandidateMetadataPrefix.orderingFront_length,
    RawCandidateMetadataPrefix.orderingStart, RawCandidateMetadataPrefix.retentionStart, checker_length]

theorem front_program : front ++ RawCandidateOrderingRAM.programAt front.length ++ afterOrdering = program := by
  exact RawCandidateMetadataPrefix.orderedProgram_eq afterOrdering

theorem ordering_slice : 542 + 303 ≤ program.length ∧
    ∀ position < 303, program.getD (542 + position) RawCandidateOrderingRAM.paddingOp =
      (RawCandidateOrderingRAM.programAt 542).getD position RawCandidateOrderingRAM.paddingOp := by
  have h := RawCandidateOrderingRAM.append_slice front afterOrdering
  rw [front_program, front_length] at h
  exact h

theorem ordering_point (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hs : RawCandidateOrderingWord.SafePoint q full program 542 state) :
    RawTreePreprocessingWordInterface.SafePoint q full state := by
  obtain ⟨hr, offset, hoff, hp, _ha, op, hd, hx⟩ := hs
  refine ⟨hr, 542 + offset, by have h := ordering_slice.1; omega, hp, ?_⟩
  intro _
  rw [hd]
  exact hx

structure Ready (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop where
  fit : RegistersFit (indexWidth 16 full.length q) state
  sorted : ∃ before, RawCandidateOrderingRAM.Sorted q full (workspaceBase full.length q) 542 before state
  inverse_bound : ∀ index < candidateCount full.length q,
    state.heap (RawCandidateOrderingRAM.arraySlot (workspaceBase full.length q) (candidateCount full.length q) 3 index) ≤
      candidateCount full.length q
  high_zero : ∀ address, workspaceBase full.length q + 5 + 4 * candidateCount full.length q ≤ address → state.heap address = 0
  pc : state.pc = 5 * 845
  active : state.halted = false

def clockBound (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  RawTreePreprocessingRetentionWord.clockBound q full + RawCandidateOrderingRAM.totalSteps (candidateCount full.length q)

theorem ordered_entry (q : Nat) (full : List (Finset (Fin q))) (hl : LaminarSchedule full) :
    ∃ clock ≤ clockBound q full,
      PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full)
        (rawIncidenceROM q full) program natInitial clock ∧
      Ready q full (natRun (rawIncidenceROM q full) program clock natInitial) ∧
      packingRun (rawIncidenceROM q full) program clock
        (packingInitial (fun _ => BitVec.ofNat (indexWidth 16 full.length q) 0)) =
          (natRun (rawIncidenceROM q full) program clock natInitial).toWord (indexWidth 16 full.length q) := by
  obtain ⟨first, hfirst, hsafePrefix, entry, _word⟩ := RawTreePreprocessingRetentionWord.retained_entry q full hl
  let before := natRun (rawIncidenceROM q full) program first natInitial
  let steps := RawCandidateOrderingRAM.totalSteps (candidateCount full.length q)
  let after := natRun (rawIncidenceROM q full) program steps before
  have hord : RawCandidateOrderingWord.OrdFits q full before := by
    intro position hp
    rw [entry.high_zero _ (by unfold RawCandidateOrderingRAM.arraySlot; omega)]
    exact RawCandidateWorkspaceWordMacros.small_constant_fits _ _ _ (by decide)
  have hend : Fits (indexWidth 16 full.length q) (5 * (542 + 303)) :=
    RawTreePreprocessingCodeBounds.constant_fits _ _ _ (by decide)
  have hs := RawCandidateOrderingWord.sort_nat_safe q full program 542 ordering_slice.1 ordering_slice.2
    before entry.fit entry.ptr entry.header entry.tables hord entry.pc entry.active hend
  have sem : RawCandidateOrderingRAM.Sorted q full (workspaceBase full.length q) 542 before after :=
    RawCandidateOrderingRAM.sort (rawIncidenceROM q full) program 542 ordering_slice.1 ordering_slice.2
    q full (workspaceBase full.length q) before (workspaceBase_ge full.length q)
    entry.ptr entry.header entry.tables entry.pc entry.active
  have hM : candidateCount full.length q = full.length + q + 1 := rfl
  have hout : Ready q full after := by
    refine ⟨hs.2, ⟨before, sem⟩, ?_, ?_, sem.returned.pc, sem.returned.active⟩
    · intro index hi
      change after.heap (RawCandidateOrderingRAM.arraySlot (workspaceBase full.length q) (full.length + q + 1) 3 index) ≤ full.length + q + 1
      rw [sem.output.inverse index hi]
      have hless := RawCandidateRankScan.lessCount_lt_candidateCount q full index hi
      split <;> omega
    · intro address hadr
      rw [sem.frame address ⟨by have hb := workspaceBase_ge full.length q; omega,
        by omega, by omega, by omega,
        fun index hi => by unfold RawCandidateOrderingRAM.arraySlot; omega,
        fun index hi => by unfold RawCandidateOrderingRAM.arraySlot; omega,
        by unfold RawCandidateOrderingRAM.arraySlot; omega⟩]
      exact entry.high_zero address (by omega)
  have lifted : PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full)
      (rawIncidenceROM q full) program before steps :=
    fun count hc => ordering_point q full _ (hs.1 count hc)
  have allSafe : PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full)
      (rawIncidenceROM q full) program natInitial (first + steps) :=
    PrefixSafe.add _ _ _ _ first steps hsafePrefix lifted
  refine ⟨first + steps, by unfold clockBound; dsimp only [steps]; omega, allSafe, ?_,
    RawTreePreprocessingStartWord.prefix_word_eq q full (first + steps) allSafe⟩
  rw [natRun_add]
  exact hout

end PaperProofs.Structure.LaminarTree.RawTreePreprocessingOrderingWord

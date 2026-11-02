module

public import PaperProofs.Structure.RawTreePreprocessingOrderingWord
public import PaperProofs.Structure.RawCandidateParentWord

/-! The same raw-input program's actual parent-cache handoff.  Runtime
candidate/order/inverse tables and every word/access invariant come from
the preceding physical run; the output parent cache is proved separately. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.RawTreePreprocessingParentWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM
open RawTreePreprocessingNat (program)
open RawCandidateWorkspaceInit (workspaceBase candidateCount workspaceBase_ge)

theorem parent_slice : 845 + 361 ≤ program.length ∧
    ∀ position < 361, program.getD (845 + position) RawCandidateParentRAM.paddingOp =
      (RawCandidateParentRAM.programAt 845).getD position RawCandidateParentRAM.paddingOp := by
  have h := RawCandidateTreePrefix.parent_slice RawTreePreprocessingNat.tail
  rw [RawCandidateTreePrefix.parentStart_eq] at h
  exact h

theorem parent_point (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hs : RawCandidateParentWordSafety.SafePoint q full program 845 state) :
    RawTreePreprocessingWordInterface.SafePoint q full state := by
  obtain ⟨hr, offset, hoff, hp, _ha, op, hd, hx⟩ := hs
  refine ⟨hr, 845 + offset, by have h := parent_slice.1; omega, hp, ?_⟩
  intro _
  rw [hd]
  exact hx

structure Ready (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop where
  fit : RegistersFit (indexWidth 16 full.length q) state
  entry : RawCandidateTreePrefix.ParentEntry q full state
  high_zero : ∀ address, workspaceBase full.length q + 5 + 5 * candidateCount full.length q ≤ address → state.heap address = 0

def clockBound (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  RawTreePreprocessingOrderingWord.clockBound q full +
    512 * (candidateCount full.length q + 1) * (candidateCount full.length q + 1) * (q + 1)

theorem parent_entry (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full) :
    ∃ clock ≤ clockBound q full,
      PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full)
        (rawIncidenceROM q full) program natInitial clock ∧
      Ready q full (natRun (rawIncidenceROM q full) program clock natInitial) ∧
      packingRun (rawIncidenceROM q full) program clock
        (packingInitial (fun _ => BitVec.ofNat (indexWidth 16 full.length q) 0)) =
          (natRun (rawIncidenceROM q full) program clock natInitial).toWord (indexWidth 16 full.length q) := by
  obtain ⟨first, hfirst, hsafePrefix, entry, _word⟩ := RawTreePreprocessingOrderingWord.ordered_entry q full hl
  let state := natRun (rawIncidenceROM q full) program first natInitial
  obtain ⟨before, sorted⟩ := entry.sorted
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  let nodes := (RawCandidateOrder.retainedCandidateIndices q full).length
  let order := RawCandidateParentRAM.observedOrder q full B state
  let inverse := RawCandidateParentRAM.observedInverse q full B state
  let steps := RawCandidateParentRAM.totalSteps full.length q nodes order
  let after := natRun (rawIncidenceROM q full) program steps state
  have hb : 16 ≤ B := workspaceBase_ge _ _
  have tables := RawCandidateParentRAM.InputTables.of_sorted q full B 542 before state sorted hq
  have hend : Fits (indexWidth 16 full.length q) (5 * (845 + 361)) :=
    RawTreePreprocessingCodeBounds.constant_fits _ _ _ (by decide)
  have hs := RawCandidateParentWord.parents_of_sorted_nat_safe q full program 845 parent_slice.1 parent_slice.2
    542 before state sorted hq entry.pc entry.active entry.fit hend
  have sem := RawCandidateParentRAM.parents q full program 845 parent_slice.1 parent_slice.2
    B nodes order inverse state hb tables entry.pc entry.active
  have hp := RawCandidateParentRAM.parents_prepared q full hq program 845 parent_slice.1 parent_slice.2
    B 542 before state hb sorted entry.pc entry.active
  have hout : Ready q full after := by
    refine ⟨hs.2, ⟨?_, hp, sem.2.2.2.2.1, sem.2.2.2.2.2⟩, ?_⟩
    · exact RawCandidateTreePrefix.inputSpec_of_parent_tables q full hq before state after sorted sem.1
    · intro address hadr
      have frame : ∀ address, RawCandidateParentRAM.ProtectedAddress B M nodes address →
          after.heap address = state.heap address := sem.2.2.2.1
      rw [frame address ⟨by omega, by omega, by omega, by omega, ?_⟩]
      · exact entry.high_zero address (by omega)
      · right
        have hnodes : nodes ≤ M := tables.nodes_le
        change B + 5 + 5 * M ≤ address at hadr
        unfold RawCandidateParentRAM.parentSlot RawCandidateOrderingRAM.arraySlot
        omega
  have lifted : PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full)
      (rawIncidenceROM q full) program state steps := fun count hc => parent_point q full _ (hs.1 count hc)
  have allSafe : PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full)
      (rawIncidenceROM q full) program natInitial (first + steps) :=
    PrefixSafe.add _ _ _ _ first steps hsafePrefix lifted
  have hcost := RawCandidateParentRAM.totalSteps_le full.length q nodes order
  have hcost' : steps ≤ 512 * (M + 1) * (M + 1) * (q + 1) := hcost.trans (by
    change 512 * (nodes + 1) * (M + 1) * (q + 1) ≤ _
    gcongr
    exact tables.nodes_le)
  refine ⟨first + steps, by unfold clockBound; dsimp only [M] at hcost'; omega, allSafe, ?_,
    RawTreePreprocessingStartWord.prefix_word_eq q full (first + steps) allSafe⟩
  rw [natRun_add]
  exact hout

end PaperProofs.Structure.LaminarTree.RawTreePreprocessingParentWord

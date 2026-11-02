module

public import Structure.PSTR_UniformQueryEmbeddings_114
public import Structure.PSTR_UniformCountProducer_120
public import Structure.PSTR_QueryReturn_111
public import Structure.PSTR_CountAllocation_102

/-! Actual NEW positive raw query computation, one containing program:
guarded count63 -> real Header82/tail719 -> true3-op common1371 return.
The command is read normally; this segment computes the OLD reply and
preserves configuration. Declaration updates are separate real code. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRUniformPositiveQuery

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRWordSegments PSTRCountKernel
open PA17A19RuntimeEntry020

def budget {q : Nat} (full : List (Finset (Fin q))) : Nat :=
  8 * CapacityBits.width q + 68 + 501 * treeSize q full +
    PA17A19RuntimeRelocate029.suffixClock q (treeSize q full) + 3

theorem budget_bound {q : Nat} (full : List (Finset (Fin q))) (hq : 0 < q) :
    budget full ≤ 1790 * liveWork q (treeSize q full) := by
  have ht := PSTRWidthOriginal.positive_tree_size full hq
  have hwork : 1 ≤ liveWork q (treeSize q full) := by
    simp only [liveWork, ne_of_gt hq, ite_false, queryWork]
    exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) ht)
  have hcount : 8 * CapacityBits.width q + 66 + 501 * treeSize q full ≤
      575 * liveWork q (treeSize q full) := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using PSTRCountCost.active_bound_work full hq
  have htail : PA17A19RuntimeQuery026.tailClock q (treeSize q full) ≤
      1128 * liveWork q (treeSize q full) := by
    simpa only [liveWork, ne_of_gt hq, ite_false, queryWork] using PA17A19RuntimeQuery026.tailClock_bound q (treeSize q full) ht
  unfold budget PA17A19RuntimeRelocate029.suffixClock
  omega

structure Result {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (allowed : Allowed full configuration command)
    (whole : List PackingOp) (initial : WordState (wordBits full)) (steps : Nat) : Prop where
  active : (packingRun (callInput q full command) whole steps initial).halted = false
  pc : (packingRun (callInput q full command) whole steps initial).pc = BitVec.ofNat (wordBits full) (5 * 1371)
  correct : ReplyCorrect q (callback q full (cursor full configuration command allowed) configuration.used)
    (replyState q (capacity full) (packingRun (callInput q full command) whole steps initial))
  represents : ∀ clock ≤ steps, HeapRepresents q full (capacity full) configuration
    (packingRun (callInput q full command) whole clock initial).heap
  capacityBound : ∀ clock ≤ steps, CapacityPrefixBounded q (capacity full)
    (logicalHeap q (capacity full) (packingRun (callInput q full command) whole clock initial).heap)
  table : ∀ clock ≤ steps, ∀ address < tableWords full.length q (treeSize q full),
    logicalHeap q (capacity full) (packingRun (callInput q full command) whole clock initial).heap address =
      logicalHeap q (capacity full) initial.heap address
  high : ∀ clock ≤ steps, ∀ physical, Fits (wordBits full) physical →
    PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical →
      (packingRun (callInput q full command) whole clock initial).heap (BitVec.ofNat (wordBits full) physical) =
        initial.heap (BitVec.ofNat (wordBits full) physical)
  safe : ∀ clock < steps, AtSafe (callInput q full command) whole (allocatedWords full)
    (packingRun (callInput q full command) whole clock initial)
  width : 0 < q → (packingRun (callInput q full command) whole steps initial).heap
    (BitVec.ofNat (wordBits full) (PSTRCountWorkspace.base q full (capacity full) (wordBits full) + 12)) =
      BitVec.ofNat (wordBits full) (CapacityBits.width q)

theorem actual_query {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (allowed : Allowed full configuration command)
    (hq : 0 < q) (hl : LaminarSchedule full) (whole : List PackingOp)
    (contains : PSTRUniformQueryCode.Contains whole)
    (hw : WordsFit (wordBits full) (packingCode whole)) (hpc : Fits (wordBits full) (5 * whole.length))
    (state : WordState (wordBits full)) (hp : state.pc = BitVec.ofNat (wordBits full) 0) (ha : state.halted = false)
    (rep : HeapRepresents q full (capacity full) configuration state.heap) :
    ∃ steps ≤ budget full, Result full command configuration allowed whole state steps := by
  let rom := callInput q full command
  obtain ⟨countSteps, _lower, upper, complete, frames, capacities, tables, fetches⟩ :=
    PSTRUniformCountProducer.actual_complete full command configuration whole 1345
      (PSTRUniformQueryCode.bootstrap_in whole contains) (PSTRUniformQueryCode.counts_in whole contains)
      hw hpc hq hl state rep hp ha
  let counted := packingRun rom whole countSteps state
  let suffixSteps := PA17A19RuntimeRelocate029.suffixClock q (treeSize q full)
  let replied := packingRun rom whole suffixSteps counted
  have suffix := PSTRUniformQueryEmbeddings.from_counts full command configuration allowed hq hl whole contains hw hpc counted complete
  have back := PSTRUniformQueryCode.positive_return_in whole contains
  have ret := PSTRQueryReturn.actual_return rom whole 1342 1371 back hw hpc replied suffix.pc suffix.active
  have ep : PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q =
      PSTRQueryLayout.endpoint (PSTRCountWorkspace.base q full (capacity full) (wordBits full))
        (prepareNormalization q full).indexed.nodes.size q := by
    change PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full (capacity full) (wordBits full))
      (treeSize q full) q = _
    rw [PSTRCountLogical.workspace_eq full _ _ hq]
    simp only [treeSize, ne_of_gt hq, ite_false]
  have slot : counted.heap (BitVec.ofNat (wordBits full)
      (PSTRCountWorkspace.base q full (capacity full) (wordBits full) + 12)) =
      BitVec.ofNat (wordBits full) (CapacityBits.width q) := by
    simpa only [Nat.add_zero, ite_true] using complete.slots 0 (by decide)
  have lowSlot : PSTRCountWorkspace.base q full (capacity full) (wordBits full) + 12 < header full := by
    unfold PA17A19RuntimeEntry020.header PA17A19RuntimeHeader011.head
    rw [PSTRCountLogical.workspace_eq full _ _ hq]
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  have widthSlot : replied.heap (BitVec.ofNat (wordBits full)
      (PSTRCountWorkspace.base q full (capacity full) (wordBits full) + 12)) =
      BitVec.ofNat (wordBits full) (CapacityBits.width q) :=
    (suffix.leading suffixSteps le_rfl _ lowSlot).trans slot
  have rawHigh (clock : Nat) (hc : clock ≤ countSteps) (physical : Nat) (hf : Fits (wordBits full) physical)
      (hh : PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical) :
      (packingRun rom whole clock state).heap (BitVec.ofNat (wordBits full) physical) =
        state.heap (BitVec.ofNat (wordBits full) physical) :=
    (frames clock hc).2 physical hf (Or.inr (by simpa only [ep] using hh))
  have runSuffix : packingRun rom whole (countSteps + suffixSteps) state = replied := by rw [run_add]
  have runFinal : packingRun rom whole (countSteps + suffixSteps + 3) state = packingRun rom whole 3 replied := by
    rw [run_add, runSuffix]
  have afterHigh (physical : Nat) (hf : Fits (wordBits full) physical)
      (hh : PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical) :
      replied.heap (BitVec.ofNat (wordBits full) physical) = state.heap (BitVec.ofNat (wordBits full) physical) :=
    (suffix.high suffixSteps le_rfl physical hf hh).trans (rawHigh countSteps le_rfl physical hf hh)
  have fields (clock : Nat) (hc : clock ≤ countSteps + suffixSteps + 3) :
      HeapRepresents q full (capacity full) configuration (packingRun rom whole clock state).heap ∧
      CapacityPrefixBounded q (capacity full) (logicalHeap q (capacity full) (packingRun rom whole clock state).heap) ∧
      (∀ address < tableWords full.length q (treeSize q full),
        logicalHeap q (capacity full) (packingRun rom whole clock state).heap address = logicalHeap q (capacity full) state.heap address) ∧
      (∀ physical, Fits (wordBits full) physical → PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical →
        (packingRun rom whole clock state).heap (BitVec.ofNat (wordBits full) physical) = state.heap (BitVec.ofNat (wordBits full) physical)) := by
    by_cases he : clock ≤ countSteps
    · exact ⟨(frames clock he).1, capacities clock he, tables clock he, rawHigh clock he⟩
    · by_cases hs : clock ≤ countSteps + suffixSteps
      · rw [show clock = countSteps + (clock - countSteps) by omega, run_add]
        have hstep : clock - countSteps ≤ suffixSteps := by omega
        refine ⟨suffix.represents _ hstep, suffix.capacityBound _ hstep, ?_, ?_⟩
        · intro address haddress
          exact (suffix.table _ hstep address haddress).trans (tables countSteps le_rfl address haddress)
        · intro physical hf hh
          exact (suffix.high _ hstep physical hf hh).trans (rawHigh countSteps le_rfl physical hf hh)
      · rw [show clock = (countSteps + suffixSteps) + (clock - (countSteps + suffixSteps)) by omega, run_add, runSuffix]
        have heap := PSTRQueryReturn.prefix_heap rom whole 1342 1371 back hw hpc replied suffix.pc suffix.active
          (clock - (countSteps + suffixSteps)) (by omega)
        rw [heap]
        exact ⟨suffix.represents _ le_rfl, suffix.capacityBound _ le_rfl,
          fun address haddress => (suffix.table _ le_rfl address haddress).trans (tables countSteps le_rfl address haddress), afterHigh⟩
  refine ⟨countSteps + suffixSteps + 3, ?_, ?_⟩
  · have hu : countSteps ≤ 8 * CapacityBits.width q + 68 + 501 * treeSize q full := by
      simpa only [treeSize, ne_of_gt hq, ite_false] using upper
    unfold budget
    change countSteps + suffixSteps + 3 ≤ 8 * CapacityBits.width q + 68 + 501 * treeSize q full + suffixSteps + 3
    omega
  · refine ⟨?_, ?_, ?_, (fun clock hc => (fields clock hc).1), (fun clock hc => (fields clock hc).2.1),
      (fun clock hc => (fields clock hc).2.2.1), (fun clock hc => (fields clock hc).2.2.2), ?_, ?_⟩
    · rw [runFinal]
      exact ret.2.1
    · rw [runFinal]
      exact ret.1
    · rw [runFinal, PSTRCountControl.fetched_back rom whole 1342 1371 back.bound back.code hw hpc replied suffix.pc suffix.active]
      exact (PSTRQueryReturn.reply_iff rom 1371 (capacity full)
        (callback q full (cursor full configuration command allowed) configuration.used) replied).mpr suffix.correct
    · intro clock hc
      by_cases he : clock < countSteps
      · exact PSTRCountAllocation.atSafe_mono rom whole _ _ _ (PSTRCountAllocation.endpoint_le full hq hl) (fetches clock he)
      · by_cases hs : clock < countSteps + suffixSteps
        · rw [show clock = countSteps + (clock - countSteps) by omega, run_add]
          exact suffix.safe _ (by omega)
        · rw [show clock = (countSteps + suffixSteps) + (clock - (countSteps + suffixSteps)) by omega, run_add, runSuffix]
          exact PSTRQueryReturn.actual_safe rom whole 1342 1371 _ back hw hpc replied suffix.pc suffix.active _ (by omega)
    · intro _hq
      rw [runFinal, ret.2.2.1]
      exact widthSlot

end PaperProofs.Structure.LaminarTree.PSTRUniformPositiveQuery

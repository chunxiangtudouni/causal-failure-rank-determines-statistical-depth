module

public import Structure.PSTR_UniformQuery_122
public import Structure.PSTR_HD_ZeroCommandCost_139

/-! All original commands through the SAME guarded1371 query body.
q0 actually performs its declaration inline; positive q retains the old
configuration for the following actual declaration blocks. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace PaperProofs.Structure.LaminarTree.PSTRLiveControllerBody

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims PA17A19RuntimeEntry020 PSTRCountKernel

structure BodyPost {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (whole : List PackingOp) (initial : WordState (wordBits full)) (steps : Nat) : Prop where
  active : (packingRun (callInput q full command) whole steps initial).halted = false
  pc : (packingRun (callInput q full command) whole steps initial).pc = BitVec.ofNat (wordBits full) (5 * 1371)
  represented : HeapRepresents q full (capacity full)
    (if q = 0 then nextConfiguration q full configuration command else configuration)
    (packingRun (callInput q full command) whole steps initial).heap
  reply : ∀ cursor : configuration.stage < full.length + 1,
    ReplyCorrect q (callback q full ⟨configuration.stage, cursor⟩ configuration.used)
      (replyState q (capacity full) (packingRun (callInput q full command) whole steps initial))
  capacity : ∀ clock ≤ steps, CapacityPrefixBounded q (PA17A19RuntimeEntry020.capacity full)
    (logicalHeap q (PA17A19RuntimeEntry020.capacity full) (packingRun (callInput q full command) whole clock initial).heap)
  table : ∀ clock ≤ steps, ∀ address < tableWords full.length q (treeSize q full), 0 < q →
    logicalHeap q (PA17A19RuntimeEntry020.capacity full) (packingRun (callInput q full command) whole clock initial).heap address =
      logicalHeap q (PA17A19RuntimeEntry020.capacity full) initial.heap address
  safe : ∀ clock < steps, AtSafe (callInput q full command) whole (allocatedWords full)
    (packingRun (callInput q full command) whole clock initial)
  width : 0 < q → (packingRun (callInput q full command) whole steps initial).heap
    (BitVec.ofNat (wordBits full) (PSTRCountWorkspace.base q full (PA17A19RuntimeEntry020.capacity full) (wordBits full) + 12)) =
      BitVec.ofNat (wordBits full) (CapacityBits.width q)

theorem actual_body {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (allowed : Allowed full configuration command) (hl : LaminarSchedule full)
    (whole : List PackingOp) (contains : PSTRUniformQueryCode.Contains whole)
    (hw : WordsFit (wordBits full) (packingCode whole)) (hpc : Fits (wordBits full) (5 * whole.length))
    (hlen : whole.length ≤ 8192) (literal : ∀ value ∈ packingCode whole, value < 65536)
    (state : WordState (wordBits full)) (hp : state.pc = BitVec.ofNat (wordBits full) 0) (ha : state.halted = false)
    (rep : HeapRepresents q full (PA17A19RuntimeEntry020.capacity full) configuration state.heap) :
    ∃ steps ≤ PSTRUniformQuery.budget full, BodyPost full configuration command whole state steps := by
  by_cases hq : q = 0
  · subst q
    have post := PSTRZeroDeclaration.actual_command_from_literals full configuration command allowed whole 1345 1371
      (PSTRUniformQueryCode.bootstrap_in whole contains) (PSTRUniformQueryCode.zero_in whole contains)
      (PSTRUniformQueryCode.zero_return_in whole contains) hlen literal state hp ha rep
    refine ⟨44, ?_, post.active, post.pc, post.represented, post.reply, post.capacity, post.table, post.safe, ?_⟩
    · change 44 ≤ 44
      exact Nat.le_refl _
    · intro hpositive
      omega
  · obtain ⟨steps, upper, post⟩ := PSTRUniformPositiveQuery.actual_query full command configuration allowed
      (Nat.pos_of_ne_zero hq) hl whole contains hw hpc state hp ha rep
    refine ⟨steps, ?_, post.active, post.pc, ?_, ?_, post.capacityBound, ?_, post.safe, post.width⟩
    · simpa only [PSTRUniformQuery.budget, hq, ite_false] using upper
    · rw [ite_eq_right hq]
      exact post.represents steps le_rfl
    · intro originalCursor
      exact post.correct
    · intro clock hc address ha _positive
      exact post.table clock hc address ha

end PaperProofs.Structure.LaminarTree.PSTRLiveControllerBody

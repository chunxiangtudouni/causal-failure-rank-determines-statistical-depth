module

public import Structure.PSTR_HD_ZeroDeclSegment_135
public import Structure.PSTR_UniformZeroQuery_112

/-! Output-only propositions about the actual44-step q0 command run. The
two real write clocks are28(failed5) and33(stage4). q0 has no capacity table:
the ORIGINAL table clause retains its 0<q guard; the nonvacuous all-physical
frame below protects every Fits address except the actual words4 and5. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRZeroDeclaration
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open PSTRCountKernel

def writeHeap {bits : Nat} (configuration : Configuration 0) (command : Command)
    (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  Function.update (failedHeap command heap) (BitVec.ofNat bits 4)
    (BitVec.ofNat bits (configuration.stage + PSTRZeroLive.increment command))

def prefixHeap {bits : Nat} (configuration : Configuration 0) (command : Command)
    (heap : BitVec bits → BitVec bits) (clock : Nat) : BitVec bits → BitVec bits :=
  if clock < 28 then heap else if clock < 33 then failedHeap command heap else writeHeap configuration command heap

theorem declarationHeap_eq_writeHeap {bits : Nat} (configuration : Configuration 0) (command : Command)
    (heap : BitVec bits → BitVec bits) (stage : heap (BitVec.ofNat bits 4) = BitVec.ofNat bits configuration.stage) :
    declarationHeap command heap = writeHeap configuration command heap := by
  unfold declarationHeap writeHeap
  rw [stage, BitVec.ofNat_add_ofNat]

theorem failed_word_of_allowed {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (command : Command) (allowed : Allowed full configuration command) (heap : BitVec bits → BitVec bits)
    (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 configuration heap) :
    heap (BitVec.ofNat bits 5) = BitVec.ofNat bits 0 := by
  have value := (PSTRHeadsRuntime.zero_physical_stage_failed full configuration heap hb rep).2
  have hf := (PSTRZeroLive.allowed_fields full configuration command allowed).1
  have word := congrArg (BitVec.ofNat bits) value
  simpa only [hf, bit, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq] using word

theorem query_writeHeap_self {bits : Nat} (configuration : Configuration 0) (heap : BitVec bits → BitVec bits)
    (hs : heap (BitVec.ofNat bits 4) = BitVec.ofNat bits configuration.stage)
    (hf : heap (BitVec.ofNat bits 5) = BitVec.ofNat bits 0) :
    writeHeap configuration .query heap = heap := by
  have fail : failedHeap .query heap = heap := by
    exact Function.update_eq_self_iff.mpr hf.symm
  unfold writeHeap
  rw [fail]
  exact Function.update_eq_self_iff.mpr (by simpa only [PSTRZeroLive.increment, Nat.add_zero] using hs.symm)

theorem query_prefixHeap_self {bits : Nat} (configuration : Configuration 0) (heap : BitVec bits → BitVec bits)
    (hs : heap (BitVec.ofNat bits 4) = BitVec.ofNat bits configuration.stage)
    (hf : heap (BitVec.ofNat bits 5) = BitVec.ofNat bits 0) (clock : Nat) :
    prefixHeap configuration .query heap clock = heap := by
  unfold prefixHeap
  split_ifs
  · rfl
  · exact Function.update_eq_self_iff.mpr hf.symm
  · exact query_writeHeap_self configuration heap hs hf

theorem prefixHeap_frame {bits : Nat} (configuration : Configuration 0) (command : Command)
    (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits) (physical : Nat) (hf : Fits bits physical)
    (h4 : physical ≠ 4) (h5 : physical ≠ 5) (clock : Nat) :
    prefixHeap configuration command heap clock (BitVec.ofNat bits physical) = heap (BitVec.ofNat bits physical) := by
  have hp : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have hw4 := PSTRZeroLive.word_ne physical 4 hf (by unfold Fits; omega) h4
  have hw5 := PSTRZeroLive.word_ne physical 5 hf (by unfold Fits; omega) h5
  unfold prefixHeap
  split_ifs
  · rfl
  · simp only [failedHeap, Function.update_of_ne hw5]
  · simp only [writeHeap, failedHeap, Function.update_of_ne hw4, Function.update_of_ne hw5]

structure CommandPost (full : List (Finset (Fin 0))) (configuration : Configuration 0) (command : Command)
    (whole : List PackingOp) (queryEnd : Nat) (initial : WordState (indexWidth 32 full.length 0)) : Prop where
  pc : (packingRun (callInput 0 full command) whole 44 initial).pc = BitVec.ofNat (indexWidth 32 full.length 0) (5 * queryEnd)
  active : (packingRun (callInput 0 full command) whole 44 initial).halted = false
  writes : (packingRun (callInput 0 full command) whole 44 initial).heap = writeHeap configuration command initial.heap
  represented : HeapRepresents 0 full 0 (nextConfiguration 0 full configuration command)
    (packingRun (callInput 0 full command) whole 44 initial).heap
  reply : ∀ cursor : configuration.stage < full.length + 1,
    ReplyCorrect 0 (callback 0 full ⟨configuration.stage, cursor⟩ configuration.used)
      (replyState 0 0 (packingRun (callInput 0 full command) whole 44 initial))
  prefix_heap : ∀ clock ≤ 44, (packingRun (callInput 0 full command) whole clock initial).heap =
    prefixHeap configuration command initial.heap clock
  frame : ∀ clock ≤ 44, ∀ physical, Fits (indexWidth 32 full.length 0) physical → physical ≠ 4 → physical ≠ 5 →
    (packingRun (callInput 0 full command) whole clock initial).heap (BitVec.ofNat (indexWidth 32 full.length 0) physical) =
      initial.heap (BitVec.ofNat (indexWidth 32 full.length 0) physical)
  capacity : ∀ clock ≤ 44, CapacityPrefixBounded 0 0
    (logicalHeap 0 0 (packingRun (callInput 0 full command) whole clock initial).heap)
  table : ∀ clock ≤ 44, ∀ address < tableWords full.length 0 (treeSize 0 full), 0 < 0 →
    logicalHeap 0 0 (packingRun (callInput 0 full command) whole clock initial).heap address = logicalHeap 0 0 initial.heap address
  safe : ∀ clock < 44, AtSafe (callInput 0 full command) whole (PSTRCountAllocation.allocation full)
    (packingRun (callInput 0 full command) whole clock initial)
  trace : (packingDynamicTrace (callInput 0 full command) whole 44 initial).length ≤ 528

theorem commandPost_of_core (full : List (Finset (Fin 0))) (configuration : Configuration 0) (command : Command)
    (whole : List PackingOp) (queryEnd : Nat) (state : WordState (indexWidth 32 full.length 0))
    (pc : (packingRun (callInput 0 full command) whole 44 state).pc = BitVec.ofNat (indexWidth 32 full.length 0) (5 * queryEnd))
    (active : (packingRun (callInput 0 full command) whole 44 state).halted = false)
    (rep : HeapRepresents 0 full 0 (nextConfiguration 0 full configuration command) (packingRun (callInput 0 full command) whole 44 state).heap)
    (reply : ∀ cursor : configuration.stage < full.length + 1,
      ReplyCorrect 0 (callback 0 full ⟨configuration.stage, cursor⟩ configuration.used)
        (replyState 0 0 (packingRun (callInput 0 full command) whole 44 state)))
    (prefixes : ∀ clock ≤ 44, (packingRun (callInput 0 full command) whole clock state).heap = prefixHeap configuration command state.heap clock)
    (safe : ∀ clock < 44, AtSafe (callInput 0 full command) whole (PSTRCountAllocation.allocation full)
      (packingRun (callInput 0 full command) whole clock state)) :
    CommandPost full configuration command whole queryEnd state := by
  refine ⟨pc, active, prefixes 44 le_rfl, rep, reply, prefixes, ?_, ?_, ?_, safe,
    packingDynamicTrace_length_le _ _ 44 state⟩
  · intro clock hc physical hf h4 h5
    rw [prefixes clock hc]
    apply prefixHeap_frame configuration command state.heap _ physical hf h4 h5 clock
    have hb := PSTROriginalCountRoom.word_lower full.length 0
    omega
  · intro clock hc address ha
    omega
  · intro clock hc address ha impossible
    omega

end PaperProofs.Structure.LaminarTree.PSTRZeroDeclaration

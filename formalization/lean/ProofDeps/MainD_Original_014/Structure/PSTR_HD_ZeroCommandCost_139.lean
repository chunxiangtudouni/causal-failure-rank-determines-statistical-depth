module

public import Structure.PSTR_HD_ZeroCommandRun_138

/-! Real q0 declaration physical effects and charged44-step costs. No
HALT is invented at the active common exit. Static literal facts can remove
all whole-code Fits premises at original w32, without runtime eligibility. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRZeroDeclaration
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine

theorem post_correct_heap (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (allowed : Allowed full configuration .correct) (whole : List PackingOp) (queryEnd : Nat)
    (state : WordState (indexWidth 32 full.length 0)) (rep : HeapRepresents 0 full 0 configuration state.heap)
    (post : CommandPost full configuration .correct whole queryEnd state) :
    (packingRun (callInput 0 full .correct) whole 44 state).heap =
      Function.update state.heap (BitVec.ofNat (indexWidth 32 full.length 0) 4)
        (BitVec.ofNat (indexWidth 32 full.length 0) (configuration.stage + 1)) := by
  have hb : 8 ≤ indexWidth 32 full.length 0 := by have h := PSTROriginalCountRoom.word_lower full.length 0; omega
  have hf := failed_word_of_allowed full configuration .correct allowed state.heap hb rep
  have fail : failedHeap .correct state.heap = state.heap := Function.update_eq_self_iff.mpr hf.symm
  rw [post.writes]
  unfold writeHeap
  rw [fail]
  rfl

theorem post_error_heap (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (whole : List PackingOp) (queryEnd : Nat) (state : WordState (indexWidth 32 full.length 0))
    (rep : HeapRepresents 0 full 0 configuration state.heap)
    (post : CommandPost full configuration .error whole queryEnd state) :
    (packingRun (callInput 0 full .error) whole 44 state).heap =
      Function.update state.heap (BitVec.ofNat (indexWidth 32 full.length 0) 5) (BitVec.ofNat (indexWidth 32 full.length 0) 1) := by
  let bits := indexWidth 32 full.length 0
  have hb : 8 ≤ bits := by have h := PSTROriginalCountRoom.word_lower full.length 0; omega
  have hp : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have h45 := PSTRZeroLive.word_ne (bits := bits) 4 5 (by unfold Fits; omega) (by unfold Fits; omega) (by decide)
  have hs := PSTRZeroLive.stage_word full configuration state.heap rep
  rw [post.writes]
  unfold writeHeap failedHeap
  change Function.update (Function.update state.heap (BitVec.ofNat bits 5) (BitVec.ofNat bits 1))
    (BitVec.ofNat bits 4) (BitVec.ofNat bits configuration.stage) = _
  apply Function.update_eq_self_iff.mpr
  rw [Function.update_of_ne h45]
  exact hs.symm

theorem post_error_no_advance (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (allowed : Allowed full configuration .error) (whole : List PackingOp) (queryEnd : Nat)
    (state : WordState (indexWidth 32 full.length 0))
    (post : CommandPost full configuration .error whole queryEnd state) :
    ((packingRun (callInput 0 full .error) whole 44 state).heap (BitVec.ofNat (indexWidth 32 full.length 0) 4)).toNat = configuration.stage ∧
    ((packingRun (callInput 0 full .error) whole 44 state).heap (BitVec.ofNat (indexWidth 32 full.length 0) 5)).toNat = 1 := by
  have hb : 8 ≤ indexWidth 32 full.length 0 := by have h := PSTROriginalCountRoom.word_lower full.length 0; omega
  have rep := post.represented
  rw [next_error_none full configuration allowed] at rep
  simpa only [bit, ↓reduceIte] using PSTRHeadsRuntime.zero_physical_stage_failed full {configuration with failed := true}
    (packingRun (callInput 0 full .error) whole 44 state).heap hb rep

theorem command_charged_cost44 (full : List (Finset (Fin 0))) (configuration : Configuration 0) (command : Command)
    (whole : List PackingOp) (queryEnd : Nat) (state : WordState (indexWidth 32 full.length 0))
    (post : CommandPost full configuration command whole queryEnd state) :
    1 + (packingCode whole).length + 8 + (packingDynamicTrace (callInput 0 full command) whole 44 state).length ≤
      (5 * whole.length + 542) * liveWork 0 (treeSize 0 full) := by
  have trace := post.trace
  simp only [packingCode_length, liveWork, ↓reduceIte, Nat.mul_one]
  omega

theorem command_callCost44 (full : List (Finset (Fin 0))) (configuration : Configuration 0) (command : Command)
    (whole : List PackingOp) (queryEnd : Nat)
    (heap : BitVec (indexWidth 32 full.length 0) → BitVec (indexWidth 32 full.length 0))
    (post : CommandPost full configuration command whole queryEnd (packingInitial heap)) :
    callCost 0 full whole command 44 heap ≤ (5 * whole.length + 542) * liveWork 0 (treeSize 0 full) :=
  command_charged_cost44 full configuration command whole queryEnd (packingInitial heap) post

theorem actual_command_from_literals (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (command : Command) (allowed : Allowed full configuration command) (whole : List PackingOp) (zeroStart queryEnd : Nat)
    (cb : PSTRUniformBootstrapCode.Contains whole zeroStart)
    (zs : PSTROuterCountCode.BlockAt whole zeroStart PSTRZeroLive.program)
    (bs : PSTROuterCountCode.BlockAt whole (zeroStart + 23) (PSTRCountControl.backBlock queryEnd))
    (hlen : whole.length ≤ 8192) (literal : ∀ value ∈ packingCode whole, value < 65536)
    (state : WordState (indexWidth 32 full.length 0))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length 0) 0) (ha : state.halted = false)
    (rep : HeapRepresents 0 full 0 configuration state.heap) :
    CommandPost full configuration command whole queryEnd state := by
  have big := PSTRZeroHeads.shared_footprint_fit full.length 32 65536 (by decide) (by decide)
  have room : Fits (indexWidth 32 full.length 0) 65536 :=
    (show 65536 ≤ 65536 * (full.length + 1) + 127 by omega).trans_lt big
  exact actual_command full configuration command allowed whole zeroStart queryEnd cb zs bs
    (fun value hv => (literal value hv).trans room) ((show 5 * whole.length ≤ 65536 by omega).trans_lt room)
    state hp ha rep

end PaperProofs.Structure.LaminarTree.PSTRZeroDeclaration

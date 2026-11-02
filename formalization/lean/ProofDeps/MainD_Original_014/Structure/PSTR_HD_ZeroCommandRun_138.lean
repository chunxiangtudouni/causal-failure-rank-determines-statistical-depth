module

public import Structure.PSTR_HD_ZeroDeclarationRun_137

/-! All THREE original q0 commands in one actual44-step containing-code
component. QUERY directly reuses frozen main112; correct/error use137.
Only original Allowed controls terminal/N0 calls; no new eligibility field,
query oracle, mode assumption or fake error transition is introduced. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRZeroDeclaration
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine

theorem actual_query_post (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (allowed : Allowed full configuration .query) (whole : List PackingOp) (zeroStart queryEnd : Nat)
    (cb : PSTRUniformBootstrapCode.Contains whole zeroStart)
    (zs : PSTROuterCountCode.BlockAt whole zeroStart PSTRZeroLive.program)
    (bs : PSTROuterCountCode.BlockAt whole (zeroStart + 23) (PSTRCountControl.backBlock queryEnd))
    (hwords : WordsFit (indexWidth 32 full.length 0) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length 0) (5 * whole.length))
    (state : WordState (indexWidth 32 full.length 0))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length 0) 0) (ha : state.halted = false)
    (rep : HeapRepresents 0 full 0 configuration state.heap) :
    CommandPost full configuration .query whole queryEnd state := by
  have hb : 8 ≤ indexWidth 32 full.length 0 := by have h := PSTROriginalCountRoom.word_lower full.length 0; omega
  have cursor : configuration.stage < full.length + 1 := Nat.lt_succ_of_le allowed.2
  have reconstruct : configuration = ⟨configuration.stage, configuration.used, configuration.failed⟩ := by cases configuration; rfl
  have normalized : configuration = ⟨configuration.stage, configuration.used, false⟩ :=
    reconstruct.trans (congrArg (fun failed => (⟨configuration.stage, configuration.used, failed⟩ : Configuration 0)) allowed.1)
  have queryRep : HeapRepresents 0 full 0 ⟨configuration.stage, configuration.used, false⟩ state.heap := by
    rw [← normalized]
    exact rep
  have query := PSTRUniformZeroQuery.actual_query full configuration.used ⟨configuration.stage, cursor⟩ whole zeroStart queryEnd
    cb zs bs hwords hpcfit state hp ha queryRep
  have hstage := PSTRZeroLive.stage_word full configuration state.heap rep
  have hfailed := failed_word_of_allowed full configuration .query allowed state.heap hb rep
  apply commandPost_of_core full configuration .query whole queryEnd state query.1 query.2.1
  · change HeapRepresents 0 full 0 configuration _
    rw [query.2.2.1]
    exact rep
  · intro originalCursor
    exact query.2.2.2.1
  · intro clock hc
    exact (query.2.2.2.2.1 clock hc).trans (query_prefixHeap_self configuration state.heap hstage hfailed clock).symm
  · exact query.2.2.2.2.2.1

theorem actual_command (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (command : Command) (allowed : Allowed full configuration command) (whole : List PackingOp) (zeroStart queryEnd : Nat)
    (cb : PSTRUniformBootstrapCode.Contains whole zeroStart)
    (zs : PSTROuterCountCode.BlockAt whole zeroStart PSTRZeroLive.program)
    (bs : PSTROuterCountCode.BlockAt whole (zeroStart + 23) (PSTRCountControl.backBlock queryEnd))
    (hwords : WordsFit (indexWidth 32 full.length 0) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length 0) (5 * whole.length))
    (state : WordState (indexWidth 32 full.length 0))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length 0) 0) (ha : state.halted = false)
    (rep : HeapRepresents 0 full 0 configuration state.heap) :
    CommandPost full configuration command whole queryEnd state := by
  cases command with
  | query => exact actual_query_post full configuration allowed whole zeroStart queryEnd cb zs bs hwords hpcfit state hp ha rep
  | correct => exact actual_declaration full configuration .correct (Or.inl rfl) allowed whole zeroStart queryEnd cb zs bs hwords hpcfit state hp ha rep
  | error => exact actual_declaration full configuration .error (Or.inr rfl) allowed whole zeroStart queryEnd cb zs bs hwords hpcfit state hp ha rep

end PaperProofs.Structure.LaminarTree.PSTRZeroDeclaration

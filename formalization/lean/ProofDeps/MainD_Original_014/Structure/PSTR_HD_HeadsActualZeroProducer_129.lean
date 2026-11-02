module

public import Structure.PSTR_HD_HeadsReplyWords_128
public import Structure.PSTR_UniformZeroQuery_112

/-! Construct the q0 heads query producer from main032's REAL44-step query.
Only literal containing-code facts remain: actual63op bootstrap at0, actual
23op q0 reply and actual3op return to the ONE queryEnd. No query execution,
reply, frame, step or safety oracle is an assumption of this theorem. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine

theorem actual_zero_query_producer (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (queryBody : List PackingOp) (zeroStart : Nat)
    (cb : PSTRUniformBootstrapCode.Contains (uniformHeadsProgram queryBody) zeroStart)
    (zs : PSTROuterCountCode.BlockAt (uniformHeadsProgram queryBody) zeroStart PSTRZeroLive.program)
    (bs : PSTROuterCountCode.BlockAt (uniformHeadsProgram queryBody) (zeroStart + 23)
      (PSTRCountControl.backBlock queryBody.length))
    (hwords : WordsFit (indexWidth 32 full.length 0) (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits (indexWidth 32 full.length 0) (5 * (uniformHeadsProgram queryBody).length)) :
    InternalZeroQueryProducer full used (PSTRCountAllocation.allocation full) 44 queryBody
      (bits := indexWidth 32 full.length 0) := by
  intro stage hs state rep hp ha
  have post := PSTRUniformZeroQuery.actual_query full used ⟨stage, callback_stage_bound full stage hs⟩
    (uniformHeadsProgram queryBody) zeroStart queryBody.length cb zs bs hwords hpcfit state hp ha rep
  dsimp only at post
  exact ⟨44, le_rfl, internal_query_exit_of_original_reply full used 0 queryBody stage hs _ post.1 post.2.1
    post.2.2.2.1, post.2.2.2.2.2.1, post.2.2.2.2.1⟩

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

module

public import Structure.PSTR_HD_HeadsTerminalOutput_069

/-! The heads controller's actual declaration+backedge: the SAME query ROM,
real stage8op update, then real3op jump0. This returns to the unique query body
with arbitrary resulting registers, original used/failed/table and output retained. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

theorem advance_query_entry {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords origin rank : Nat) (entries : List Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (recorded : RecordedHeads (endpoint full capWords bits) q rank entries state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 56))) (ha : state.halted = false)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset))
    (hnext : Fits bits (configuration.stage + 1))
    (he : Fits bits (endpoint full capWords bits + 10 + entries.length)) :
    let after := packingRun (callInput q full .query) whole 11 state
    after.pc = BitVec.ofNat bits 0 ∧ after.halted = false ∧
    HeapRepresents q full capWords (nextConfiguration q full configuration .correct) after.heap ∧
    RecordedHeads (endpoint full capWords bits) q rank entries after.heap := by
  dsimp only
  let rom := callInput q full .query
  let advanced := executeOps rom headsCorrect state
  have advanced_pc : advanced.pc = BitVec.ofNat bits (5 * (origin + 64)) := by
    change (executeOps rom headsCorrect state).pc = _
    rw [executeOps_pc rom headsCorrect state PSTRRuntimeAdvance.program_straight, hp, BitVec.ofNat_add_ofNat]
    congr 1
  have advanced_halt : advanced.halted = false := (executeOps_halted rom headsCorrect state).trans ha
  have run8 : packingRun rom whole 8 state = advanced :=
    containing_headsCorrect full whole (origin + 56) (by have h := tailAt_length origin; rw [headsCorrect_length]; omega)
      (headsCorrect_tail_code whole origin hbound hcode) hwords hpcfit state hp ha
  have back := same_heap_query_jump rom whole (origin + 64)
    (by have h := tailAt_length origin; rw [jumpBack_length]; omega)
    (jumpBack_tail_code whole origin hbound hcode) hwords hpcfit advanced advanced_pc advanced_halt
  have hbefore : 4 + packedCapacityWords q capWords bits < endpoint full capWords bits := by
    have h := endpoint_metadata_after full capWords hq (bits := bits)
    omega
  have heE : Fits bits (endpoint full capWords bits) :=
    (show endpoint full capWords bits ≤ endpoint full capWords bits + 10 + entries.length by omega).trans_lt he
  have advanced_recorded : RecordedHeads (endpoint full capWords bits) q rank entries advanced.heap := by
    apply recorded_of_query_frame _ q rank entries state.heap advanced.heap recorded he
    intro physical hf hphysical
    exact headsCorrect_prefix_frame full configuration capWords _ state rep hbefore heE physical hf hphysical 8 (by decide)
  rw [show 11 = 8 + 3 from rfl, run_add, run8]
  refine ⟨back.1, back.2.1, ?_, ?_⟩
  · rw [back.2.2.1]
    exact headsCorrect_rep full configuration capWords state hb hq rep bitmap hr hi hnext
  · rw [back.2.2.1]
    exact advanced_recorded

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

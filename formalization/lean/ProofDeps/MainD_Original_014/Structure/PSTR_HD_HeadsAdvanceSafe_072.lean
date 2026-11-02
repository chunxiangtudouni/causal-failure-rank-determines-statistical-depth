module

public import Structure.PSTR_HD_HeadsAdvancePrefixes_071

/-! Actual EVERY-clock fetch/decode/access and high physical frame for the
real8+3 declaration/backedge. No frame outside allocated addresses is assumed;
all Fits physical p>=E, including untouched spare words, are preserved. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel

theorem advance_prefix_safe {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords origin heapWords : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (he : Fits bits (endpoint full capWords bits)) (hroom : endpoint full capWords bits < heapWords)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 56))) (ha : state.halted = false)
    (clock : Nat) (hc : clock < 11) :
    AtSafe (callInput q full .query) whole heapWords (packingRun (callInput q full .query) whole clock state) ∧
    HeapFrame (fun physical => endpoint full capWords bits ≤ physical) state.heap
      (packingRun (callInput q full .query) whole clock state).heap := by
  let rom := callInput q full .query
  let E := endpoint full capWords bits
  let region := fun physical => E ≤ physical
  have hbefore : 4 + packedCapacityWords q capWords bits < E := by
    have h := endpoint_metadata_after full capWords hq (bits := bits)
    omega
  have correctSafe : PrefixOK rom heapWords region headsCorrect state := by
    constructor
    · exact headsCorrect_prefix_access full configuration capWords heapWords state rep (hbefore.trans hroom)
    · intro count hcount physical hf hphysical
      exact headsCorrect_prefix_frame full configuration capWords E state rep hbefore he physical hf hphysical count hcount
  have jumpSafe : PrefixOK rom heapWords region (jumpLead 0) (executeOps rom headsCorrect state) :=
    readOnly_prefixOK rom heapWords region (jumpLead 0) _
      (by simp [jumpLead, ReadOnly]) (by
        intro count hcount
        change count < 2 at hcount
        interval_cases count <;> trivial)
  have leadSafe : PrefixOK rom heapWords region advanceLead state :=
    prefixOK_append rom heapWords region headsCorrect (jumpLead 0) state correctSafe jumpSafe
  have leadCode := tail_slice whole advanceLead origin 56 hbound hcode (by change 56 + 10 ≤ 111; decide) rfl
  exact branch_prefix_safe rom whole advanceLead heapWords (origin + 56) region
    (by have h := tailAt_length origin; rw [advanceLead_length]; omega) leadCode
    (hcode 66 (by change 66 < 111; decide)) advanceLead_straight hwords hpcfit state hp ha leadSafe clock
    (by rw [advanceLead_length]; omega)

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

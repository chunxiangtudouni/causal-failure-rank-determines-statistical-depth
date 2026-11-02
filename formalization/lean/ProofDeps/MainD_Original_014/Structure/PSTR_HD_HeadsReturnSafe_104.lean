module

public import Structure.PSTR_HD_HeadsDispatchSafe_103

/-! Real return-prefix safety: the actual7op stage probe and first-return
branch use a read-only8op lead; positive q first executes the original31op
endpoint locator. Every proper clock is fetched from the SAME whole code,
and the entire heap is unchanged, without rank or query-output premises. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel

def probeReturnLead (origin : Nat) : List PackingOp :=
  stageProbe ++ [.base (.base (.constant .total (5 * (origin + 80))))]

theorem probeReturnLead_length (origin : Nat) : (probeReturnLead origin).length = 8 := rfl

theorem probeReturnLead_straight (origin : Nat) : StraightProgram (probeReturnLead origin) := by
  simp [probeReturnLead, stageProbe, StraightProgram, StraightOp]

theorem probeReturnLead_readOnly (origin : Nat) : ∀ op ∈ probeReturnLead origin, ReadOnly op := by
  simp [probeReturnLead, stageProbe, ReadOnly]

theorem probe_return_prefix_safe {bits q : Nat} (full : List (Finset (Fin q)))
    (packed origin heapWords : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 31))) (ha : state.halted = false)
    (hpacked : state.heap (BitVec.ofNat bits 2) = BitVec.ofNat bits packed)
    (hroom : 4 + packed < heapWords) (clock : Nat) (hc : clock < 9) :
    AtSafe (callInput q full .query) whole heapWords (packingRun (callInput q full .query) whole clock state) ∧
      (packingRun (callInput q full .query) whole clock state).heap = state.heap := by
  let rom := callInput q full .query
  have probeSafe : PrefixOK rom heapWords (fun _ => True) stageProbe state :=
    readOnly_prefixOK rom heapWords (fun _ => True) stageProbe state (by simp [stageProbe, ReadOnly])
      (stageProbe_prefix_access full packed heapWords state hpacked hroom)
  have constantSafe : PrefixOK rom heapWords (fun _ => True)
      [.base (.base (.constant .total (5 * (origin + 80))))] (executeOps rom stageProbe state) :=
    readOnly_prefixOK rom heapWords (fun _ => True) _ _ (by simp [ReadOnly]) (by
      intro count hcount
      have hc0 : count = 0 := by change count < 1 at hcount; omega
      subst count
      trivial)
  have leadSafe : PrefixOK rom heapWords (fun _ => True) (probeReturnLead origin) state :=
    prefixOK_append rom heapWords (fun _ => True) stageProbe _ state probeSafe constantSafe
  exact readonly_branch_prefix_safe rom whole (probeReturnLead origin) heapWords (origin + 31) .old .total
    (by have h := tailAt_length origin; rw [probeReturnLead_length]; omega)
    (tail_slice whole (probeReturnLead origin) origin 31 hbound hcode (by change 31 + 8 ≤ 111; decide) rfl)
    (hcode 39 (by change 39 < 111; decide)) (probeReturnLead_straight origin) (probeReturnLead_readOnly origin)
    hwords hpcfit state hp ha leadSafe.access clock (by rw [probeReturnLead_length]; omega)

theorem query_return_prefix_safe {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords origin heapWords : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents q full capWords configuration state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (hroom : PSTRCountWorkspace.base q full capWords bits < heapWords)
    (clock : Nat) (hc : clock < 40) :
    AtSafe (callInput q full .query) whole heapWords (packingRun (callInput q full .query) whole clock state) ∧
      (packingRun (callInput q full .query) whole clock state).heap = state.heap := by
  let rom := callInput q full .query
  have endpointCode := endpoint_tail_code whole origin hbound hcode
  have endpointBound : origin + endpointProgram.length ≤ whole.length := by
    have h := tailAt_length origin
    rw [endpointProgram_length]
    omega
  by_cases hfirst : clock < 31
  · have safe : PrefixOK rom heapWords (fun _ => True) endpointProgram state :=
      readOnly_prefixOK rom heapWords (fun _ => True) endpointProgram state endpointProgram_readOnly
        (endpoint_prefix_access full .query configuration capWords heapWords state hb rep hroom)
    have h := straight_prefix_safe rom whole endpointProgram heapWords origin (fun _ => True)
      endpointBound endpointCode endpointProgram_straight hwords hpcfit state hp ha safe clock hfirst
    refine ⟨h.1, ?_⟩
    rw [fetched_prefix rom whole endpointProgram origin endpointBound endpointCode endpointProgram_straight hwords hpcfit state hp ha clock (by rw [endpointProgram_length]; omega)]
    exact endpoint_prefix_heap rom state clock
  · let located := executeOps rom endpointProgram state
    have located_heap : located.heap = state.heap := readOnly_ops_heap rom endpointProgram state endpointProgram_readOnly
    have located_pc : located.pc = BitVec.ofNat bits (5 * (origin + 31)) := by
      dsimp only [located]
      rw [executeOps_pc rom endpointProgram state endpointProgram_straight, hp, BitVec.ofNat_add_ofNat]
      congr 1
    have located_halt : located.halted = false := (executeOps_halted rom endpointProgram state).trans ha
    have located_packed : located.heap (BitVec.ofNat bits 2) = BitVec.ofNat bits (packedCapacityWords q capWords bits) := by
      rw [located_heap]
      exact (PSTRStaticHeap.headers full configuration capWords state.heap rep).2.2.1
    have packed_room : 4 + packedCapacityWords q capWords bits < heapWords := by
      unfold PSTRCountWorkspace.base at hroom
      omega
    have run31 : packingRun rom whole 31 state = located :=
      containing_endpoint rom whole origin endpointBound endpointCode hwords hpcfit state hp ha
    have hclock : clock = 31 + (clock - 31) := by omega
    rw [hclock, run_add, run31]
    have h := probe_return_prefix_safe full (packedCapacityWords q capWords bits) origin heapWords whole hbound hcode hwords hpcfit
      located located_pc located_halt located_packed packed_room (clock - 31) (by omega)
    exact ⟨h.1, h.2.trans located_heap⟩

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

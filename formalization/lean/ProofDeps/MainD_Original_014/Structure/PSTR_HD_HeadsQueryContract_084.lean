module

public import Structure.PSTR_HD_HeadsUniformTerminal_083

/-! INTERNAL pending same-run query ABI for the heads proof. This is a Prop
about actual execution of the ONE fixed whole uniform program; it is NOT an
implementation field, input datum, ROM, query opcode, or original claim.
It must be proved by the actual query producer before HeadExtraction closes.
Every datum and prefix safety/frame assertion uses the SAME existential clock. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem callback_stage_bound {q : Nat} (full : List (Finset (Fin q))) (stage : Nat) (hs : stage ≤ full.length) :
    stage < full.length + 1 := by omega

structure InternalQueryExit {bits q : Nat} (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (queryBody : List PackingOp) (stage : Nat) (hs : stage ≤ full.length) (after : WordState bits) : Prop where
  pc : after.pc = BitVec.ofNat bits (5 * queryBody.length)
  active : after.halted = false
  rank : after.register .value = BitVec.ofNat bits (encodeRank q
    (callback q full ⟨stage, callback_stage_bound full stage hs⟩ used).rank)
  bad : after.register .fresh = BitVec.ofNat bits (encodeRank q
    (callback q full ⟨stage, callback_stage_bound full stage hs⟩ used).bad)

def InternalQueryProducer {bits q : Nat} (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (capWords heapWords budget : Nat) (queryBody : List PackingOp) : Prop :=
  ∀ (stage : Nat) (hs : stage ≤ full.length) (state : WordState bits),
    HeapRepresents q full capWords ⟨stage, used, false⟩ state.heap →
    state.pc = BitVec.ofNat bits 0 → state.halted = false →
    ∃ steps ≤ budget,
      InternalQueryExit full used queryBody stage hs
        (packingRun (callInput q full .query) (uniformHeadsProgram queryBody) steps state) ∧
      (∀ clock < steps, AtSafe (callInput q full .query) (uniformHeadsProgram queryBody) heapWords
        (packingRun (callInput q full .query) (uniformHeadsProgram queryBody) clock state)) ∧
      (∀ clock ≤ steps,
        HeapRepresents q full capWords ⟨stage, used, false⟩
          (packingRun (callInput q full .query) (uniformHeadsProgram queryBody) clock state).heap ∧
        HeapFrame (fun physical => endpoint full capWords bits ≤ physical) state.heap
          (packingRun (callInput q full .query) (uniformHeadsProgram queryBody) clock state).heap)

structure CommonScan {bits q : Nat} (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (capWords : Nat) (queryBody : List PackingOp) (stage : Nat) (state : WordState bits) : Prop where
  pc : state.pc = BitVec.ofNat bits (5 * (queryBody.length + 48))
  active : state.halted = false
  represented : HeapRepresents q full capWords ⟨stage, used, false⟩ state.heap
  recorded : RecordedHeads (endpoint full capWords bits) q (encodeRank q (PSTRHeadScan.initialRank q full used))
    (scanPrefix q full used stage) state.heap
  old : state.register .old = BitVec.ofNat bits stage
  index : state.register .index = BitVec.ofNat bits full.length
  address : state.register .address = BitVec.ofNat bits (endpoint full capWords bits)
  bad : ∀ hs : stage < full.length,
    state.register .fresh = BitVec.ofNat bits (encodeRank q (badAt q full used ⟨stage, hs⟩))

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

module

public import Structure.PSTR_HD_HeadsGivenQuerySafe_121
public import Structure.PSTR_HD_HeadsZeroUniformTerminal_099

/-! INTERNAL pending q0 query ABI, not an original input/implementation
field or existence claim. Real q0 query code is read-only up to self-stores
at stage4/failed5, so the eventual actual producer can prove ENTIRE prefix
heap identity. This protects endpoint46 independently of positive layout E. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open PSTRCountKernel
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

def InternalZeroQueryProducer {bits : Nat} (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (heapWords budget : Nat) (queryBody : List PackingOp) : Prop :=
  ∀ (stage : Nat) (hs : stage ≤ full.length) (state : WordState bits),
    HeapRepresents 0 full 0 ⟨stage, used, false⟩ state.heap →
    state.pc = BitVec.ofNat bits 0 → state.halted = false →
    ∃ steps ≤ budget,
      InternalQueryExit full used queryBody stage hs
        (packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) steps state) ∧
      (∀ clock < steps, AtSafe (callInput 0 full .query) (uniformHeadsProgram queryBody) heapWords
        (packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) clock state)) ∧
      (∀ clock ≤ steps,
        (packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) clock state).heap = state.heap)

structure ZeroCommonScan {bits : Nat} (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (queryBody : List PackingOp) (stage : Nat) (state : WordState bits) : Prop where
  pc : state.pc = BitVec.ofNat bits (5 * (queryBody.length + 48))
  active : state.halted = false
  represented : HeapRepresents 0 full 0 ⟨stage, used, false⟩ state.heap
  recorded : RecordedHeads 46 0 (encodeRank 0 (PSTRHeadScan.initialRank 0 full used))
    (scanPrefix 0 full used stage) state.heap
  old : state.register .old = BitVec.ofNat bits stage
  index : state.register .index = BitVec.ofNat bits full.length
  address : state.register .address = BitVec.ofNat bits 46
  bad : ∀ hs : stage < full.length,
    state.register .fresh = BitVec.ofNat bits (encodeRank 0 (badAt 0 full used ⟨stage, hs⟩))

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

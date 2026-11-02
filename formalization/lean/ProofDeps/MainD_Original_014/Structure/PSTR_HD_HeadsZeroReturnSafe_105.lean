module

public import Structure.PSTR_HD_HeadsReturnSafe_104
public import Structure.PSTR_HD_HeadsZeroHeap_089

/-! The q0 dispatcher lands directly at the SAME real stage-probe31.
Original q0 HeapRep supplies the physical header2=0, and no positive cached
metadata or heap6 is read. All9 real return clocks preserve the entire heap. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel

theorem zero_return_prefix_safe {bits : Nat} (full : List (Finset (Fin 0)))
    (configuration : Configuration 0) (origin heapWords : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 configuration state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 31))) (ha : state.halted = false)
    (hroom : 6 ≤ heapWords) (clock : Nat) (hc : clock < 9) :
    AtSafe (callInput 0 full .query) whole heapWords (packingRun (callInput 0 full .query) whole clock state) ∧
      (packingRun (callInput 0 full .query) whole clock state).heap = state.heap :=
  probe_return_prefix_safe full 0 origin heapWords whole hbound hcode hwords hpcfit state hp ha
    (zero_packed_header full configuration state.heap (by omega) rep) (by omega) clock hc

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009q
public import PaperProofs.Structure.PSTR_RepairHeap_024

/-! Internal reverse-loop invariant. The original packed table and used bits
remain represented; only locally materialized count/parent/header facts are
carried across runtime iterations. These are not original A19 caller inputs. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

structure ReverseLayout (bits q : Nat) (full : List (Finset (Fin q)))
    (capWords heapWords header base counts parents size : Nat) : Prop where
  bits8 : 8 ≤ bits
  positive : 0 < q
  width : CapacityBits.width q ≤ bits
  size_eq : size = treeSize q full
  header_eq : header = PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
  capacityFits : Fits bits (4 + capWords * CapacityBits.width q)
  heapFits : Fits bits heapWords
  endpointFits : Fits bits (endpoint header q size)
  allocated : endpoint header q size ≤ heapWords
  bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords
  payloadBound : base + size ≤ capWords
  payloadFits : Fits bits (base + size)
  countsEnd : counts + size ≤ header + 8
  parentsEnd : parents + size + 1 ≤ header + 8

structure ReverseHeapData {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords header base counts parents size : Nat) (heap : BitVec bits → BitVec bits) : Prop where
  represents : HeapRepresents q full capWords configuration heap
  width : heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
    BitVec.ofNat bits (CapacityBits.width q)
  mask : heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
    lowMask bits (CapacityBits.width q)
  payload : heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits base
  candidates : heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits (childBase header q)
  countsBase : heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits counts
  parentsBase : heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits parents
  parentBound : ∀ node < size, (heap (BitVec.ofNat bits (parents + (node + 1)))).toNat ≤ size

structure ReverseReady {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (origin capWords header base counts parents size remaining : Nat) (state : WordState bits) : Prop where
  bound : remaining ≤ size
  address : state.register .address = BitVec.ofNat bits header
  counter : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits remaining
  pc : state.pc = BitVec.ofNat bits (5 * origin)
  active : state.halted = false
  data : ReverseHeapData full configuration capWords header base counts parents size state.heap

namespace ReverseLayout

variable {bits q capWords heapWords header base counts parents size : Nat} {full : List (Finset (Fin q))}

theorem headerFits (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (offset : Nat) (ho : offset ≤ 15) : Fits bits (header + offset) := by
  apply (show header + offset ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits

theorem oneFits (layout : ReverseLayout bits q full capWords heapWords header base counts parents size) : Fits bits 1 := by
  apply (show 1 ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits

theorem sizeFits (layout : ReverseLayout bits q full capWords heapWords header base counts parents size) : Fits bits size := by
  apply (show size ≤ endpoint header q size by unfold endpoint; omega).trans_lt layout.endpointFits

theorem targetFits (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (parent : Nat) (hp : parent ≤ size) : Fits bits (childBase header q + parent + 1) := by
  apply (show childBase header q + parent + 1 ≤ endpoint header q size by unfold endpoint; omega).trans_lt layout.endpointFits

theorem headerAllocated (layout : ReverseLayout bits q full capWords heapWords header base counts parents size) : header + 12 < heapWords := by
  have he : header + 12 < endpoint header q size := by unfold endpoint childBase; omega
  exact he.trans_le layout.allocated

theorem metadata_le (layout : ReverseLayout bits q full capWords heapWords header base counts parents size) :
    4 + packedCapacityWords q capWords bits + (2 + (staticMetadata q full).length) ≤ header + 8 := by
  have hh := layout.header_eq
  unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    PSTRQueryLayout.physicalWorkspace PSTRStaticHeap.metadataAddress at hh
  omega

theorem cache_lt (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (offset : Nat) (ho : offset ≤ 13) :
    PSTRQueryLayout.physicalWorkspace full capWords bits + offset < header + 8 := by
  have hh := layout.header_eq
  unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase at hh
  omega

end ReverseLayout

def reverseStepHeap {bits : Nat} (header candidates parent node : Nat) (selected : BitVec bits)
    (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  Function.update (Function.update heap (BitVec.ofNat bits (candidates + parent)) selected)
    (BitVec.ofNat bits (header + 8)) (BitVec.ofNat bits node)

theorem reverseStepHeap_frame {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (parent node : Nat) (hp : parent ≤ size) (selected : BitVec bits) (heap : BitVec bits → BitVec bits)
    (physical : Nat) (hfit : Fits bits physical)
    (hneH : physical ≠ header + 8) (hneC : physical ≠ childBase header q + parent) :
    reverseStepHeap header (childBase header q) parent node selected heap (BitVec.ofNat bits physical) = heap (BitVec.ofNat bits physical) := by
  have hnH := (ofNat_injective_of_fit _ _ hfit (layout.headerFits 8 (by decide))).not.mpr hneH
  have hnC := (ofNat_injective_of_fit _ _ hfit ((Nat.le_succ _).trans_lt (layout.targetFits parent hp))).not.mpr hneC
  rw [reverseStepHeap, Function.update_of_ne hnH, Function.update_of_ne hnC]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

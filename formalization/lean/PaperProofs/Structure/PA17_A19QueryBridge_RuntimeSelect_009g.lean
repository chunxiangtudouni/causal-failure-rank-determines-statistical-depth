module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009f

/-! Physical access and frame of the fixed parent-push continuation.
Only the particular materialized runtime cells actually read are constrained. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

theorem pushProgram_access {bits : Nat} (rom : PhysicalROM)
    (header candidates counts parents node parent heapWords : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hn : Fits bits (node + 1))
    (hh : state.register .address = BitVec.ofNat bits header)
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (node + 1))
    (hcandidates : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits candidates)
    (hcounts : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits counts)
    (hparents : state.heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits parents)
    (hreadParent : state.heap (BitVec.ofNat bits (parents + (node + 1))) = BitVec.ofNat bits parent)
    (hheader : header + 12 < heapWords) (hcountAlloc : counts + node < heapWords)
    (hparentAlloc : parents + (node + 1) < heapWords) (hcandidateAlloc : candidates + parent < heapWords)
    (clock : Nat) (hc : clock < pushProgram.length) :
    packingAccessFits rom heapWords (executeOps rom (pushProgram.take clock) state) pushProgram[clock] := by
  have h8 : header + 8 < heapWords := by omega
  have h10 : header + 10 < heapWords := by omega
  have h11 : header + 11 < heapWords := by omega
  change clock < 24 at hc
  interval_cases clock <;> try exact True.intro
  all_goals simp +decide only [pushProgram, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, packingAccessFits, AccessFits, hh, hnode, hcandidates, hcounts, hparents,
    hreadParent, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hn,
    Nat.add_sub_cancel]
  all_goals exact (Nat.mod_le _ _).trans_lt (by omega)

theorem pushProgram_prefix_frame {bits : Nat} (rom : PhysicalROM)
    (header candidates counts parents node parent cap count : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hn : Fits bits (node + 1)) (hparentFit : Fits bits parent)
    (hcap : Fits bits cap) (hcount : Fits bits count)
    (hh : state.register .address = BitVec.ofNat bits header) (hv : state.register .value = BitVec.ofNat bits cap)
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (node + 1))
    (hcandidates : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits candidates)
    (hcounts : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits counts)
    (hparents : state.heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits parents)
    (hreadCount : state.heap (BitVec.ofNat bits (counts + node)) = BitVec.ofNat bits count)
    (hreadParent : state.heap (BitVec.ofNat bits (parents + (node + 1))) = BitVec.ofNat bits parent)
    (clock : Nat) (hc : clock ≤ 24) (address : BitVec bits)
    (hne : address ≠ BitVec.ofNat bits (candidates + parent)) :
    (executeOps rom (pushProgram.take clock) state).heap address = state.heap address := by
  by_cases hlast : clock = 24
  · subst clock
    rw [show 24 = pushProgram.length from rfl, List.take_length]
    have hs := pushProgram_result rom header candidates counts parents node parent cap count state h1 hn hparentFit
      hcap hcount hh hv hnode hcandidates hcounts hparents hreadCount hreadParent
    rw [hs.2.2.2, Function.update_of_ne hne]
  · have hshort : clock ≤ 23 := by omega
    apply congrFun (executeOps_heap_of_no_store rom (pushProgram.take clock) state ?_) address
    intro op ho
    have htake : pushProgram.take clock = (pushProgram.take 23).take clock := by
      rw [List.take_take, Nat.min_eq_left hshort]
    rw [htake] at ho
    have hm := List.mem_of_mem_take ho
    have hnAll : ∀ item ∈ pushProgram.take 23, HeapPreservingOp item := by
      simp [pushProgram, HeapPreservingOp]
    exact hnAll op hm

theorem pushProgram_actual_prefix_access {bits : Nat} (rom : PhysicalROM)
    (containing : List PackingOp) (origin header candidates counts parents node parent heapWords : Nat) (state : WordState bits)
    (hbound : origin + pushProgram.length ≤ containing.length)
    (hcode : ∀ i (hi : i < pushProgram.length), containing[origin + i]'(by omega) = pushProgram[i])
    (hw : WordsFit bits (packingCode containing)) (hpc : Fits bits (5 * containing.length))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (h1 : Fits bits 1) (hn : Fits bits (node + 1))
    (hh : state.register .address = BitVec.ofNat bits header)
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (node + 1))
    (hcandidates : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits candidates)
    (hcounts : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits counts)
    (hparents : state.heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits parents)
    (hreadParent : state.heap (BitVec.ofNat bits (parents + (node + 1))) = BitVec.ofNat bits parent)
    (hheader : header + 12 < heapWords) (hcountAlloc : counts + node < heapWords)
    (hparentAlloc : parents + (node + 1) < heapWords) (hcandidateAlloc : candidates + parent < heapWords)
    (clock : Nat) (hc : clock < 24) :
    let before := packingRun rom containing clock state
    before.halted = false ∧ Fits bits (before.pc.toNat + 4) ∧
      before.pc.toNat + 4 < (packingCode containing).length ∧
      PackingOp.decode (physicalFetch bits (packingCode containing) before.pc.toNat) = some pushProgram[clock] ∧
      packingAccessFits rom heapWords before pushProgram[clock] := by
  have hcl : clock < pushProgram.length := by rwa [pushProgram_length]
  have hrun := PA17A19RuntimeRanks008.straight_prefix rom containing pushProgram origin hbound hcode pushProgram_straight hw hpc
    state hp ha clock hcl.le
  have hpcWord := PA17A19RuntimeRanks008.prefix_pc rom pushProgram origin pushProgram_straight state hp clock hcl.le
  have hindex : origin + clock < containing.length := by omega
  have hpNat : (executeOps rom (pushProgram.take clock) state).pc.toNat = 5 * (origin + clock) := by
    rw [hpcWord, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt ((Nat.mul_le_mul_left 5 hindex.le).trans_lt hpc)
  dsimp only
  rw [hrun]
  refine ⟨by rw [executeOps_halted, ha], ?_, ?_, ?_, ?_⟩
  · rw [hpNat]
    exact (show 5 * (origin + clock) + 4 < 5 * containing.length by omega).trans hpc
  · rw [hpNat, packingCode_length]
    omega
  · rw [hpNat, physicalFetch_eq bits (packingCode containing) _ hw]
    change PackingOp.decode (natFetch containing (5 * (origin + clock))) = some pushProgram[clock]
    rw [natFetch_body containing (origin + clock) hindex, hcode clock hcl, decode_encode]
  · exact pushProgram_access rom header candidates counts parents node parent heapWords state h1 hn hh hnode hcandidates
      hcounts hparents hreadParent hheader hcountAlloc hparentAlloc hcandidateAlloc clock hcl

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

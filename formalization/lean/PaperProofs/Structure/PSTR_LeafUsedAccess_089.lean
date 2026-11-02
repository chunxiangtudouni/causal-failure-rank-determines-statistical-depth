module

public import PaperProofs.Structure.PSTR_BranchAccess_088
public import PaperProofs.Structure.PSTR_RuntimePackedReadSafety_010

/-! Actual cached-label branch and positive packed used-bit access. The
real original heap determines none/some and the SAME3/36 duration as068;
the positive reader's next physical word is derived from packed capacity. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRLeafUsedAccess

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRCountKernel PSTRLeafUsedEmbedded PSTRCountWorkspace PSTRStaticLayout PSTRStaticHeap

theorem setup_access {bits : Nat} (rom : PhysicalROM) (heapWords : Nat) (state : WordState bits)
    (hinput : 1 < rom.input.length) (hheap : 0 < heapWords)
    (count : Nat) (hc : count < PSTRLeafUsed.setup.length) :
    packingAccessFits rom heapWords (executeOps rom (PSTRLeafUsed.setup.take count) state) PSTRLeafUsed.setup[count] := by
  change count < 16 at hc
  interval_cases count <;> try exact True.intro
  all_goals
    simp +decide only [PSTRLeafUsed.setup, List.take_succ_cons, List.take_zero,
      List.getElem_cons_zero, List.getElem_cons_succ, packingAccessFits, AccessFits,
      executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply,
      ↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mod, PhysicalROM.words]
    first | exact hheap | exact (Nat.mod_le _ _).trans_lt hinput | omega

theorem body_prefixOK {bits : Nat} (rom : PhysicalROM) (heapWords : Nat) (state : WordState bits)
    (N q t tool : Nat) (hb : 8 ≤ bits) (hw : CapacityBits.width q ≤ bits)
    (hN : (rom.words .input).getD 0 0 = N) (hq : (rom.words .input).getD 1 0 = q)
    (ht : (state.heap (BitVec.ofNat bits 0)).toNat = t)
    (hbits : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hlabel : (state.register .value).toNat = tool + 1)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hN1 : Fits bits (N + 1)) (hq2 : Fits bits (q + 2))
    (ht1 : Fits bits (t + 1)) (hprod : Fits bits ((N + 1) * (q + 2)))
    (haddress : Fits bits (tableWords N q t + tool))
    (hs : Fits bits ((tableWords N q t + tool) * CapacityBits.width q))
    (hn : Fits bits (4 + (tableWords N q t + tool) * CapacityBits.width q / bits + 1))
    (hinput : 1 < rom.input.length)
    (hheap : 4 + (tableWords N q t + tool) * CapacityBits.width q / bits + 1 < heapWords) :
    PrefixOK rom heapWords (fun _ => True) PSTRLeafUsed.body state := by
  let current := executeOps rom PSTRLeafUsed.setup state
  have haddr : (current.register .address).toNat = tableWords N q t + tool := by
    rw [PSTRLeafUsed.setup_address rom state N q t tool hb hN hq ht hlabel hN1 hq2 ht1 hprod,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddress]
  have first : PrefixOK rom heapWords (fun _ => True) PSTRLeafUsed.setup state := by
    apply readOnly_prefixOK
    · simp [PSTRLeafUsed.setup, ReadOnly]
    · exact setup_access rom heapWords state hinput ((Nat.zero_le _).trans_lt hheap)
  have last : PrefixOK rom heapWords (fun _ => True) PSTRRuntimePackedRead.program current := by
    apply readOnly_prefixOK
    · simp [PSTRRuntimePackedRead.program, ReadOnly]
    · exact PSTRRuntimePackedReadSafety.access_prefix rom current heapWords hb hw
        (by rw [PSTRLeafUsed.setup_width]; exact hwidth)
        (by rw [PSTRLeafUsed.setup_heap]; exact hbits)
        (by rw [haddr]; exact hs) (by rw [haddr]; exact hn) (by rw [haddr]; exact hheap)
  exact prefixOK_append rom heapWords (fun _ => True) PSTRLeafUsed.setup PSTRRuntimePackedRead.program state first last

theorem kernel_safe {bits q : Nat} (whole : List PackingOp) (start : Nat)
    (hbound : start + (kernel start).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (kernel start).length), whole[start + i]'(by omega) = (kernel start)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (full : List (Finset (Fin q))) (command : Command) (configuration : Configuration q)
    (capWords heapWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hN1 : Fits bits (full.length + 1)) (hq2 : Fits bits (q + 2))
    (ht1 : Fits bits (treeSize q full + 1)) (hprod : Fits bits ((full.length + 1) * (q + 2)))
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (haddress : state.register .address = BitVec.ofNat bits (metadataAddress q capWords bits (offset q full 6 + node.val)))
    (hroom : base q full capWords bits < heapWords)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < PSTRLeafPrefix.duration state) :
    AtSafe (callInput q full command) whole heapWords (packingRun (callInput q full command) whole clock state) := by
  let rom := callInput q full command
  have hmeta : metadataAddress q capWords bits (offset q full 6 + node.val) < heapWords := by
    have hpos := chunk_in_bounds q full hq 6 node.val (by decide) (by simp [chunks])
    rw [base_metadata_end q full hq] at hroom
    unfold metadataAddress at hroom ⊢
    omega
  have haccess : (state.register .address).toNat < heapWords := by
    rw [haddress, BitVec.toNat_ofNat]
    exact (Nat.mod_le _ _).trans_lt hmeta
  have leadSafe : PrefixOK rom heapWords (fun _ => True) (leadAt start) state := by
    apply readOnly_prefixOK
    · simp [leadAt, ReadOnly]
    · intro count hc
      change count < 2 at hc
      interval_cases count
      · exact haccess
      · trivial
  by_cases hlead : clock ≤ 2
  · apply (PSTRBranchAccess.branch_safe rom whole (leadAt start) .value .fresh heapWords start (fun _ => True)
      (by rw [kernel_length] at hbound; rw [leadAt_length]; omega) ?_ ?_ (leadAt_straight start)
      hwords hpcfit state hp ha leadSafe clock hlead).1
    · intro i hi
      exact (hcode i (by rw [kernel_length]; rw [leadAt_length] at hi; omega)).trans (kernel_lead start i hi)
    · simpa only [leadAt_length, PSTRLeafUsed.branch] using
        (hcode 2 (by rw [kernel_length]; decide)).trans (kernel_branch start)
  · have hnonzero : ¬(state.heap (state.register .address)).toNat = 0 := by
      intro hz
      simp only [PSTRLeafPrefix.duration, hz, ite_true] at hclock
      omega
    have hread : state.heap (state.register .address) = BitVec.ofNat bits
        (match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
          | none => 0 | some tool => tool.val + 1) := by
      rw [haddress]
      exact PSTRStaticHeap.leaf_word full configuration capWords state.heap hq rep node
    cases hl : (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
    | none =>
      have hz : (state.heap (state.register .address)).toNat = 0 := by rw [hread, hl]; rfl
      exact (hnonzero hz).elim
    | some tool =>
      have hfit : tool.val + 1 < 2 ^ bits :=
        (show tool.val + 1 ≤ q + 2 by have ht := tool.isLt; omega).trans_lt hq2
      have hlabel : (state.heap (state.register .address)).toNat = tool.val + 1 := by
        rw [hread, hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
      let current := executeOps rom (leadAt start ++ [PSTRLeafUsed.branch]) state
      have cp : current.pc = BitVec.ofNat bits (5 * (start + 3)) := by
        rw [prefix_pc rom start state hp, ite_eq_right hnonzero]
      have ca : current.halted = false := by rw [executeOps_halted, ha]
      have cv : (current.register .value).toNat = tool.val + 1 := by rw [prefix_value]; exact hlabel
      have room := PSTRLeafBitmap.bitmap_room full.length (treeSize q full) capWords tool hq bitmap hr
      have wp : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
        intro hz
        exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp hz))
      have hdiv : (tableWords full.length q (treeSize q full) + tool.val) * CapacityBits.width q / bits <
          packedCapacityWords q capWords bits :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < bits)).mpr
          ((Nat.mul_lt_mul_of_pos_right room.2.2.2 wp).trans_le (packedCapacityWords_mul_bits q capWords (by omega)))
      have hnext : 4 + (tableWords full.length q (treeSize q full) + tool.val) * CapacityBits.width q / bits + 1 < heapWords := by
        rw [base_metadata_end q full hq] at hroom
        unfold metadataAddress physicalHeaderWords at hroom
        omega
      have hinput : 1 < rom.input.length := by
        have he := PSTRLiveHeader.input_length q full command
        change 1 < (callInput q full command).input.length
        omega
      have safe := body_prefixOK rom heapWords current full.length q (treeSize q full) tool.val hb hw rfl rfl
        (by rw [prefix_heap]; exact rep.1) (by rw [prefix_heap]; exact rep.2.2.2.1) cv
        (by rw [prefix_width]; exact hwidth) hN1 hq2 ht1 hprod room.1 room.2.1 room.2.2.1 hinput hnext
      have hbody (i : Nat) (hi : i < PSTRLeafUsed.body.length) :
          whole[start + 3 + i]'(by rw [kernel_length] at hbound; rw [PSTRLeafUsed.body_length] at hi; omega) = PSTRLeafUsed.body[i] := by
        have he := hcode (3 + i) (by rw [kernel_length]; rw [PSTRLeafUsed.body_length] at hi; omega)
        simpa only [Nat.add_assoc] using he.trans (kernel_body start i hi)
      have countBound : clock - 3 < PSTRLeafUsed.body.length := by
        have ht := PSTRLeafPrefix.duration_bound state
        rw [PSTRLeafUsed.body_length]
        omega
      rw [show clock = 3 + (clock - 3) by omega, PSTRWordSegments.run_add,
        prefix_run rom whole start hbound hcode hwords hpcfit state hp ha]
      exact (straight_prefix_safe rom whole PSTRLeafUsed.body heapWords (start + 3) (fun _ => True)
        (by rw [kernel_length] at hbound; rw [PSTRLeafUsed.body_length]; omega) hbody PSTRLeafUsed.body_straight
        hwords hpcfit current cp ca safe (clock - 3) countBound).1

end PaperProofs.Structure.LaminarTree.PSTRLeafUsedAccess

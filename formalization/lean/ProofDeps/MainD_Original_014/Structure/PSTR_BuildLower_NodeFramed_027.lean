module

public import Structure.PSTR_BuildLower_GetterWord_024

/-! Complete real decoder+node-getter prefix/access interface. All frames and
accesses come from actual execution, with the SAME bounded return witness. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.NodeInput
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawTreePreprocessingClaims

variable {bits : Nat}

theorem prep_run_prefix (rom : PhysicalROM) (left right : List PackingOp) (pointer : Register)
    (hcode : WordsFit bits (packingCode (left ++ prep pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ prep pointer ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length))
    (ha : state.halted = false) (count : Nat) (hc : count ≤ 17) :
    packingRun rom (left ++ prep pointer ++ right) count state =
      executeOps rom ((prep pointer).take count) state := by
  have hlen : ((prep pointer).take count).length = count :=
    List.length_take_of_le (by rw [prep_length]; exact hc)
  conv_lhs => rw [← hlen]
  apply PSTRWordSegments.straight_segment rom _ _ left.length
    (by simp only [List.length_append, prep_length]; omega) ?_ ?_ hcode hpcfit state hpc ha
  · intro index hi
    have hx : index < (prep pointer).length := by rw [hlen] at hi; rw [prep_length]; omega
    simpa only [List.getElem_take] using PA17UniformGenerator035a.segment_index left (prep pointer) right index hx
  · intro op hm
    exact prep_straight pointer op (List.mem_of_mem_take hm)

theorem nodeBit_call_framed (factor q : Nat) (full : List (Finset (Fin q))) (hf : 16 ≤ factor)
    (initialUsed : Finset (Fin q)) (left right : List PackingOp) (pointer : Register)
    (base heapWords : Nat) (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (before : WordState (indexWidth factor full.length q))
    (hpc : before.pc = BitVec.ofNat _ (5 * left.length)) (ha : before.halted = false)
    (hN : (before.heap (before.register .address)).toNat = full.length)
    (hq : (before.heap (before.register .address + BitVec.ofNat _ 1)).toNat = q)
    (hptr : (Ordinary.pointerValue before pointer).toNat =
      3 + full.length * q + (node.val * q + tool.val))
    (hbase : (before.register .address).toNat = base)
    (cached : PA06A19PrepareBankNodeBit022.CachedWordNode full base node before.heap)
    (hroom : PA06A19PrepareBankNodeBit022.ordAddress full.length q base node.val < heapWords)
    (hheap : Fits (indexWidth factor full.length q) heapWords)
    (hcode : WordsFit (indexWidth factor full.length q)
      (packingCode (left ++ nodeBitCode left.length pointer ++ right)))
    (hpcfit : Fits (indexWidth factor full.length q)
      (5 * (left ++ nodeBitCode left.length pointer ++ right).length)) :
    ∃ count ≤ 52,
      let after := packingRun (CompactControllerClaims.controllerInput q full initialUsed)
        (left ++ nodeBitCode left.length pointer ++ right) count before
      (after.register .value).toNat = bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) ∧
        (after.register .fresh).toNat = tool.val ∧ after.register .address = before.register .address ∧
        after.heap = before.heap ∧ after.pc.toNat = 5 * (left.length + 63) ∧ after.halted = false ∧
      (∀ k ≤ count,
        let current := packingRun (CompactControllerClaims.controllerInput q full initialUsed)
          (left ++ nodeBitCode left.length pointer ++ right) k before
        current.heap = before.heap ∧ current.register .address = before.register .address) ∧
      ∀ k < count,
        let current := packingRun (CompactControllerClaims.controllerInput q full initialUsed)
          (left ++ nodeBitCode left.length pointer ++ right) k before
        current.halted = false ∧ current.register .address = before.register .address ∧
          current.pc.toNat + 4 < (packingCode (left ++ nodeBitCode left.length pointer ++ right)).length ∧
          ∃ op, PackingOp.decode (fetch (left ++ nodeBitCode left.length pointer ++ right) current) = some op ∧
            packingAccessFits (CompactControllerClaims.controllerInput q full initialUsed) heapWords current op := by
  let runtime := CompactControllerClaims.controllerInput q full initialUsed
  let containing := left ++ nodeBitCode left.length pointer ++ right
  let mid := executeOps runtime (prep pointer) before
  have hfront' :=
    prep_run runtime left (PA06A19PrepareBankNodeBit022.programAt (left.length + 17) ++ right)
      pointer (by simpa only [nodeBitCode, List.append_assoc] using hcode)
      (by simpa only [nodeBitCode, List.append_assoc] using hpcfit) before hpc ha
  have hfront : packingRun runtime containing 17 before = mid := by
    simpa only [containing, nodeBitCode, List.append_assoc] using hfront'
  have hm := prep_prefix_frame runtime pointer before (prep pointer).length
  rw [List.take_length] at hm
  have hmheap : mid.heap = before.heap := hm.1
  have hmbase : mid.register .address = before.register .address := hm.2
  have hmactive : mid.halted = false := (executeOps_halted runtime _ before).trans ha
  have hmvalue := prep_node_tool runtime pointer before full.length q node.val tool hN hq hptr
  have hmPCWord : mid.pc = BitVec.ofNat _ (5 * (left.length + 17)) := by
    have he : 5 * left.length + 85 = 5 * (left.length + 17) := by omega
    rw [prep_pc, hpc, BitVec.ofNat_add_ofNat, he]
  have hend : Fits (indexWidth factor full.length q) (5 * (left.length + 17 + 46)) := by
    apply lt_of_le_of_lt (Nat.mul_le_mul_left 5 ?_) hpcfit
    simp only [List.length_append, nodeBitCode_length]
    omega
  have hmidFit : Fits (indexWidth factor full.length q) (5 * (left.length + 17)) :=
    lt_of_le_of_lt (by omega) hend
  have hmPC : mid.pc.toNat = 5 * (left.length + 17) := by
    rw [hmPCWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmidFit]
  have hmBaseNat : (mid.register .address).toNat = base := by rw [hmbase, hbase]
  have hmCached : PA06A19PrepareBankNodeBit022.CachedWordNode full base node mid.heap := by
    rw [hmheap]
    exact cached
  obtain ⟨count, hcount, returned⟩ := GetterFrame.word_query_framed factor q full hf initialUsed
    containing (left.length + 17) (nodeBitCode_getter_slice left right pointer) base heapWords node tool
    mid hmPC hmactive hmvalue.1 hmvalue.2 hmBaseNat hmCached hroom hheap hend hcode
  dsimp only at returned
  rcases returned with ⟨hvalue, hfresh, haddr, hdata, hlastPC, hactive, hframes, hsafe⟩
  have front (k : Nat) (hk : k ≤ 17) : packingRun runtime containing k before =
      executeOps runtime ((prep pointer).take k) before := by
    have hh := prep_run_prefix runtime left
      (PA06A19PrepareBankNodeBit022.programAt (left.length + 17) ++ right) pointer
      (by simpa only [nodeBitCode, List.append_assoc] using hcode)
      (by simpa only [nodeBitCode, List.append_assoc] using hpcfit) before hpc ha k hk
    simpa only [containing, nodeBitCode, List.append_assoc] using hh
  have slice (k : Nat) (hk : k < 17) :
      containing[left.length + k]'(by dsimp only [containing]; simp only [List.length_append, nodeBitCode_length]; omega) =
        (prep pointer)[k]'(by simpa only [prep_length] using hk) := by
    have hh := PA17UniformGenerator035a.segment_index left (prep pointer)
      (PA06A19PrepareBankNodeBit022.programAt (left.length + 17) ++ right)
      k (by simpa only [prep_length] using hk)
    simpa only [containing, nodeBitCode, List.append_assoc] using hh
  have bankRoom (offset : Nat) (ho : offset < 39) :
      (before.register .address + BitVec.ofNat _ offset).toNat < heapWords := by
    have hs : base + offset < heapWords := by
      dsimp only [PA06A19PrepareBankNodeBit022.ordAddress] at hroom
      omega
    have hoFit : offset < 2 ^ indexWidth factor full.length q := lt_of_le_of_lt (by omega) (hs.trans hheap)
    rw [BitVec.toNat_add, hbase, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoFit,
      Nat.mod_eq_of_lt (hs.trans hheap)]
    exact hs
  refine ⟨17 + count, by omega, ?_⟩
  have hrun : packingRun runtime containing (17 + count) before = packingRun runtime containing count mid := by
    rw [PSTRWordSegments.run_add, hfront]
  change ((packingRun runtime containing (17 + count) before).register .value).toNat = _ ∧ _
  rw [hrun]
  refine ⟨hvalue, ?_, haddr.trans hmbase, hdata.trans hmheap, ?_, hactive, ?_, ?_⟩
  · rw [hfresh]
    exact hmvalue.2
  · simpa only [Nat.add_assoc] using hlastPC
  · intro k hk
    by_cases kh : k ≤ 17
    · rw [front k kh]
      exact prep_prefix_frame runtime pointer before k
    · have kr : k = 17 + (k - 17) := by omega
      rw [kr, PSTRWordSegments.run_add, hfront]
      have hh := hframes (k - 17) (by omega)
      exact ⟨hh.1.trans hmheap, hh.2.2.trans hmbase⟩
  · intro k hk
    by_cases kh : k < 17
    · rw [front k kh.le]
      have hlen : ((prep pointer).take k).length = k :=
        List.length_take_of_le (by rw [prep_length]; exact kh.le)
      have hs : StraightProgram ((prep pointer).take k) :=
        fun op hm => prep_straight pointer op (List.mem_of_mem_take hm)
      have hp : (executeOps runtime ((prep pointer).take k) before).pc.toNat = 5 * (left.length + k) := by
        rw [executeOps_pc _ _ _ hs, hlen, hpc, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
        have he : 5 * left.length + 5 * k = 5 * (left.length + k) := by omega
        rw [he, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left 5 ?_) hpcfit)]
        simp only [List.length_append, nodeBitCode_length]
        omega
      have hi : left.length + k < containing.length := by
        dsimp only [containing]
        simp only [List.length_append, nodeBitCode_length]
        omega
      refine ⟨(executeOps_halted runtime _ before).trans ha,
        (prep_prefix_frame runtime pointer before k).2, ?_,
        (prep pointer)[k]'(by simpa only [prep_length] using kh), ?_, ?_⟩
      · rw [hp, packingCode_length]
        change 5 * (left.length + k) + 4 < 5 * containing.length + 5
        omega
      · change PackingOp.decode (physicalFetch _ (packingCode containing)
          (executeOps runtime ((prep pointer).take k) before).pc.toNat) = _
        rw [physicalFetch_eq _ _ _ hcode, hp]
        change PackingOp.decode (natFetch containing (5 * (left.length + k))) = _
        rw [natFetch_body containing (left.length + k) hi, slice k kh, decode_encode]
      · apply prep_prefix_access runtime pointer before heapWords k
        · apply bankRoom
          cases pointer <;> decide
        · simpa using bankRoom 0 (by decide)
        · exact bankRoom 1 (by decide)
        · exact kh
    · have kr : k = 17 + (k - 17) := by omega
      rw [kr, PSTRWordSegments.run_add, hfront]
      have hh := hsafe (k - 17) (by omega)
      exact ⟨hh.1, hh.2.1.trans hmbase, hh.2.2⟩

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.NodeInput

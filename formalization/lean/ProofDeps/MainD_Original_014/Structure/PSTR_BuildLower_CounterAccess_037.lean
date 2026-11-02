module

public import Structure.PSTR_BuildLower_CounterInit_036

/-! Actual64-clock counter initialization: every fetched prefix retains CB,
frames every other word and makes only allocated primitive stores. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.CounterInit
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawTreePreprocessingClaims PA17PackedTranslator034
variable {bits : Nat}

private theorem relativeWrite_safe (rom : PhysicalROM) (offset heapWords : Nat) (state : WordState bits)
    (hr : (state.register .address + BitVec.ofNat bits offset).toNat < heapWords) :
    PackedAccessSafe heapWords rom (relativeWrite offset) state := by
  simp [BitVec.toNat_add] at hr
  intro count hc
  change count < 3 at hc
  interval_cases count <;>
    simp [relativeWrite, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits]
  exact hr

private theorem clearOps_safe (rom : PhysicalROM) (points : List Nat) (heapWords : Nat) (state : WordState bits)
    (hr : ∀ offset ∈ points, (state.register .address + BitVec.ofNat bits offset).toNat < heapWords) :
    PackedAccessSafe heapWords rom (clearOps points) state := by
  induction points generalizing state with
  | nil => exact PackedAccessSafe.nil heapWords rom state
  | cons offset later ih =>
    apply PackedAccessSafe.append heapWords rom (relativeWrite offset) (clearOps later) state
      (relativeWrite_safe rom offset heapWords state (hr offset List.mem_cons_self))
    apply ih
    intro point hp
    have hb : (executeOps rom (relativeWrite offset) state).register .address = state.register .address := rfl
    rw [hb]
    exact hr point (List.mem_cons_of_mem _ hp)

theorem code_safe (rom : PhysicalROM) (heapWords : Nat) (state : WordState bits)
    (hr : ∀ counter < 21, (state.register .address + BitVec.ofNat bits (64 + counter)).toNat < heapWords) :
    PackedAccessSafe heapWords rom code state := by
  apply PackedAccessSafe.append heapWords rom [.base (.base (.constant .value 0))] (clearOps offsets) state
  · intro count hc
    change count < 1 at hc
    have he : count = 0 := by omega
    subst count
    trivial
  · apply clearOps_safe
    intro offset hm
    obtain ⟨counter, hi, rfl⟩ := List.mem_map.mp hm
    exact hr counter (List.mem_range.mp hi)

theorem run_prefix (rom : PhysicalROM) (left right : List PackingOp) (state : WordState bits)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ code ++ right)))
    (hpcfit : Fits bits (5 * (left ++ code ++ right).length)) (count : Nat) (hc : count ≤ 64) :
    packingRun rom (left ++ code ++ right) count state = executeOps rom (code.take count) state := by
  have hlen : (code.take count).length = count := List.length_take_of_le (by rw [code_length]; exact hc)
  conv_lhs => rw [← hlen]
  apply PSTRWordSegments.straight_segment rom _ _ left.length
    (by simp only [List.length_append, code_length]; omega) ?_ ?_ hcode hpcfit state hpc ha
  · intro index hi
    have hx : index < code.length := by rw [hlen] at hi; rw [code_length]; omega
    simpa only [List.getElem_take] using PA17UniformGenerator035a.segment_index left code right index hx
  · intro op hm
    exact code_straight op (List.mem_of_mem_take hm)

theorem actual_prefix_safe (rom : PhysicalROM) (left right : List PackingOp) (heapWords : Nat) (state : WordState bits)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ code ++ right)))
    (hpcfit : Fits bits (5 * (left ++ code ++ right).length))
    (hr : ∀ counter < 21, (state.register .address + BitVec.ofNat bits (64 + counter)).toNat < heapWords) :
    (∀ count ≤ 64,
      let current := packingRun rom (left ++ code ++ right) count state
      current.halted = false ∧ current.register .address = state.register .address ∧
        ∀ point : BitVec bits, (∀ offset, 64 ≤ offset → offset < 85 →
          point ≠ state.register .address + BitVec.ofNat bits offset) → current.heap point = state.heap point) ∧
    ∀ count < 64,
      let current := packingRun rom (left ++ code ++ right) count state
      current.pc.toNat + 4 < (packingCode (left ++ code ++ right)).length ∧
        ∃ op, PackingOp.decode (fetch (left ++ code ++ right) current) = some op ∧
          packingAccessFits rom heapWords current op := by
  constructor
  · intro count hc
    rw [run_prefix rom left right state hpc ha hcode hpcfit count hc]
    refine ⟨(executeOps_halted rom _ state).trans ha, (code_range rom).1 state count, ?_⟩
    intro point outside
    exact (code_range rom).2 state point outside count
  · intro count hc
    rw [run_prefix rom left right state hpc ha hcode hpcfit count hc.le]
    have hlen : (code.take count).length = count := List.length_take_of_le (by rw [code_length]; exact hc.le)
    have hs : StraightProgram (code.take count) := fun op hm => code_straight op (List.mem_of_mem_take hm)
    have hp : (executeOps rom (code.take count) state).pc.toNat = 5 * (left.length + count) := by
      rw [executeOps_pc _ _ _ hs, hlen, hpc, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
      have he : 5 * left.length + 5 * count = 5 * (left.length + count) := by omega
      rw [he, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left 5 ?_) hpcfit)]
      simp only [List.length_append, code_length]
      omega
    have hi : left.length + count < (left ++ code ++ right).length := by
      simp only [List.length_append, code_length]
      omega
    refine ⟨?_, code[count]'(by rw [code_length]; exact hc), ?_, code_safe rom heapWords state hr count (by rw [code_length]; exact hc)⟩
    · rw [hp, packingCode_length]
      omega
    · change PackingOp.decode (physicalFetch _ (packingCode (left ++ code ++ right))
        (executeOps rom (code.take count) state).pc.toNat) = _
      rw [physicalFetch_eq _ _ _ hcode, hp]
      change PackingOp.decode (natFetch (left ++ code ++ right) (5 * (left.length + count))) = _
      rw [natFetch_body _ _ hi, PA17UniformGenerator035a.segment_index left code right count (by rw [code_length]; exact hc), decode_encode]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.CounterInit

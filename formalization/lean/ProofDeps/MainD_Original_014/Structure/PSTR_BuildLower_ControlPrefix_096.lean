module

public import Structure.PSTR_BuildLower_LoopData_082
public import Structure.PSTR_BuildLower_ResourceTrace_094

/-! Actual fetched prefixes of countdown control, including the final
conditional/unconditional jump. The jump is executed as the last instruction
of a segment; it is never declared straight or silently omitted. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ControlPrefix
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035a
section Generic
variable {bits : Nat}

theorem head_prefix (physical : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (hcode : WordsFit bits (packingCode (left ++ relativeLoopBlock counter left.length body ++ right)))
    (hpcfit : Fits bits (5 * (left ++ relativeLoopBlock counter left.length body ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length))
    (ha : state.halted = false) (count : Nat) (hc : count ≤ 5) :
    packingRun physical (left ++ relativeLoopBlock counter left.length body ++ right) count state =
      executeOps physical ((relativeLoopHead counter (5 * (left.length + body.length + 14))).take count) state := by
  let lead := (relativeLoopHead counter (5 * (left.length + body.length + 14))).take 4
  have hlen : lead.length = 4 := rfl
  have blockLength := relativeLoopBlock_length counter left.length body
  apply PSTRWordSegments.segment_prefix physical _ lead (.jumpIfZero .value .fresh) left.length
    (by simp only [List.length_append, hlen, blockLength]; omega) ?_ ?_ ?_ hcode hpcfit state hpc ha count (by rw [hlen]; omega)
  · intro position hp
    rw [hlen] at hp
    have hh := segment_index left (relativeLoopHead counter (5 * (left.length + body.length + 14)))
      (body ++ relativeLoopTail counter (5 * left.length) ++ right) position (by change position < 5; omega)
    simpa only [relativeLoopBlock, List.append_assoc, lead, List.getElem_take] using hh
  · have hh := segment_index left (relativeLoopHead counter (5 * (left.length + body.length + 14)))
      (body ++ relativeLoopTail counter (5 * left.length) ++ right) 4 (by change 4 < 5; decide)
    have hj : (relativeLoopHead counter (5 * (left.length + body.length + 14)))[4]'(by rw [relativeLoopHead_length]; omega) =
        PackingOp.jumpIfZero .value .fresh := rfl
    rw [hj] at hh
    simpa only [relativeLoopBlock, List.append_assoc, hlen] using hh
  · simp [lead, relativeLoopHead, relativeRead, StraightProgram, StraightOp]

theorem tail_prefix (physical : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (hcode : WordsFit bits (packingCode (left ++ relativeLoopBlock counter left.length body ++ right)))
    (hpcfit : Fits bits (5 * (left ++ relativeLoopBlock counter left.length body ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * (left.length + 5 + body.length)))
    (ha : state.halted = false) (count : Nat) (hc : count ≤ 9) :
    packingRun physical (left ++ relativeLoopBlock counter left.length body ++ right) count state =
      executeOps physical ((relativeLoopTail counter (5 * left.length)).take count) state := by
  let lead := (relativeLoopTail counter (5 * left.length)).take 8
  have hlen : lead.length = 8 := rfl
  have blockLength := relativeLoopBlock_length counter left.length body
  have headLength : (relativeLoopHead counter (5 * (left.length + body.length + 14))).length = 5 := rfl
  have prefixLength : (left ++ relativeLoopHead counter (5 * (left.length + body.length + 14)) ++ body).length =
      left.length + 5 + body.length := by simp only [List.length_append, headLength]
  apply PSTRWordSegments.segment_prefix physical _ lead (.jumpIfZero .flag .fresh)
    (left.length + 5 + body.length) (by simp only [List.length_append, hlen, blockLength]; omega)
    ?_ ?_ ?_ hcode hpcfit state hpc ha count (by rw [hlen]; omega)
  · intro position hp
    rw [hlen] at hp
    have hh := segment_index (left ++ relativeLoopHead counter (5 * (left.length + body.length + 14)) ++ body)
      (relativeLoopTail counter (5 * left.length)) right position (by change position < 9; omega)
    simp only [prefixLength] at hh
    simpa only [relativeLoopBlock, List.append_assoc, lead, List.getElem_take] using hh
  · have hh := segment_index (left ++ relativeLoopHead counter (5 * (left.length + body.length + 14)) ++ body)
      (relativeLoopTail counter (5 * left.length)) right 8 (by change 8 < 9; decide)
    simp only [prefixLength] at hh
    have hj : (relativeLoopTail counter (5 * left.length))[8]'(by rw [relativeLoopTail_length]; omega) =
        PackingOp.jumpIfZero .flag .fresh := rfl
    rw [hj] at hh
    simpa only [relativeLoopBlock, List.append_assoc, hlen] using hh
  · simp [lead, relativeLoopTail, relativeRead, StraightProgram, StraightOp]

theorem head_heap_prefix (physical : PhysicalROM) (counter exit : Nat) (state : WordState bits) (count : Nat) :
    (executeOps physical ((relativeLoopHead counter exit).take count) state).heap = state.heap := by
  by_cases hc : count ≤ 5
  · interval_cases count <;> rfl
  · rw [List.take_of_length_le (by rw [relativeLoopHead_length]; omega), relativeLoopHead_word_heap]

end Generic

theorem head_keeps (q : Nat) (full : List (Finset (Fin q)))
    (physical : PhysicalROM) (counter : Nat) (left body right : List PackingOp)
    (state : WordState (bits q full)) (bounded : GlobalCapacity.Bounded q full state.heap)
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeLoopBlock counter left.length body ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeLoopBlock counter left.length body ++ right).length)) :
    ResourceTrace.Keeps q full physical (left ++ relativeLoopBlock counter left.length body ++ right) state 5 := by
  intro clock hclock
  rw [head_prefix physical left body right counter hcode hpcfit state hpc ha clock hclock, head_heap_prefix]
  exact ⟨bounded, ResourceTrace.CacheFrame.refl q full state.heap⟩

theorem tail_keeps (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (counter : Nat) (hc : counter < 512) (left body right : List PackingOp)
    (state : WordState (bits q full)) (hbase : state.register .address = BitVec.ofNat _ (controlBase q full))
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hpc : state.pc = BitVec.ofNat _ (5 * (left.length + 5 + body.length))) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeLoopBlock counter left.length body ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeLoopBlock counter left.length body ++ right).length)) :
    ResourceTrace.Keeps q full physical (left ++ relativeLoopBlock counter left.length body ++ right) state 9 := by
  intro clock hclock
  rw [tail_prefix physical left body right counter hcode hpcfit state hpc ha clock hclock]
  have frame := LoopData.tail_range (q := q) (full := full) physical counter (5 * left.length)
  exact ⟨GlobalCapacity.bank_range_prefix q full hq physical _ counter (counter + 1) (by omega) (by omega)
      frame state hbase bounded clock,
    ResourceTrace.bank_range_cache q full hq physical _ counter (counter + 1) (by omega) frame state hbase clock⟩

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ControlPrefix

module

public import Structure.PSTR_NodeLeaf_047
public import Structure.PSTR_WidthPrefix_035

/-! Actual every-clock heap preservation for the leaf's real short-circuit
branch. The duration is read from the actual source word, so the zero branch
stops at its ACTIVE exit and does not accidentally execute the caller's tail. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRLeafPrefix

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PSTRLeafUsedEmbedded

def duration {bits : Nat} (state : WordState bits) : Nat :=
  if (state.heap (state.register .address)).toNat = 0 then 3 else 36

theorem duration_bound {bits : Nat} (state : WordState bits) : duration state ≤ 36 := by
  unfold duration
  split <;> omega

theorem lead_prefix {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (start : Nat) (hbound : start + (kernel start).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (kernel start).length), whole[start + i]'(by omega) = (kernel start)[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 3) :
    packingRun rom whole count state = executeOps rom ((leadAt start ++ [PSTRLeafUsed.branch]).take count) state := by
  apply PSTRWordSegments.segment_prefix rom whole (leadAt start) PSTRLeafUsed.branch start
    (by rw [kernel_length, leadAt_length] at *; omega) ?_ ?_ (leadAt_straight start)
    hw hpcfit state hp ha count hc
  · intro i hi
    exact (hcode i (by rw [kernel_length]; rw [leadAt_length] at hi; omega)).trans (kernel_lead start i hi)
  · simpa only [leadAt_length] using (hcode 2 (by rw [kernel_length]; decide)).trans (kernel_branch start)

theorem lead_prefix_heap {bits : Nat} (rom : PhysicalROM) (start : Nat) (state : WordState bits)
    (count : Nat) (hc : count ≤ 3) :
    (executeOps rom ((leadAt start ++ [PSTRLeafUsed.branch]).take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem body_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (count : Nat) :
    (executeOps rom (PSTRLeafUsed.body.take count) state).heap = state.heap := by
  apply executeOps_heap_of_no_store
  intro op ho
  have hno : ∀ entry ∈ PSTRLeafUsed.body, HeapPreservingOp entry := by
    simp [PSTRLeafUsed.body, PSTRLeafUsed.setup, PSTRRuntimePackedRead.program, HeapPreservingOp]
  exact hno op (List.mem_of_mem_take ho)

theorem body_prefix {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (start : Nat) (hbound : start + (kernel start).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (kernel start).length), whole[start + i]'(by omega) = (kernel start)[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (start + 3))) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 33) :
    packingRun rom whole count state = executeOps rom (PSTRLeafUsed.body.take count) state := by
  apply PSTRWidthPrefix.straight_prefix rom whole PSTRLeafUsed.body (start + 3)
    (by rw [kernel_length] at hbound; rw [PSTRLeafUsed.body_length]; omega) ?_
    PSTRLeafUsed.body_straight hw hpcfit state hp ha count hc
  intro i hi
  have hh := hcode (3 + i) (by rw [kernel_length]; rw [PSTRLeafUsed.body_length] at hi; omega)
  simpa only [Nat.add_assoc] using hh.trans (kernel_body start i hi)

theorem actual_prefix_heap {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (start : Nat) (hbound : start + (kernel start).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (kernel start).length), whole[start + i]'(by omega) = (kernel start)[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (clock : Nat) (hc : clock ≤ duration state) :
    (packingRun rom whole clock state).heap = state.heap := by
  by_cases hlead : clock ≤ 3
  · rw [lead_prefix rom whole start hbound hcode hw hpcfit state hp ha clock hlead]
    exact lead_prefix_heap rom start state clock hlead
  · have hz : ¬(state.heap (state.register .address)).toNat = 0 := by
      intro he
      simp only [duration, he, ite_true] at hc
      omega
    have hclock : clock ≤ 36 := hc.trans (duration_bound state)
    let tested := executeOps rom (leadAt start ++ [PSTRLeafUsed.branch]) state
    have htp : tested.pc = BitVec.ofNat bits (5 * (start + 3)) := by
      rw [prefix_pc rom start state hp, ite_eq_right hz]
    have hta : tested.halted = false := by rw [executeOps_halted, ha]
    rw [show clock = 3 + (clock - 3) by omega, PSTRWordSegments.run_add,
      prefix_run rom whole start hbound hcode hw hpcfit state hp ha,
      body_prefix rom whole start hbound hcode hw hpcfit tested htp hta (clock - 3) (by omega)]
    exact (body_prefix_heap rom tested _).trans (prefix_heap rom start state)

theorem actual_exit {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (start : Nat) (hbound : start + (kernel start).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (kernel start).length), whole[start + i]'(by omega) = (kernel start)[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    let after := packingRun rom whole (duration state) state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (start + 36)) ∧ after.heap = state.heap := by
  by_cases hz : (state.heap (state.register .address)).toNat = 0
  · have result := actual_none rom whole start hbound hcode hw hpcfit state hp ha hz
    simpa only [duration, hz, ite_true] using And.intro result.1 (And.intro result.2.1 result.2.2.1)
  · simpa only [duration, hz, ite_false] using actual_some rom whole start hbound hcode hw hpcfit state hp ha hz

theorem prepare_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (count : Nat) :
    (executeOps rom (PSTRLeafPrepare.program.take count) state).heap = state.heap := by
  apply executeOps_heap_of_no_store
  intro op ho
  have hno : ∀ entry ∈ PSTRLeafPrepare.program, HeapPreservingOp entry := by
    simp [PSTRLeafPrepare.program, PSTRStaticFields.program, PSTRLeafPrepare.parkAddress,
      PSTRCountWorkspace.program, PSTRLeafPrepare.loadWidth, HeapPreservingOp]
  exact hno op (List.mem_of_mem_take ho)

theorem prepared_prefix {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : PSTRNodeLeaf.Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    let prepared := executeOps rom PSTRLeafPrepare.program state
    let steps := 51 + duration prepared
    steps ≤ 87 ∧
      (packingRun rom whole steps state).halted = false ∧
      (packingRun rom whole steps state).pc = BitVec.ofNat bits (5 * (start + 87)) ∧
      ∀ clock ≤ steps, (packingRun rom whole clock state).heap = state.heap := by
  let prepared := executeOps rom PSTRLeafPrepare.program state
  have hp' : prepared.pc = BitVec.ofNat bits (5 * (start + 51)) := by
    rw [executeOps_pc rom _ state PSTRLeafPrepare.program_straight, hp,
      PSTRLeafPrepare.program_length, BitVec.ofNat_add_ofNat]
    exact congrArg (BitVec.ofNat bits) (by omega)
  have ha' : prepared.halted = false := by rw [executeOps_halted, ha]
  have finished := actual_exit rom whole (start + 51) (PSTRNodeLeaf.leaf_bounds whole start hc)
    (PSTRNodeLeaf.leaf_code whole start hc) hw hpcfit prepared hp' ha'
  dsimp only
  refine ⟨by have := duration_bound (executeOps rom PSTRLeafPrepare.program state); omega, ?_, ?_, ?_⟩
  · rw [PSTRWordSegments.run_add, PSTRNodeLeaf.prepare_run rom whole start hc hw hpcfit state hp ha]
    exact finished.1
  · rw [PSTRWordSegments.run_add, PSTRNodeLeaf.prepare_run rom whole start hc hw hpcfit state hp ha]
    exact finished.2.1.trans (congrArg (BitVec.ofNat bits) (by omega))
  · intro clock hclock
    change clock ≤ 51 + duration prepared at hclock
    by_cases hfirst : clock ≤ 51
    · rw [PSTRWidthPrefix.straight_prefix rom whole PSTRLeafPrepare.program start
        (by have hh := hc.bound; rw [PSTRNodeLeaf.programAt_length] at hh; rw [PSTRLeafPrepare.program_length]; omega)
        (fun i hi => (hc.code i (by rw [PSTRNodeLeaf.programAt_length]; rw [PSTRLeafPrepare.program_length] at hi; omega)).trans
          (PSTRNodeLeaf.prepare_code start i hi))
        PSTRLeafPrepare.program_straight hw hpcfit state hp ha clock hfirst]
      exact prepare_prefix_heap rom state clock
    · rw [show clock = 51 + (clock - 51) by omega, PSTRWordSegments.run_add,
        PSTRNodeLeaf.prepare_run rom whole start hc hw hpcfit state hp ha]
      have frame := (actual_prefix_heap rom whole (start + 51) (PSTRNodeLeaf.leaf_bounds whole start hc)
        (PSTRNodeLeaf.leaf_code whole start hc) hw hpcfit prepared hp' ha' (clock - 51) (by omega)).trans
        (prepare_prefix_heap rom state PSTRLeafPrepare.program.length)
      simpa only [List.take_length] using frame

end PaperProofs.Structure.LaminarTree.PSTRLeafPrefix

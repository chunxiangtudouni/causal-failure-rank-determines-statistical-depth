module

public import Structure.PSTR_IterationsSafe_096

/-! Every proper clock of the actual width/mask loop is fetched and
decoded from the same containing code. Its real branches and Word state
are followed; none of these literal operations accesses data memory. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRWidthAccess

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRCountKernel
open PSTRWidthKernel PSTRWidthEmbedded RawTreePreprocessingClaims

theorem init_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start heapWords : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 4) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) := by
  have safe : PrefixOK rom heapWords (fun _ => True) PSTRRuntimeWidth.initCode state := by
    apply readOnly_prefixOK
    · simp [PSTRRuntimeWidth.initCode, ReadOnly]
    · intro count hn
      change count < 4 at hn
      interval_cases count <;> trivial
  apply (straight_prefix_safe rom whole PSTRRuntimeWidth.initCode heapWords start (fun _ => True)
    (by have hh := hc.bound; rw [kernel_length] at hh; change start + 4 ≤ whole.length; omega)
    ?_ init_straight hw hpcfit state hp ha safe clock hclock).1
  intro i hi
  exact (hc.code i (by rw [kernel_length]; change i < 4 at hi; omega)).trans (kernel_init start i hi)

theorem test_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start heapWords : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (start + 4))) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 3) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) := by
  have safe : PrefixOK rom heapWords (fun _ => True) (testLeadAt start) state := by
    apply readOnly_prefixOK
    · simp [testLeadAt, ReadOnly]
    · intro count hn
      change count < 2 at hn
      interval_cases count <;> trivial
  apply (PSTRBranchAccess.branch_safe rom whole (testLeadAt start) .flag .address heapWords (start + 4) (fun _ => True)
    (by have hh := hc.bound; rw [kernel_length] at hh; rw [PSTRWidthKernel.testLead_length]; omega)
    ?_ ?_ (test_straight start) hw hpcfit state hp ha safe clock (by change clock ≤ 2; omega)).1
  · intro i hi
    have he := hc.code (4 + i) (by rw [kernel_length]; rw [PSTRWidthKernel.testLead_length] at hi; omega)
    simpa only [Nat.add_assoc] using he.trans (kernel_test start i hi)
  · have he := hc.code 6 (by rw [kernel_length]; decide)
    have hl : (kernel start)[6]'(by rw [kernel_length]; decide) = .jumpIfZero .flag .address := rfl
    simpa only [PSTRWidthKernel.testLead_length, Nat.add_assoc] using he.trans hl

theorem body_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start heapWords : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (start + 7))) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 5) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) := by
  have safe : PrefixOK rom heapWords (fun _ => True) (bodyLeadAt start) state := by
    apply readOnly_prefixOK
    · simp [bodyLeadAt, ReadOnly]
    · intro count hn
      change count < 4 at hn
      interval_cases count <;> trivial
  apply (PSTRBranchAccess.branch_safe rom whole (bodyLeadAt start) .flag .address heapWords (start + 7) (fun _ => True)
    (by have hh := hc.bound; rw [kernel_length] at hh; rw [PSTRWidthKernel.bodyLead_length]; omega)
    ?_ ?_ (body_straight start) hw hpcfit state hp ha safe clock (by change clock ≤ 4; omega)).1
  · intro i hi
    have he := hc.code (7 + i) (by rw [kernel_length]; rw [PSTRWidthKernel.bodyLead_length] at hi; omega)
    simpa only [Nat.add_assoc] using he.trans (kernel_body start i hi)
  · have he := hc.code 11 (by rw [kernel_length]; decide)
    have hl : (kernel start)[11]'(by rw [kernel_length]; decide) = .jumpIfZero .flag .address := rfl
    simpa only [PSTRWidthKernel.bodyLead_length, Nat.add_assoc] using he.trans hl

theorem loop_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start heapWords : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (q k : Nat) (state : WordState bits)
    (hs : Ready q k start state) (hroom : Fits bits (2 * (q + 1))) (hk : k < CapacityBits.width q)
    (clock : Nat) (hclock : clock < 8) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) := by
  by_cases ht : clock < 3
  · exact test_safe rom whole start heapWords hc hw hpcfit state hs.pc hs.active clock ht
  · have hq : Fits bits (q + 1) := by unfold Fits at hroom ⊢; omega
    have hpow := power_room q k hroom hk.le
    have hlt : 2 ^ k < q + 1 := Nat.pow_lt_of_lt_clog hk
    have hne : q + 1 - 2 ^ k ≠ 0 := by omega
    let tested := executeOps rom (testAt start) state
    have hp : tested.pc = BitVec.ofNat bits (5 * (start + 7)) := by
      rw [test_pc rom q k start state hs hq hpow, ite_eq_right hne]
    have ha : tested.halted = false := by rw [executeOps_halted, hs.active]
    rw [show clock = 3 + (clock - 3) by omega, PSTRWordSegments.run_add,
      test_run rom whole start hc hw hpcfit state hs.pc hs.active]
    exact body_safe rom whole start heapWords hc hw hpcfit tested hp ha (clock - 3) (by omega)

theorem iterations_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start heapWords : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (q k count : Nat) (state : WordState bits)
    (hs : Ready q k start state) (hroom : Fits bits (2 * (q + 1)))
    (hk : k + count ≤ CapacityBits.width q) (clock : Nat) (hclock : clock < 8 * count) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) := by
  induction count generalizing k state clock with
  | zero => omega
  | succ count ih =>
    by_cases hfirst : clock < 8
    · exact loop_safe rom whole start heapWords hc hw hpcfit q k state hs hroom (by omega) clock hfirst
    · have next := (loop_step rom whole start hc hw hpcfit q k state hs hroom (by omega)).1
      rw [show clock = 8 + (clock - 8) by omega, PSTRWordSegments.run_add]
      exact ih (k + 1) (packingRun rom whole 8 state) next (by omega) (clock - 8) (by omega)

theorem width_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start heapWords : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (q : Nat) (state : WordState bits)
    (hf : (state.register .fresh).toNat = q)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (hroom : Fits bits (2 * (q + 1))) (clock : Nat) (hclock : clock < 8 * CapacityBits.width q + 7) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) := by
  by_cases hfirst : clock < 4
  · exact init_safe rom whole start heapWords hc hw hpcfit state hp ha clock hfirst
  · have hinit : Ready q 0 start (packingRun rom whole 4 state) := by
      rw [init_run rom whole start hc hw hpcfit state hp ha]
      exact init_ready rom q start state hf hp ha
    by_cases hloop : clock - 4 < 8 * CapacityBits.width q
    · rw [show clock = 4 + (clock - 4) by omega, PSTRWordSegments.run_add]
      exact iterations_safe rom whole start heapWords hc hw hpcfit q 0 (CapacityBits.width q)
        (packingRun rom whole 4 state) hinit hroom (by omega) (clock - 4) hloop
    · have hlooped := iterations rom whole start hc hw hpcfit q 0 (CapacityBits.width q)
        (packingRun rom whole 4 state) hinit hroom (by omega)
      simp only [Nat.zero_add] at hlooped
      rw [show clock = 4 + (8 * CapacityBits.width q + (clock - (4 + 8 * CapacityBits.width q))) by omega,
        PSTRWordSegments.run_add, PSTRWordSegments.run_add]
      exact test_safe rom whole start heapWords hc hw hpcfit _ hlooped.1.pc hlooped.1.active
        (clock - (4 + 8 * CapacityBits.width q)) (by omega)

theorem width_mask_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start heapWords : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (hbound : start + 13 ≤ whole.length)
    (hmask : whole[start + 12]'(by omega) = maskOp)
    (q : Nat) (state : WordState bits) (hf : (state.register .fresh).toNat = q)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (hroom : Fits bits (2 * (q + 1))) (clock : Nat) (hclock : clock < 8 * CapacityBits.width q + 8) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) := by
  by_cases hbefore : clock < 8 * CapacityBits.width q + 7
  · exact width_safe rom whole start heapWords hc hw hpcfit q state hf hp ha hroom clock hbefore
  · have he : clock = 8 * CapacityBits.width q + 7 := by omega
    subst clock
    have result := actual_width rom whole start hc hw hpcfit q state hf hp ha hroom
    have hindex : start + 12 < whole.length := by omega
    have pcNat : (packingRun rom whole (8 * CapacityBits.width q + 7) state).pc.toNat = 5 * (start + 12) := by
      rw [result.2.1, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt ((Nat.mul_le_mul_left 5 hindex.le).trans_lt hpcfit)
    have hfet : fetch whole (packingRun rom whole (8 * CapacityBits.width q + 7) state) = natFetch whole (5 * (start + 12)) := by
      change physicalFetch bits (packingCode whole) _ = _
      rw [physicalFetch_eq bits _ _ hw, pcNat]
      rfl
    refine ⟨result.1, ?_, maskOp, ?_, trivial⟩
    · rw [pcNat, packingCode_length]
      omega
    · rw [hfet, natFetch_body whole (start + 12) hindex, hmask, decode_encode]

end PaperProofs.Structure.LaminarTree.PSTRWidthAccess


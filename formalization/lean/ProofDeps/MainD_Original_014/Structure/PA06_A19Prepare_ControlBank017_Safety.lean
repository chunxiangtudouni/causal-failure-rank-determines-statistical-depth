module

public import Structure.PA06_A19Prepare_ControlBank017
public import PaperProofs.Structure.RawIncidenceOuterSafety

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Private uncompiled prefix/value/access safety for the fixed runtime
relocation. Real source/target bounds and source word values imply RunSafe;
no RunSafe or all-prefix premise is taken from the original caller. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareControlBank017
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety PA17UniformGenerator035j PA17UniformGenerator035m

theorem initializeControls_numeric (rom : PhysicalROM) (B heapWords : Nat)
    (hone : 1 ≤ B) (state : NatState) (hr : RegistersLE B state) :
    NumericSafe B heapWords rom initializeControls state := by
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 2 at hc
    interval_cases count <;> cases register <;>
      simp [initializeControls, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 2 at hc
    interval_cases count <;> trivial

theorem copy_loop_safe (rom : PhysicalROM) (B heapWords : Nat) (left right : List PackingOp)
    (source target length : Nat) (original : Nat → Nat)
    (hd : source + length ≤ target)
    (hwords : ∀ position < length, original (source + position) ≤ B)
    (hsourceB : source + length ≤ B) (hsourceH : source + length ≤ heapWords)
    (htargetB : target + length ≤ B) (htargetH : target + length ≤ heapWords)
    (hpcB : 5 * (left ++ programAt left.length ++ right).length ≤ B)
    (remaining moved : Nat) (state : NatState) (hsum : moved + remaining = length)
    (hpc : state.pc = 5 * (left.length + 2)) (ha : state.halted = false)
    (hr : RegistersLE B state) (hi : CopyInv source target original moved remaining state) :
    RunSafe B heapWords rom (left ++ programAt left.length ++ right) (9 * remaining + 2) state := by
  induction remaining generalizing moved state with
  | zero =>
    have hp : (left ++ initializeControls).length = left.length + 2 := by simp [initializeControls]
    have hh := PA17UniformGenerator035aa.copyHead_safe rom B heapWords (left.length + 11)
      (left ++ initializeControls) (tail (5 * (left.length + 2)) ++ right)
      (by simp only [List.length_append, programAt_length] at hpcB; omega)
      (by
        have hhead : (head (5 * (left.length + 11))).length = 2 := rfl
        have htail : (tail (5 * (left.length + 2))).length = 7 := rfl
        simp only [List.length_append, hp, hhead, htail]
        omega)
      state (by rw [hp]; exact hpc) ha hr
    simpa only [Nat.mul_zero, Nat.zero_add, programAt, head, tail, List.append_assoc] using hh
  | succ remaining ih =>
    let allCode := left ++ programAt left.length ++ right
    let tested := runOps rom (head (5 * (left.length + 11))) state
    have hshead : RunSafe B heapWords rom allCode 2 state := by
      have hp : (left ++ initializeControls).length = left.length + 2 := by simp [initializeControls]
      have hh := PA17UniformGenerator035aa.copyHead_safe rom B heapWords (left.length + 11)
        (left ++ initializeControls) (tail (5 * (left.length + 2)) ++ right)
        (by simp only [List.length_append, programAt_length] at hpcB; omega)
        (by
          have hhead : (head (5 * (left.length + 11))).length = 2 := rfl
          have htail : (tail (5 * (left.length + 2))).length = 7 := rfl
          simp only [List.length_append, hp, hhead, htail]
          omega)
        state (by rw [hp]; exact hpc) ha hr
      simpa only [allCode, programAt, head, tail, List.append_assoc] using hh
    have hheadRun : natRun rom allCode 2 state = tested := head_run rom left right state hpc ha
    have ht := head_inv rom (5 * (left.length + 11)) source target moved (remaining + 1) original state hi
    have htpc : tested.pc = 5 * (left.length + 4) := by
      rw [PA17UniformGenerator035g.copy_head_pc, hi.2.2.1, ite_eq_right (by omega), hpc]
      omega
    have hta : tested.halted = false := (runOps_halted rom _ state).trans ha
    have htreg : RegistersLE B tested := by
      have hh := (hshead.final _ _ _ _ _).1
      rw [hheadRun] at hh
      exact hh
    have hstail : RunSafe B heapWords rom allCode 7 tested := by
      let lead := left ++ initializeControls ++ head (5 * (left.length + 11))
      have hp : lead.length = left.length + 4 := by
        simp [lead, initializeControls, head, PA17UniformGenerator035g.copyHead]
      have hh := PA17UniformGenerator035aa.copyTail_safe rom B heapWords (left.length + 2) lead right
        (by simp only [List.length_append, programAt_length] at hpcB; omega)
        (by simp only [List.length_append, hp]; change left.length + 2 ≤ left.length + 4 + 7 + right.length; omega)
        tested (by rw [hp]; exact htpc) hta htreg ht.2.2.2.2.1
        (by
          rw [ht.2.1, ht.2.2.2.2.2, relocatedHeap_source original source target moved length hd (by omega)]
          exact hwords moved (by omega))
        (by rw [ht.2.1]; omega) (by rw [ht.1]; omega)
        (by rw [ht.2.1, ht.2.2.2.1]; omega) (by rw [ht.1, ht.2.2.2.1]; omega)
      simpa only [allCode, programAt, head, tail, lead, List.append_assoc] using hh
    let movedState := runOps rom (tail (5 * (left.length + 2))) tested
    have htailRun : natRun rom allCode 7 tested = movedState := tail_run rom left right tested htpc hta
    have hm : CopyInv source target original (moved + 1) remaining movedState := by
      simpa only [Nat.add_sub_cancel] using
        tail_inv rom (5 * (left.length + 2)) source target moved (remaining + 1) length original tested ht hd (by omega)
    have hmpc : movedState.pc = 5 * (left.length + 2) :=
      PA17UniformGenerator035g.copy_tail_pc rom _ tested ht.2.2.2.2.1
    have hma : movedState.halted = false := (runOps_halted rom _ tested).trans hta
    have hmreg : RegistersLE B movedState := by
      have hh := (hstail.final _ _ _ _ _).1
      rw [htailRun] at hh
      exact hh
    have hremaining := ih (moved + 1) movedState (by omega) hmpc hma hmreg hm
    have hcycleRun : natRun rom allCode (2 + 7) state = movedState := by
      rw [natRun_add, hheadRun, htailRun]
    have hfirst := RunSafe.add _ _ _ allCode 2 7 state hshead (by rw [hheadRun]; exact hstail)
    have hall := RunSafe.add _ _ _ allCode (2 + 7) (9 * remaining + 2) state hfirst
      (by rw [hcycleRun]; exact hremaining)
    have htime : 9 * (remaining + 1) + 2 = (2 + 7) + (9 * remaining + 2) := by omega
    rw [htime]
    exact hall

theorem copy_safe (rom : PhysicalROM) (B heapWords : Nat) (left right : List PackingOp)
    (source target length : Nat) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (hone : 1 ≤ B) (hs : state.register .address = source) (ht : state.register .index = target)
    (hn : state.register .total = length) (hd : source + length ≤ target)
    (hsourceB : source + length ≤ B) (hsourceH : source + length ≤ heapWords)
    (htargetB : target + length ≤ B) (htargetH : target + length ≤ heapWords)
    (hwords : ∀ position < length, state.heap (source + position) ≤ B)
    (hpcB : 5 * (left ++ programAt left.length ++ right).length ≤ B) :
    RunSafe B heapWords rom (left ++ programAt left.length ++ right) (9 * length + 4) state := by
  let allCode := left ++ programAt left.length ++ right
  let prepared := runOps rom initializeControls state
  have hinit := initializeControls_numeric rom B heapWords hone state hr
  have hinitSafe : RunSafe B heapWords rom allCode 2 state := by
    have hh := straight_segment_safe rom B heapWords left initializeControls
      (head (5 * (left.length + 11)) ++ tail (5 * (left.length + 2)) ++ right)
      initializeControls_noJump state hpc ha hinit
    simpa only [allCode, programAt, List.append_assoc, initializeControls_length] using hh
  have hinitRun : natRun rom allCode 2 state = prepared := init_run rom left right state hpc ha
  have hp : prepared.pc = 5 * (left.length + 2) := by
    rw [runOps_pc rom _ state initializeControls_noJump, hpc]
    rfl
  have hreg : RegistersLE B prepared := by
    have hh := (hinitSafe.final _ _ _ _ _).1
    rw [hinitRun] at hh
    exact hh
  have hlater := copy_loop_safe rom B heapWords left right source target length state.heap
    hd hwords hsourceB hsourceH htargetB htargetH hpcB length 0 prepared (by omega) hp
    ((runOps_halted rom _ state).trans ha) hreg (init_inv rom source target length state hs ht hn)
  have htime : 9 * length + 4 = 2 + (9 * length + 2) := by omega
  rw [htime]
  exact RunSafe.add _ _ _ _ _ _ state hinitSafe (by rw [hinitRun]; exact hlater)

/-- The exact numeric/access proof gives actual Word execution; the real
whole code has a WordsFit obligation, as in the existing ISA refinement. -/
theorem copy_word {bits : Nat} (rom : PhysicalROM) (B heapWords : Nat) (left right : List PackingOp)
    (source target length : Nat) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (hone : 1 ≤ B) (hs : state.register .address = source) (ht : state.register .index = target)
    (hn : state.register .total = length) (hd : source + length ≤ target)
    (hsourceB : source + length ≤ B) (hsourceH : source + length ≤ heapWords)
    (htargetB : target + length ≤ B) (htargetH : target + length ≤ heapWords)
    (hwords : ∀ position < length, state.heap (source + position) ≤ B)
    (hpcB : 5 * (left ++ programAt left.length ++ right).length ≤ B)
    (hB : Fits bits B) (hcode : WordsFit bits (packingCode (left ++ programAt left.length ++ right))) :
    let fresh := packingRun rom (left ++ programAt left.length ++ right) (9 * length + 4) (state.toWord bits)
    fresh.halted = false ∧ fresh.pc.toNat = 5 * (left.length + 11) ∧
      ∀ index < length, (fresh.heap (BitVec.ofNat bits (target + index))).toNat = state.heap (source + index) := by
  have hsafe := copy_safe rom B heapWords left right source target length state hpc ha hr hone
    hs ht hn hd hsourceB hsourceH htargetB htargetH hwords hpcB
  have hprefix (count : Nat) (hc : count < 9 * length + 4) :
      RegistersFit bits (natRun rom (left ++ programAt left.length ++ right) count state) ∧
        Fits bits (natRun rom (left ++ programAt left.length ++ right) count state).pc := by
    obtain ⟨hreg, _ha, index, hi, hp⟩ := hsafe.1 count hc.le
    constructor
    · intro reg
      exact (hreg reg).trans_lt hB
    · rw [hp]
      exact ((Nat.mul_le_mul_left 5 hi).trans hpcB).trans_lt hB
  rw [natRun_toWord _ _ _ _ hcode hprefix]
  have hout := copy_run rom left right source target length state hpc ha hs ht hn hd
  refine ⟨hout.2.2, ?_, ?_⟩
  · change (BitVec.ofNat bits (natRun rom (left ++ programAt left.length ++ right)
      (9 * length + 4) state).pc).toNat = _
    rw [hout.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have hp : 5 * (left.length + 11) ≤ B := by
        simp only [List.length_append, programAt_length] at hpcB
        omega
      exact hp.trans_lt hB)]
  · intro index hi
    have hv := (copy_values_frame rom left right source target length state hpc ha hs ht hn hd).1 index hi
    change (BitVec.ofNat bits ((natRun rom (left ++ programAt left.length ++ right)
      (9 * length + 4) state).heap (BitVec.ofNat bits (target + index)).toNat)).toNat = _
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show target + index < 2 ^ bits from
      (by omega : target + index ≤ B).trans_lt hB), hv,
      Nat.mod_eq_of_lt ((hwords index hi).trans_lt hB)]

/-- Internal finite-word transport of an independently proved actual
RunSafe result, used below with copy_safe rather than an original premise. -/
theorem safe_word_prefix {bits : Nat} (rom : PhysicalROM) (B heapWords : Nat)
    (code : List PackingOp) (steps : Nat) (state : NatState)
    (hsafe : RunSafe B heapWords rom code steps state) (hB : Fits bits B)
    (hpcB : 5 * code.length ≤ B) (hcode : WordsFit bits (packingCode code))
    (count : Nat) (hc : count < steps) :
    let fresh := packingRun rom code count (state.toWord bits)
    ∃ index, ∃ hi : index < code.length, fresh.pc.toNat = 5 * index ∧
      PackingOp.decode (fetch code fresh) = some code[index] ∧
      packingAccessFits rom heapWords fresh code[index] := by
  have hfit (k : Nat) (hk : k < count + 1) :
      RegistersFit bits (natRun rom code k state) ∧ Fits bits (natRun rom code k state).pc := by
    obtain ⟨hr, _ha, index, hi, hp⟩ := hsafe.1 k (by omega)
    constructor
    · intro reg
      exact (hr reg).trans_lt hB
    · rw [hp]
      exact ((Nat.mul_le_mul_left 5 hi).trans hpcB).trans_lt hB
  rw [natRun_toWord _ _ _ count hcode (fun k hk => hfit k (by omega))]
  obtain ⟨index, hi, hp, access⟩ := hsafe.2 count hc
  have hpcFit := (hfit count (by omega)).2
  have hpcNat : (BitVec.ofNat bits (natRun rom code count state).pc).toNat = 5 * index := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpcFit, hp]
  refine ⟨index, hi, hpcNat, ?_, ?_⟩
  · change PackingOp.decode (physicalFetch bits (packingCode code)
      (BitVec.ofNat bits (natRun rom code count state).pc).toNat) = _
    rw [hpcNat, physicalFetch_eq _ _ _ hcode]
    change PackingOp.decode (natFetch code (5 * index)) = _
    rw [natFetch_body code index hi, decode_encode]
  · exact physical_access_of_nat rom heapWords _ _ (hfit count (by omega)).1 access

/-- All genuinely fetched Word prefixes of this copy, with real accesses.
All safety is derived from source data, numeric room and the fixed code. -/
theorem copy_word_prefix {bits : Nat} (rom : PhysicalROM) (B heapWords : Nat) (left right : List PackingOp)
    (source target length : Nat) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (hone : 1 ≤ B) (hs : state.register .address = source) (ht : state.register .index = target)
    (hn : state.register .total = length) (hd : source + length ≤ target)
    (hsourceB : source + length ≤ B) (hsourceH : source + length ≤ heapWords)
    (htargetB : target + length ≤ B) (htargetH : target + length ≤ heapWords)
    (hwords : ∀ position < length, state.heap (source + position) ≤ B)
    (hpcB : 5 * (left ++ programAt left.length ++ right).length ≤ B)
    (hB : Fits bits B) (hcode : WordsFit bits (packingCode (left ++ programAt left.length ++ right)))
    (count : Nat) (hc : count < 9 * length + 4) :
    let code := left ++ programAt left.length ++ right
    let fresh := packingRun rom code count (state.toWord bits)
    ∃ index, ∃ hi : index < code.length, fresh.pc.toNat = 5 * index ∧
      PackingOp.decode (fetch code fresh) = some code[index] ∧
      packingAccessFits rom heapWords fresh code[index] := by
  exact safe_word_prefix rom B heapWords _ _ state
    (copy_safe rom B heapWords left right source target length state hpc ha hr hone hs ht hn hd
      hsourceB hsourceH htargetB htargetH hwords hpcB) hB hpcB hcode count hc

end PaperProofs.Structure.LaminarTree.PA06A19PrepareControlBank017

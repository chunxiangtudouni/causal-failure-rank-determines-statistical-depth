module

public import Structure.PA06_A19Prepare_InitialUsed037_Run
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate whole-loop strict-prefix composition. The existing real Word
head5/tail9 and body88 are used in the original containing code, after the
actual setup33. Loop length and both source controls are actual setup
outputs. BodyExits and access safety are proved from Current, not supplied
by the original caller. This source remains a candidate until strict,
public-build and dependency axiom checks have actually passed. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PSTRBuildLower
open PA17PackedTranslator034 (PackedAccessSafe)

variable {bits : Nat}

/- Keep the fixed88-op PC calculation on an abstract state.  Using this
at the reached loop-head state avoids reducing its entire concrete body. -/
private theorem body_pc_of_pc (rom : PhysicalROM) (state : WordState bits)
    (start : Nat) (hpc : state.pc = BitVec.ofNat bits (5 * start)) :
    (executeOps rom body state).pc = BitVec.ofNat bits (5 * (start + body.length)) := by
  rw [executeOps_pc rom body state body_straight, hpc, BitVec.ofNat_add_ofNat]
  congr 1

def Fetched (H : Nat) (rom : PhysicalROM) (code : List PackingOp) (state : WordState bits) : Prop :=
  state.halted = false ∧ state.pc.toNat + 4 < (packingCode code).length ∧
    ∃ op, PackingOp.decode (RawTreePreprocessingClaims.fetch code state) = some op ∧ packingAccessFits rom H state op

private theorem fetched_prefix (rom : PhysicalROM) (H : Nat) (code block : List PackingOp) (start : Nat)
    (hbound : start + block.length ≤ code.length)
    (hsegment : ∀ i (hi : i < block.length), code[start + i]'(by omega) = block[i])
    (hwords : WordsFit bits (packingCode code)) (hpcFit : Fits bits (5 * code.length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (count : Nat) (hc : count < block.length) (hstraight : StraightProgram (block.take count))
    (haccess : packingAccessFits rom H (executeOps rom (block.take count) state) block[count]) :
    Fetched H rom code (packingRun rom code count state) := by
  have hlen : (block.take count).length = count := List.length_take_of_le hc.le
  have hrun : packingRun rom code count state = executeOps rom (block.take count) state := by
    conv_lhs => rw [← hlen]
    apply PSTRWordSegments.straight_segment rom code (block.take count) start (by omega) ?_
      hstraight hwords hpcFit state hpc ha
    intro i hi
    have hib : i < block.length := by rw [hlen] at hi; omega
    simpa only [List.getElem_take] using hsegment i hib
  have hp : (executeOps rom (block.take count) state).pc.toNat = 5 * (start + count) := by
    rw [executeOps_pc rom _ state hstraight, hpc, hlen, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    rw [show 5 * start + 5 * count = 5 * (start + count) by omega]
    exact Nat.mod_eq_of_lt ((by omega : 5 * (start + count) ≤ 5 * code.length).trans_lt hpcFit)
  dsimp only [Fetched]
  simp only [hrun]
  refine ⟨(executeOps_halted rom _ state).trans ha, ?_, block[count], ?_, haccess⟩
  · rw [hp, packingCode_length]
    omega
  · change PackingOp.decode (physicalFetch bits (packingCode code)
      (executeOps rom (block.take count) state).pc.toNat) = _
    rw [hp, physicalFetch_eq _ _ _ hwords]
    change PackingOp.decode (natFetch code (5 * (start + count))) = _
    rw [natFetch_body code (start + count) (by omega), decode_encode, hsegment count hc]

theorem head_accessSafe (rom : PhysicalROM) (H exit : Nat) (state : WordState bits)
    (hfit : Fits bits ((state.register .address).toNat + counterSlot))
    (hroom : (state.register .address).toNat + counterSlot < H) :
    PackedAccessSafe H rom (relativeLoopHead counterSlot exit) state := by
  intro count hc
  change count < 5 at hc
  interval_cases count <;> try exact True.intro
  change (state.register .address + BitVec.ofNat bits counterSlot).toNat < H
  rw [PA06A19PrepareBankPacked021.bankWord_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
  exact hroom

theorem tail_accessSafe (rom : PhysicalROM) (H entry : Nat) (state : WordState bits)
    (hfit : Fits bits ((state.register .address).toNat + counterSlot))
    (hroom : (state.register .address).toNat + counterSlot < H) :
    PackedAccessSafe H rom (relativeLoopTail counterSlot entry) state := by
  intro count hc
  change count < 9 at hc
  interval_cases count <;> try exact True.intro
  all_goals
    change (state.register .address + BitVec.ofNat bits counterSlot).toNat < H
    rw [PA06A19PrepareBankPacked021.bankWord_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
    exact hroom

theorem head_prefix_fetched (rom : PhysicalROM) (H : Nat) (left right : List PackingOp)
    (hwords : WordsFit bits (packingCode (left ++ relativeLoopBlock counterSlot left.length body ++ right)))
    (hpcFit : Fits bits (5 * (left ++ relativeLoopBlock counterSlot left.length body ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hfit : Fits bits ((state.register .address).toNat + counterSlot))
    (hroom : (state.register .address).toNat + counterSlot < H)
    (count : Nat) (hc : count < 5) :
    Fetched H rom (left ++ relativeLoopBlock counterSlot left.length body ++ right)
      (packingRun rom (left ++ relativeLoopBlock counterSlot left.length body ++ right) count state) := by
  let head := relativeLoopHead counterSlot (5 * (left.length + body.length + 14))
  have hstraight : StraightProgram (head.take count) := by
    interval_cases count <;> simp [head, relativeLoopHead, relativeRead, StraightProgram, StraightOp]
  apply fetched_prefix rom H _ head left.length
    (by simp only [List.length_append, relativeLoopBlock_length, head, relativeLoopHead_length]; omega) ?_
    hwords hpcFit state hpc ha count (by change count < 5; exact hc) hstraight
    (head_accessSafe rom H _ state hfit hroom count (by change count < 5; exact hc))
  intro i hi
  have hh := PA17UniformGenerator035a.segment_index left head
    (body ++ relativeLoopTail counterSlot (5 * left.length) ++ right) i hi
  simpa only [relativeLoopBlock, head, List.append_assoc] using hh

theorem tail_prefix_fetched (rom : PhysicalROM) (H : Nat) (left right : List PackingOp)
    (hwords : WordsFit bits (packingCode (left ++ relativeLoopBlock counterSlot left.length body ++ right)))
    (hpcFit : Fits bits (5 * (left ++ relativeLoopBlock counterSlot left.length body ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * (left.length + 5 + body.length))) (ha : state.halted = false)
    (hfit : Fits bits ((state.register .address).toNat + counterSlot))
    (hroom : (state.register .address).toNat + counterSlot < H)
    (count : Nat) (hc : count < 9) :
    Fetched H rom (left ++ relativeLoopBlock counterSlot left.length body ++ right)
      (packingRun rom (left ++ relativeLoopBlock counterSlot left.length body ++ right) count state) := by
  let tail := relativeLoopTail counterSlot (5 * left.length)
  let lead := left ++ relativeLoopHead counterSlot (5 * (left.length + body.length + 14)) ++ body
  have hlead : lead.length = left.length + 5 + body.length := by
    simp only [lead, List.length_append, relativeLoopHead_length]
  have hstraight : StraightProgram (tail.take count) := by
    interval_cases count <;> simp [tail, relativeLoopTail, relativeRead, StraightProgram, StraightOp]
  apply fetched_prefix rom H _ tail (left.length + 5 + body.length)
    (by simp only [List.length_append, relativeLoopBlock_length, tail, relativeLoopTail_length]; omega) ?_
    hwords hpcFit state hpc ha count (by change count < 9; exact hc) hstraight
    (tail_accessSafe rom H _ state hfit hroom count (by change count < 9; exact hc))
  intro i hi
  have hh := PA17UniformGenerator035a.segment_index lead tail right i hi
  have hh' : (lead ++ tail ++ right)[left.length + 5 + body.length + i]'(by
      simp only [List.length_append, hlead]
      omega) = tail[i] := by
    simpa only [hlead] using hh
  simpa only [relativeLoopBlock, lead, tail, List.append_assoc] using hh'

theorem valid_counter_room (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original : WordState (indexWidth 32 full.length q)) (hd : BankData q full original)
    (state : WordState (indexWidth 32 full.length q)) (hv : valid q full used original state) :
    Fits (indexWidth 32 full.length q) ((state.register .address).toNat + counterSlot) ∧
      (state.register .address).toNat + counterSlot < PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full) := by
  obtain ⟨j, hj, h⟩ := hv
  simp only [h.base, hd.base]
  have hr := actual_control_room q full hq counterSlot (by decide)
  exact ⟨hr.2, hr.1⟩

theorem cycle_prefix_fetched (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original : WordState (indexWidth 32 full.length q)) (hd : BankData q full original)
    (left right : List PackingOp)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ relativeLoopBlock counterSlot left.length body ++ right)))
    (hpcFit : Fits (indexWidth 32 full.length q) (5 * (left ++ relativeLoopBlock counterSlot left.length body ++ right).length))
    (state : WordState (indexWidth 32 full.length q)) (hv : valid q full used original state)
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hn : (state.heap (state.register .address + BitVec.ofNat _ counterSlot)).toNat ≠ 0)
    (count : Nat) (hc : count < 102) :
    Fetched (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)) (controllerInput q full used)
      (left ++ relativeLoopBlock counterSlot left.length body ++ right)
      (packingRun (controllerInput q full used) (left ++ relativeLoopBlock counterSlot left.length body ++ right) count state) := by
  let rom := controllerInput q full used
  let bits := indexWidth 32 full.length q
  let C := capacityWords 8192 full.length q (treeSize q full)
  let H := PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)
  let code := left ++ relativeLoopBlock counterSlot left.length body ++ right
  obtain ⟨j, hj, h⟩ := hv
  have hjlt : j < q := by have hh := current_remaining q full used original j state h; omega
  have b := current_bounds q full used hq original hd j hjlt state h
  by_cases hhead : count < 5
  · exact head_prefix_fetched rom H left right hwords hpcFit state hpc ha b.fit_counter b.room_counter count hhead
  · let tested := executeOps rom (relativeLoopHead counterSlot (5 * (left.length + body.length + 14))) state
    let bodyLead := left ++ relativeLoopHead counterSlot (5 * (left.length + body.length + 14))
    let bodyRight := relativeLoopTail counterSlot (5 * left.length) ++ right
    have ht := current_head q full used original j state h rom (5 * (left.length + body.length + 14))
    have bt := current_bounds q full used hq original hd j hjlt tested ht
    have hlead : bodyLead.length = left.length + 5 := by simp only [bodyLead, List.length_append, relativeLoopHead_length]
    have hbodyCode : code = bodyLead ++ body ++ bodyRight := by
      simp only [code, relativeLoopBlock, bodyLead, bodyRight, List.append_assoc]
    have hpTest : tested.pc = BitVec.ofNat bits (5 * (left.length + 5)) := by
      have he : 5 * left.length + 25 = 5 * (left.length + 5) := by omega
      simpa only [tested, relativeLoopHead_word_pc, ite_eq_right hn, hpc, BitVec.ofNat_add_ofNat]
        using congrArg (BitVec.ofNat bits) he
    have haTest : tested.halted = false := (executeOps_halted rom _ state).trans ha
    have hheadRun : packingRun rom code 5 state = tested :=
      PSTRBuildLower.WordLoop.head_run rom left body right counterSlot hwords hpcFit state hpc ha
    by_cases hbodyCount : count < 93
    · have hk : count - 5 < 88 := by omega
      have hs := body_prefix_actual q C H rom bodyLead bodyRight
        (by rw [← hbodyCode]; exact hwords) (by rw [← hbodyCode]; exact hpcFit) tested
        (by rw [hlead]; exact hpTest) haTest ht.header hq
        (by have hb := PA17GeneratorStatic048.bits_ge_64 full.length q hq; omega)
        (PA17PackingBounds043.width_le_bits full.length q) bt.pointer_lt bt.product bt.physical bt.physical_room
        bt.after_lookahead bt.fit_pointer bt.room_pointer bt.fit_cursor bt.room_cursor
        (current_rom_room q full used original j hjlt tested ht) (count - 5) hk
      have hf : Fetched H rom code (packingRun rom code (count - 5) tested) := by
        rw [hbodyCode]
        exact ⟨hs.1, hs.2.2.1, body[count - 5]'(by rw [body_length]; exact hk), hs.2.2.2.1, hs.2.2.2.2⟩
      rw [show count = 5 + (count - 5) by omega, PSTRWordSegments.run_add, hheadRun]
      exact hf
    · let done := executeOps rom body tested
      have hbodyRun : packingRun rom code 88 tested = done := by
        rw [hbodyCode]
        exact body_run rom bodyLead bodyRight (by rw [← hbodyCode]; exact hwords)
          (by rw [← hbodyCode]; exact hpcFit) tested (by rw [hlead]; exact hpTest) haTest
      have hpDone : done.pc = BitVec.ofNat bits (5 * (left.length + 5 + body.length)) := by
        exact body_pc_of_pc rom tested (left.length + 5) hpTest
      have haDone : done.halted = false := (executeOps_halted rom body tested).trans haTest
      have hDoneBase : done.register .address = state.register .address :=
        (body_address rom tested).trans (relativeLoopHead_word_base rom counterSlot _ state)
      have hk : count - 93 < 9 := by omega
      have hf := tail_prefix_fetched rom H left right hwords hpcFit done hpDone haDone
        (by rw [hDoneBase]; exact b.fit_counter) (by rw [hDoneBase]; exact b.room_counter) (count - 93) hk
      rw [show count = (5 + 88) + (count - 93) by omega,
        PSTRWordSegments.run_add, PSTRWordSegments.run_add, hheadRun, hbodyRun]
      exact hf

theorem loop_prefix_fetched (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original : WordState (indexWidth 32 full.length q)) (hd : BankData q full original)
    (left right : List PackingOp)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ relativeLoopBlock counterSlot left.length body ++ right)))
    (hpcFit : Fits (indexWidth 32 full.length q) (5 * (left ++ relativeLoopBlock counterSlot left.length body ++ right).length))
    (remaining : Nat) (state : WordState (indexWidth 32 full.length q)) (hv : valid q full used original state)
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcount : (state.heap (state.register .address + BitVec.ofNat _ counterSlot)).toNat = remaining)
    (count : Nat) (hc : count < 102 * remaining + 5) :
    Fetched (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)) (controllerInput q full used)
      (left ++ relativeLoopBlock counterSlot left.length body ++ right)
      (packingRun (controllerInput q full used) (left ++ relativeLoopBlock counterSlot left.length body ++ right) count state) := by
  let rom := controllerInput q full used
  let H := PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)
  let code := left ++ relativeLoopBlock counterSlot left.length body ++ right
  have hb := concrete_body_exits q full used hq original hd left right hwords hpcFit
  induction remaining generalizing state count with
  | zero =>
    have hr := valid_counter_room q full used hq original hd state hv
    exact head_prefix_fetched rom H left right hwords hpcFit state hpc ha hr.1 hr.2 count (by omega)
  | succ remaining ih =>
    have hn : (state.heap (state.register .address + BitVec.ofNat _ counterSlot)).toNat ≠ 0 := by omega
    by_cases hfirst : count < 102
    · exact cycle_prefix_fetched q full used hq original hd left right hwords hpcFit state hv hpc ha hn count hfirst
    · let next := PSTRBuildLower.WordLoop.cycleResult rom left body right counterSlot (fun _ => 88) state
      have ht := PSTRBuildLower.WordLoop.cycle_control (valid q full used original) rom left body right counterSlot (fun _ => 88)
        hb state hv hpc ha hn
      have hrun : packingRun rom code 102 state = next := by
        have hh := PSTRBuildLower.WordLoop.cycle_run (valid q full used original) rom left body right counterSlot (fun _ => 88)
          hb hwords hpcFit state hv hpc ha hn
        simpa only [PSTRBuildLower.WordLoop.cycleSteps] using hh
      have hf := ih next ht.2.2.2.2 ht.1 ht.2.1 (by rw [ht.2.2.2.1, hcount]; omega)
        (count - 102) (by omega)
      rw [show count = 102 + (count - 102) by omega, PSTRWordSegments.run_add, hrun]
      exact hf

theorem actual_initialUsed_prefix (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false) (hd : BankData q full before)
    (hh : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hbound : CapacityPrefixBounded q (capacityWords 8192 full.length q (treeSize q full))
      (unpackHeap q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) (dataHeap before.heap)))
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ programAt left.length ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ programAt left.length ++ right).length))
    (count : Nat) (hc : count < clock q) :
    Fetched (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)) (controllerInput q full used)
      (left ++ programAt left.length ++ right)
      (packingRun (controllerInput q full used) (left ++ programAt left.length ++ right) count before) := by
  let rom := controllerInput q full used
  let bits := indexWidth 32 full.length q
  let allCode := left ++ programAt left.length ++ right
  let lead := left ++ setup
  let prepared := packingRun rom allCode 33 before
  have hlead : lead.length = left.length + 33 := by simp only [lead, List.length_append, setup_length]
  have hcodeLoop : allCode = lead ++ relativeLoopBlock counterSlot lead.length body ++ right := by
    simp only [allCode, programAt, lead, hlead, List.append_assoc]
  have hcodeSetup : allCode = left ++ setup ++ (relativeLoopBlock counterSlot (left.length + 33) body ++ right) := by
    simp only [allCode, programAt, List.append_assoc]
  by_cases hs : count < 33
  · have hf := setup_prefix_access q full used hq left (relativeLoopBlock counterSlot (left.length + 33) body ++ right)
      before hpc ha hd (by rw [← hcodeSetup]; exact hcode) (by rw [← hcodeSetup]; exact hpcCode) count hs
    change Fetched _ rom allCode (packingRun rom allCode count before)
    rw [hcodeSetup]
    exact hf
  · have hcur := setup_current q full used hq left (relativeLoopBlock counterSlot (left.length + 33) body ++ right)
      before hpc ha hd hh hbound (by rw [← hcodeSetup]; exact hcode) (by rw [← hcodeSetup]; exact hpcCode)
    have hcurrent : Current q full used before 0 prepared := by simpa only [← hcodeSetup] using hcur
    have hsControl := setup_word_control q full used hq left
      (relativeLoopBlock counterSlot (left.length + 33) body ++ right) before hpc ha hd
      (by rw [← hcodeSetup]; exact hcode) (by rw [← hcodeSetup]; exact hpcCode)
    have hp : prepared.pc.toNat = 5 * lead.length := by
      rw [hlead]
      simpa only [← hcodeSetup] using hsControl.2.1
    have hpFit : Fits bits (5 * lead.length) := (by
      simp only [hlead, allCode, List.length_append, programAt_length]
      omega : 5 * lead.length ≤ 5 * allCode.length).trans_lt hpcCode
    have hpWord : prepared.pc = BitVec.ofNat bits (5 * lead.length) := by
      apply BitVec.eq_of_toNat_eq
      rw [hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpFit]
    have haPrepared : prepared.halted = false := by simpa only [← hcodeSetup] using hsControl.1
    have hcPrepared : (prepared.heap (prepared.register .address + BitVec.ofNat bits counterSlot)).toNat = q :=
      current_remaining q full used before 0 prepared hcurrent
    have hf := loop_prefix_fetched q full used hq before hd lead right
      (by rw [← hcodeLoop]; exact hcode) (by rw [← hcodeLoop]; exact hpcCode) q prepared
      ⟨0, Nat.zero_le q, hcurrent⟩ hpWord haPrepared hcPrepared (count - 33)
      (by unfold clock at hc; omega)
    change Fetched _ rom allCode (packingRun rom allCode count before)
    rw [show count = 33 + (count - 33) by omega, PSTRWordSegments.run_add]
    rw [← hcodeLoop] at hf
    exact hf

/-- One consumer interface for the actual end state, every strict fetched
prefix and the charged dynamic trace. Its internal BankData/Header/bounded
inputs are exactly those of actual_initialUsed; the surrounding prepare
assembly must discharge them using its reached state. No caller BodyExits,
source cursor/count, arbitrary full-run access premise or PC reset is used. -/
theorem actual_initialUsed_run_prefix (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false) (hd : BankData q full before)
    (hh : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hbound : CapacityPrefixBounded q (capacityWords 8192 full.length q (treeSize q full))
      (unpackHeap q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) (dataHeap before.heap)))
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ programAt left.length ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ programAt left.length ++ right).length)) :
    let code := left ++ programAt left.length ++ right
    let after := packingRun (controllerInput q full used) code (clock q) before
    (Current q full used before q after ∧ after.halted = false ∧ after.pc.toNat = 5 * (left.length + 135) ∧
      after.register .address = before.register .address) ∧
    (∀ count < clock q, Fetched (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) code (packingRun (controllerInput q full used) code count before)) ∧
    (packingDynamicTrace (controllerInput q full used) code (clock q) before).length ≤ 1224 * q + 456 := by
  exact ⟨actual_initialUsed q full used hq left right before hpc ha hd hh hbound hcode hpcCode,
    fun count hc => actual_initialUsed_prefix q full used hq left right before hpc ha hd hh hbound hcode hpcCode count hc,
    actual_initialUsed_trace q full used left right before⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037

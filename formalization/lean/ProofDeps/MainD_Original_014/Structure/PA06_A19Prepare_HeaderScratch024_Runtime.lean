module

public import Structure.PA06_A19Prepare_HeaderScratch024
public import Structure.PA06_A19Prepare_RuntimeHeader019
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Uncompiled candidate: actual save -> relocated 019 -> restore. The
original raw ROM is unchanged. The two original halving loops execute at
their true PC after save20. The four temporary headers survive restore,
and every actual cache word at address>=16 is restored/preserved. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareHeaderScratch024

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  CompactControllerClaims RawIncidenceScanSafety
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035h
  PA17UniformGenerator035i PA17UniformGenerator035j PA17UniformGenerator035l
  PA17UniformGenerator035m PA17UniformGenerator035p PA17UniformGenerator035z

def program (start : Nat) : List PackingOp :=
  save ++ PA06A19PrepareRuntimeHeader019.program (start + 20) ++ restore

def clock (N q : Nat) : Nat := PA06A19PrepareRuntimeHeader019.clock N q + 40

def NatHeader (q N : Nat) (heap : Nat → Nat) : Prop :=
  heap 0 = CapacityBits.width q ∧ heap 1 = 2 ^ CapacityBits.width q - 1 ∧
    heap 2 = 2 ^ indexWidth 32 N q - 1 ∧ heap 3 = indexWidth 32 N q

theorem program_length (start : Nat) : (program start).length = 104 := by
  simp only [program, List.length_append, save_length, restore_length,
    PA06A19PrepareRuntimeHeader019.program_length]

theorem code_length : (packingCode (program 0)).length = 525 := by
  rw [packingCode_length, program_length]

theorem extra_steps (N q : Nat) : clock N q = PA06A19PrepareRuntimeHeader019.clock N q + 40 := rfl

theorem extra_events : (save.flatMap PackingOp.events).length + (restore.flatMap PackingOp.events).length = 380 := by
  rw [save_events_length, restore_events_length]

theorem save_noJump : ∀ op ∈ save, NoJump op := by simp [save, copyWord, NoJump]
theorem restore_noJump : ∀ op ∈ restore, NoJump op := by simp [restore, copyWord, NoJump]

theorem copyWord_nat_heap (source target : Nat) (rom : PhysicalROM) (state : NatState) :
    (runOps rom (copyWord source target) state).heap = Function.update state.heap target (state.heap source) := rfl

theorem save_nat_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom save state).heap = Function.update (Function.update (Function.update (Function.update (Function.update (state.heap) 9 (state.heap 64)) 10 (state.heap 65)) 11 (state.heap 66)) 12 (state.heap 67)) 13 (state.heap 68) := by
  simp only [save, runOps_append, copyWord_nat_heap]
  simp +decide only [Function.update_apply, ↓reduceIte]

theorem restore_nat_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom restore state).heap = Function.update (Function.update (Function.update (Function.update (Function.update (state.heap) 64 (state.heap 9)) 65 (state.heap 10)) 66 (state.heap 11)) 67 (state.heap 12)) 68 (state.heap 13) := by
  simp only [restore, runOps_append, copyWord_nat_heap]
  simp +decide only [Function.update_apply, ↓reduceIte]

theorem save_nat_value (rom : PhysicalROM) (state : NatState) (index : Nat) (hi : index < 5) :
    (runOps rom save state).heap (9 + index) = state.heap (64 + index) := by
  rw [save_nat_heap]
  interval_cases index <;> simp

theorem restore_nat_value (rom : PhysicalROM) (state : NatState) (index : Nat) (hi : index < 5) :
    (runOps rom restore state).heap (64 + index) = state.heap (9 + index) := by
  rw [restore_nat_heap]
  interval_cases index <;> simp

theorem save_nat_frame (rom : PhysicalROM) (state : NatState) (address : Nat) (ha : 16 ≤ address) :
    (runOps rom save state).heap address = state.heap address := by
  rw [save_nat_heap]
  simp only [Function.update_of_ne (show address ≠ 9 by omega),
    Function.update_of_ne (show address ≠ 10 by omega), Function.update_of_ne (show address ≠ 11 by omega),
    Function.update_of_ne (show address ≠ 12 by omega), Function.update_of_ne (show address ≠ 13 by omega)]

theorem restore_nat_frame (rom : PhysicalROM) (state : NatState) (address : Nat)
    (ha : address < 64 ∨ 69 ≤ address) :
    (runOps rom restore state).heap address = state.heap address := by
  rw [restore_nat_heap]
  simp only [Function.update_of_ne (show address ≠ 64 by omega),
    Function.update_of_ne (show address ≠ 65 by omega), Function.update_of_ne (show address ≠ 66 by omega),
    Function.update_of_ne (show address ≠ 67 by omega), Function.update_of_ne (show address ≠ 68 by omega)]

/-- This strengthens 019's published high frame at precisely the needed
saved cells. It comes from actual prelude_run and postamble_frame; no new
caller metadata premise or free ROM change is involved. -/
theorem header_frame (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (address : Nat) (haddress : 4 ≤ address) (hout : address < 64 ∨ 69 ≤ address) :
    (natRun (controllerInput q full used)
      (left ++ PA06A19PrepareRuntimeHeader019.program left.length ++ right)
      (PA06A19PrepareRuntimeHeader019.clock full.length q) state).heap address = state.heap address := by
  let rom := controllerInput q full used
  let allCode := left ++ PA06A19PrepareRuntimeHeader019.program left.length ++ right
  let lead := left ++ dimensionPrelude left.length
  let pre := natRun rom allCode (dimensionClock full.length q) state
  have hpre := PA06A19PrepareRuntimeHeader019.prelude_run q full used left
    (PA06A19PrepareRuntimeHeader019.postamble ++ right) state hpc ha
  have hp : pre.pc = 5 * (left.length + 45) ∧ pre.halted = false ∧
      pre.heap 1 = CapacityBits.width q ∧ pre.heap 2 = indexWidth 32 full.length q ∧
      (∀ a, (a < 64 ∨ 69 ≤ a) → a ≠ 1 → a ≠ 2 → pre.heap a = state.heap a) := by
    simpa only [pre, allCode, PA06A19PrepareRuntimeHeader019.program, List.append_assoc] using hpre
  have hlead : lead.length = left.length + 45 := by
    simp only [lead, List.length_append, dimensionPrelude_length]
  have htail : natRun rom allCode PA06A19PrepareRuntimeHeader019.postamble.length pre =
      runOps rom PA06A19PrepareRuntimeHeader019.postamble pre := by
    have hs := natRun_of_straight_segment rom (lead ++ PA06A19PrepareRuntimeHeader019.postamble ++ right)
      PA06A19PrepareRuntimeHeader019.postamble lead.length
      (by simp only [List.length_append]; omega) (segment_index lead _ right)
      PA06A19PrepareRuntimeHeader019.postamble_noJump pre (by rw [hlead]; exact hp.1) hp.2.1
    simpa only [lead, allCode, PA06A19PrepareRuntimeHeader019.program, List.append_assoc] using hs
  have hrun : natRun rom allCode (PA06A19PrepareRuntimeHeader019.clock full.length q) state =
      runOps rom PA06A19PrepareRuntimeHeader019.postamble pre := by
    change natRun rom allCode (dimensionClock full.length q + PA06A19PrepareRuntimeHeader019.postamble.length) state = _
    rw [natRun_add, htail]
  rw [hrun]
  exact (PA06A19PrepareRuntimeHeader019.postamble_frame rom pre address haddress).trans
    (hp.2.2.2.2 address hout (by omega) (by omega))

/-- Real embedded save/header/restore execution. The header starts at
left.length+20, and restore starts at left.length+84; PC is never reset. -/
theorem program_run (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    let fresh := natRun (controllerInput q full used) (left ++ program left.length ++ right) (clock full.length q) state
    fresh.pc = 5 * (left.length + 104) ∧ fresh.halted = false ∧ NatHeader q full.length fresh.heap ∧
      (∀ address, 16 ≤ address → fresh.heap address = state.heap address) := by
  let rom := controllerInput q full used
  let lead := left ++ save
  let headerCode := PA06A19PrepareRuntimeHeader019.program lead.length
  let lastLead := lead ++ headerCode
  let allCode := lead ++ headerCode ++ restore ++ right
  let saved := runOps rom save state
  let middle := natRun rom allCode (PA06A19PrepareRuntimeHeader019.clock full.length q) saved
  have hlead : lead.length = left.length + 20 := by simp only [lead, List.length_append, save_length]
  have hcode : left ++ program left.length ++ right = allCode := by
    simp only [program, lead, headerCode, allCode, List.length_append, save_length, List.append_assoc]
  have hsaveRun : natRun rom allCode 20 state = saved := by
    have hs := natRun_of_straight_segment rom (left ++ save ++ (headerCode ++ restore ++ right))
      save left.length (by simp only [List.length_append]; omega) (segment_index left save _)
      save_noJump state hpc ha
    simpa only [allCode, lead, saved, save_length, List.append_assoc] using hs
  have hsPC : saved.pc = 5 * lead.length := by
    rw [runOps_pc rom save state save_noJump, hpc, hlead, save_length]
    omega
  have hsActive : saved.halted = false := (runOps_halted rom save state).trans ha
  have hm := PA06A19PrepareRuntimeHeader019.program_run q full used lead (restore ++ right) saved hsPC hsActive
  have hmiddle : middle.pc = 5 * (lead.length + 64) ∧ middle.halted = false ∧
      middle.heap 0 = CapacityBits.width q ∧ middle.heap 1 = 2 ^ CapacityBits.width q - 1 ∧
      middle.heap 2 = 2 ^ indexWidth 32 full.length q - 1 ∧ middle.heap 3 = indexWidth 32 full.length q ∧
      (∀ address, 69 ≤ address → middle.heap address = saved.heap address) := by
    simpa only [middle, headerCode, allCode, List.append_assoc] using hm
  have hmiddleFrame (address : Nat) (haddr : 4 ≤ address) (hout : address < 64 ∨ 69 ≤ address) :
      middle.heap address = saved.heap address := by
    have hf := header_frame q full used lead (restore ++ right) saved hsPC hsActive address haddr hout
    simpa only [middle, headerCode, allCode, List.append_assoc] using hf
  have hlast : lastLead.length = lead.length + 64 := by
    simp only [lastLead, headerCode, List.length_append, PA06A19PrepareRuntimeHeader019.program_length]
  have hrestoreRun : natRun rom allCode 20 middle = runOps rom restore middle := by
    have hs := natRun_of_straight_segment rom (lastLead ++ restore ++ right) restore lastLead.length
      (by simp only [List.length_append]; omega) (segment_index lastLead restore right)
      restore_noJump middle (by rw [hlast]; exact hmiddle.1) hmiddle.2.1
    simpa only [allCode, lastLead, restore_length, List.append_assoc] using hs
  have hrun : natRun (controllerInput q full used) (left ++ program left.length ++ right)
      (clock full.length q) state = runOps rom restore middle := by
    rw [hcode]
    have hc : clock full.length q = 20 + PA06A19PrepareRuntimeHeader019.clock full.length q + 20 := by
      unfold clock; omega
    rw [hc, natRun_add, natRun_add, hsaveRun, hrestoreRun]
  simp only [hrun]
  refine ⟨?_, (runOps_halted rom restore middle).trans hmiddle.2.1, ?_, ?_⟩
  · rw [runOps_pc rom restore middle restore_noJump, hmiddle.1, hlead, restore_length]
    omega
  · constructor
    · rw [restore_nat_frame rom middle 0 (Or.inl (by decide))]; exact hmiddle.2.2.1
    · constructor
      · rw [restore_nat_frame rom middle 1 (Or.inl (by decide))]; exact hmiddle.2.2.2.1
      · constructor
        · rw [restore_nat_frame rom middle 2 (Or.inl (by decide))]; exact hmiddle.2.2.2.2.1
        · rw [restore_nat_frame rom middle 3 (Or.inl (by decide))]; exact hmiddle.2.2.2.2.2.1
  · intro address haddr
    by_cases hstack : 64 ≤ address ∧ address < 69
    · let index := address - 64
      have hi : index < 5 := by dsimp only [index]; omega
      have heq : address = 64 + index := by dsimp only [index]; omega
      rw [heq, restore_nat_value rom middle index hi,
        hmiddleFrame (9 + index) (by omega) (Or.inl (by omega)), save_nat_value rom state index hi]
    · have hout : address < 64 ∨ 69 ≤ address := by omega
      rw [restore_nat_frame rom middle address hout, hmiddleFrame address (by omega) hout,
        save_nat_frame rom state address haddr]

theorem save_numeric (rom : PhysicalROM) (B heapWords : Nat) (hsmall : 68 ≤ B) (hheap : 69 ≤ heapWords)
    (state : NatState) (hr : RegistersLE B state) (hv : ∀ index < 5, state.heap (64 + index) ≤ B) :
    NumericSafe B heapWords rom save state := by
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  have h4 := hv 4 (by decide)
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 20 at hc
    interval_cases count <;> cases register <;>
      simp +decide [save, copyWord, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 20 at hc
    interval_cases count <;>
      simp +decide [save, copyWord, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals omega

theorem restore_numeric (rom : PhysicalROM) (B heapWords : Nat) (hsmall : 68 ≤ B) (hheap : 69 ≤ heapWords)
    (state : NatState) (hr : RegistersLE B state) (hv : ∀ index < 5, state.heap (9 + index) ≤ B) :
    NumericSafe B heapWords rom restore state := by
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  have h4 := hv 4 (by decide)
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 20 at hc
    interval_cases count <;> cases register <;>
      simp +decide [restore, copyWord, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 20 at hc
    interval_cases count <;>
      simp +decide [restore, copyWord, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals omega

theorem maxWord_pc (N q : Nat) (hq : 0 < q) : 520 ≤ 2 ^ indexWidth 32 N q - 1 := by
  have hb := PA17GeneratorStatic048.bits_ge_64 N q hq
  have hp : 2 ^ 64 ≤ 2 ^ indexWidth 32 N q := Nat.pow_le_pow_right (by decide) hb
  have hs : 520 < 2 ^ 64 := by decide
  omega

/-- Prefix safety is derived from the three actual segments. Incoming
Nat heap/register bounds are exactly the Word view's internal bounds. -/
theorem program_safe (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (t : Nat)
    (hq : 0 < q) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hr : RegistersLE (2 ^ indexWidth 32 full.length q - 1) state)
    (hv : ∀ index < 5, state.heap (64 + index) ≤ 2 ^ indexWidth 32 full.length q - 1)
    (hpcB : 5 * (left ++ program left.length ++ right).length ≤ 2 ^ indexWidth 32 full.length q - 1) :
    RunSafe (2 ^ indexWidth 32 full.length q - 1) (PA06A19PrepareRuntimeHeader019.heapWords full.length q t)
      (controllerInput q full used) (left ++ program left.length ++ right) (clock full.length q) state := by
  let B := 2 ^ indexWidth 32 full.length q - 1
  let H := PA06A19PrepareRuntimeHeader019.heapWords full.length q t
  let rom := controllerInput q full used
  let lead := left ++ save
  let headerCode := PA06A19PrepareRuntimeHeader019.program lead.length
  let lastLead := lead ++ headerCode
  let allCode := lead ++ headerCode ++ restore ++ right
  let saved := runOps rom save state
  let middle := natRun rom allCode (PA06A19PrepareRuntimeHeader019.clock full.length q) saved
  have hlead : lead.length = left.length + 20 := by simp only [lead, List.length_append, save_length]
  have hcode : left ++ program left.length ++ right = allCode := by
    simp only [program, lead, headerCode, allCode, List.length_append, save_length, List.append_assoc]
  have hsmall := maxWord_pc full.length q hq
  have hroom := PA06A19PrepareRuntimeHeader019.heapWords_room full.length q t
  have hsaveNumeric := save_numeric rom B H (by omega) hroom state hr hv
  have hsaveSafe := straight_segment_safe rom B H left save (headerCode ++ restore ++ right)
    save_noJump state hpc ha hsaveNumeric
  have hsaveSafe' : RunSafe B H rom allCode 20 state := by
    simpa only [allCode, lead, save_length, List.append_assoc] using hsaveSafe
  have hsaveRun : natRun rom allCode 20 state = saved := by
    have hs := natRun_of_straight_segment rom (left ++ save ++ (headerCode ++ restore ++ right)) save left.length
      (by simp only [List.length_append]; omega) (segment_index left save _) save_noJump state hpc ha
    simpa only [allCode, lead, saved, save_length, List.append_assoc] using hs
  have hsPC : saved.pc = 5 * lead.length := by
    rw [runOps_pc rom save state save_noJump, hpc, hlead, save_length]
    omega
  have hsActive : saved.halted = false := (runOps_halted rom save state).trans ha
  have hheaderSafe := PA06A19PrepareRuntimeHeader019.program_safe q full used t hq lead (restore ++ right) saved
    hsPC hsActive (hsaveNumeric.final _ _ _ _ _)
    (by simpa only [hcode, allCode, headerCode, List.append_assoc] using hpcB)
  have hheaderSafe' : RunSafe B H rom allCode (PA06A19PrepareRuntimeHeader019.clock full.length q) saved := by
    simpa only [allCode, headerCode, List.append_assoc] using hheaderSafe
  have hm := PA06A19PrepareRuntimeHeader019.program_run q full used lead (restore ++ right) saved hsPC hsActive
  have hmiddle : middle.pc = 5 * (lead.length + 64) ∧ middle.halted = false := by
    have hh := And.intro hm.1 hm.2.1
    simpa only [middle, allCode, headerCode, List.append_assoc] using hh
  have hlast : lastLead.length = lead.length + 64 := by
    simp only [lastLead, headerCode, List.length_append, PA06A19PrepareRuntimeHeader019.program_length]
  have hlow (index : Nat) (hi : index < 5) : middle.heap (9 + index) ≤ B := by
    have hf := header_frame q full used lead (restore ++ right) saved hsPC hsActive (9 + index)
      (by omega) (Or.inl (by omega))
    have hf' : middle.heap (9 + index) = saved.heap (9 + index) := by
      simpa only [middle, allCode, headerCode, List.append_assoc] using hf
    rw [hf', save_nat_value rom state index hi]
    exact hv index hi
  have hrestoreNumeric := restore_numeric rom B H (by omega) hroom middle
    (hheaderSafe'.final _ _ _ _ _).1 hlow
  have hrestoreSafe := straight_segment_safe rom B H lastLead restore right restore_noJump middle
    (by rw [hlast]; exact hmiddle.1) hmiddle.2 hrestoreNumeric
  have hrestoreSafe' : RunSafe B H rom allCode 20 middle := by
    simpa only [allCode, lastLead, restore_length, List.append_assoc] using hrestoreSafe
  have hfirstRun : natRun rom allCode (20 + PA06A19PrepareRuntimeHeader019.clock full.length q) state = middle := by
    rw [natRun_add, hsaveRun]
  have hfirst := RunSafe.add B H rom allCode 20 (PA06A19PrepareRuntimeHeader019.clock full.length q) state
    hsaveSafe' (by rw [hsaveRun]; exact hheaderSafe')
  have hall := RunSafe.add B H rom allCode (20 + PA06A19PrepareRuntimeHeader019.clock full.length q) 20 state
    hfirst (by rw [hfirstRun]; exact hrestoreSafe')
  rw [hcode]
  have hc : clock full.length q = 20 + PA06A19PrepareRuntimeHeader019.clock full.length q + 20 := by unfold clock; omega
  rw [hc]
  exact hall

theorem program0_code_fit {bits : Nat} (hb : 10 ≤ bits) : WordsFit bits (packingCode (program 0)) := by
  have hp : 2 ^ 10 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hb
  intro value hv
  simp [packingCode, program, save, restore, copyWord, PA06A19PrepareRuntimeHeader019.program,
    dimensionPrelude, computeLog, widthExpr, bitsExpr, Expr.compile, spill, finish, Binary.instruction,
    logBlock, logInit, logHead, logTail, storeLog, PA06A19PrepareRuntimeHeader019.postamble,
    PackingOp.encode, Op.encodeWords, Instruction.encodeWords, PackingPrimitive.word, Register.word, Region.word, haltWords] at hv
  simp only [Fits]
  omega

theorem program0_pc_fit {bits : Nat} (hb : 10 ≤ bits) : Fits bits (5 * (program 0).length) := by
  have hp : 2 ^ 10 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hb
  rw [program_length]
  change 520 < 2 ^ bits
  omega

/-- The original arbitrary Word heap supplies every incoming bound. The
final temp Header and all cache>=16 frame are outputs of actual execution. -/
theorem actual_header_cache (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (t : Nat)
    (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false) :
    let fresh := packingRun (controllerInput q full used) (program 0) (clock full.length q) state
    fresh.pc = BitVec.ofNat _ 520 ∧ fresh.halted = false ∧ PA06A19PrepareRuntimePacked016.Header q fresh.heap ∧
      (∀ address : BitVec (indexWidth 32 full.length q), 16 ≤ address.toNat → fresh.heap address = state.heap address) := by
  let bits := indexWidth 32 full.length q
  let B := 2 ^ bits - 1
  let start := PA06A19PrepareRuntimeHeader019.natView state
  let freshNat := natRun (controllerInput q full used) (program 0) (clock full.length q) start
  have hb64 : 64 ≤ bits := PA17GeneratorStatic048.bits_ge_64 full.length q hq
  have hsmall := maxWord_pc full.length q hq
  have hstartpc : start.pc = 5 * ([] : List PackingOp).length := by
    change state.pc.toNat = 0
    rw [hpc]
    rfl
  have hv (index : Nat) (hi : index < 5) : start.heap (64 + index) ≤ B := by
    have hb := (state.heap (BitVec.ofNat bits (64 + index))).toNat_lt_twoPow_of_le (Nat.le_refl bits)
    change (state.heap (BitVec.ofNat bits (64 + index))).toNat ≤ 2 ^ bits - 1
    omega
  have hs := program_safe q full used t hq [] [] start hstartpc ha
    (PA06A19PrepareRuntimeHeader019.natView_registers state) hv
    (by simpa only [List.nil_append, List.append_nil, program_length] using hsmall)
  have hs' : RunSafe B (PA06A19PrepareRuntimeHeader019.heapWords full.length q t) (controllerInput q full used)
      (program 0) (clock full.length q) start := by
    simpa only [B, bits, List.nil_append, List.append_nil, List.length_nil] using hs
  have hw := actual_word_run (controllerInput q full used) B (PA06A19PrepareRuntimeHeader019.heapWords full.length q t)
    bits (program 0) (clock full.length q) start hs' (PA17GeneratorStatic048.maxWord_fits bits)
    (program0_code_fit (by omega)) (program0_pc_fit (by omega)) (clock full.length q) le_rfl
  rw [PA06A19PrepareRuntimeHeader019.natView_toWord] at hw
  have hn := program_run q full used [] [] start hstartpc ha
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hn
  have hheader : NatHeader q full.length freshNat.heap := hn.2.2.1
  have h0 : (BitVec.ofNat bits 0).toNat = 0 := small_toNat (by omega) 0 (by decide)
  have h1 : (BitVec.ofNat bits 1).toNat = 1 := small_toNat (by omega) 1 (by decide)
  have h2 : (BitVec.ofNat bits 2).toNat = 2 := small_toNat (by omega) 2 (by decide)
  have h3 : (BitVec.ofNat bits 3).toNat = 3 := small_toNat (by omega) 3 (by decide)
  simp only [hw]
  refine ⟨?_, hn.2.1, ?_, ?_⟩
  · change BitVec.ofNat bits freshNat.pc = BitVec.ofNat bits 520
    rw [hn.1]
  · constructor
    · change BitVec.ofNat bits (freshNat.heap (BitVec.ofNat bits 0).toNat) = _
      rw [h0, hheader.1]
    · change BitVec.ofNat bits (freshNat.heap (BitVec.ofNat bits 1).toNat) = _
      rw [h1, hheader.2.1]
      rfl
    · change BitVec.ofNat bits (freshNat.heap (BitVec.ofNat bits 2).toNat) = _
      rw [h2, hheader.2.2.1]
    · change BitVec.ofNat bits (freshNat.heap (BitVec.ofNat bits 3).toNat) = _
      rw [h3, hheader.2.2.2]
  · intro address haddr
    change BitVec.ofNat bits (freshNat.heap address.toNat) = state.heap address
    rw [hn.2.2.2 address.toNat haddr]
    change BitVec.ofNat bits ((state.heap (BitVec.ofNat bits address.toNat)).toNat) = state.heap address
    dsimp only [bits]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Conservative cost on the actual fetched trace. The extra 40 executed
save/restore instructions are charged; there is no free cache copy. -/
theorem actual_trace_bound (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (state : WordState (indexWidth 32 full.length q)) :
    (packingDynamicTrace (controllerInput q full used) (program 0) (clock full.length q) state).length ≤
      12 * PA06A19PrepareRuntimeHeader019.clock full.length q + 480 := by
  have hh := packingDynamicTrace_length_le (controllerInput q full used) (program 0) (clock full.length q) state
  simpa only [clock, Nat.mul_add] using hh

/-- Standalone terminal HALT is also fetched. Embedded clients use the
active body theorem above and continue at its actual PC instead. -/
theorem actual_halting (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (t : Nat)
    (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false) :
    let fresh := packingRun (controllerInput q full used) (program 0) (clock full.length q + 1) state
    fresh.halted = true ∧ PA06A19PrepareRuntimePacked016.Header q fresh.heap ∧
      (∀ address : BitVec (indexWidth 32 full.length q), 16 ≤ address.toNat → fresh.heap address = state.heap address) := by
  let result := packingRun (controllerInput q full used) (program 0) (clock full.length q) state
  have hb := actual_header_cache q full used t hq state hpc ha
  have hbits := PA17GeneratorStatic048.bits_ge_64 full.length q hq
  have hfit : Fits (indexWidth 32 full.length q) 520 := by
    simpa only [program_length] using (program0_pc_fit (bits := indexWidth 32 full.length q) (by omega))
  have hp : result.pc.toNat = 5 * (program 0).length := by
    change (packingRun (controllerInput q full used) (program 0) (clock full.length q) state).pc.toNat = _
    rw [hb.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit, program_length]
  have hs : packingRun (controllerInput q full used) (program 0) (clock full.length q + 1) state =
      { result with halted := true } := by
    rw [packingRun_succ]
    exact packingStep_halt (controllerInput q full used) (program 0) result (program0_code_fit (by omega)) hp hb.2.1
  simp only [hs]
  exact ⟨True.intro, hb.2.2.1, hb.2.2.2⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareHeaderScratch024

module

public import Structure.PA06_A19Prepare_FiniteClear031_Setup
public import Structure.PA06_A19Prepare_FiniteClear029_InitialView
public import PaperProofs.Structure.PA17_UniformGenerator_035p
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate: actual setup19 -> finite clear10 in the containing code.
The bank is an internal representation produced by026; index/length,
zero view, safety and original allocation room are derived here. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteInit032

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety RawTreePreprocessingClaims CompactControllerClaims
  PA17UniformGenerator035j PA17UniformGenerator035m PA17UniformGenerator035p
open AlgorithmClaims.PackedCapacityRAM
open PA06A19PrepareFiniteClear031Setup (ordinaryWords)

def programAt (start : Nat) : List PackingOp :=
  PA06A19PrepareFiniteClear031Setup.setup ++ PA06A19PrepareFiniteClear025.programAt (start + 19)

theorem programAt_length (start : Nat) : (programAt start).length = 29 := rfl

def clearLength (N q t : Nat) : Nat :=
  packedCapacityWords q (capacityWords 8192 N q t) (indexWidth 32 N q) + ordinaryWords N q t

def clock (N q t : Nat) : Nat := 19 + (7 * clearLength N q t + 5)

theorem clock_eq (N q t : Nat) : clock N q t = 7 * clearLength N q t + 24 := by unfold clock; omega

/-- Physical intermediate data only. The original raw caller does not
supply these fields;026's actual bank writer must establish this record. -/
structure BankData (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (indexWidth 32 full.length q)) : Prop where
  base : (state.register .address).toNat = PA06A19PrepareControlBank017.controlBase full.length q
    (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))
  N : (state.heap (BitVec.ofNat _ (PA06A19PrepareControlBank017.controlBase full.length q
    (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))))).toNat = full.length
  Q : (state.heap (BitVec.ofNat _ (PA06A19PrepareControlBank017.controlBase full.length q
    (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) + 1))).toNat = q
  T : (state.heap (BitVec.ofNat _ (PA06A19PrepareControlBank017.controlBase full.length q
    (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) + 2))).toNat = treeSize q full
  P : (state.heap (BitVec.ofNat _ (PA06A19PrepareControlBank017.controlBase full.length q
    (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) + 5))).toNat =
      packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)

theorem actual_end_room (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    4 + clearLength full.length q (treeSize q full) ≤
      PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full) := by
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
  have he := PA06A19PrepareFiniteClear031Setup.clear_end_le_control full.length q t P
  have hc := PA06A19PrepareControlBank017.controls_cache_disjoint full.length q t P 0 (by decide)
  have hr := (PA06A19PrepareControlBank017.actual_cache_room full hq).1
  have hAlloc : PA06A19PrepareControlBank017.allocation full.length q t P =
      PA06A19PrepareRuntimeHeader019.heapWords full.length q t := by
    dsimp only [PA06A19PrepareControlBank017.allocation, PA06A19PrepareControlBank017.dimensions,
      PA06A19PrepareControlBank017.mass, PA06A19PrepareRuntimeHeader019.heapWords, P]
    omega
  have hr' : PA06A19PrepareControlBank017.cacheBase full.length q t P +
      PA06A19PrepareControlBank017.cacheAllowance full.length q <
      PA06A19PrepareRuntimeHeader019.heapWords full.length q t := by
    rw [← hAlloc]
    exact hr
  change 4 + (P + ordinaryWords full.length q t) ≤ PA06A19PrepareRuntimeHeader019.heapWords full.length q t
  have hc' : PA06A19PrepareControlBank017.controlBase full.length q t P <
      PA06A19PrepareControlBank017.cacheBase full.length q t P := by
    simpa only [Nat.add_zero] using hc
  exact he.trans (hc'.trans ((Nat.le_add_right _ _).trans_lt hr')).le

theorem init_safe (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hr : RegistersLE (2 ^ indexWidth 32 full.length q - 1) state)
    (hcb : state.register .address = PA06A19PrepareControlBank017.controlBase full.length q
      (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)))
    (hN : state.heap (state.register .address) = full.length) (hQ : state.heap (state.register .address + 1) = q)
    (ht : state.heap (state.register .address + 2) = treeSize q full)
    (hP : state.heap (state.register .address + 5) = packedCapacityWords q
      (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))
    (hpcB : 5 * (left ++ programAt left.length ++ right).length ≤ 2 ^ indexWidth 32 full.length q - 1) :
    RunSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) (left ++ programAt left.length ++ right)
      (clock full.length q (treeSize q full)) state := by
  let rom := controllerInput q full used
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
  let B := 2 ^ indexWidth 32 full.length q - 1
  let H := PA06A19PrepareRuntimeHeader019.heapWords full.length q t
  let allCode := left ++ programAt left.length ++ right
  let lead := left ++ PA06A19PrepareFiniteClear031Setup.setup
  let prepared := runOps rom PA06A19PrepareFiniteClear031Setup.setup state
  have hlead : lead.length = left.length + 19 := by
    simp only [lead, List.length_append, PA06A19PrepareFiniteClear031Setup.setup_length]
  have hcode : allCode = lead ++ PA06A19PrepareFiniteClear025.programAt lead.length ++ right := by
    simp only [allCode, programAt, lead, hlead, List.append_assoc]
  have hsetup := PA06A19PrepareFiniteClear031Setup.actual_setup_numeric q full used hq state hr hcb hN hQ ht hP
  have hs : RunSafe B H rom allCode 19 state := by
    have hh := straight_segment_safe rom B H left PA06A19PrepareFiniteClear031Setup.setup
      (PA06A19PrepareFiniteClear025.programAt (left.length + 19) ++ right)
      PA06A19PrepareFiniteClear031Setup.setup_noJump state hpc ha hsetup
    simpa only [allCode, programAt, List.append_assoc, PA06A19PrepareFiniteClear031Setup.setup_length] using hh
  have hfirst : natRun rom allCode 19 state = prepared := by
    have hh := natRun_of_straight_segment rom
      (left ++ PA06A19PrepareFiniteClear031Setup.setup ++ (PA06A19PrepareFiniteClear025.programAt (left.length + 19) ++ right))
      PA06A19PrepareFiniteClear031Setup.setup left.length (by simp only [List.length_append]; omega)
      (PA17UniformGenerator035a.segment_index left PA06A19PrepareFiniteClear031Setup.setup _)
      PA06A19PrepareFiniteClear031Setup.setup_noJump state hpc ha
    simpa only [allCode, programAt, List.append_assoc, PA06A19PrepareFiniteClear031Setup.setup_length] using hh
  have hdata := PA06A19PrepareFiniteClear031Setup.setup_data rom state (state.register .address)
    full.length q t P rfl hN hQ ht hP
  have hp : prepared.pc = 5 * lead.length := by
    rw [runOps_pc rom _ state PA06A19PrepareFiniteClear031Setup.setup_noJump, hpc,
      PA06A19PrepareFiniteClear031Setup.setup_length, hlead]
    omega
  have hend := PA06A19PrepareFiniteClear031Setup.actual_clear_end_fits q full hq
  have hendB : 4 + (P + ordinaryWords full.length q t) ≤ B := by
    change 4 + (P + ordinaryWords full.length q t) < 2 ^ indexWidth 32 full.length q at hend
    dsimp only [B]
    omega
  have hsmall := PA06A19PrepareRuntimeHeader019.maxWord_small full.length q hq
  have hclear := PA06A19PrepareFiniteClear025Safety.clear_safe rom B H lead right 4
    (P + ordinaryWords full.length q t) prepared hp
    ((runOps_halted rom _ state).trans ha) (hsetup.final _ _ _ _ _) (by omega)
    hdata.1 hdata.2.1 hendB (actual_end_room q full hq) (by rw [← hcode]; exact hpcB)
  have hclear' : RunSafe B H rom allCode (7 * (P + ordinaryWords full.length q t) + 5) prepared := by
    simpa only [hcode] using hclear
  exact RunSafe.add B H rom allCode 19 (7 * (P + ordinaryWords full.length q t) + 5) state hs
    (by rw [hfirst]; exact hclear')

private theorem wordRun_add {bits : Nat} (rom : PhysicalROM) (code : List PackingOp)
    (left right : Nat) (state : WordState bits) :
    packingRun rom code (left + right) state = packingRun rom code right (packingRun rom code left state) := by
  induction left generalizing state with
  | zero => simp only [Nat.zero_add, packingRun]
  | succ left ih =>
    rw [Nat.succ_add]
    change packingRun rom code (left + right) (packingStep rom ((packingCode code).map (BitVec.ofNat bits)) state) = _
    exact ih _

theorem bank_natView (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (indexWidth 32 full.length q)) (hbank : BankData q full state) :
    let natural := PA06A19PrepareRuntimeHeader019.natView state
    natural.heap (natural.register .address) = full.length ∧
    natural.heap (natural.register .address + 1) = q ∧
    natural.heap (natural.register .address + 2) = treeSize q full ∧
    natural.heap (natural.register .address + 5) = packedCapacityWords q
      (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) := by
  dsimp only [PA06A19PrepareRuntimeHeader019.natView]
  simp only [hbank.base]
  exact ⟨hbank.N, hbank.Q, hbank.T, hbank.P⟩

/-- Every actual fetched prefix is safe, including arbitrary incoming
full-width registers. Code and absolute-PC fit are upper assembly facts. -/
theorem actual_init_word (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false) (hbank : BankData q full before)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ programAt left.length ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ programAt left.length ++ right).length))
    (count : Nat) (hc : count ≤ clock full.length q (treeSize q full)) :
    packingRun (controllerInput q full used) (left ++ programAt left.length ++ right) count before =
      (natRun (controllerInput q full used) (left ++ programAt left.length ++ right) count
        (PA06A19PrepareRuntimeHeader019.natView before)).toWord (indexWidth 32 full.length q) := by
  let start := PA06A19PrepareRuntimeHeader019.natView before
  have hd := bank_natView q full before hbank
  have hpcB : 5 * (left ++ programAt left.length ++ right).length ≤ 2 ^ indexWidth 32 full.length q - 1 := by
    unfold AlgorithmClaims.Fits at hpcCode
    omega
  have hs := init_safe q full used hq left right start hpc ha
    (PA06A19PrepareRuntimeHeader019.natView_registers before) hbank.base hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 hpcB
  have hw := actual_word_run _ _ _ _ _ (clock full.length q (treeSize q full)) start hs
    (PA17GeneratorStatic048.maxWord_fits _) hcode hpcCode count hc
  simpa only [start, PA06A19PrepareRuntimeHeader019.natView_toWord] using hw

/-- Finite old-view initialization in the SAME actual heap. No initial
zero heap, register index/count, end-fit, or allocation-room assumption is
accepted from the original caller. -/
theorem actual_init_data (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false) (hbank : BankData q full before)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ programAt left.length ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ programAt left.length ++ right).length)) :
    let t := treeSize q full
    let bits := indexWidth 32 full.length q
    let C := capacityWords 8192 full.length q t
    let P := packedCapacityWords q C bits
    let I := ordinaryWords full.length q t
    let after := packingRun (controllerInput q full used) (left ++ programAt left.length ++ right)
      (clock full.length q t) before
    (∀ a < PA06A19PreparePackedView013.oldCapacity full.length q t + I,
      PA06A19PreparePackedView013.view q (PA06A19PreparePackedView013.oldCapacity full.length q t) C (4 + P) after.heap a = 0) ∧
    CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap after.heap)) ∧
    (∀ point : BitVec bits, point.toNat < 4 ∨ 4 + (P + I) ≤ point.toNat → after.heap point = before.heap point) ∧
    after.register .address = before.register .address ∧ after.pc.toNat = 5 * (left.length + 29) ∧ after.halted = false := by
  let rom := controllerInput q full used
  let bits := indexWidth 32 full.length q
  let t := treeSize q full
  let C := capacityWords 8192 full.length q t
  let P := packedCapacityWords q C bits
  let I := ordinaryWords full.length q t
  let H := PA06A19PrepareRuntimeHeader019.heapWords full.length q t
  let allCode := left ++ programAt left.length ++ right
  let lead := left ++ PA06A19PrepareFiniteClear031Setup.setup
  let start := PA06A19PrepareRuntimeHeader019.natView before
  let natural := runOps rom PA06A19PrepareFiniteClear031Setup.setup start
  let prepared := natural.toWord bits
  have hlead : lead.length = left.length + 19 := by
    simp only [lead, List.length_append, PA06A19PrepareFiniteClear031Setup.setup_length]
  have hcodeEq : allCode = lead ++ PA06A19PrepareFiniteClear025.programAt lead.length ++ right := by
    simp only [allCode, programAt, lead, hlead, List.append_assoc]
  have hd := bank_natView q full before hbank
  have hdata := PA06A19PrepareFiniteClear031Setup.setup_data rom start (start.register .address)
    full.length q t P rfl hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
  have hfirstNat : natRun rom allCode 19 start = natural := by
    have hh := natRun_of_straight_segment rom
      (left ++ PA06A19PrepareFiniteClear031Setup.setup ++ (PA06A19PrepareFiniteClear025.programAt (left.length + 19) ++ right))
      PA06A19PrepareFiniteClear031Setup.setup left.length (by simp only [List.length_append]; omega)
      (PA17UniformGenerator035a.segment_index left PA06A19PrepareFiniteClear031Setup.setup _)
      PA06A19PrepareFiniteClear031Setup.setup_noJump start hpc ha
    simpa only [allCode, programAt, List.append_assoc, PA06A19PrepareFiniteClear031Setup.setup_length] using hh
  have hfirstWord : packingRun rom allCode 19 before = prepared := by
    have hh := actual_init_word q full used hq left right before hpc ha hbank hcode hpcCode 19 (by unfold clock; omega)
    change packingRun rom allCode 19 before = (natRun rom allCode 19 start).toWord bits at hh
    rw [hfirstNat] at hh
    exact hh
  have hpNat : natural.pc = 5 * lead.length := by
    rw [runOps_pc rom _ start PA06A19PrepareFiniteClear031Setup.setup_noJump,
      PA06A19PrepareFiniteClear031Setup.setup_length, hlead]
    change before.pc.toNat + 5 * 19 = _
    rw [hpc]
    omega
  have hpFit : Fits bits (5 * lead.length) := by
    apply (show 5 * lead.length ≤ 5 * allCode.length from ?_).trans_lt hpcCode
    simp only [allCode, List.length_append, programAt_length, hlead]
    omega
  have hp : prepared.pc.toNat = 5 * lead.length := by
    change (BitVec.ofNat bits natural.pc).toNat = _
    rw [hpNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpFit]
  have hend : Fits bits (4 + (P + I)) := PA06A19PrepareFiniteClear031Setup.actual_clear_end_fits q full hq
  have hfour : Fits bits 4 := (Nat.le_add_right 4 (P + I)).trans_lt hend
  have hlenFit : Fits bits (P + I) := (by omega : P + I ≤ 4 + (P + I)).trans_lt hend
  have hbase : (prepared.register .index).toNat = 4 := by
    change (BitVec.ofNat bits (natural.register .index)).toNat = 4
    rw [hdata.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfour]
  have hlen : (prepared.register .total).toNat = P + I := by
    change (BitVec.ofNat bits (natural.register .total)).toNat = P + I
    rw [hdata.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlenFit]
  have hactive : prepared.halted = false := (runOps_halted rom _ start).trans ha
  have hheap : prepared.heap = before.heap := by
    funext point
    change BitVec.ofNat bits (natural.heap point.toNat) = before.heap point
    rw [hdata.2.2.2]
    dsimp only [bits]
    simp only [start, PA06A19PrepareRuntimeHeader019.natView, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have haddress : prepared.register .address = before.register .address := by
    change BitVec.ofNat bits (natural.register .address) = before.register .address
    rw [hdata.2.2.1]
    dsimp only [bits]
    simp only [start, PA06A19PrepareRuntimeHeader019.natView, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hone : Fits bits 1 := (by decide : 1 ≤ 8).trans_lt (PA17WordBounds023.small_word_fit full.length q)
  have hview := PA06A19PrepareFiniteClear029InitialView.clear_word_initial_view rom H lead right q
    (PA06A19PreparePackedView013.oldCapacity full.length q t) C I prepared hq
    (PA17PackingBounds043.bits_pos full.length q) (PA17PackingBounds043.width_le_bits full.length q)
    (PA06A19PreparePackedView013.oldCapacity_le_capacity full.length q t hq)
    (by dsimp only [I, ordinaryWords]; omega) hone hp hactive hbase hlen hend (actual_end_room q full hq)
    (by rw [← hcodeEq]; exact hpcCode) (by rw [← hcodeEq]; exact hcode)
  have hrun : packingRun rom allCode (clock full.length q t) before =
      packingRun rom (lead ++ PA06A19PrepareFiniteClear025.programAt lead.length ++ right) (7 * (P + I) + 5) prepared := by
    change packingRun rom allCode (19 + (7 * (P + I) + 5)) before = _
    rw [wordRun_add, hfirstWord, hcodeEq]
  dsimp only
  let after := packingRun rom allCode (clock full.length q t) before
  change (∀ a < PA06A19PreparePackedView013.oldCapacity full.length q t + I,
    PA06A19PreparePackedView013.view q (PA06A19PreparePackedView013.oldCapacity full.length q t) C (4 + P) after.heap a = 0) ∧
    CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap after.heap)) ∧
    (∀ point : BitVec bits, point.toNat < 4 ∨ 4 + (P + I) ≤ point.toNat → after.heap point = before.heap point) ∧
    after.register .address = before.register .address ∧ after.pc.toNat = 5 * (left.length + 29) ∧ after.halted = false
  simp only [after, hrun]
  refine ⟨hview.1, hview.2.1, ?_, hview.2.2.2.1.trans haddress, ?_, hview.2.2.2.2.2⟩
  · intro point hout
    exact (hview.2.2.1 point hout).trans (congrFun hheap point)
  · rw [hview.2.2.2.2.1, hlead]

theorem actual_init_header (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false) (hbank : BankData q full before)
    (hheader : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ programAt left.length ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ programAt left.length ++ right).length)) :
    PA06A19PrepareRuntimePacked016.Header q
      (packingRun (controllerInput q full used) (left ++ programAt left.length ++ right)
        (clock full.length q (treeSize q full)) before).heap := by
  have hf := (actual_init_data q full used hq left right before hpc ha hbank hcode hpcCode).2.2.1
  have hsmall : Fits (indexWidth 32 full.length q) 3 :=
    (by decide : 3 ≤ 8).trans_lt (PA17WordBounds023.small_word_fit full.length q)
  have hpoint (n : Nat) (hn : n < 4) : (BitVec.ofNat (indexWidth 32 full.length q) n).toNat < 4 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((by omega : n ≤ 3).trans_lt hsmall)]
    exact hn
  constructor
  · rw [hf _ (Or.inl (hpoint 0 (by decide)))]
    exact hheader.width
  · rw [hf _ (Or.inl (hpoint 1 (by decide)))]
    exact hheader.mask
  · rw [hf _ (Or.inl (hpoint 2 (by decide)))]
    exact hheader.ones
  · rw [hf _ (Or.inl (hpoint 3 (by decide)))]
    exact hheader.wordBits

theorem actual_init_trace_bound (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q)) :
    (packingDynamicTrace (controllerInput q full used) (left ++ programAt left.length ++ right)
      (clock full.length q (treeSize q full)) before).length ≤ 84 * clearLength full.length q (treeSize q full) + 288 := by
  exact (packingDynamicTrace_length_le _ _ _ before).trans_eq (by rw [clock_eq]; omega)

theorem actual_init_prefix_access (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false) (hbank : BankData q full before)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ programAt left.length ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ programAt left.length ++ right).length))
    (count : Nat) (hc : count < clock full.length q (treeSize q full)) :
    let code := left ++ programAt left.length ++ right
    let actual := packingRun (controllerInput q full used) code count before
    actual.halted = false ∧ actual.pc.toNat + 4 < (packingCode code).length ∧
    let fetched := physicalFetch (indexWidth 32 full.length q) (packingCode code) actual.pc.toNat
    ∃ op, PackingOp.decode fetched = some op ∧
      packingAccessFits (controllerInput q full used)
        (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)) actual op := by
  let start := PA06A19PrepareRuntimeHeader019.natView before
  have hd := bank_natView q full before hbank
  have hpcB : 5 * (left ++ programAt left.length ++ right).length ≤ 2 ^ indexWidth 32 full.length q - 1 := by
    unfold AlgorithmClaims.Fits at hpcCode
    omega
  have hs := init_safe q full used hq left right start hpc ha
    (PA06A19PrepareRuntimeHeader019.natView_registers before) hbank.base hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 hpcB
  have hw := actual_word_fetch_access _ _ _ _ _ (clock full.length q (treeSize q full)) start hs
    (PA17GeneratorStatic048.maxWord_fits _) hcode hpcCode count hc
  simpa only [start, PA06A19PrepareRuntimeHeader019.natView_toWord] using hw

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteInit032

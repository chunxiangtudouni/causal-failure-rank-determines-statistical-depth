module

public import Structure.PA06_A19Prepare_FiniteInit032_Word
public import Structure.PA06_A19Prepare_FiniteInit038_VirtualFrame

set_option autoImplicit false
set_option warningAsError true

/-! Same-program finite clear29 followed by the actual VM-register wipe22.
The only state qualifications are the preceding producer's physical BankData
and temporary Header. Code/PC fit belong to the containing assembly. No zero
view, zero VM register, zero cache, or all-prefix safety premise is accepted.
This candidate has not been compiled by its author; ROOT_LEAN_SLOT owns checks. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareClearVM045

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawTreePreprocessingClaims CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM
open PA06A19PrepareFiniteClear031Setup (ordinaryWords)

def programAt (start : Nat) : List PackingOp :=
  PA06A19PrepareFiniteInit032.programAt start ++ PA06A19PrepareFiniteClear025.clearVirtual

theorem programAt_length (start : Nat) : (programAt start).length = 51 := by
  simp only [programAt, List.length_append, PA06A19PrepareFiniteInit032.programAt_length,
    PA06A19PrepareFiniteClear025.clearVirtual_length]

def clock (N q t : Nat) : Nat := PA06A19PrepareFiniteInit032.clock N q t + 22

theorem clock_eq (N q t : Nat) :
    clock N q t = 7 * PA06A19PrepareFiniteInit032.clearLength N q t + 46 := by
  rw [clock, PA06A19PrepareFiniteInit032.clock_eq]

private theorem wordRun_add {bits : Nat} (rom : PhysicalROM) (code : List PackingOp)
    (first second : Nat) (state : WordState bits) :
    packingRun rom code (first + second) state =
      packingRun rom code second (packingRun rom code first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, packingRun]
  | succ first ih =>
    rw [Nat.succ_add]
    change packingRun rom code (first + second)
      (packingStep rom ((packingCode code).map (BitVec.ofNat bits)) state) = _
    exact ih _

private def PrefixAccess {bits : Nat} (rom : PhysicalROM) (heapWords : Nat)
    (code : List PackingOp) (state : WordState bits) : Prop :=
  state.halted = false ∧ state.pc.toNat + 4 < (packingCode code).length ∧
    ∃ op, PackingOp.decode (fetch code state) = some op ∧
      packingAccessFits rom heapWords state op

private theorem prefix_access_out {bits : Nat} (rom : PhysicalROM) (heapWords : Nat)
    (code : List PackingOp) (state : WordState bits)
    (hgood : PrefixAccess rom heapWords code state) :
    state.halted = false ∧ state.pc.toNat + 4 < (packingCode code).length ∧
      ∃ op, PackingOp.decode (fetch code state) = some op ∧
        packingAccessFits rom heapWords state op := hgood

/- Equality transport and VM projection are checked with abstract code, count,
and state parameters, before instantiating the large concrete clear endpoint. -/
private theorem prefix_access_transport {bits : Nat} (rom : PhysicalROM) (heapWords : Nat)
    (code otherCode : List PackingOp) (state otherState : WordState bits)
    (hcode : code = otherCode) (hstate : state = otherState)
    (hgood : PrefixAccess rom heapWords otherCode otherState) :
    PrefixAccess rom heapWords code state := by
  cases hcode
  cases hstate
  exact hgood

private theorem virtual_prefix_access {bits : Nat} (rom : PhysicalROM) (heapWords : Nat)
    (left right : List PackingOp) (before : WordState bits)
    (hcode : WordsFit bits (packingCode (left ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right)))
    (hpcCode : Fits bits (5 * (left ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right).length))
    (hpc : before.pc = BitVec.ofNat bits (5 * left.length)) (ha : before.halted = false)
    (hfit : Fits bits ((before.register .address).toNat + 38))
    (hroom : (before.register .address).toNat + 39 ≤ heapWords)
    (count : Nat) (hc : count < 22) :
    PrefixAccess rom heapWords (left ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right)
      (packingRun rom (left ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right) count before) := by
  have hh := PA06A19PrepareFiniteClear025Virtual.body_prefix_safe rom heapWords left right before
    hcode hpcCode hpc ha hfit hroom count hc
  rcases hh with ⟨hactive, _, _, hfetchRoom, hdecode, haccess⟩
  exact ⟨hactive, hfetchRoom, _, hdecode, haccess⟩

private theorem joined_virtual_prefix_access {bits : Nat} (rom : PhysicalROM) (heapWords : Nat)
    (code lead right : List PackingOp) (before mid : WordState bits) (first count : Nat)
    (heq : code = lead ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right)
    (hmid : mid = packingRun rom code first before)
    (hcode : WordsFit bits (packingCode code)) (hpcCode : Fits bits (5 * code.length))
    (hpc : mid.pc = BitVec.ofNat bits (5 * lead.length)) (ha : mid.halted = false)
    (hfit : Fits bits ((mid.register .address).toNat + 38))
    (hroom : (mid.register .address).toNat + 39 ≤ heapWords)
    (hfirst : first ≤ count) (hcount : count < first + 22) :
    PrefixAccess rom heapWords code (packingRun rom code count before) := by
  have hremain : count - first < 22 := by omega
  have hgood := virtual_prefix_access rom heapWords lead right mid
    (by rw [← heq]; exact hcode) (by rw [← heq]; exact hpcCode)
    hpc ha hfit hroom (count - first) hremain
  have htime : count = first + (count - first) := by omega
  have hrun : packingRun rom code count before =
      packingRun rom (lead ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right)
        (count - first) mid := by
    calc
      packingRun rom code count before = packingRun rom code (first + (count - first)) before :=
        congrArg (fun ticks => packingRun rom code ticks before) htime
      _ = packingRun rom code (count - first) (packingRun rom code first before) :=
        wordRun_add rom code first (count - first) before
      _ = packingRun rom code (count - first) mid :=
        congrArg (fun state => packingRun rom code (count - first) state) hmid.symm
      _ = packingRun rom (lead ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right)
          (count - first) mid :=
        congrArg (fun body => packingRun rom body (count - first) mid) heq
  exact prefix_access_transport rom heapWords code
    (lead ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right)
    (packingRun rom code count before)
    (packingRun rom (lead ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right) (count - first) mid)
    heq hrun hgood

/-- VM bank room is derived from the unchanged original allocation.
In particular no CB+38 fit/room premise is passed through from a raw caller. -/
theorem actual_virtual_room (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    let t := treeSize q full
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
    let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
    Fits (indexWidth 32 full.length q) (CB + 38) ∧
      CB + 39 ≤ PA06A19PrepareRuntimeHeader019.heapWords full.length q t := by
  dsimp only
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  have hd := PA06A19PrepareControlBank017.controls_cache_disjoint full.length q t P 38 (by decide)
  have hr := PA06A19PrepareControlBank017.actual_cache_room full hq
  have hroom : CB + 38 < PA06A19PrepareControlBank017.allocation full.length q t P :=
    hd.trans ((Nat.le_add_right _ _).trans_lt hr.1)
  have hAlloc : PA06A19PrepareControlBank017.allocation full.length q t P =
      PA06A19PrepareRuntimeHeader019.heapWords full.length q t := by
    dsimp only [PA06A19PrepareControlBank017.allocation, PA06A19PrepareControlBank017.dimensions,
      PA06A19PrepareControlBank017.mass, PA06A19PrepareRuntimeHeader019.heapWords]
    omega
  refine ⟨hroom.trans (PA06A19PrepareControlBank017.actual_allocation_fits full), ?_⟩
  change CB + 39 ≤ PA06A19PrepareRuntimeHeader019.heapWords full.length q t
  exact Nat.succ_le_of_lt (hAlloc ▸ hroom)

section Actual

variable (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
  (hq : 0 < q) (left right : List PackingOp)
  (before : WordState (indexWidth 32 full.length q))
  (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
  (hbank : PA06A19PrepareFiniteInit032.BankData q full before)
  (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ programAt left.length ++ right)))
  (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ programAt left.length ++ right).length))

include hq hpc ha hbank hcode hpcCode

/-- The real clear endpoint in the very same containing program. -/
theorem clear_data :
    let t := treeSize q full
    let bits := indexWidth 32 full.length q
    let C := capacityWords 8192 full.length q t
    let P := packedCapacityWords q C bits
    let I := ordinaryWords full.length q t
    let mid := packingRun (controllerInput q full used) (left ++ programAt left.length ++ right)
      (PA06A19PrepareFiniteInit032.clock full.length q t) before
    (∀ a < PA06A19PreparePackedView013.oldCapacity full.length q t + I,
      PA06A19PreparePackedView013.view q (PA06A19PreparePackedView013.oldCapacity full.length q t)
        C (4 + P) mid.heap a = 0) ∧
    CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap mid.heap)) ∧
    (∀ point : BitVec bits, point.toNat < 4 ∨ 4 + (P + I) ≤ point.toNat → mid.heap point = before.heap point) ∧
    mid.register .address = before.register .address ∧
    mid.pc.toNat = 5 * (left.length + 29) ∧ mid.halted = false := by
  have hc : WordsFit (indexWidth 32 full.length q)
      (packingCode (left ++ PA06A19PrepareFiniteInit032.programAt left.length ++
        (PA06A19PrepareFiniteClear025.clearVirtual ++ right))) := by
    simpa only [programAt, List.append_assoc] using hcode
  have hp : Fits (indexWidth 32 full.length q)
      (5 * (left ++ PA06A19PrepareFiniteInit032.programAt left.length ++
        (PA06A19PrepareFiniteClear025.clearVirtual ++ right)).length) := by
    simpa only [programAt, List.append_assoc] using hpcCode
  simpa only [programAt, List.append_assoc] using
    PA06A19PrepareFiniteInit032.actual_init_data q full used hq left
      (PA06A19PrepareFiniteClear025.clearVirtual ++ right) before hpc ha hbank hc hp

/-- Finite oldC0+I initialization, packed bound, Header, original CB, and
all seven actual source-register cells. The lower and outer heap frames
are consequences of execution; ST's separate 64..84 counters are not inputs. -/
theorem actual_data (hheader : PA06A19PrepareRuntimePacked016.Header q before.heap) :
    let t := treeSize q full
    let bits := indexWidth 32 full.length q
    let C := capacityWords 8192 full.length q t
    let P := packedCapacityWords q C bits
    let I := ordinaryWords full.length q t
    let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
    let code := left ++ programAt left.length ++ right
    let mid := packingRun (controllerInput q full used) code
      (PA06A19PrepareFiniteInit032.clock full.length q t) before
    let after := packingRun (controllerInput q full used) code (clock full.length q t) before
    (∀ a < PA06A19PreparePackedView013.oldCapacity full.length q t + I,
      PA06A19PreparePackedView013.view q (PA06A19PreparePackedView013.oldCapacity full.length q t)
        C (4 + P) after.heap a = 0) ∧
    CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap after.heap)) ∧
    PA06A19PrepareRuntimePacked016.Header q after.heap ∧
    after.register .address = before.register .address ∧
    after.pc.toNat = 5 * (left.length + 51) ∧ after.halted = false ∧
    (∀ slot, 32 ≤ slot → slot < 39 →
      after.heap (before.register .address + BitVec.ofNat bits slot) = 0) ∧
    (∀ point : BitVec bits, point.toNat < CB → after.heap point = mid.heap point) ∧
    (∀ point : BitVec bits, (point.toNat < 4 ∨ 4 + (P + I) ≤ point.toNat) →
      (∀ slot ∈ PA06A19PrepareFiniteClear025Virtual.virtualSlots,
        point ≠ before.register .address + BitVec.ofNat bits slot) → after.heap point = before.heap point) := by
  let rom := controllerInput q full used
  let bits := indexWidth 32 full.length q
  let t := treeSize q full
  let C := capacityWords 8192 full.length q t
  let P := packedCapacityWords q C bits
  let I := ordinaryWords full.length q t
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  let code := left ++ programAt left.length ++ right
  let lead := left ++ PA06A19PrepareFiniteInit032.programAt left.length
  let mid := packingRun rom code (PA06A19PrepareFiniteInit032.clock full.length q t) before
  let after := packingRun rom code (clock full.length q t) before
  have hlead : lead.length = left.length + 29 := by
    simp only [lead, List.length_append, PA06A19PrepareFiniteInit032.programAt_length]
  have heq : code = lead ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right := by
    simp only [code, programAt, lead, List.append_assoc]
  have hc : WordsFit bits (packingCode (lead ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right)) := by
    rw [← heq]
    exact hcode
  have hp : Fits bits (5 * (lead ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right).length) := by
    rw [← heq]
    exact hpcCode
  have hd := clear_data q full used hq left right before hpc ha hbank hcode hpcCode
  rcases hd with ⟨hview, hbounded, hframe, haddress, hmidpc, hmidactive⟩
  change mid.register .address = before.register .address at haddress
  have hbase : (mid.register .address).toNat = CB := by
    rw [haddress]
    exact hbank.base
  have hmidfit : Fits bits (5 * lead.length) := by
    apply (show 5 * lead.length ≤ 5 * code.length from ?_).trans_lt hpcCode
    rw [heq]
    simp only [List.length_append, PA06A19PrepareFiniteClear025.clearVirtual_length]
    omega
  have hmidpcWord : mid.pc = BitVec.ofNat bits (5 * lead.length) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmidfit, hlead]
    exact hmidpc
  have hr := actual_virtual_room q full hq
  have hfit : Fits bits ((mid.register .address).toNat + 38) := by
    rw [hbase]
    exact hr.1
  have hrun : after = packingRun rom
      (lead ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right) 22 mid := by
    calc
      after = packingRun rom code 22 mid :=
        wordRun_add rom code (PA06A19PrepareFiniteInit032.clock full.length q t) 22 before
      _ = packingRun rom (lead ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right) 22 mid :=
        congrArg (fun body => packingRun rom body 22 mid) heq
  have hbody : after = executeOps rom PA06A19PrepareFiniteClear025.clearVirtual mid :=
    hrun.trans (PA06A19PrepareFiniteClear025Virtual.body_run rom lead right mid hc hp hmidpcWord hmidactive)
  have hlower (point : BitVec bits) (hpoint : point.toNat < CB) : after.heap point = mid.heap point := by
    rw [hrun]
    exact PA06A19PrepareFiniteInit038VirtualFrame.body_lower_frame rom lead right mid hc hp
      hmidpcWord hmidactive hfit point (by rw [hbase]; exact hpoint)
  have hregionCB : 4 + (P + I) ≤ CB :=
    PA06A19PrepareFiniteClear031Setup.clear_end_le_control full.length q t P
  have hregion : 4 + (P + I) ≤ (mid.register .address).toNat := by
    rw [hbase]
    exact hregionCB
  have hC := PA06A19PreparePackedView013.oldCapacity_le_capacity full.length q t hq
  have hI : 0 < I := by dsimp only [I, ordinaryWords]; omega
  have hCBfit : Fits bits CB := (Nat.le_add_right CB 38).trans_lt hr.1
  have hviewAfter (a : Nat) (ha0 : a < PA06A19PreparePackedView013.oldCapacity full.length q t + I) :
      PA06A19PreparePackedView013.view q (PA06A19PreparePackedView013.oldCapacity full.length q t)
        C (4 + P) after.heap a = 0 := by
    rw [hrun, PA06A19PrepareFiniteInit038VirtualFrame.body_view rom lead right mid hc hp
      hmidpcWord hmidactive hfit q (PA06A19PreparePackedView013.oldCapacity full.length q t) C I hq
      (PA17PackingBounds043.bits_pos full.length q) (PA17PackingBounds043.width_le_bits full.length q)
      hC hI hregion a ha0]
    exact hview a ha0
  have hboundAfter : CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap after.heap)) := by
    intro a ha0
    rw [PA06A19PrepareFiniteInit038VirtualFrame.unpack_lower_frame q C CB mid.heap after.heap hq
      (PA17PackingBounds043.bits_pos full.length q) (PA17PackingBounds043.width_le_bits full.length q)
      (by change 4 + P < CB; omega) hCBfit hlower a ha0]
    exact hbounded a ha0
  have hheaderMid : PA06A19PrepareRuntimePacked016.Header q mid.heap := by
    have hh := PA06A19PrepareFiniteInit032.actual_init_header q full used hq left
      (PA06A19PrepareFiniteClear025.clearVirtual ++ right) before hpc ha hbank hheader
      (by simpa only [programAt, List.append_assoc] using hcode)
      (by simpa only [programAt, List.append_assoc] using hpcCode)
    simpa only [mid, code, programAt, List.append_assoc] using hh
  have hsmall : Fits bits 3 :=
    (by decide : 3 ≤ 8).trans_lt (PA17WordBounds023.small_word_fit full.length q)
  have hheaderCell (n : Nat) (hn : n < 4) :
      after.heap (BitVec.ofNat bits n) = mid.heap (BitVec.ofNat bits n) := by
    apply hlower
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((by omega : n ≤ 3).trans_lt hsmall)]
    have hlow : 4 ≤ CB := (Nat.le_add_right 4 (P + I)).trans (by rw [← hbase]; exact hregion)
    omega
  have hheaderAfter : PA06A19PrepareRuntimePacked016.Header q after.heap := by
    constructor
    · rw [hheaderCell 0 (by decide)]; exact hheaderMid.width
    · rw [hheaderCell 1 (by decide)]; exact hheaderMid.mask
    · rw [hheaderCell 2 (by decide)]; exact hheaderMid.ones
    · rw [hheaderCell 3 (by decide)]; exact hheaderMid.wordBits
  have hafterpc : after.pc.toNat = 5 * (left.length + 51) := by
    rw [hbody, executeOps_pc rom _ mid PA06A19PrepareFiniteClear025.clearVirtual_straight,
      hmidpcWord, PA06A19PrepareFiniteClear025.clearVirtual_length, BitVec.ofNat_add_ofNat,
      BitVec.toNat_ofNat]
    have he : 5 * lead.length + 5 * 22 = 5 * (left.length + 51) := by rw [hlead]; omega
    rw [he]
    exact Nat.mod_eq_of_lt ((show 5 * (left.length + 51) ≤ 5 * code.length from by
      simp only [code, List.length_append, programAt_length]
      omega).trans_lt hpcCode)
  dsimp only
  change (∀ a < PA06A19PreparePackedView013.oldCapacity full.length q t + I,
      PA06A19PreparePackedView013.view q (PA06A19PreparePackedView013.oldCapacity full.length q t)
        C (4 + P) after.heap a = 0) ∧
    CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap after.heap)) ∧
    PA06A19PrepareRuntimePacked016.Header q after.heap ∧
    after.register .address = before.register .address ∧
    after.pc.toNat = 5 * (left.length + 51) ∧ after.halted = false ∧
    (∀ slot, 32 ≤ slot → slot < 39 → after.heap (before.register .address + BitVec.ofNat bits slot) = 0) ∧
    (∀ point : BitVec bits, point.toNat < CB → after.heap point = mid.heap point) ∧
    (∀ point : BitVec bits, (point.toNat < 4 ∨ 4 + (P + I) ≤ point.toNat) →
      (∀ slot ∈ PA06A19PrepareFiniteClear025Virtual.virtualSlots,
        point ≠ before.register .address + BitVec.ofNat bits slot) → after.heap point = before.heap point)
  refine ⟨hviewAfter, hboundAfter, hheaderAfter, ?_, hafterpc, ?_, ?_, hlower, ?_⟩
  · rw [hbody, PA06A19PrepareFiniteClear025.clearVirtual_base]
    exact haddress
  · rw [hbody]
    exact (executeOps_halted rom _ mid).trans hmidactive
  · intro slot hlo hhi
    rw [hbody, ← haddress]
    exact PA06A19PrepareFiniteClear025.clearVirtual_zero rom mid slot hlo hhi
  · intro point hout hslots
    rw [hrun, PA06A19PrepareFiniteClear025Virtual.body_frame rom lead right mid hc hp hmidpcWord hmidactive
      point (by
        intro slot hslot he
        exact hslots slot hslot (he.trans (congrArg (fun base => base + BitVec.ofNat bits slot) haddress)))]
    exact hframe point hout

/-- The original permanent scalar bank and high cache are preserved outside
the seven actual VM stores. This numerical frame needs no caller cache values. -/
theorem actual_permanent_frame (hheader : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (point : BitVec (indexWidth 32 full.length q))
    (hout : let t := treeSize q full
      let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
      let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
      (CB ≤ point.toNat ∧ point.toNat < CB + 32) ∨ CB + 39 ≤ point.toNat) :
    (packingRun (controllerInput q full used) (left ++ programAt left.length ++ right)
      (clock full.length q (treeSize q full)) before).heap point = before.heap point := by
  let bits := indexWidth 32 full.length q
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  rcases actual_data q full used hq left right before hpc ha hbank hcode hpcCode hheader with
    ⟨_, _, _, _, _, _, _, _, hframe⟩
  apply hframe point
  · have he := PA06A19PrepareFiniteClear031Setup.clear_end_le_control full.length q t P
    exact Or.inr (he.trans (by change (CB ≤ point.toNat ∧ point.toNat < CB + 32) ∨ CB + 39 ≤ point.toNat at hout; omega))
  · intro slot hslot heq
    have hslotBounds : 32 ≤ slot ∧ slot ≤ 38 := by
      simp only [PA06A19PrepareFiniteClear025Virtual.virtualSlots, List.mem_cons, List.not_mem_nil, or_false] at hslot
      omega
    have hfit := (actual_virtual_room q full hq).1
    have hs : Fits bits slot := (by omega : slot ≤ CB + 38).trans_lt hfit
    have hsum : Fits bits (CB + slot) := (by omega : CB + slot ≤ CB + 38).trans_lt hfit
    have hn := congrArg BitVec.toNat heq
    rw [BitVec.toNat_add, hbank.base, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs,
      Nat.mod_eq_of_lt hsum] at hn
    change (CB ≤ point.toNat ∧ point.toNat < CB + 32) ∨ CB + 39 ≤ point.toNat at hout
    omega

/-- Every strict-clock prefix fetches and decodes a real instruction and
uses the original allocation. The clear/VM boundary uses the actual PC. -/
theorem actual_prefix_access (count : Nat) (hc : count < clock full.length q (treeSize q full)) :
    let code := left ++ programAt left.length ++ right
    let actual := packingRun (controllerInput q full used) code count before
    actual.halted = false ∧ actual.pc.toNat + 4 < (packingCode code).length ∧
    ∃ op, PackingOp.decode (fetch code actual) = some op ∧
      packingAccessFits (controllerInput q full used)
        (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)) actual op := by
  let rom := controllerInput q full used
  let t := treeSize q full
  let bits := indexWidth 32 full.length q
  let code := left ++ programAt left.length ++ right
  let clearClock := PA06A19PrepareFiniteInit032.clock full.length q t
  by_cases hclear : count < clearClock
  · have hh := PA06A19PrepareFiniteInit032.actual_init_prefix_access q full used hq left
      (PA06A19PrepareFiniteClear025.clearVirtual ++ right) before hpc ha hbank
      (by simpa only [programAt, List.append_assoc] using hcode)
      (by simpa only [programAt, List.append_assoc] using hpcCode) count hclear
    simpa only [programAt, List.append_assoc, fetch, physicalFetch] using hh
  · let lead := left ++ PA06A19PrepareFiniteInit032.programAt left.length
    let mid := packingRun rom code clearClock before
    have hlead : lead.length = left.length + 29 := by
      simp only [lead, List.length_append, PA06A19PrepareFiniteInit032.programAt_length]
    have heq : code = lead ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right := by
      simp only [code, programAt, lead, List.append_assoc]
    have hd := clear_data q full used hq left right before hpc ha hbank hcode hpcCode
    have haddress : mid.register .address = before.register .address := hd.2.2.2.1
    have hmidfit : Fits bits (5 * lead.length) := by
      apply (show 5 * lead.length ≤ 5 * code.length from ?_).trans_lt hpcCode
      rw [heq]
      simp only [List.length_append, PA06A19PrepareFiniteClear025.clearVirtual_length]
      omega
    have hmidpc : mid.pc = BitVec.ofNat bits (5 * lead.length) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmidfit, hlead]
      exact hd.2.2.2.2.1
    have hr := actual_virtual_room q full hq
    have hb : (mid.register .address).toNat =
        PA06A19PrepareControlBank017.controlBase full.length q t
          (packedCapacityWords q (capacityWords 8192 full.length q t) bits) := by
      rw [haddress]
      exact hbank.base
    have hcount : count < clearClock + 22 := by
      change count < clearClock + 22 at hc
      exact hc
    exact prefix_access_out rom (PA06A19PrepareRuntimeHeader019.heapWords full.length q t)
      code (packingRun rom code count before)
      (joined_virtual_prefix_access rom (PA06A19PrepareRuntimeHeader019.heapWords full.length q t)
        code lead right before mid clearClock count heq rfl hcode hpcCode
        hmidpc hd.2.2.2.2.2 (by rw [hb]; exact hr.1) (by rw [hb]; exact hr.2)
        (by omega) hcount)

end Actual

/-- Real dynamic events, charging both the clear's runtime loop and all22
VM instructions. No terminal HALT is executed by this embedded block. -/
theorem actual_trace_bound (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q)) :
    (packingDynamicTrace (controllerInput q full used) (left ++ programAt left.length ++ right)
      (clock full.length q (treeSize q full)) before).length ≤
        84 * PA06A19PrepareFiniteInit032.clearLength full.length q (treeSize q full) + 552 := by
  exact (packingDynamicTrace_length_le _ _ _ before).trans_eq (by rw [clock_eq]; omega)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareClearVM045

module
public import PaperProofs.Structure.PA17_GivenWord_031c
import Mathlib.Tactic.IntervalCases

/-! Shared actual import/minimum/normalizer/export numeric certificates for
the full table and two-row builders, with the original capacity certificates. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17GivenWord031d

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022 PA17GivenWord031a PA17TagBridge001

theorem copyWords_numeric_of_addresses (B heapWords size source target : Nat) (rom : PhysicalROM)
    (hs : ∀ index < size, AddressBound B heapWords (source + index))
    (ht : ∀ index < size, AddressBound B heapWords (target + index))
    (state : State) (hi : RegistersLE (2 * B) state) (hv : ∀ index < size, state.heap (source + index) ≤ 2 * B) :
    NumericSafe (2 * B) heapWords rom ((IndexedCellRAM.copyWords source target size).map Op.base) state :=
  copyIndices_numeric B heapWords size source target rom (List.range size) (fun _ hm => List.mem_range.mp hm) hs ht state hi hv

theorem toTagFirst_numeric (B heapWords size source target : Nat) (rom : PhysicalROM)
    (hs : AddressBound B heapWords (source + size)) (ht : AddressBound B heapWords (target + size))
    (hd : DisjointSlots size source target) (state : State) (hi : RegistersLE (2 * B) state)
    (hv : ∀ offset ≤ size, state.heap (source + offset) ≤ 2 * B) :
    NumericSafe (2 * B) heapWords rom (toTagFirst size source target) state := by
  have hsa := hs.1
  have hsb := hs.2
  have hta := ht.1
  have htb := ht.2
  have hp := copyWords_numeric_of_addresses B heapWords size source (target + 1) rom
    (by intro index hi; exact ⟨by omega, by omega⟩) (by intro index hi; exact ⟨by omega, by omega⟩)
    state hi (by intro offset ho; exact hv offset ho.le)
  rw [toTagFirst, List.map_append]
  apply NumericSafe.append _ _ rom _ _ state hp
  apply copyWords_numeric_of_addresses B heapWords 1 (source + size) target rom
    (by intro index hi; exact ⟨by omega, by omega⟩) (by intro index hi; exact ⟨by omega, by omega⟩)
    _ (hp.final _ _ _ _ _)
  intro offset ho
  have he : offset = 0 := by omega
  subst offset
  simp only [Nat.add_zero]
  rw [execute_base, IndexedCellRAM.copyWords_frame rom.semantic source (target + 1) size state (source + size) (by
    intro index hi
    simpa only [Nat.add_assoc] using hd size le_rfl (1 + index) (by omega))]
  exact hv size le_rfl

theorem toTagLast_numeric (B heapWords size source target : Nat) (rom : PhysicalROM)
    (hs : AddressBound B heapWords (source + size)) (ht : AddressBound B heapWords (target + size))
    (hd : DisjointSlots size source target) (state : State) (hi : RegistersLE (2 * B) state)
    (hv : ∀ offset ≤ size, state.heap (source + offset) ≤ 2 * B) :
    NumericSafe (2 * B) heapWords rom (toTagLast size source target) state := by
  have hsa := hs.1
  have hsb := hs.2
  have hta := ht.1
  have htb := ht.2
  have hp := copyWords_numeric_of_addresses B heapWords size (source + 1) target rom
    (by intro index hi; exact ⟨by omega, by omega⟩) (by intro index hi; exact ⟨by omega, by omega⟩)
    state hi (by intro offset ho; simpa only [Nat.add_assoc] using hv (1 + offset) (by omega))
  rw [toTagLast, List.map_append]
  apply NumericSafe.append _ _ rom _ _ state hp
  apply copyWords_numeric_of_addresses B heapWords 1 source (target + size) rom
    (by intro index hi; exact ⟨by omega, by omega⟩) (by intro index hi; exact ⟨by omega, by omega⟩)
    _ (hp.final _ _ _ _ _)
  intro offset ho
  have he : offset = 0 := by omega
  subst offset
  simp only [Nat.add_zero]
  rw [execute_base, IndexedCellRAM.copyWords_frame rom.semantic (source + 1) target size state source (by
    intro index hi
    simpa only [Nat.add_zero] using hd 0 (Nat.zero_le _) index hi.le)]
  simpa only [Nat.add_zero] using hv 0 (Nat.zero_le _)

structure Layout (B heapWords q capWords size work good acc parents stage : Nat)
    extends PA17GivenWord031c.Layout B heapWords q capWords size work parents stage where
  good_region : good + size < capWords
  accumulator : acc + size + 1 ≤ capWords

theorem minimumPass_numeric_of_capacity (B heapWords q capWords size work good : Nat) (rom : PhysicalROM)
    (hcapAccess : capWords ≤ heapWords) (hcapBound : capWords ≤ B) (hq : q ≤ B)
    (hwork : work + size < capWords) (hgood : good + size < capWords)
    (state : State) (hi : RegistersLE (2 * B) state)
    (hc : CapacityThroughout q capWords rom (PA17UniformCell002.minimumPass size work good) state) :
    NumericSafe (2 * B) heapWords rom (PA17UniformCell002.minimumPass size work good) state := by
  apply numeric_flatMap_of_capacity (2 * B) heapWords q capWords rom
    (PA17UniformCell002.minimumBlock work good) (List.range size) _ state hi hc
  intro node hn before hregister hcapacity
  have hnode := List.mem_range.mp hn
  have hw : work + node < capWords := by omega
  have hg : good + 1 + node < capWords := by omega
  exact minimumBlock_numeric B heapWords work good node rom
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ before hregister
    ((hcapacity _ hw).trans (by omega)) ((hcapacity _ hg).trans (by omega))

theorem intersectionProgram_numeric_of_capacity (B heapWords q capWords size work good acc parents stage : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords q capWords size work good acc parents stage)
    (hd : PA17GivenWord031b.InternalData size rom) (state : State) (hi : RegistersLE (2 * B) state)
    (hc : CapacityThroughout q capWords rom (PA17UniformCell002.intersectionProgram size work good acc) state) :
    NumericSafe (2 * B) heapWords rom (PA17UniformCell002.intersectionProgram size work good acc) state := by
  rw [PA17UniformCell002.intersectionProgram] at hc ⊢
  have hmn := capacityThroughout_left q capWords rom _ _ state hc
  have hm := capacityThroughout_left q capWords rom _ _ state hmn
  have hn := capacityThroughout_right q capWords rom _ _ state hmn
  have hmin := minimumPass_numeric_of_capacity B heapWords q capWords size work good rom
    hl.cap_access hl.cap_bound hl.q_bound hl.work_region hl.good_region state hi hm
  have hnorm := PA17GivenWord031b.program_numeric_of_capacity B heapWords q capWords size work acc rom
    ⟨hl.cap_access, hl.cap_bound, hl.q_bound, hl.size_bound, by have := hl.work_region; omega, hl.accumulator⟩ hd
    _ (hmin.final _ _ _ _ _) hn
  have hleft := NumericSafe.append _ _ rom _ _ state hmin hnorm
  apply NumericSafe.append _ _ rom _ _ state hleft
  have hb := capacityThroughout_right q capWords rom _ _ state hc 0 (Nat.zero_le _)
  have hwa := hl.work_region
  have hga : good < capWords := by have := hl.good_region; omega
  exact tagTail_numeric B heapWords size work good rom
    ⟨hwa.trans_le hl.cap_access, hwa.le.trans hl.cap_bound⟩
    ⟨hga.trans_le hl.cap_access, hga.le.trans hl.cap_bound⟩ _ (hleft.final _ _ _ _ _)
    ((hb _ hwa).trans (by have := hl.q_bound; omega)) ((hb _ hga).trans (by have := hl.q_bound; omega))

theorem kernelProgram_numeric_of_capacity (B heapWords q capWords size work good acc parents stage : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords q capWords size work good acc parents stage)
    (hd : PA17GivenWord031b.InternalData size rom) (state : State) (hi : RegistersLE (2 * B) state)
    (hs : state.heap stage ≤ size) (hp : ∀ encoded ≤ size, state.heap (parents + encoded) ≤ size)
    (hc : CapacityThroughout q capWords rom (PA17UniformCell002.kernelProgram size work good acc parents stage) state) :
    NumericSafe (2 * B) heapWords rom (PA17UniformCell002.kernelProgram size work good acc parents stage) state := by
  rw [PA17UniformCell002.kernelProgram] at hc ⊢
  have he := PA17GivenWord031c.extensionProgram_numeric B heapWords q capWords size work parents stage rom
    hl.toLayout state hi (hc 0 (Nat.zero_le _)) hs hp
  apply NumericSafe.append _ _ rom _ _ state he
  exact intersectionProgram_numeric_of_capacity B heapWords q capWords size work good acc parents stage rom hl hd
    _ (he.final _ _ _ _ _) (capacityThroughout_right q capWords rom _ _ state hc)

theorem cell_numeric_of_capacity (B heapWords q capWords size work good bad acc parents stage output : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords q capWords size work good acc parents stage)
    (hd : PA17GivenWord031b.InternalData size rom)
    (hbad : bad + size < capWords) (hout : output + size < capWords)
    (hworkbad : DisjointSlots size bad work) (hworkout : DisjointSlots size work output)
    (hparents : capWords ≤ parents) (hstage : capWords ≤ stage)
    (state : State) (hi : RegistersLE (2 * B) state)
    (hs : state.heap stage ≤ size) (hp : ∀ encoded ≤ size, state.heap (parents + encoded) ≤ size)
    (hc : CapacityThroughout q capWords rom
      (toTagLast size bad work ++ PA17UniformCell002.kernelProgram size work good acc parents stage ++ toTagFirst size work output) state) :
    NumericSafe (2 * B) heapWords rom
      (toTagLast size bad work ++ PA17UniformCell002.kernelProgram size work good acc parents stage ++ toTagFirst size work output) state := by
  have hb := hc 0 (Nat.zero_le _)
  have hcbase : AddressBound B heapWords (work + size) :=
    ⟨hl.work_region.trans_le hl.cap_access, hl.work_region.le.trans hl.cap_bound⟩
  have him := toTagLast_numeric B heapWords size bad work rom
    ⟨hbad.trans_le hl.cap_access, hbad.le.trans hl.cap_bound⟩ hcbase hworkbad state hi (by
      intro offset ho
      exact (hb _ (by omega)).trans (by have := hl.q_bound; omega))
  let copied := execute rom.semantic (toTagLast size bad work) state
  have hf (address : Nat) (ha : capWords ≤ address) : copied.heap address = state.heap address := by
    apply toTagLast_frame
    intro offset ho
    have hw := hl.work_region
    omega
  have hkcap := capacityThroughout_right q capWords rom _ _ state (capacityThroughout_left q capWords rom _ _ state hc)
  have hk := kernelProgram_numeric_of_capacity B heapWords q capWords size work good acc parents stage rom hl hd copied
    (him.final _ _ _ _ _) (by rw [hf stage hstage]; exact hs)
    (by intro encoded he; rw [hf _ (by omega)]; exact hp encoded he) hkcap
  have hleft := NumericSafe.append _ _ rom _ _ state him hk
  apply NumericSafe.append _ _ rom _ _ state hleft
  have hbefore := capacityThroughout_right q capWords rom _ _ state hc 0 (Nat.zero_le _)
  apply toTagFirst_numeric B heapWords size work output rom hcbase
    ⟨hout.trans_le hl.cap_access, hout.le.trans hl.cap_bound⟩ hworkout _ (hleft.final _ _ _ _ _)
  intro offset ho
  have hwork := hl.work_region
  exact (hbefore _ (by omega)).trans (by have := hl.q_bound; omega)

end PaperProofs.Structure.LaminarTree.PA17GivenWord031d

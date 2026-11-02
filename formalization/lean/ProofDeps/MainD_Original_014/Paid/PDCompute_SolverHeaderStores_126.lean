module

public import Paid.PDCompute_SolverInitialStore_125

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute storeSlot storeSlotResult)

/-- Analysis notation for the existing literal3-op stores. This is NOT
a new ISA command, and every occurrence expands to the original code. -/
def headerStoresCode : List (ℕ × Register) → List Instruction
  | [] => []
  | spec::specs => storeSlot spec.1 spec.2++headerStoresCode specs

theorem headerStoresCode_cons_length (spec : ℕ × Register) (specs : List (ℕ × Register)) :
    (headerStoresCode (spec::specs)).length=3+(headerStoresCode specs).length := by
  rw [headerStoresCode,List.length_append]
  rfl

/-- All successful prefixes of a real finite store sequence preserve
one actual bit budget and modify only Header48, without prefilled cells. -/
theorem headerStores_prefix_resources (specs : List (ℕ × Register)) (input : List Cell) (before after : State)
    (base budget count : ℕ) (safe : RootD27.Bits.SafeBits before budget)
    (fresh : before.register .fresh=.natural base)
    (valid : ∀ spec ∈ specs,spec.1 < headerWords ∧ spec.2 ≠ .address)
    (addressBits : 1+natBits (base+headerWords) ≤ budget)
    (pcBits : natBits (before.pc+(headerStoresCode specs).length) ≤ budget)
    (countBound : count ≤ (headerStoresCode specs).length)
    (executed : linearExecute input ((headerStoresCode specs).take count) before=some after) :
    RegionMemory before after (cellRegion base headerWords) ∧ RootD27.Bits.SafeBits after budget := by
  induction specs generalizing before count with
  | nil =>
    have same : before=after := by
      simpa only [headerStoresCode,List.take_nil,linearExecute,Option.some.injEq] using executed
    subst after
    exact ⟨RegionMemory.refl before _,safe⟩
  | cons spec specs ih =>
    have firstValid:=valid spec (by simp)
    have tailValid : ∀ item ∈ specs,item.1 < headerWords ∧ item.2 ≠ .address :=
      fun item member => valid item (by simp only [List.mem_cons]; exact Or.inr member)
    have lengthEq:=headerStoresCode_cons_length spec specs
    have firstAddress : 1+natBits (base+spec.1) ≤ budget := by
      have mono:=natBits_mono (Nat.add_le_add_left (Nat.le_of_lt firstValid.1) base)
      omega
    have firstPC : natBits (before.pc+3) ≤ budget :=
      (natBits_mono (by rw [lengthEq]; omega : before.pc+3 ≤ before.pc+(headerStoresCode (spec::specs)).length)).trans pcBits
    by_cases short : count ≤ 3
    · have takeEq : (headerStoresCode (spec::specs)).take count=(storeSlot spec.1 spec.2).take count :=
        List.take_append_of_le_length short
      rw [takeEq] at executed
      exact ⟨initialStore_prefix_region input before after base spec.1 count spec.2 fresh firstValid.2 firstValid.1 short executed,
        RootD27.Bits.storeSlot_prefix_safe input before after base spec.1 budget count spec.2 safe fresh firstValid.2
          firstAddress firstPC short executed⟩
    · let middle:=storeSlotResult before base spec.1 spec.2
      have firstRun:=PDLower.CalibrationCompute.storeSlot_execute input before base spec.1 spec.2 fresh firstValid.2
      have firstMemory : RegionMemory before middle (cellRegion base headerWords) :=
        initialStore_prefix_region input before middle base spec.1 3 spec.2 fresh firstValid.2 firstValid.1 (le_refl _) firstRun
      have middleSafe:=RootD27.Bits.storeSlotResult_safe before base spec.1 budget spec.2 safe firstAddress firstPC
      have middleFresh : middle.register .fresh=.natural base := by
        simpa only [middle,storeSlotResult,Function.update_of_ne (by decide : (.fresh : Register) ≠ .address)] using fresh
      have middlePC : middle.pc=before.pc+3 := rfl
      have split : (headerStoresCode (spec::specs)).take count=
          storeSlot spec.1 spec.2++(headerStoresCode specs).take (count-3) := by
        change ((storeSlot spec.1 spec.2)++headerStoresCode specs).take count=_
        rw [List.take_append,List.take_of_length_le (by change 3 ≤ count; omega)]
        rfl
      rw [split,PDLower.CalibrationCompute.linearExecute_append,firstRun,Option.bind_some] at executed
      have tailCount : count-3 ≤ (headerStoresCode specs).length := by rw [lengthEq] at countBound; omega
      have tailPC : natBits (middle.pc+(headerStoresCode specs).length) ≤ budget := by
        simpa only [middlePC,lengthEq,Nat.add_assoc] using pcBits
      have tail:=ih middle (count-3) middleSafe middleFresh tailValid tailPC tailCount executed
      exact ⟨firstMemory.trans tail.1,tail.2⟩

end PDCompute.Solver

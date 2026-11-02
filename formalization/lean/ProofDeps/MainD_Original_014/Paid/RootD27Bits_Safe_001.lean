module

public import Paid.RootD27Core_Arguments_001
public import PaperProofs.Paid.PDROC_DataBits_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Bits

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

/-- The ORIGINAL complete stateCellBits, including every register, live
heap address and value, output cell and actual pc. -/
def SafeBits (state : State) (budget : ℕ) : Prop :=
  ∀ bits∈stateCellBits state,bits≤budget

theorem SafeBits.register {state : State} {budget : ℕ} (safe : SafeBits state budget) (target : Register) :
    (state.register target).bits≤budget := by
  apply safe
  simp only [stateCellBits,List.append_assoc,List.mem_append]
  apply Or.inl
  apply List.mem_map.mpr
  refine ⟨target,?_,rfl⟩
  cases target <;> simp [registers]

theorem SafeBits.address {state : State} {budget : ℕ} (safe : SafeBits state budget)
    (address : ℕ) (live : address∈state.live) : natBits address≤budget := by
  apply safe
  simp only [stateCellBits,List.append_assoc,List.mem_append]
  apply Or.inr;apply Or.inl
  exact List.mem_flatMap.mpr ⟨address,Finset.mem_toList.mpr live,by simp⟩

theorem SafeBits.heap {state : State} {budget : ℕ} (safe : SafeBits state budget)
    (address : ℕ) (live : address∈state.live) : (state.heap address).bits≤budget := by
  apply safe
  simp only [stateCellBits,List.append_assoc,List.mem_append]
  apply Or.inr;apply Or.inl
  exact List.mem_flatMap.mpr ⟨address,Finset.mem_toList.mpr live,by simp⟩

theorem SafeBits.output {state : State} {budget : ℕ} (safe : SafeBits state budget)
    (value : Cell) (member : value∈state.output) : value.bits≤budget := by
  apply safe
  simp only [stateCellBits,List.append_assoc,List.mem_append]
  apply Or.inr;apply Or.inr;apply Or.inl
  exact List.mem_map.mpr ⟨value,member,rfl⟩

theorem SafeBits.pc {state : State} {budget : ℕ} (safe : SafeBits state budget) : natBits state.pc≤budget := by
  apply safe
  simp only [stateCellBits,List.append_assoc,List.mem_append]
  exact Or.inr (Or.inr (Or.inr (by simp)))

theorem SafeBits.of_fields (state : State) (budget : ℕ)
    (register : ∀ target,(state.register target).bits≤budget)
    (address : ∀ location∈state.live,natBits location≤budget)
    (heap : ∀ location∈state.live,(state.heap location).bits≤budget)
    (output : ∀ value∈state.output,value.bits≤budget)
    (pc : natBits state.pc≤budget) : SafeBits state budget := by
  intro bits member
  simp only [stateCellBits,List.append_assoc,List.mem_append] at member
  rcases member with registers|heaps|outputs|counter
  · obtain ⟨target,_,rfl⟩:=List.mem_map.mp registers
    exact register target
  · obtain ⟨location,live,kind⟩:=List.mem_flatMap.mp heaps
    have live':location∈state.live:=Finset.mem_toList.mp live
    simp only [List.mem_cons,List.not_mem_nil,or_false] at kind
    rcases kind with rfl|rfl
    · exact address location live'
    · exact heap location live'
  · obtain ⟨value,inside,rfl⟩:=List.mem_map.mp outputs
    exact output value inside
  · have same:=List.mem_singleton.mp counter
    subst bits
    exact pc

end RootD27.Bits

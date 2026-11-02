module

public import PaperProofs.Structure.PA17_QuerySelection_010b

/-! Every actual selector Op prefix preserves every heap word below private
scratch. This is an instruction-prefix proof, not a final frame extrapolation.
No parent/result correctness, tree ordering, physical-card or capacity-vector
premise is required for this Nat-heap frame: all stores are at scratch+Nat. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QuerySelectionSafety020

open IndexedRAM IndexedClosureRAM AlgorithmClaims UniformFreeTableSafety

def readOnly : Op → Bool
  | .base (.storeHeap _ _) => false
  | _ => true

theorem readOnly_op_heap (rom : ROM) (op : Op) (hread : readOnly op = true) (state : State) :
    (Op.execute rom op state).heap = state.heap := by
  cases op with
  | subtract _ _ _ => rfl
  | base instruction =>
    cases instruction <;> first | rfl | cases hread

theorem readOnly_execute_heap (rom : ROM) (program : List Op)
    (hread : ∀ op ∈ program, readOnly op = true) (state : State) :
    (execute rom program state).heap = state.heap := by
  induction program generalizing state with
  | nil => rfl
  | cons op later ih =>
    rw [IndexedClosureRAM.execute, ih (fun item hi => hread item (List.mem_cons_of_mem _ hi))]
    exact readOnly_op_heap rom op (hread op List.mem_cons_self) state

theorem readOnly_prefixFrame (rom : ROM) (program : List Op)
    (hread : ∀ op ∈ program, readOnly op = true) (address : Nat) : PrefixFrame rom program address := by
  intro state count _
  rw [readOnly_execute_heap rom (program.take count)
    (fun op ho => hread op (List.mem_of_mem_take ho)) state]

theorem parentBlock_prefixFrame (rom : ROM) (countBase payloadPointer childBase node address : Nat)
    (ha : address < childBase) :
    PrefixFrame rom (PA17QuerySelection010.parentBlock countBase payloadPointer childBase node) address := by
  intro state count hc
  change count ≤ 17 at hc
  by_cases hshort : count < 17
  · interval_cases count <;> rfl
  · have heq : count = (PA17QuerySelection010.parentBlock countBase payloadPointer childBase node).length := by
      rw [PA17QuerySelection010.parentBlock_length]
      omega
    rw [heq, List.take_length]
    exact PA17QuerySelection010.parentBlock_frame rom countBase payloadPointer childBase node state address (by omega)

theorem clearWords_prefixFrame (rom : ROM) (size childBase address : Nat) (ha : address < childBase) :
    PrefixFrame rom (UniformNormalizationRAM.clearWords childBase (size + 1)) address := by
  rw [UniformNormalizationRAM.clearWords]
  apply PrefixFrame.flatMap
  intro index _
  exact UniformFreeTableSafety.clearBlock_prefixFrame rom (childBase + index) address (by omega)

theorem parentProgram_prefixFrame (rom : ROM) (size countBase payloadPointer childBase address : Nat)
    (ha : address < childBase) :
    PrefixFrame rom (PA17QuerySelection010.program size countBase payloadPointer childBase) address := by
  rw [PA17QuerySelection010.program]
  apply PrefixFrame.append rom _ _ address (clearWords_prefixFrame rom size childBase address ha)
  rw [PA17QuerySelection010.pushList]
  exact PrefixFrame.flatMap rom _ _ address (fun node _ => parentBlock_prefixFrame rom countBase payloadPointer childBase node address ha)

theorem preludeTail_prefixFrame (rom : ROM) (payloadPointer address : Nat) (hne : address ≠ payloadPointer) :
    PrefixFrame rom (PA17QuerySelection010b.preludeTail payloadPointer) address := by
  intro state count hc
  change count ≤ 4 at hc
  by_cases hshort : count < 4
  · interval_cases count <;> rfl
  · have heq : count = (PA17QuerySelection010b.preludeTail payloadPointer).length := by change count = 4; omega
    rw [heq, List.take_length, PA17QuerySelection010b.preludeTail_heap, Function.update_of_ne hne]

theorem prelude_prefixFrame (rom : ROM) (size header childBase address : Nat) (ha : address < childBase) :
    PrefixFrame rom (PA17QuerySelection010b.prelude size header (childBase + size + 1)) address := by
  rw [PA17QuerySelection010b.prelude]
  apply PrefixFrame.append rom _ _ address
  · apply PrefixFrame.append rom _ _ address
    · apply readOnly_prefixFrame
      intro op hm
      simp only [PA17QuerySelection010b.preludeStart, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> rfl
    · apply readOnly_prefixFrame
      intro op hm
      have heq := (List.mem_replicate.mp hm).2
      subst op
      rfl
  · exact preludeTail_prefixFrame rom (childBase + size + 1) address (by omega)

theorem descentInit_prefixFrame (rom : ROM) (header address : Nat) :
    PrefixFrame rom (PA17QuerySelection010b.descentInit header) address := by
  apply readOnly_prefixFrame
  intro op hm
  simp only [PA17QuerySelection010b.descentInit, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> rfl

theorem descentBlock_prefixFrame (rom : ROM) (leafBase childBase address : Nat) :
    PrefixFrame rom (PA17QuerySelection010b.block leafBase childBase) address := by
  apply readOnly_prefixFrame
  intro op hm
  simp only [PA17QuerySelection010b.block, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem descentLoop_prefixFrame (rom : ROM) (leafBase childBase fuel address : Nat) :
    PrefixFrame rom (PA17QuerySelection010b.loop leafBase childBase fuel) address := by
  induction fuel with
  | zero =>
    intro state count _
    simp only [PA17QuerySelection010b.loop, List.replicate_zero, List.flatten_nil, List.take_nil, IndexedClosureRAM.execute]
  | succ fuel ih =>
    rw [PA17QuerySelection010b.loop, List.replicate_succ, List.flatten_cons]
    exact PrefixFrame.append rom _ _ address (descentBlock_prefixFrame rom leafBase childBase address) ih

set_option maxRecDepth 10000 in
theorem finish_prefix_heap (rom : ROM) (header payloadPointer toolAddress : Nat) (state : State)
    (count : Nat) (hc : count ≤ (PA17QuerySelection010b.finish header payloadPointer toolAddress).length) :
    (execute rom ((PA17QuerySelection010b.finish header payloadPointer toolAddress).take count) state).heap =
      if count ≤ 10 then state.heap else (execute rom (PA17QuerySelection010b.finish header payloadPointer toolAddress) state).heap := by
  change count ≤ 12 at hc
  interval_cases count <;> rfl

theorem finish_prefixFrame (rom : ROM) (header payloadPointer toolAddress address : Nat) (hne : address ≠ toolAddress) :
    PrefixFrame rom (PA17QuerySelection010b.finish header payloadPointer toolAddress) address := by
  intro state count hc
  rw [finish_prefix_heap rom header payloadPointer toolAddress state count hc]
  split_ifs
  · rfl
  · rw [PA17QuerySelection010b.finish_heap, Function.update_of_ne hne]

theorem core_prefixFrame (rom : ROM) (size countBase leafBase header childBase address : Nat)
    (ha : address < childBase) :
    PrefixFrame rom (PA17QuerySelection010b.core size countBase leafBase header childBase) address := by
  rw [PA17QuerySelection010b.core]
  apply PrefixFrame.append rom _ _ address
  · apply PrefixFrame.append rom _ _ address
    · exact PrefixFrame.append rom _ _ address (prelude_prefixFrame rom size header childBase address ha)
        (parentProgram_prefixFrame rom size countBase (childBase + size + 1) childBase address ha)
    · exact descentInit_prefixFrame rom header address
  · exact descentLoop_prefixFrame rom leafBase childBase size address

theorem program_prefixFrame (rom : ROM) (size countBase leafBase header childBase address : Nat)
    (ha : address < childBase) :
    PrefixFrame rom (PA17QuerySelection010b.program size countBase leafBase header childBase) address := by
  rw [PA17QuerySelection010b.program]
  exact PrefixFrame.append rom _ _ address (core_prefixFrame rom size countBase leafBase header childBase address ha)
    (finish_prefixFrame rom header (childBase + size + 1) (childBase + size + 2) address (by omega))

theorem program_take_frame (rom : ROM) (size countBase leafBase header childBase : Nat) (state : State)
    (count : Nat) (hc : count ≤ (PA17QuerySelection010b.program size countBase leafBase header childBase).length)
    (address : Nat) (ha : address < childBase) :
    (execute rom ((PA17QuerySelection010b.program size countBase leafBase header childBase).take count) state).heap address =
      state.heap address := program_prefixFrame rom size countBase leafBase header childBase address ha state count hc

theorem program_capacityThroughout (q capWords : Nat) (rom : PhysicalROM)
    (size countBase leafBase header childBase : Nat) (hcapWords : capWords ≤ childBase)
    (state : State) (hcapacity : CapacityPrefixBounded q capWords state.heap) :
    CapacityThroughout q capWords rom (PA17QuerySelection010b.program size countBase leafBase header childBase) state := by
  intro count hc address ha
  rw [program_take_frame rom.semantic size countBase leafBase header childBase state count hc address (ha.trans_le hcapWords)]
  exact hcapacity address ha

end PaperProofs.Structure.LaminarTree.PA17QuerySelectionSafety020

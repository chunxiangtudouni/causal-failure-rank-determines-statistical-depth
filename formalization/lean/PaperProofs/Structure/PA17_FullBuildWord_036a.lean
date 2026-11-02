module
public import PaperProofs.Structure.PA17_QueryDataWord_024c
public import PaperProofs.Structure.PA17_GivenWord_031a

/-! Reuse the actual metadata register proof on zero-extended ROM, while
checking all actual accesses against the shorter original given-tree ROM.
No query-length format assumption is imposed on the original input. -/
@[expose] public section
set_option maxRecDepth 20000
namespace PaperProofs.Structure.LaminarTree.PA17FullBuildWord036a

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022

def AccessSafe (heapWords : Nat) (rom : PhysicalROM) (code : List Op) : Prop :=
  ∀ state : State, ∀ count (hc : count < code.length),
    AccessFits rom heapWords (execute rom.semantic (code.take count) state) code[count]

theorem AccessSafe.append (heapWords : Nat) (rom : PhysicalROM) (left right : List Op)
    (hl : AccessSafe heapWords rom left) (hr : AccessSafe heapWords rom right) :
    AccessSafe heapWords rom (left ++ right) := by
  intro state count hc
  by_cases hs : count < left.length
  · rw [List.take_append_of_le_length hs.le, List.getElem_append_left hs]
    exact hl state count hs
  · obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le (show left.length ≤ count by omega)
    have he : extra < right.length := by rw [List.length_append] at hc; omega
    subst count
    rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      IndexedClosureRAM.execute_append, List.getElem_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left] using hr (execute rom.semantic left state) extra he

theorem AccessSafe.flatMap (heapWords : Nat) (rom : PhysicalROM) (block : Nat → List Op)
    (indices : List Nat) (hblock : ∀ index ∈ indices, AccessSafe heapWords rom (block index)) :
    AccessSafe heapWords rom (indices.flatMap block) := by
  induction indices with
  | nil => intro state count hc; change count < 0 at hc; omega
  | cons head later ih =>
    rw [List.flatMap_cons]
    exact AccessSafe.append _ _ _ _ (hblock head List.mem_cons_self)
      (ih (fun index hi => hblock index (List.mem_cons_of_mem _ hi)))

theorem readBit_access (heapWords N q size node tool : Nat) (rom : PhysicalROM)
    (hinput : 3 + N * q + size * q ≤ rom.input.length) (hn : node < size) (ht : tool < q) :
    AccessSafe heapWords rom (UniformTreeMetadataRAM.readBit N q node tool) := by
  have hm := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hn)
  rw [Nat.succ_mul] at hm
  intro state count hc
  change count < 3 at hc
  interval_cases count <;>
    simp [UniformTreeMetadataRAM.readBit, IndexedClosureRAM.execute, Op.execute, Instruction.execute,
      AccessFits, PhysicalROM.words]
  omega

theorem tail_access (heapWords size base node : Nat) (rom : PhysicalROM)
    (houtput : base + 3 * size + 1 ≤ heapWords) (hinternal : 2 * size ≤ rom.internal.length)
    (hn : node < size) : AccessSafe heapWords rom (UniformTreeMetadataRAM.nodeTail size base node) := by
  intro state count hc
  change count < 13 at hc
  interval_cases count <;>
    simp [UniformTreeMetadataRAM.nodeTail, UniformTreeMetadataRAM.cardAddress,
      UniformTreeMetadataRAM.parentAddress, UniformTreeMetadataRAM.internalAddress,
      IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, PhysicalROM.words]
  all_goals omega

theorem init_access (heapWords : Nat) (rom : PhysicalROM) :
    AccessSafe heapWords rom [.base (.constant .total 0)] := by
  intro state count hc
  change count < 1 at hc
  have he : count = 0 := by omega
  subst count
  trivial

theorem node_access (heapWords N q size base node : Nat) (rom : PhysicalROM)
    (hinput : 3 + N * q + size * q ≤ rom.input.length)
    (houtput : base + 3 * size + 1 ≤ heapWords) (hinternal : 2 * size ≤ rom.internal.length)
    (hn : node < size) : AccessSafe heapWords rom (UniformTreeMetadataRAM.nodeBlock N q size base node) := by
  rw [UniformTreeMetadataRAM.nodeBlock]
  exact AccessSafe.append _ _ _ _ (AccessSafe.append _ _ _ _ (init_access _ _)
    (AccessSafe.flatMap _ _ _ (List.range q) (by
      intro tool ht
      exact readBit_access heapWords N q size node tool rom hinput hn (List.mem_range.mp ht))))
    (tail_access _ _ _ _ _ houtput hinternal hn)

theorem program_access (heapWords N q size base : Nat) (rom : PhysicalROM)
    (hinput : 3 + N * q + size * q ≤ rom.input.length)
    (houtput : base + 3 * size + 1 ≤ heapWords) (hinternal : 2 * size ≤ rom.internal.length) :
    AccessSafe heapWords rom (UniformTreeMetadataRAM.program N q size base) := by
  rw [UniformTreeMetadataRAM.program]
  apply AccessSafe.append
  · intro state count hc
    change count < 3 at hc
    interval_cases count <;>
      simp [UniformNormalizationRAM.clearBlock, UniformTreeMetadataRAM.parentAddress,
        IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits]
    omega
  · exact AccessSafe.flatMap _ _ _ (List.range size) (by
      intro node hn
      exact node_access heapWords N q size base node rom hinput houtput hinternal (List.mem_range.mp hn))

theorem getD_append_zeros (values : List Nat) (count index : Nat) :
    (values ++ List.replicate count 0).getD index 0 = values.getD index 0 := by
  by_cases hi : index < values.length
  · exact List.getD_append values _ 0 index hi
  · calc
      _ = (List.replicate count 0).getD (index - values.length) 0 :=
        List.getD_append_right _ _ _ _ (by omega)
      _ = 0 := List.getElem?_getD_replicate_default_eq 0 count (index - values.length)
      _ = values.getD index 0 := (List.getD_eq_default values 0 (by omega)).symm

theorem queryROM_zero_semantic (q : Nat) (full : List (Finset (Fin q))) :
    (queryROM q full 0 ∅).semantic = (givenTreeROM q full).semantic := by
  suffices hread : (queryROM q full 0 ∅).semantic.read = (givenTreeROM q full).semantic.read from
    congrArg ROM.mk hread
  funext region index
  cases region with
  | input =>
    have hbits : (List.finRange q).map (fun tool => bit (decide (tool ∈ (∅ : Finset (Fin q))))) =
        List.replicate q 0 := by simp [bit]
    change (((givenTreeROM q full).input ++ [0]) ++ _).getD index 0 = _
    rw [hbits, getD_append_zeros]
    exact getD_append_zeros (givenTreeROM q full).input 1 index
  | internal => rfl
  | children => rfl

theorem given_metadata_numeric (q : Nat) (full : List (Finset (Fin q))) (B heapWords base : Nat)
    (hl : PA17QueryDataWord024c.Layout B heapWords q (prepareNormalization q full).indexed.nodes.size base
      (queryROM q full 0 ∅)) (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords (givenTreeROM q full)
      (UniformTreeMetadataRAM.program full.length q (prepareNormalization q full).indexed.nodes.size base) state := by
  have hn := PA17QueryDataWord024c.prepared_program_numeric q full 0 ∅ B heapWords base hl state hi
  constructor
  · intro count hc
    rw [← queryROM_zero_semantic q full]
    exact hn.1 count hc
  · exact program_access heapWords full.length q (prepareNormalization q full).indexed.nodes.size base
      (givenTreeROM q full) (by rw [PA17QueryCounts008.givenTreeROM_input_length]) hl.output_access
      (by simp only [givenTreeROM, List.length_append, List.length_map, List.length_finRange]; omega) state

end PaperProofs.Structure.LaminarTree.PA17FullBuildWord036a

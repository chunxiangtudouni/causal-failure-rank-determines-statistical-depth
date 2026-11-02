module

public import PaperProofs.Structure.PA17_QueryDataWord_024a
public import PaperProofs.Structure.PA17_QueryMetadata_010
public import PaperProofs.Structure.RawTreeOutputWords
import Mathlib.Tactic.IntervalCases

/-! Every register value and actual access in the raw metadata pass.
Cardinality counters are bounded from the actual incidence bits; parent and
degree reads are bounded by the actual serialized original cache. No initial
scratch-heap correctness is required. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryDataWord024c

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022

structure Data (N q size : Nat) (rom : PhysicalROM) extends PA17QueryDataWord024a.Data N q size rom where
  internal_length : rom.internal.length = 2 * size
  internal_word : ∀ address < 2 * size, rom.semantic.read .internal address ≤ size

structure Layout (B heapWords q size base : Nat) (rom : PhysicalROM) : Prop where
  input_bound : rom.input.length ≤ B
  output_bound : base + 3 * size + 1 ≤ B
  output_access : base + 3 * size + 1 ≤ heapWords
  q_bound : q ≤ B

theorem givenTreeROM_internal_word_le (q : Nat) (full : List (Finset (Fin q))) (value : Nat)
    (hv : value ∈ (givenTreeROM q full).internal) : value ≤ (prepareNormalization q full).indexed.nodes.size := by
  simp only [givenTreeROM, List.mem_append] at hv
  rcases hv with hp | hd
  · obtain ⟨node, _, rfl⟩ := List.mem_map.mp hp
    exact UniformNormalizationRAM.encodedNode_le _ _
  · obtain ⟨node, _, rfl⟩ := List.mem_map.mp hd
    exact RawTreeOutputWords.prepared_child_size_le q full node

theorem queryROM_data (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q)) :
    Data full.length q (prepareNormalization q full).indexed.nodes.size (queryROM q full stage used) := by
  have hlen : (givenTreeROM q full).internal.length = 2 * (prepareNormalization q full).indexed.nodes.size := by
    simp only [givenTreeROM, List.length_append, List.length_map, List.length_finRange]
    omega
  refine ⟨PA17QueryDataWord024a.queryROM_data q full stage used, hlen, ?_⟩
  intro address ha
  apply givenTreeROM_internal_word_le q full
  have hi : address < (givenTreeROM q full).internal.length := by rw [hlen]; exact ha
  change (givenTreeROM q full).internal.getD address 0 ∈ (givenTreeROM q full).internal
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem readBit_numeric (B heapWords N q size base node tool : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom) (hn : node < size) (ht : tool < q)
    (state : State) (hi : RegistersLE (2 * B) state) (htotal : state.register .total + 1 ≤ q) :
    NumericSafe (2 * B) heapWords rom (UniformTreeMetadataRAM.readBit N q node tool) state := by
  have hv := hd.node_bit node hn tool ht
  have haddr := PA17QueryDataWord024a.node_address_lt N q size node tool rom hd.toData hn ht
  have hbound := haddr.le.trans hl.input_bound
  have hq := hl.q_bound
  have hone : 1 ≤ B := by have hh := hl.output_bound; omega
  constructor
  · intro k hk r
    have hr := hi r
    change k ≤ 3 at hk
    interval_cases k <;> cases r <;>
      simp [UniformTreeMetadataRAM.readBit, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro k hk
    change k < 3 at hk
    interval_cases k <;>
      simp [UniformTreeMetadataRAM.readBit, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, PhysicalROM.words]
    all_goals omega

theorem readBits_numeric (B heapWords N q size base node : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom) (hn : node < size)
    (tools : List Nat) (hvalid : ∀ tool ∈ tools, tool < q) (state : State) (hi : RegistersLE (2 * B) state)
    (hbudget : state.register .total + tools.length ≤ q) :
    NumericSafe (2 * B) heapWords rom (tools.flatMap (UniformTreeMetadataRAM.readBit N q node)) state := by
  induction tools generalizing state with
  | nil =>
    constructor
    · intro count _
      simpa only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hi
    · intro count hc
      simp only [List.flatMap_nil, List.length_nil, Nat.not_lt_zero] at hc
  | cons tool later ih =>
    rw [List.flatMap_cons]
    have ht := hvalid tool List.mem_cons_self
    have hfirst := readBit_numeric B heapWords N q size base node tool rom hl hd hn ht state hi (by
      simp only [List.length_cons] at hbudget
      omega)
    let after := execute rom.semantic (UniformTreeMetadataRAM.readBit N q node tool) state
    have hafter : after.register .total + later.length ≤ q := by
      have hv := hd.node_bit node hn tool ht
      have he := UniformTreeMetadataRAM.readBit_total rom.semantic N q node tool state
      change after.register .total = _ at he
      simp only [List.length_cons] at hbudget
      omega
    exact NumericSafe.append _ _ rom _ _ state hfirst
      (ih (fun other ho => hvalid other (List.mem_cons_of_mem _ ho)) after (hfirst.final _ _ _ _ _) hafter)

theorem readBits_total_le (N q size node : Nat) (rom : PhysicalROM) (hd : Data N q size rom) (hn : node < size)
    (tools : List Nat) (hvalid : ∀ tool ∈ tools, tool < q) (state : State) :
    (execute rom.semantic (tools.flatMap (UniformTreeMetadataRAM.readBit N q node)) state).register .total ≤
      state.register .total + tools.length := by
  induction tools generalizing state with
  | nil => simp only [List.flatMap_nil, IndexedClosureRAM.execute, List.length_nil, Nat.add_zero, le_refl]
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    have hh := ih (fun other ho => hvalid other (List.mem_cons_of_mem _ ho))
      (execute rom.semantic (UniformTreeMetadataRAM.readBit N q node tool) state)
    rw [UniformTreeMetadataRAM.readBit_total] at hh
    have hv := hd.node_bit node hn tool (hvalid tool List.mem_cons_self)
    simp only [List.length_cons]
    omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem tail_numeric (B heapWords N q size base node : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom) (hn : node < size) (state : State)
    (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (UniformTreeMetadataRAM.nodeTail size base node) state := by
  have ho := hl.output_bound
  have he := hl.output_access
  have hq := hl.q_bound
  have hone : 1 ≤ B := by omega
  have hs : size ≤ B := by omega
  have hcard : base + node < heapWords := by omega
  have hparent : base + size + (node + 1) < heapWords := by omega
  have hinternal : base + 2 * size + 1 + node < heapWords := by omega
  have hcardB : base + node ≤ B := by omega
  have hparentB : base + size + (node + 1) ≤ B := by omega
  have hinternalB : base + 2 * size + 1 + node ≤ B := by omega
  have hparentWord := hd.internal_word node (by omega)
  have hdegreeWord := hd.internal_word (size + node) (by omega)
  have hparentROM : node < rom.internal.length := by rw [hd.internal_length]; omega
  have hdegreeROM : size + node < rom.internal.length := by rw [hd.internal_length]; omega
  constructor
  · intro k hk r
    have hr := hi r
    change k ≤ 13 at hk
    interval_cases k <;> cases r <;>
      simp [UniformTreeMetadataRAM.nodeTail, UniformTreeMetadataRAM.cardAddress,
        UniformTreeMetadataRAM.parentAddress, UniformTreeMetadataRAM.internalAddress,
        IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals (try split_ifs)
    all_goals omega
  · intro k hk
    change k < 13 at hk
    interval_cases k <;>
      simp [UniformTreeMetadataRAM.nodeTail, UniformTreeMetadataRAM.cardAddress,
        UniformTreeMetadataRAM.parentAddress, UniformTreeMetadataRAM.internalAddress,
        IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, PhysicalROM.words]
    all_goals omega

theorem clear_numeric (B heapWords q size base : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (UniformNormalizationRAM.clearBlock (UniformTreeMetadataRAM.parentAddress size base 0)) state := by
  have ho := hl.output_bound
  have he := hl.output_access
  constructor
  · intro k hk r
    have hr := hi r
    change k ≤ 3 at hk
    interval_cases k <;> cases r <;>
      simp [UniformNormalizationRAM.clearBlock, UniformTreeMetadataRAM.parentAddress,
        IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro k hk
    change k < 3 at hk
    interval_cases k <;>
      simp [UniformNormalizationRAM.clearBlock, UniformTreeMetadataRAM.parentAddress,
        IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits]
    all_goals omega

theorem node_numeric (B heapWords N q size base node : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom) (hn : node < size)
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (UniformTreeMetadataRAM.nodeBlock N q size base node) state := by
  let start := execute rom.semantic [.base (.constant .total 0)] state
  let middle := execute rom.semantic ((List.range q).flatMap (UniformTreeMetadataRAM.readBit N q node)) start
  have hinit := PA17QueryDataWord024a.init_numeric B heapWords rom state hi
  have hbits := readBits_numeric B heapWords N q size base node rom hl hd hn (List.range q)
    (fun tool ht => List.mem_range.mp ht) start (hinit.final _ _ _ _ _) (by
      change 0 + (List.range q).length ≤ q
      simp only [List.length_range, Nat.zero_add, le_refl])
  have htail := tail_numeric B heapWords N q size base node rom hl hd hn middle (hbits.final _ _ _ _ _)
  rw [UniformTreeMetadataRAM.nodeBlock]
  exact NumericSafe.append _ _ rom _ _ state (NumericSafe.append _ _ rom _ _ state hinit hbits) htail

theorem nodes_numeric (B heapWords N q size base : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom)
    (nodes : List Nat) (hvalid : ∀ node ∈ nodes, node < size) (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (nodes.flatMap (UniformTreeMetadataRAM.nodeBlock N q size base)) state := by
  induction nodes generalizing state with
  | nil =>
    constructor
    · intro count _
      simpa only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hi
    · intro count hc
      simp only [List.flatMap_nil, List.length_nil, Nat.not_lt_zero] at hc
  | cons node later ih =>
    rw [List.flatMap_cons]
    have hfirst := node_numeric B heapWords N q size base node rom hl hd (hvalid node List.mem_cons_self) state hi
    exact NumericSafe.append _ _ rom _ _ state hfirst
      (ih (fun other ho => hvalid other (List.mem_cons_of_mem _ ho)) _ (hfirst.final _ _ _ _ _))

theorem program_numeric (B heapWords N q size base : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom) (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (UniformTreeMetadataRAM.program N q size base) state := by
  have hclear := clear_numeric B heapWords q size base rom hl state hi
  rw [UniformTreeMetadataRAM.program]
  exact NumericSafe.append _ _ rom _ _ state hclear
    (nodes_numeric B heapWords N q size base rom hl hd (List.range size) (fun _ hn => List.mem_range.mp hn) _ (hclear.final _ _ _ _ _))

theorem prepared_program_numeric (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q))
    (B heapWords base : Nat)
    (hl : Layout B heapWords q (prepareNormalization q full).indexed.nodes.size base (queryROM q full stage used))
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords (queryROM q full stage used)
      (PA17QueryMetadata010.program full.length q (prepareNormalization q full).indexed.nodes.size base) state :=
  program_numeric _ _ _ _ _ _ _ hl (queryROM_data q full stage used) state hi

end PaperProofs.Structure.LaminarTree.PA17QueryDataWord024c

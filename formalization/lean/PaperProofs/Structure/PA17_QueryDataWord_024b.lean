module

public import PaperProofs.Structure.PA17_QueryDataWord_024a
public import PaperProofs.Structure.PA17_LeafLabels_005
import Mathlib.Tactic.IntervalCases

/-! Actual leaf-label prefix numeric safety. Bounds apply to
the original queryROM and arbitrary incoming heap contents. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryDataWord024b

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022
open PA17QueryDataWord024a

theorem leafBit_numeric (B heapWords N q size base node tool : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom) (hn : node < size) (ht : tool < q)
    (state : State) (hi : RegistersLE (2 * B) state) (htotal : state.register .total + 1 ≤ q) :
    NumericSafe (2 * B) heapWords rom (PA17LeafLabels005.bitBlock N q node tool) state := by
  have hnode := hd.node_bit node hn tool ht
  have hnA := node_address_lt N q size node tool rom hd hn ht
  have hnB := hnA.le.trans hl.input_bound
  have hq := hl.q_bound
  have hone := hl.one_bound
  constructor
  · intro k hk r
    have hr := hi r
    change k ≤ 5 at hk
    interval_cases k <;> cases r <;>
      simp [PA17LeafLabels005.bitBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals (try split_ifs)
    all_goals omega
  · intro k hk
    change k < 5 at hk
    interval_cases k <;>
      simp [PA17LeafLabels005.bitBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, PhysicalROM.words]
    all_goals omega

theorem leafBits_numeric (B heapWords N q size base node : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom) (hn : node < size)
    (tools : List Nat) (hvalid : ∀ tool ∈ tools, tool < q) (state : State) (hi : RegistersLE (2 * B) state)
    (hbudget : state.register .total + tools.length ≤ q) :
    NumericSafe (2 * B) heapWords rom (tools.flatMap (PA17LeafLabels005.bitBlock N q node)) state := by
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
    have hfirst := leafBit_numeric B heapWords N q size base node tool rom hl hd hn ht state hi (by
      simp only [List.length_cons] at hbudget
      omega)
    let after := execute rom.semantic (PA17LeafLabels005.bitBlock N q node tool) state
    have hafter : after.register .total + later.length ≤ q := by
      have hv : PA17LeafLabels005.readValue rom.semantic N q node tool ≤ 1 := hd.node_bit node hn tool ht
      have he := PA17LeafLabels005.bitBlock_total rom.semantic N q node tool state
      change after.register .total = _ at he
      simp only [List.length_cons] at hbudget
      omega
    exact NumericSafe.append _ _ rom _ _ state hfirst
      (ih (fun other ho => hvalid other (List.mem_cons_of_mem _ ho)) after (hfirst.final _ _ _ _ _) hafter)

theorem leafBits_total_le (N q size node : Nat) (rom : PhysicalROM) (hd : Data N q size rom) (hn : node < size)
    (tools : List Nat) (hvalid : ∀ tool ∈ tools, tool < q) (state : State) :
    (execute rom.semantic (tools.flatMap (PA17LeafLabels005.bitBlock N q node)) state).register .total ≤
      state.register .total + tools.length := by
  induction tools generalizing state with
  | nil => simp only [List.flatMap_nil, IndexedClosureRAM.execute, List.length_nil, Nat.add_zero, le_refl]
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    have hh := ih (fun other ho => hvalid other (List.mem_cons_of_mem _ ho))
      (execute rom.semantic (PA17LeafLabels005.bitBlock N q node tool) state)
    rw [PA17LeafLabels005.bitBlock_total] at hh
    have hv : PA17LeafLabels005.readValue rom.semantic N q node tool ≤ 1 := hd.node_bit node hn tool (hvalid tool List.mem_cons_self)
    simp only [List.length_cons]
    omega

theorem leafInit_numeric (B heapWords : Nat) (rom : PhysicalROM) (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom [.base (.constant .total 0), .base (.constant .value 0)] state := by
  constructor
  · intro k hk r
    have hr := hi r
    change k ≤ 2 at hk
    interval_cases k <;> cases r <;> simp [IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro k hk
    change k < 2 at hk
    interval_cases k <;> trivial

theorem leafTail_numeric (B heapWords q size base node : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hn : node < size) (state : State)
    (hi : RegistersLE (2 * B) state) (htotal : state.register .total ≤ q) :
    NumericSafe (2 * B) heapWords rom (PA17LeafLabels005.nodeTail base node) state := by
  have haddr : base + node < heapWords := lt_of_lt_of_le (by omega) hl.output_access
  have hbound : base + node ≤ B := (show base + node ≤ base + size from by omega).trans hl.output_bound
  have hq := hl.q_bound
  have hone := hl.one_bound
  constructor
  · intro k hk r
    have hr := hi r
    change k ≤ 8 at hk
    interval_cases k <;> cases r <;>
      simp [PA17LeafLabels005.nodeTail, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals (try split_ifs)
    all_goals omega
  · intro k hk
    change k < 8 at hk
    interval_cases k <;>
      simp [PA17LeafLabels005.nodeTail, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, haddr]

theorem leafNode_numeric (B heapWords N q size base node : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom) (hn : node < size)
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (PA17LeafLabels005.nodeBlock N q base node) state := by
  let start := execute rom.semantic [.base (.constant .total 0), .base (.constant .value 0)] state
  let middle := execute rom.semantic ((List.range q).flatMap (PA17LeafLabels005.bitBlock N q node)) start
  have hinit := leafInit_numeric B heapWords rom state hi
  have hbits := leafBits_numeric B heapWords N q size base node rom hl hd hn (List.range q)
    (fun tool ht => List.mem_range.mp ht) start (hinit.final _ _ _ _ _) (by
      change 0 + (List.range q).length ≤ q
      simp only [List.length_range, Nat.zero_add, le_refl])
  have htotal : middle.register .total ≤ q := by
    have hh := leafBits_total_le N q size node rom hd hn (List.range q) (fun tool ht => List.mem_range.mp ht) start
    simpa only [List.length_range, show start.register .total = 0 from rfl, Nat.zero_add] using hh
  have htail := leafTail_numeric B heapWords q size base node rom hl hn middle (hbits.final _ _ _ _ _) htotal
  rw [PA17LeafLabels005.nodeBlock]
  exact NumericSafe.append _ _ rom _ _ state (NumericSafe.append _ _ rom _ _ state hinit hbits) htail

theorem leafNodes_numeric (B heapWords N q size base : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom)
    (nodes : List Nat) (hvalid : ∀ node ∈ nodes, node < size) (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (nodes.flatMap (PA17LeafLabels005.nodeBlock N q base)) state := by
  induction nodes generalizing state with
  | nil =>
    constructor
    · intro count _
      simpa only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hi
    · intro count hc
      simp only [List.flatMap_nil, List.length_nil, Nat.not_lt_zero] at hc
  | cons node later ih =>
    rw [List.flatMap_cons]
    have hfirst := leafNode_numeric B heapWords N q size base node rom hl hd (hvalid node List.mem_cons_self) state hi
    exact NumericSafe.append _ _ rom _ _ state hfirst
      (ih (fun other ho => hvalid other (List.mem_cons_of_mem _ ho)) _ (hfirst.final _ _ _ _ _))

theorem leafProgram_numeric (B heapWords N q size base : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom) (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (PA17LeafLabels005.program N q size base) state :=
  leafNodes_numeric B heapWords N q size base rom hl hd (List.range size) (fun _ hn => List.mem_range.mp hn) state hi

theorem prepared_leafProgram_numeric (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q))
    (B heapWords base : Nat)
    (hl : Layout B heapWords q (prepareNormalization q full).indexed.nodes.size base (queryROM q full stage used))
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords (queryROM q full stage used)
      (PA17LeafLabels005.program full.length q (prepareNormalization q full).indexed.nodes.size base) state :=
  leafProgram_numeric _ _ _ _ _ _ _ hl (queryROM_data q full stage used) state hi

end PaperProofs.Structure.LaminarTree.PA17QueryDataWord024b

module

public import PaperProofs.Structure.PA17_QueryCounts_008
public import PaperProofs.Structure.PA17_QueryHeaderWord_022a
import Mathlib.Tactic.IntervalCases

/-! Genuine register/address bounds for every actual raw-used-count Op
prefix. Incoming scratch heap contents are arbitrary and are never read.
The only ROM conditions are literal format/bit bounds, proved below for
the original queryROM. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryDataWord024a

open IndexedRAM IndexedClosureRAM AlgorithmClaims
open PA17QueryHeaderWord022

structure Data (N q size : Nat) (rom : PhysicalROM) : Prop where
  input_length : rom.input.length = 4 + N * q + size * q + q
  node_bit : ∀ node < size, ∀ tool < q, rom.semantic.read .input (3 + N * q + node * q + tool) ≤ 1
  used_bit : ∀ tool < q, rom.semantic.read .input (4 + N * q + size * q + tool) ≤ 1

structure Layout (B heapWords q size base : Nat) (rom : PhysicalROM) : Prop where
  input_bound : rom.input.length ≤ B
  output_bound : base + size ≤ B
  output_access : base + size ≤ heapWords
  q_bound : q ≤ B
  one_bound : 1 ≤ B

theorem queryROM_data (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q)) :
    Data full.length q (prepareNormalization q full).indexed.nodes.size (queryROM q full stage used) := by
  constructor
  · simp only [queryROM, List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_finRange,
      PA17QueryCounts008.givenTreeROM_input_length]
    omega
  · intro node hn tool ht
    rw [PA17QueryCounts008.queryROM_node_bit q full stage used ⟨node, hn⟩ ⟨tool, ht⟩]
    unfold bit
    split_ifs <;> omega
  · intro tool ht
    rw [PA17QueryCounts008.queryROM_used_bit q full stage used ⟨tool, ht⟩]
    unfold bit
    split_ifs <;> omega

theorem node_address_lt (N q size node tool : Nat) (rom : PhysicalROM) (hd : Data N q size rom)
    (hn : node < size) (ht : tool < q) : 3 + N * q + node * q + tool < rom.input.length := by
  have hm := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hn)
  rw [Nat.succ_mul] at hm
  rw [hd.input_length]
  omega

theorem used_address_lt (N q size tool : Nat) (rom : PhysicalROM) (hd : Data N q size rom)
    (ht : tool < q) : 4 + N * q + size * q + tool < rom.input.length := by
  rw [hd.input_length]
  omega

theorem contribution_le (N q size node tool : Nat) (rom : PhysicalROM) (hd : Data N q size rom)
    (hn : node < size) (ht : tool < q) : PA17QueryCounts008.contribution rom.semantic N q size node tool ≤ 1 := by
  unfold PA17QueryCounts008.contribution
  split_ifs
  · omega
  · exact hd.node_bit node hn tool ht

theorem bitBlock_numeric (B heapWords N q size base node tool : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom) (hn : node < size) (ht : tool < q)
    (state : State) (hi : RegistersLE (2 * B) state) (htotal : state.register .total + 1 ≤ q) :
    NumericSafe (2 * B) heapWords rom (PA17QueryCounts008.bitBlock N q size node tool) state := by
  have hnode := hd.node_bit node hn tool ht
  have hused := hd.used_bit tool ht
  have hnA := node_address_lt N q size node tool rom hd hn ht
  have huA := used_address_lt N q size tool rom hd ht
  have hnB := hnA.le.trans hl.input_bound
  have huB := huA.le.trans hl.input_bound
  have hq := hl.q_bound
  have hone := hl.one_bound
  constructor
  · intro k hk r
    have hr := hi r
    change k ≤ 7 at hk
    interval_cases k <;> cases r <;>
      simp [PA17QueryCounts008.bitBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals (try split_ifs)
    all_goals omega
  · intro k hk
    change k < 7 at hk
    interval_cases k <;>
      simp [PA17QueryCounts008.bitBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, PhysicalROM.words]
    all_goals omega

theorem bits_numeric (B heapWords N q size base node : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom) (hn : node < size)
    (tools : List Nat) (hvalid : ∀ tool ∈ tools, tool < q) (state : State) (hi : RegistersLE (2 * B) state)
    (hbudget : state.register .total + tools.length ≤ q) :
    NumericSafe (2 * B) heapWords rom (tools.flatMap (PA17QueryCounts008.bitBlock N q size node)) state := by
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
    have hfirst := bitBlock_numeric B heapWords N q size base node tool rom hl hd hn ht state hi (by
      simp only [List.length_cons] at hbudget
      omega)
    let after := execute rom.semantic (PA17QueryCounts008.bitBlock N q size node tool) state
    have hafter : after.register .total + later.length ≤ q := by
      have hv := contribution_le N q size node tool rom hd hn ht
      have he := PA17QueryCounts008.bitBlock_total rom.semantic N q size node tool state
      change after.register .total = _ at he
      simp only [List.length_cons] at hbudget
      omega
    exact NumericSafe.append _ _ rom _ _ state hfirst
      (ih (fun other ho => hvalid other (List.mem_cons_of_mem _ ho)) after (hfirst.final _ _ _ _ _) hafter)

theorem init_numeric (B heapWords : Nat) (rom : PhysicalROM) (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom [.base (.constant .total 0)] state := by
  constructor
  · intro k hk r
    have hr := hi r
    change k ≤ 1 at hk
    interval_cases k <;> cases r <;> simp [IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro k hk
    have hz : k = 0 := by change k < 1 at hk; omega
    subst k
    trivial

theorem tail_numeric (B heapWords q size base node : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hn : node < size) (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (PA17QueryCounts008.nodeTail base node) state := by
  have haddr : base + node < heapWords := lt_of_lt_of_le (by omega) hl.output_access
  have hbound : base + node ≤ B := (show base + node ≤ base + size from by omega).trans hl.output_bound
  constructor
  · intro k hk r
    have hr := hi r
    change k ≤ 2 at hk
    interval_cases k <;> cases r <;> simp [PA17QueryCounts008.nodeTail, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro k hk
    change k < 2 at hk
    interval_cases k <;> simp [PA17QueryCounts008.nodeTail, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, haddr]

theorem nodeBlock_numeric (B heapWords N q size base node : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom) (hn : node < size)
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (PA17QueryCounts008.nodeBlock N q size base node) state := by
  let start := execute rom.semantic [.base (.constant .total 0)] state
  let middle := execute rom.semantic ((List.range q).flatMap (PA17QueryCounts008.bitBlock N q size node)) start
  have hinit := init_numeric B heapWords rom state hi
  have hbits := bits_numeric B heapWords N q size base node rom hl hd hn (List.range q)
    (fun tool ht => List.mem_range.mp ht) start (hinit.final _ _ _ _ _) (by
      change 0 + (List.range q).length ≤ q
      simp only [List.length_range, Nat.zero_add, le_refl])
  have htail := tail_numeric B heapWords q size base node rom hl hn middle (hbits.final _ _ _ _ _)
  rw [PA17QueryCounts008.nodeBlock]
  exact NumericSafe.append _ _ rom _ _ state (NumericSafe.append _ _ rom _ _ state hinit hbits) htail

theorem nodes_numeric (B heapWords N q size base : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom)
    (nodes : List Nat) (hvalid : ∀ node ∈ nodes, node < size) (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (nodes.flatMap (PA17QueryCounts008.nodeBlock N q size base)) state := by
  induction nodes generalizing state with
  | nil =>
    constructor
    · intro count _
      simpa only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hi
    · intro count hc
      simp only [List.flatMap_nil, List.length_nil, Nat.not_lt_zero] at hc
  | cons node later ih =>
    rw [List.flatMap_cons]
    have hfirst := nodeBlock_numeric B heapWords N q size base node rom hl hd (hvalid node List.mem_cons_self) state hi
    exact NumericSafe.append _ _ rom _ _ state hfirst
      (ih (fun other ho => hvalid other (List.mem_cons_of_mem _ ho)) _ (hfirst.final _ _ _ _ _))

theorem program_numeric (B heapWords N q size base : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q size base rom) (hd : Data N q size rom) (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (PA17QueryCounts008.program N q size base) state :=
  nodes_numeric B heapWords N q size base rom hl hd (List.range size) (fun _ hn => List.mem_range.mp hn) state hi

theorem prepared_program_numeric (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q))
    (B heapWords base : Nat)
    (hl : Layout B heapWords q (prepareNormalization q full).indexed.nodes.size base (queryROM q full stage used))
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords (queryROM q full stage used)
      (PA17QueryCounts008.program full.length q (prepareNormalization q full).indexed.nodes.size base) state :=
  program_numeric _ _ _ _ _ _ _ hl (queryROM_data q full stage used) state hi

end PaperProofs.Structure.LaminarTree.PA17QueryDataWord024a

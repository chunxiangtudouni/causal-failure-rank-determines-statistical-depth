module
public import PaperProofs.Structure.PA17_GivenWord_031d
public import PaperProofs.Structure.PA17_QueryHeaderWord_022
public import PaperProofs.Structure.PA17_QueryRanksWord_027
public import PaperProofs.Structure.PA17_QueryDataWord_024c
import Mathlib.Tactic.IntervalCases

/-! Real original stage/node incidence comparisons. The full builder writes
one word per stage; the rolling builder uses the same scan with one fixed word. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17GivenWord031e

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022

structure Data (N q size : Nat) (rom : PhysicalROM) : Prop where
  tree_access : 3 + N * q + size * q ≤ rom.input.length
  stage_bit : ∀ stage < N, ∀ tool < q, rom.semantic.read .input (3 + stage * q + tool) ≤ 1
  node_bit : ∀ node < size, ∀ tool < q, rom.semantic.read .input (3 + N * q + node * q + tool) ≤ 1

theorem queryROM_data (q : Nat) (full : List (Finset (Fin q))) (stage : Fin (full.length + 1)) (used : Finset (Fin q)) :
    Data full.length q (prepareNormalization q full).indexed.nodes.size (queryROM q full stage.val used) := by
  have hd := PA17QueryHeaderWord022.queryROM_data q full stage used
  exact ⟨by rw [hd.input_length]; omega, hd.stage_bit, hd.node_bit⟩

theorem givenTreeROM_data (q : Nat) (full : List (Finset (Fin q))) :
    Data full.length q (prepareNormalization q full).indexed.nodes.size (givenTreeROM q full) := by
  have hlen := PA17QueryCounts008.givenTreeROM_input_length q full
  have hd := queryROM_data q full ⟨0, by omega⟩ ∅
  constructor
  · rw [hlen]
  · intro stage hs tool ht
    rw [← PA17QueryCounts008.queryROM_tree_input_read q full 0 ∅ _ (by
      rw [hlen]
      have hh := Nat.mul_le_mul_right q (show stage + 1 ≤ full.length by omega)
      rw [Nat.add_mul, Nat.one_mul] at hh
      omega)]
    exact hd.stage_bit stage hs tool ht
  · intro node hn tool ht
    rw [← PA17QueryCounts008.queryROM_tree_input_read q full 0 ∅ _ (by
      rw [hlen]
      have hh := Nat.mul_le_mul_right q (show node + 1 ≤ (prepareNormalization q full).indexed.nodes.size by omega)
      rw [Nat.add_mul, Nat.one_mul] at hh
      omega)]
    exact hd.node_bit node hn tool ht

theorem bitBlock_numeric (B heapWords N q size stage node tool : Nat) (rom : PhysicalROM)
    (hd : Data N q size rom) (hinput : rom.input.length ≤ B) (hq : q ≤ B) (_hone : 1 ≤ B)
    (hs : stage < N) (hn : node < size) (ht : tool < q)
    (state : State) (hi : RegistersLE (2 * B) state) (hbudget : state.register .total + 2 ≤ 2 * q) :
    NumericSafe (2 * B) heapWords rom (PA17StageMap001.bitBlock N q stage node tool) state := by
  have hleft := hd.stage_bit stage hs tool ht
  have hright := hd.node_bit node hn tool ht
  have hsaddr : 3 + stage * q + tool < rom.input.length := by
    have hh := Nat.mul_le_mul_right q (show stage + 1 ≤ N by omega)
    rw [Nat.add_mul, Nat.one_mul] at hh
    have := hd.tree_access
    omega
  have hnaddr : 3 + N * q + node * q + tool < rom.input.length := by
    have hh := Nat.mul_le_mul_right q (show node + 1 ≤ size by omega)
    rw [Nat.add_mul, Nat.one_mul] at hh
    have := hd.tree_access
    omega
  have hls : rom.semantic.read .input (3 + stage * q + tool) - rom.semantic.read .input (3 + N * q + node * q + tool) ≤ 1 := by omega
  have hrs : rom.semantic.read .input (3 + N * q + node * q + tool) - rom.semantic.read .input (3 + stage * q + tool) ≤ 1 := by omega
  constructor
  · intro count hc register
    have hr := hi register
    change count ≤ 8 at hc
    interval_cases count <;> cases register <;>
      simp [PA17StageMap001.bitBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 8 at hc
    interval_cases count <;>
      simp [PA17StageMap001.bitBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, PhysicalROM.words]
    all_goals omega

theorem bits_numeric (B heapWords N q size stage node : Nat) (rom : PhysicalROM)
    (hd : Data N q size rom) (hinput : rom.input.length ≤ B) (hq : q ≤ B) (hone : 1 ≤ B)
    (hs : stage < N) (hn : node < size) (tools : List Nat) (ht : ∀ tool ∈ tools, tool < q)
    (state : State) (hi : RegistersLE (2 * B) state) (hbudget : state.register .total + 2 * tools.length ≤ 2 * q) :
    NumericSafe (2 * B) heapWords rom (tools.flatMap (PA17StageMap001.bitBlock N q stage node)) state := by
  induction tools generalizing state with
  | nil => exact PA17GivenWord031a.NumericSafe.nil _ _ rom state hi
  | cons head later ih =>
    rw [List.flatMap_cons]
    have hh := bitBlock_numeric B heapWords N q size stage node head rom hd hinput hq hone hs hn
      (ht head List.mem_cons_self) state hi (by simp only [List.length_cons] at hbudget; omega)
    apply NumericSafe.append _ _ rom _ _ state hh
    apply ih (fun tool hm => ht tool (List.mem_cons_of_mem _ hm)) _ (hh.final _ _ _ _ _)
    rw [PA17StageMap001.bitBlock_total]
    have hleft := hd.stage_bit stage hs head (ht head List.mem_cons_self)
    have hright := hd.node_bit node hn head (ht head List.mem_cons_self)
    simp only [List.length_cons, PA17StageMap001.difference] at hbudget ⊢
    omega

theorem nodeTail_numeric (B heapWords node : Nat) (rom : PhysicalROM) (hnode : node + 1 ≤ 2 * B)
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (PA17StageMap001.nodeTail node) state := by
  constructor
  · intro count hc register
    have hr := hi register
    have hv := hi .value
    change count ≤ 2 at hc
    interval_cases count <;> cases register <;>
      simp [PA17StageMap001.nodeTail, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals (try split_ifs)
    all_goals omega
  · intro count hc
    change count < 2 at hc
    interval_cases count <;> trivial

theorem nodeBlock_numeric (B heapWords N q size stage node : Nat) (rom : PhysicalROM)
    (hd : Data N q size rom) (hinput : rom.input.length ≤ B) (hq : q ≤ B) (hsize : size ≤ B) (hone : 1 ≤ B)
    (hs : stage < N) (hn : node < size) (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (PA17StageMap001.nodeBlock N q stage node) state := by
  have hinit := PA17QueryRanksWord027.constant_numeric (2 * B) heapWords 0 rom .total (Nat.zero_le _) state hi
  have hbits := bits_numeric B heapWords N q size stage node rom hd hinput hq hone hs hn (List.range q)
    (fun _ hm => List.mem_range.mp hm) _ (hinit.final _ _ _ _ _) (by
      change 0 + 2 * (List.range q).length ≤ 2 * q
      simp only [List.length_range, Nat.zero_add, le_refl])
  have hleft := NumericSafe.append _ _ rom _ _ state hinit hbits
  rw [PA17StageMap001.nodeBlock]
  apply NumericSafe.append _ _ rom _ _ state hleft
  exact nodeTail_numeric B heapWords node rom (by omega) _ (hleft.final _ _ _ _ _)

theorem nodes_numeric (B heapWords N q size stage : Nat) (rom : PhysicalROM)
    (hd : Data N q size rom) (hinput : rom.input.length ≤ B) (hq : q ≤ B) (hsize : size ≤ B) (hone : 1 ≤ B)
    (hs : stage < N) (nodes : List Nat) (hn : ∀ node ∈ nodes, node < size)
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (nodes.flatMap (PA17StageMap001.nodeBlock N q stage)) state := by
  induction nodes generalizing state with
  | nil => exact PA17GivenWord031a.NumericSafe.nil _ _ rom state hi
  | cons head later ih =>
    rw [List.flatMap_cons]
    have hh := nodeBlock_numeric B heapWords N q size stage head rom hd hinput hq hsize hone hs (hn head List.mem_cons_self) state hi
    exact NumericSafe.append _ _ rom _ _ state hh
      (ih (fun node hm => hn node (List.mem_cons_of_mem _ hm)) _ (hh.final _ _ _ _ _))

theorem stageBlock_numeric (B heapWords N q size base stage : Nat) (rom : PhysicalROM)
    (hd : Data N q size rom) (hinput : rom.input.length ≤ B) (hq : q ≤ B) (hsize : size ≤ B) (hone : 1 ≤ B)
    (hs : stage < N) (haddr : PA17GivenWord031a.AddressBound B heapWords (base + stage))
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (PA17StageMap001.stageBlock N q size base stage) state := by
  have hinit := PA17QueryRanksWord027.constant_numeric (2 * B) heapWords 0 rom .value (Nat.zero_le _) state hi
  have hnodes := nodes_numeric B heapWords N q size stage rom hd hinput hq hsize hone hs (List.range size)
    (fun _ hm => List.mem_range.mp hm) _ (hinit.final _ _ _ _ _)
  have hleft := NumericSafe.append _ _ rom _ _ state hinit hnodes
  rw [PA17StageMap001.stageBlock]
  apply NumericSafe.append _ _ rom _ _ state hleft
  exact PA17QueryRanksWord027.storeValue_numeric (2 * B) heapWords (base + stage) rom haddr.1 (by have := haddr.2; omega)
    _ (hleft.final _ _ _ _ _)

theorem matchedStage_numeric (B heapWords N q size stage target : Nat) (rom : PhysicalROM)
    (hd : Data N q size rom) (hinput : rom.input.length ≤ B) (hq : q ≤ B) (hsize : size ≤ B) (hone : 1 ≤ B)
    (hs : stage < N) (haddr : PA17GivenWord031a.AddressBound B heapWords target)
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom
      ([.base (.constant .value 0)] ++ (List.range size).flatMap (PA17StageMap001.nodeBlock N q stage) ++
        [.base (.constant .index target), .base (.storeHeap .index .value)]) state := by
  have hinit := PA17QueryRanksWord027.constant_numeric (2 * B) heapWords 0 rom .value (Nat.zero_le _) state hi
  have hnodes := nodes_numeric B heapWords N q size stage rom hd hinput hq hsize hone hs (List.range size)
    (fun _ hm => List.mem_range.mp hm) _ (hinit.final _ _ _ _ _)
  have hleft := NumericSafe.append _ _ rom _ _ state hinit hnodes
  apply NumericSafe.append _ _ rom _ _ state hleft
  exact PA17QueryRanksWord027.storeValue_numeric (2 * B) heapWords target rom haddr.1 (by have := haddr.2; omega)
    _ (hleft.final _ _ _ _ _)

theorem stages_numeric (B heapWords N q size base : Nat) (rom : PhysicalROM)
    (hd : Data N q size rom) (hinput : rom.input.length ≤ B) (hq : q ≤ B) (hsize : size ≤ B) (hone : 1 ≤ B)
    (stages : List Nat) (hs : ∀ stage ∈ stages, stage < N)
    (haddr : ∀ stage ∈ stages, PA17GivenWord031a.AddressBound B heapWords (base + stage))
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (stages.flatMap (PA17StageMap001.stageBlock N q size base)) state := by
  induction stages generalizing state with
  | nil => exact PA17GivenWord031a.NumericSafe.nil _ _ rom state hi
  | cons head later ih =>
    rw [List.flatMap_cons]
    have hh := stageBlock_numeric B heapWords N q size base head rom hd hinput hq hsize hone
      (hs head List.mem_cons_self) (haddr head List.mem_cons_self) state hi
    exact NumericSafe.append _ _ rom _ _ state hh
      (ih (fun stage hm => hs stage (List.mem_cons_of_mem _ hm))
        (fun stage hm => haddr stage (List.mem_cons_of_mem _ hm)) _ (hh.final _ _ _ _ _))

theorem program_numeric (B heapWords N q size base : Nat) (rom : PhysicalROM)
    (hd : Data N q size rom) (hinput : rom.input.length ≤ B) (hq : q ≤ B) (hsize : size ≤ B) (hone : 1 ≤ B)
    (haccess : base + N ≤ heapWords) (hbound : base + N ≤ B)
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (PA17StageMap001.program N q size base) state :=
  stages_numeric B heapWords N q size base rom hd hinput hq hsize hone (List.range N)
    (fun _ hm => List.mem_range.mp hm)
    (by intro stage hm; have := List.mem_range.mp hm; exact ⟨by omega, by omega⟩) state hi

end PaperProofs.Structure.LaminarTree.PA17GivenWord031e

module

public import PaperProofs.Structure.PA17_QueryHeader_009
public import PaperProofs.Structure.PA17_QueryHeaderWord_022a

/-! Concrete numeric/register/access certificates for the actual Header009
program. The heap is arbitrary initially: header words used by later phases
are established by earlier instructions of the same run. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryHeaderWord022

open IndexedRAM IndexedClosureRAM AlgorithmClaims
open PA17QueryHeader009

structure Layout (B heapWords N q size head : Nat) (rom : PhysicalROM) : Prop where
  head_access : head + 9 ≤ heapWords
  input_le : rom.input.length ≤ B
  table_le : tableWords N q size ≤ B
  head_le : head + 16 ≤ B
  q_le : q ≤ B
  size_le : size + 1 ≤ B
  N_le : N + 1 ≤ B
  one_le : 1 ≤ B

structure ROMData (N q size stage : Nat) (rom : PhysicalROM) : Prop where
  input_length : rom.input.length = 4 + N * q + size * q + q
  stage_word : rom.semantic.read .input (3 + N * q + size * q) = stage
  stage_le : stage ≤ N
  stage_bit : ∀ row < N, ∀ tool < q, rom.semantic.read .input (3 + row * q + tool) ≤ 1
  node_bit : ∀ node < size, ∀ tool < q, rom.semantic.read .input (3 + N * q + node * q + tool) ≤ 1

theorem stage_address_lt (N q size stage : Nat) (rom : PhysicalROM) (hd : ROMData N q size stage rom) :
    3 + N * q + size * q < rom.input.length := by rw [hd.input_length]; omega

theorem row_bit_address_lt (N q size stage : Nat) (rom : PhysicalROM) (hd : ROMData N q size stage rom)
    (row tool : Nat) (hr : row < N) (ht : tool < q) : 3 + row * q + tool < rom.input.length := by
  have hh := Nat.mul_le_mul_right q (show row + 1 ≤ N by omega)
  rw [Nat.add_mul, Nat.one_mul] at hh
  rw [hd.input_length]
  omega

theorem node_bit_address_lt (N q size stage : Nat) (rom : PhysicalROM) (hd : ROMData N q size stage rom)
    (node tool : Nat) (hn : node < size) (ht : tool < q) : 3 + N * q + node * q + tool < rom.input.length := by
  have hh := Nat.mul_le_mul_right q (show node + 1 ≤ size by omega)
  rw [Nat.add_mul, Nat.one_mul] at hh
  rw [hd.input_length]
  omega

theorem queryROM_stage_bit (q : Nat) (full : List (Finset (Fin q))) (rawStage : Nat) (used : Finset (Fin q))
    (row : Fin full.length) (tool : Fin q) :
    (queryROM q full rawStage used).semantic.read .input (3 + row.val * q + tool.val) = bit (decide (tool ∈ full[row.val])) := by
  have hrow := Nat.mul_le_mul_right q (show row.val + 1 ≤ full.length from row.isLt)
  rw [Nat.add_mul, Nat.one_mul] at hrow
  rw [PA17QueryCounts008.queryROM_tree_input_read q full rawStage used _ (by
    rw [PA17QueryCounts008.givenTreeROM_input_length]
    have := tool.isLt
    omega)]
  let cache := (prepareNormalization q full).indexed
  change (([full.length, q, cache.nodes.size] ++ incidence full) ++ _).getD _ 0 = _
  rw [List.getD_append _ _ _ _ (by
    simp only [List.length_append, List.length_cons, List.length_nil, RawIncidenceLaminarRAM.incidence_length]
    have := tool.isLt
    omega), List.getD_append_right _ _ _ _ (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil]
  have ho : 3 + row.val * q + tool.val - (1 + (1 + (1 + 0))) = row.val * q + tool.val := by omega
  rw [ho]
  exact RawIncidenceLaminarRAM.incidence_getD q full row.val row.isLt tool

theorem queryROM_data (q : Nat) (full : List (Finset (Fin q))) (stage : Fin (full.length + 1)) (used : Finset (Fin q)) :
    ROMData full.length q (prepareNormalization q full).indexed.nodes.size stage.val (queryROM q full stage.val used) := by
  constructor
  · simp only [queryROM, List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_finRange,
      PA17QueryCounts008.givenTreeROM_input_length]
    omega
  · exact PA17QueryHeader009.queryROM_stage q full stage.val used
  · exact Nat.lt_succ_iff.mp stage.isLt
  · intro row hr tool ht
    rw [queryROM_stage_bit q full stage.val used ⟨row, hr⟩ ⟨tool, ht⟩]
    unfold bit
    split_ifs <;> omega
  · intro node hn tool ht
    rw [PA17QueryCounts008.queryROM_node_bit q full stage.val used ⟨node, hn⟩ ⟨tool, ht⟩]
    unfold bit
    split_ifs <;> omega

theorem addLoop_numeric (bound heapWords : Nat) (rom : PhysicalROM) (count : Nat) (state : State)
    (hregister : RegistersLE bound state) (htotal : state.register .total + count * state.register .old ≤ bound) :
    NumericSafe bound heapWords rom (addLoop count) state := by
  constructor
  · intro k _ register
    have heq : (addLoop count).take k = addLoop (min k count) := by
      simp only [addLoop, List.take_replicate]
    rw [heq]
    by_cases hr : register = .total
    · subst register
      rw [addLoop_total]
      have hh := Nat.mul_le_mul_right (state.register .old) (Nat.min_le_right k count)
      omega
    · rw [addLoop_register rom.semantic _ state register hr]
      exact hregister register
  · intro k hp
    simp only [addLoop, List.getElem_replicate, AccessFits]

theorem save_numeric (B heapWords : Nat) (rom : PhysicalROM) (target : Nat) (source : Register)
    (htarget : target ≤ B) (haccess : target < heapWords) (state : State) (hregister : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (save target source) state := by
  constructor
  · intro k hk r
    have hr := hregister r
    change k ≤ 2 at hk
    interval_cases k <;> cases r <;>
      simp [save, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro k hk
    change k < 2 at hk
    interval_cases k <;> simp [save, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, haccess]

theorem set_numeric (B heapWords : Nat) (rom : PhysicalROM) (target value : Nat)
    (htarget : target ≤ B) (hvalue : value ≤ B) (haccess : target < heapWords)
    (state : State) (hregister : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (set target value) state := by
  constructor
  · intro k hk r
    have hr := hregister r
    change k ≤ 3 at hk
    interval_cases k <;> cases r <;>
      simp [PA17QueryHeader009.set, IndexedCellRAM.constantBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro k hk
    change k < 3 at hk
    interval_cases k <;> simp [PA17QueryHeader009.set, IndexedCellRAM.constantBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, haccess]

theorem readStage_numeric (B heapWords N q size head stage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords N q size head rom) (hd : ROMData N q size stage rom)
    (state : State) (hregister : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (readStage N q size head) state := by
  have hi := stage_address_lt N q size stage rom hd
  have hI := hl.input_le
  have hH := hl.head_le
  have hN := hl.N_le
  have hs := hd.stage_le
  constructor
  · intro k hk r
    have hr := hregister r
    change k ≤ 4 at hk
    interval_cases k <;> cases r <;>
      simp [readStage, save, IndexedClosureRAM.execute, Op.execute, Instruction.execute, hd.stage_word]
    all_goals omega
  · intro k hk
    have ha := hl.head_access
    change k < 4 at hk
    interval_cases k <;> simp [readStage, save, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, PhysicalROM.words]
    all_goals omega

theorem activeInit_numeric (B heapWords N : Nat) (rom : PhysicalROM)
    (hN : N + 1 ≤ B) (state : State) (hregister : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (activeInit N) state := by
  constructor
  · intro k hk r
    have hr := hregister r
    change k ≤ 5 at hk
    interval_cases k <;> cases r <;>
      simp [activeInit, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals (try split_ifs)
    all_goals omega
  · intro k hk
    change k < 5 at hk
    interval_cases k <;> simp [activeInit, AccessFits]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem finish_numeric (B heapWords N q size head : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords N q size head rom) (state : State)
    (hregister : RegistersLE (2 * B) state) (hactive : state.heap (head + 2) ≤ 1) :
    NumericSafe (2 * B) heapWords rom (finish head) state := by
  have hh := hl.head_le
  have hone := hl.one_le
  constructor
  · intro k hk r
    have hr := hregister r
    change k ≤ 18 at hk
    interval_cases k <;> cases r <;>
      simp [finish, save, PA17QueryHeader009.set, IndexedCellRAM.constantBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals (try split_ifs)
    all_goals omega
  · intro k hk
    have ha := hl.head_access
    change k < 18 at hk
    interval_cases k <;>
      simp [finish, save, PA17QueryHeader009.set, IndexedCellRAM.constantBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits]
    all_goals omega

theorem singleton_numeric (bound heapWords : Nat) (rom : PhysicalROM) (op : Op) (state : State)
    (hi : RegistersLE bound state) (ho : RegistersLE bound (op.execute rom.semantic state))
    (ha : AccessFits rom heapWords state op) : NumericSafe bound heapWords rom [op] state := by
  constructor
  · intro k hk
    change k ≤ 1 at hk
    interval_cases k
    · exact hi
    · exact ho
  · intro k hk
    have hz : k = 0 := by change k < 1 at hk; omega
    subst k
    exact ha

theorem select_numeric (bound heapWords : Nat) (rom : PhysicalROM)
    (target condition whenTrue whenFalse : Register) (state : State) (hi : RegistersLE bound state) :
    NumericSafe bound heapWords rom [.base (.select target condition whenTrue whenFalse)] state := by
  apply singleton_numeric bound heapWords rom (.base (.select target condition whenTrue whenFalse)) state hi _ trivial
  intro register
  change Function.update state.register target
    (if state.register condition = 0 then state.register whenFalse else state.register whenTrue) register ≤ bound
  by_cases heq : register = target
  · subst register
    rw [Function.update_self]
    split_ifs <;> exact hi _
  · rw [Function.update_of_ne heq]
    exact hi register

theorem constant_numeric (bound heapWords : Nat) (rom : PhysicalROM)
    (target : Register) (value : Nat) (hv : value ≤ bound) (state : State) (hi : RegistersLE bound state) :
    NumericSafe bound heapWords rom [.base (.constant target value)] state := by
  apply singleton_numeric bound heapWords rom (.base (.constant target value)) state hi _ trivial
  intro register
  change Function.update state.register target value register ≤ bound
  by_cases heq : register = target
  · subst register; rw [Function.update_self]; exact hv
  · rw [Function.update_of_ne heq]; exact hi register

theorem rowHead_numeric (B heapWords N stage : Nat) (rom : PhysicalROM) (hN : N + 1 ≤ B) (hs : stage ≤ N)
    (state : State) (hi : RegistersLE (2 * B) state) (hold : state.register .old = stage) :
    NumericSafe (2 * B) heapWords rom
      [.base (.constant .fresh 1), .base (.add .old .old .fresh), .base (.constant .total 0)] state := by
  constructor
  · intro k hk register
    have hr := hi register
    change k ≤ 3 at hk
    interval_cases k <;> cases register <;>
      simp [IndexedClosureRAM.execute, Op.execute, Instruction.execute, hold]
    all_goals omega
  · intro k hk
    change k < 3 at hk
    interval_cases k <;> simp [AccessFits]

theorem rowArithmetic_numeric (B heapWords N q size head stage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords N q size head rom) (hs : stage ≤ N)
    (state : State) (hi : RegistersLE (2 * B) state) (hold : state.register .old = stage) :
    NumericSafe (2 * B) heapWords rom (rowArithmetic q size) state := by
  let first : List Op := [.base (.constant .fresh 1), .base (.add .old .old .fresh), .base (.constant .total 0)]
  let after := execute rom.semantic first state
  have hh := rowHead_numeric B heapWords N stage rom hl.N_le hs state hi hold
  have hm : stride q size * (stage + 1) ≤ tableWords N q size := by
    calc
      _ ≤ stride q size * (N + 1) := Nat.mul_le_mul_left _ (Nat.add_le_add_right hs 1)
      _ = tableWords N q size := by dsimp [stride, tableWords, cells]; ring
  have hbudget : after.register .total + stride q size * after.register .old ≤ 2 * B := by
    change 0 + stride q size * (state.register .old + 1) ≤ 2 * B
    rw [hold]
    have ht := hl.table_le
    omega
  have ha := addLoop_numeric (2 * B) heapWords rom (stride q size) after
    (NumericSafe.final _ _ _ _ state hh) hbudget
  rw [rowArithmetic]
  exact NumericSafe.append _ _ rom _ _ state
    (NumericSafe.append _ _ rom first (addLoop (stride q size)) state hh ha)
    (select_numeric (2 * B) heapWords rom .total .flag .total .address _ (NumericSafe.final _ _ _ _ after ha))

theorem rowProgram_numeric (B heapWords N q size head stage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords N q size head rom) (hs : stage ≤ N)
    (state : State) (hi : RegistersLE (2 * B) state) (hold : state.register .old = stage) :
    NumericSafe (2 * B) heapWords rom (rowProgram N q size head) state := by
  let a := execute rom.semantic (activeInit N) state
  let b := execute rom.semantic (save (head + 2) .flag) a
  have hH := hl.head_le
  have hA := hl.head_access
  have h1 := activeInit_numeric B heapWords N rom hl.N_le state hi
  have h2 := save_numeric B heapWords rom (head + 2) .flag (by omega) (by omega) a (NumericSafe.final _ _ _ _ state h1)
  have hb : b.register .old = stage := (save_register rom.semantic (head + 2) .flag .old (by decide) a).trans hold
  have h3 := rowArithmetic_numeric B heapWords N q size head stage rom hl hs b (NumericSafe.final _ _ _ _ a h2) hb
  have h4 := save_numeric B heapWords rom head .total (by omega) (by omega) _ (NumericSafe.final _ _ _ _ b h3)
  rw [rowProgram_split]
  exact NumericSafe.append _ _ rom _ _ state
    (NumericSafe.append _ _ rom _ _ state (NumericSafe.append _ _ rom _ _ state h1 h2) h3) h4

theorem stageHead_numeric (B heapWords N q size head stage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords N q size head rom) (hs : stage ≤ N)
    (state : State) (hi : RegistersLE (2 * B) state) (h3 : state.heap (head + 3) = stage) :
    NumericSafe (2 * B) heapWords rom
      [.base (.constant .index (head + 3)), .base (.loadHeap .old .index),
       .base (.constant .fresh (N - 1)), .base (.minimum .old .old .fresh), .base (.constant .total 3)] state := by
  have hH := hl.head_le
  have hN := hl.N_le
  constructor
  · intro k hk r
    have hr := hi r
    change k ≤ 5 at hk
    interval_cases k <;> cases r <;>
      simp [IndexedClosureRAM.execute, Op.execute, Instruction.execute, h3]
    all_goals omega
  · intro k hk
    have hA := hl.head_access
    change k < 5 at hk
    interval_cases k <;> simp [IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits]
    all_goals omega

theorem stageStart_numeric (B heapWords N q size head stage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords N q size head rom) (hd : ROMData N q size stage rom)
    (state : State) (hi : RegistersLE (2 * B) state) (h3 : state.heap (head + 3) = stage) :
    NumericSafe (2 * B) heapWords rom (stageStartProgram N q head) state := by
  let first : List Op := [.base (.constant .index (head + 3)), .base (.loadHeap .old .index),
    .base (.constant .fresh (N - 1)), .base (.minimum .old .old .fresh), .base (.constant .total 3)]
  let after := execute rom.semantic first state
  have h1 := stageHead_numeric B heapWords N q size head stage rom hl hd.stage_le state hi h3
  have hm : q * min stage (N - 1) ≤ N * q := by
    have hh := Nat.mul_le_mul_left q ((Nat.min_le_right stage (N - 1)).trans (Nat.sub_le N 1))
    nlinarith
  have hbudget : after.register .total + q * after.register .old ≤ 2 * B := by
    change 3 + q * min (state.heap (head + 3)) (N - 1) ≤ 2 * B
    rw [h3]
    have hi' := hl.input_le
    rw [hd.input_length] at hi'
    omega
  have h2 := addLoop_numeric (2 * B) heapWords rom q after (NumericSafe.final _ _ _ _ state h1) hbudget
  have hH := hl.head_le
  have hA := hl.head_access
  have h3' := save_numeric B heapWords rom (head + 8) .total (by omega) (by omega) _ (NumericSafe.final _ _ _ _ after h2)
  rw [stageStartProgram]
  exact NumericSafe.append _ _ rom _ _ state (NumericSafe.append _ _ rom first (addLoop q) state h1 h2) h3'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem bitBlock_numeric (B heapWords N q size head rawStage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords N q size head rom) (hd : ROMData N q size rawStage rom)
    (scanStage node tool : Nat) (hs : scanStage < N) (hn : node < size) (ht : tool < q)
    (state : State) (hi : RegistersLE (2 * B) state)
    (hrow : state.heap (head + 8) = 3 + scanStage * q)
    (hbudget : state.register .total + 2 ≤ 2 * B) :
    NumericSafe (2 * B) heapWords rom (bitBlock N q (head + 8) node tool) state ∧
      (execute rom.semantic (bitBlock N q (head + 8) node tool) state).register .total ≤ state.register .total + 2 := by
  have hStageAddress := row_bit_address_lt N q size rawStage rom hd scanStage tool hs ht
  have hNodeAddress := node_bit_address_lt N q size rawStage rom hd node tool hn ht
  have hStageBit := hd.stage_bit scanStage hs tool ht
  have hNodeBit := hd.node_bit node hn tool ht
  have hInput := hl.input_le
  have hHead := hl.head_le
  have hTool := hl.q_le
  have hOne := hl.one_le
  constructor
  · constructor
    · intro k hk r
      have hr := hi r
      change k ≤ 11 at hk
      interval_cases k <;> cases r <;>
        simp [bitBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, hrow]
      all_goals omega
    · intro k hk
      have hHeap := hl.head_access
      change k < 11 at hk
      interval_cases k <;>
        simp [bitBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, PhysicalROM.words, hrow]
      all_goals omega
  · rw [bitBlock_total rom.semantic N q (head + 8) node tool scanStage state hrow]
    dsimp [PA17StageMap001.difference]
    omega

theorem bits_numeric (B heapWords N q size head rawStage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords N q size head rom) (hd : ROMData N q size rawStage rom)
    (scanStage node : Nat) (hs : scanStage < N) (hn : node < size)
    (tools : List Nat) (htools : ∀ tool ∈ tools, tool < q)
    (state : State) (hi : RegistersLE (2 * B) state)
    (hrow : state.heap (head + 8) = 3 + scanStage * q)
    (hbudget : state.register .total + 2 * tools.length ≤ 2 * B) :
    NumericSafe (2 * B) heapWords rom (tools.flatMap (bitBlock N q (head + 8) node)) state ∧
      (execute rom.semantic (tools.flatMap (bitBlock N q (head + 8) node)) state).register .total ≤
        state.register .total + 2 * tools.length := by
  induction tools generalizing state with
  | nil =>
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro k _
      simpa only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hi
    · intro k hk
      simp only [List.flatMap_nil, List.length_nil] at hk
      omega
    · simp only [List.flatMap_nil, IndexedClosureRAM.execute, List.length_nil, Nat.mul_zero, Nat.add_zero, le_refl]
  | cons tool later ih =>
    have ht := bitBlock_numeric B heapWords N q size head rawStage rom hl hd scanStage node tool hs hn
      (htools tool List.mem_cons_self) state hi hrow (by rw [List.length_cons, Nat.mul_add] at hbudget; omega)
    let after := execute rom.semantic (bitBlock N q (head + 8) node tool) state
    have hrow' : after.heap (head + 8) = 3 + scanStage * q := by rw [bitBlock_heap]; exact hrow
    have hbudget' : after.register .total + 2 * later.length ≤ 2 * B := by
      rw [List.length_cons, Nat.mul_add] at hbudget
      have hh : after.register .total ≤ state.register .total + 2 := ht.2
      omega
    have hrest := ih (fun item hm => htools item (List.mem_cons_of_mem _ hm)) after
      (NumericSafe.final _ _ _ _ state ht.1) hrow' hbudget'
    constructor
    · rw [List.flatMap_cons]
      exact NumericSafe.append _ _ rom _ _ state ht.1 hrest.1
    · rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
      change (execute rom.semantic (later.flatMap (bitBlock N q (head + 8) node)) after).register .total ≤ _
      have hh : after.register .total ≤ state.register .total + 2 := ht.2
      have hr := hrest.2
      rw [List.length_cons, Nat.mul_add]
      omega

theorem nodeBlock_numeric (B heapWords N q size head rawStage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords N q size head rom) (hd : ROMData N q size rawStage rom)
    (scanStage node : Nat) (hs : scanStage < N) (hn : node < size)
    (state : State) (hi : RegistersLE (2 * B) state)
    (hrow : state.heap (head + 8) = 3 + scanStage * q) :
    NumericSafe (2 * B) heapWords rom (nodeBlock N q (head + 8) node) state := by
  let start := execute rom.semantic [.base (.constant .total 0)] state
  let middle := execute rom.semantic ((List.range q).flatMap (bitBlock N q (head + 8) node)) start
  have h1 := constant_numeric (2 * B) heapWords rom .total 0 (by omega) state hi
  have h2 := bits_numeric B heapWords N q size head rawStage rom hl hd scanStage node hs hn (List.range q)
    (fun tool hm => List.mem_range.mp hm) start (NumericSafe.final _ _ _ _ state h1) hrow (by
      have hh := hl.q_le
      change 0 + 2 * (List.range q).length ≤ 2 * B
      rw [List.length_range]
      omega)
  have hm : node + 1 ≤ 2 * B := by have hh := hl.size_le; omega
  have h3 := constant_numeric (2 * B) heapWords rom .old (node + 1) hm middle
    (NumericSafe.final _ _ _ _ start h2.1)
  have h4 := select_numeric (2 * B) heapWords rom .value .total .value .old _
    (NumericSafe.final _ _ _ _ middle h3)
  have htail : NumericSafe (2 * B) heapWords rom (PA17StageMap001.nodeTail node) middle :=
    NumericSafe.append _ _ rom _ _ middle h3 h4
  rw [nodeBlock]
  exact NumericSafe.append _ _ rom _ _ state (NumericSafe.append _ _ rom _ _ state h1 h2.1) htail

theorem nodes_numeric (B heapWords N q size head rawStage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords N q size head rom) (hd : ROMData N q size rawStage rom)
    (scanStage : Nat) (hs : scanStage < N) (nodes : List Nat) (hnodes : ∀ node ∈ nodes, node < size)
    (state : State) (hi : RegistersLE (2 * B) state) (hrow : state.heap (head + 8) = 3 + scanStage * q) :
    NumericSafe (2 * B) heapWords rom (nodes.flatMap (nodeBlock N q (head + 8))) state := by
  induction nodes generalizing state with
  | nil =>
    constructor
    · intro k _
      simpa only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hi
    · intro k hk
      simp only [List.flatMap_nil, List.length_nil] at hk
      omega
  | cons node later ih =>
    have hh := nodeBlock_numeric B heapWords N q size head rawStage rom hl hd scanStage node hs
      (hnodes node List.mem_cons_self) state hi hrow
    have hr := ih (fun n hm => hnodes n (List.mem_cons_of_mem _ hm)) _
      (NumericSafe.final _ _ _ _ state hh) (by rw [nodeBlock_heap]; exact hrow)
    rw [List.flatMap_cons]
    exact NumericSafe.append _ _ rom _ _ state hh hr

theorem scanProgram_numeric (B heapWords N q size head rawStage scanStage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords N q size head rom) (hd : ROMData N q size rawStage rom)
    (state : State) (hi : RegistersLE (2 * B) state)
    (hscan : N = 0 ∨ scanStage < N ∧ state.heap (head + 8) = 3 + scanStage * q) :
    NumericSafe (2 * B) heapWords rom (scanProgram N q size (head + 8)) state := by
  have h1 := constant_numeric (2 * B) heapWords rom .value 0 (by omega) state hi
  by_cases hN : N = 0
  · simpa only [scanProgram, hN, ite_true, List.append_nil] using h1
  · obtain ⟨hs, hrow⟩ := hscan.resolve_left hN
    have h2 := nodes_numeric B heapWords N q size head rawStage rom hl hd scanStage hs (List.range size)
      (fun n hm => List.mem_range.mp hm) _ (NumericSafe.final _ _ _ _ state h1) hrow
    rw [scanProgram, ite_eq_right hN]
    exact NumericSafe.append _ _ rom _ _ state h1 h2

theorem program_numeric (B heapWords N q size head stage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords N q size head rom) (hd : ROMData N q size stage rom)
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (program N q size head) state := by
  let a := execute rom.semantic (readStage N q size head) state
  let b := execute rom.semantic (rowProgram N q size head) a
  let c := execute rom.semantic (stageStartProgram N q head) b
  let d := execute rom.semantic (scanProgram N q size (head + 8)) c
  let scanStage := min stage (N - 1)
  have h1 := readStage_numeric B heapWords N q size head stage rom hl hd state hi
  have haold : a.register .old = stage := (readStage_old rom.semantic N q size head state).trans hd.stage_word
  have haheap : a.heap = Function.update state.heap (head + 3) stage := by
    rw [readStage_heap, hd.stage_word]
  have h2 := rowProgram_numeric B heapWords N q size head stage rom hl hd.stage_le a
    (NumericSafe.final _ _ _ _ state h1) haold
  have hbheap : b.heap = Function.update (Function.update a.heap (head + 2) (if stage < N then 1 else 0)) head
      (if stage < N then (stage + 1) * stride q size else 0) := by
    rw [rowProgram_heap, haold]
  have hb3 : b.heap (head + 3) = stage := by simp [hbheap, haheap]
  have h3 := stageStart_numeric B heapWords N q size head stage rom hl hd b
    (NumericSafe.final _ _ _ _ a h2) hb3
  have hcheap : c.heap = Function.update b.heap (head + 8) (3 + q * scanStage) := by
    rw [stageStartProgram_heap, hb3]
  have hrow : c.heap (head + 8) = 3 + scanStage * q := by rw [hcheap, Function.update_self, Nat.mul_comm q scanStage]
  have hscan : N = 0 ∨ scanStage < N ∧ c.heap (head + 8) = 3 + scanStage * q := by
    by_cases hN : N = 0
    · exact Or.inl hN
    · exact Or.inr ⟨lt_of_le_of_lt (Nat.min_le_right stage (N - 1)) (by omega), hrow⟩
  have h4 := scanProgram_numeric B heapWords N q size head stage scanStage rom hl hd c
    (NumericSafe.final _ _ _ _ b h3) hscan
  have hactive : d.heap (head + 2) ≤ 1 := by
    rw [scanProgram_heap, hcheap]
    simp only [Function.update_of_ne (show head + 2 ≠ head + 8 by omega)]
    rw [hbheap]
    simp only [Function.update_of_ne (show head + 2 ≠ head by omega), Function.update_self]
    split_ifs <;> omega
  have h5 := finish_numeric B heapWords N q size head rom hl d (NumericSafe.final _ _ _ _ c h4) hactive
  simp only [program, List.append_assoc]
  exact NumericSafe.append _ _ rom _ _ state h1
    (NumericSafe.append _ _ rom _ _ a h2
      (NumericSafe.append _ _ rom _ _ b h3 (NumericSafe.append _ _ rom _ _ c h4 h5)))

theorem layout_of_sumBound (B heapWords N q size head : Nat) (rom : PhysicalROM)
    (hheap : head + 9 ≤ heapWords)
    (hB : rom.input.length + tableWords N q size + head + 16 + q + size + N + 16 ≤ B) :
    Layout B heapWords N q size head rom := by
  constructor <;> omega

theorem prepared_program_numeric (q : Nat) (full : List (Finset (Fin q)))
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (head heapWords B : Nat)
    (hheap : head + 9 ≤ heapWords)
    (hB : (queryROM q full stage.val used).input.length +
      tableWords full.length q (prepareNormalization q full).indexed.nodes.size +
      head + 16 + q + (prepareNormalization q full).indexed.nodes.size + full.length + 16 ≤ B)
    (state : State) (hregister : RegistersLE B state) :
    NumericSafe (2 * B) heapWords (queryROM q full stage.val used)
      (program full.length q (prepareNormalization q full).indexed.nodes.size head) state := by
  apply program_numeric B heapWords full.length q (prepareNormalization q full).indexed.nodes.size head stage.val
    (queryROM q full stage.val used) (layout_of_sumBound B heapWords full.length q _ head _ hheap hB)
    (queryROM_data q full stage used) state
  intro register
  have hh := hregister register
  omega

end PaperProofs.Structure.LaminarTree.PA17QueryHeaderWord022

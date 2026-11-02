module

public import PaperProofs.Structure.PA17_QueryCounts_008
public import PaperProofs.Structure.UniformFreeTableSafety
import Mathlib.Tactic.IntervalCases

/-! A17: real query header. No correctness of the incoming heap's metadata
or stage map is assumed. The current stage is read from queryROM and its
node is found by comparing its actual incidence row with every node row.
The ninth word is private row-start scratch; header words 0..7 are public. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryHeader009

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def stride (q size : Nat) : Nat := (q + 2) * (size + 1)

def save (target : Nat) (source : Register) : List Op :=
  [.base (.constant .index target), .base (.storeHeap .index source)]

def set (target value : Nat) : List Op :=
  (IndexedCellRAM.constantBlock target value).map Op.base

def addLoop (count : Nat) : List Op := List.replicate count (.base (.add .total .total .old))

def readStage (N q size head : Nat) : List Op :=
  [.base (.constant .index (3 + N * q + size * q)), .base (.loadROM .input .old .index)] ++ save (head + 3) .old

def activeInit (N : Nat) : List Op :=
  [.base (.constant .total N), .subtract .total .total .old,
   .base (.constant .fresh 1), .base (.constant .address 0),
   .base (.select .flag .total .fresh .address)]

def rowProgram (N q size head : Nat) : List Op :=
  activeInit N ++ save (head + 2) .flag ++
    [.base (.constant .fresh 1), .base (.add .old .old .fresh), .base (.constant .total 0)] ++
    addLoop (stride q size) ++ [.base (.select .total .flag .total .address)] ++ save head .total

def stageStartProgram (N q head : Nat) : List Op :=
  [.base (.constant .index (head + 3)), .base (.loadHeap .old .index),
   .base (.constant .fresh (N - 1)), .base (.minimum .old .old .fresh), .base (.constant .total 3)] ++
    addLoop q ++ save (head + 8) .total

def bitBlock (N q rowScratch node tool : Nat) : List Op :=
  [.base (.constant .address rowScratch), .base (.loadHeap .index .address),
   .base (.constant .old tool), .base (.add .index .index .old), .base (.loadROM .input .old .index),
   .base (.constant .index (3 + N * q + node * q + tool)), .base (.loadROM .input .fresh .index),
   .subtract .flag .old .fresh, .subtract .index .fresh .old,
   .base (.add .flag .flag .index), .base (.add .total .total .flag)]

def nodeBlock (N q rowScratch node : Nat) : List Op :=
  [.base (.constant .total 0)] ++ (List.range q).flatMap (bitBlock N q rowScratch node) ++ PA17StageMap001.nodeTail node

def scanProgram (N q size rowScratch : Nat) : List Op :=
  [.base (.constant .value 0)] ++
    if N = 0 then [] else (List.range size).flatMap (nodeBlock N q rowScratch)

def finish (head : Nat) : List Op :=
  [.base (.constant .index (head + 2)), .base (.loadHeap .flag .index), .base (.constant .old 0),
   .base (.select .value .flag .value .old)] ++ save (head + 1) .value ++
    set (head + 4) 0 ++ set (head + 5) 0 ++ set (head + 6) 0 ++ set (head + 7) 0

def program (N q size head : Nat) : List Op :=
  readStage N q size head ++ rowProgram N q size head ++ stageStartProgram N q head ++
    scanProgram N q size (head + 8) ++ finish head

theorem queryROM_stage (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q)) :
    (queryROM q full stage used).semantic.read .input
      (3 + full.length * q + (prepareNormalization q full).indexed.nodes.size * q) = stage := by
  change (((givenTreeROM q full).input ++ [stage]) ++ _).getD _ 0 = _
  rw [List.getD_append _ _ _ _ (by
    rw [List.length_append, PA17QueryCounts008.givenTreeROM_input_length]
    simp only [List.length_cons, List.length_nil]
    omega), List.getD_append_right _ _ _ _ (by
      rw [PA17QueryCounts008.givenTreeROM_input_length])]
  rw [PA17QueryCounts008.givenTreeROM_input_length, Nat.sub_self]
  rfl

theorem addLoop_heap (rom : ROM) (count : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (addLoop count) state).heap = state.heap := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    rw [addLoop, List.replicate_succ, IndexedClosureRAM.execute]
    exact ih _

theorem addLoop_register (rom : ROM) (count : Nat) (state : State) (register : Register) (hne : register ≠ .total) :
    (IndexedClosureRAM.execute rom (addLoop count) state).register register = state.register register := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    rw [addLoop, List.replicate_succ, IndexedClosureRAM.execute]
    change (IndexedClosureRAM.execute rom (addLoop count)
      ((.base (.add .total .total .old) : Op).execute rom state)).register register = _
    rw [ih]
    exact Function.update_of_ne hne _ _

theorem addLoop_total (rom : ROM) (count : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (addLoop count) state).register .total =
      state.register .total + count * state.register .old := by
  induction count generalizing state with
  | zero => simp only [addLoop, List.replicate_zero, IndexedClosureRAM.execute, Nat.zero_mul, Nat.add_zero]
  | succ count ih =>
    rw [addLoop, List.replicate_succ, IndexedClosureRAM.execute]
    change (IndexedClosureRAM.execute rom (addLoop count)
      ((.base (.add .total .total .old) : Op).execute rom state)).register .total = _
    rw [ih]
    change (state.register .total + state.register .old) + count * state.register .old = _
    ring

theorem save_heap (rom : ROM) (target : Nat) (source : Register) (hne : source ≠ .index) (state : State) :
    (IndexedClosureRAM.execute rom (save target source) state).heap =
      Function.update state.heap target (state.register source) := by
  change Function.update state.heap target (Function.update state.register .index target source) = _
  rw [Function.update_of_ne hne]

theorem activeInit_flag (rom : ROM) (N : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (activeInit N) state).register .flag =
      if state.register .old < N then 1 else 0 := by
  change (if N - state.register .old = 0 then 0 else 1) = _
  by_cases h : state.register .old < N <;> simp [Nat.sub_eq_zero_iff_le, h, show (N ≤ state.register .old) ↔ ¬state.register .old < N by omega]

theorem stageStartProgram_heap (rom : ROM) (N q head : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (stageStartProgram N q head) state).heap =
      Function.update state.heap (head + 8) (3 + q * min (state.heap (head + 3)) (N - 1)) := by
  rw [stageStartProgram, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append,
    save_heap rom _ .total (by decide), addLoop_heap, addLoop_total]
  rfl

theorem bitBlock_heap (rom : ROM) (N q rowScratch node tool : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (bitBlock N q rowScratch node tool) state).heap = state.heap := rfl

theorem bitBlock_value (rom : ROM) (N q rowScratch node tool : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (bitBlock N q rowScratch node tool) state).register .value = state.register .value := rfl

theorem bitBlock_total (rom : ROM) (N q rowScratch node tool stage : Nat) (state : State)
    (hrow : state.heap rowScratch = 3 + stage * q) :
    (IndexedClosureRAM.execute rom (bitBlock N q rowScratch node tool) state).register .total =
      state.register .total + PA17StageMap001.difference rom N q stage node tool := by
  change state.register .total + ((rom.read .input (state.heap rowScratch + tool) -
      rom.read .input (3 + N * q + node * q + tool)) +
      (rom.read .input (3 + N * q + node * q + tool) - rom.read .input (state.heap rowScratch + tool))) = _
  rw [hrow]
  rfl

theorem bits_heap (rom : ROM) (N q rowScratch node : Nat) (tools : List Nat) (state : State) :
    (IndexedClosureRAM.execute rom (tools.flatMap (bitBlock N q rowScratch node)) state).heap = state.heap := by
  induction tools generalizing state with
  | nil => rfl
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, bitBlock_heap]

theorem bits_value (rom : ROM) (N q rowScratch node : Nat) (tools : List Nat) (state : State) :
    (IndexedClosureRAM.execute rom (tools.flatMap (bitBlock N q rowScratch node)) state).register .value = state.register .value := by
  induction tools generalizing state with
  | nil => rfl
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, bitBlock_value]

theorem bits_total (rom : ROM) (N q rowScratch node stage : Nat) (tools : List Nat) (state : State)
    (hrow : state.heap rowScratch = 3 + stage * q) :
    (IndexedClosureRAM.execute rom (tools.flatMap (bitBlock N q rowScratch node)) state).register .total =
      state.register .total + (tools.map (PA17StageMap001.difference rom N q stage node)).sum := by
  induction tools generalizing state with
  | nil => simp only [List.flatMap_nil, IndexedClosureRAM.execute, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append,
      ih _ (by rw [bitBlock_heap]; exact hrow), bitBlock_total _ _ _ _ _ _ _ state hrow]
    simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem nodeBlock_heap (rom : ROM) (N q rowScratch node : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (nodeBlock N q rowScratch node) state).heap = state.heap := by
  rw [nodeBlock, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  change (IndexedClosureRAM.execute rom ((List.range q).flatMap (bitBlock N q rowScratch node))
    (IndexedClosureRAM.execute rom [.base (.constant .total 0)] state)).heap = _
  rw [bits_heap]
  rfl

theorem nodeBlock_value (rom : ROM) (N q rowScratch node stage : Nat) (state : State)
    (hrow : state.heap rowScratch = 3 + stage * q) :
    (IndexedClosureRAM.execute rom (nodeBlock N q rowScratch node) state).register .value =
      if PA17StageMap001.mismatch rom N q stage node = 0 then node + 1 else state.register .value := by
  rw [nodeBlock, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  change (if (IndexedClosureRAM.execute rom ((List.range q).flatMap (bitBlock N q rowScratch node))
      (IndexedClosureRAM.execute rom [.base (.constant .total 0)] state)).register .total = 0 then node + 1
    else (IndexedClosureRAM.execute rom ((List.range q).flatMap (bitBlock N q rowScratch node))
      (IndexedClosureRAM.execute rom [.base (.constant .total 0)] state)).register .value) = _
  rw [bits_total rom N q rowScratch node stage (List.range q)
    (IndexedClosureRAM.execute rom [.base (.constant .total 0)] state) (by exact hrow), bits_value]
  have hi : (IndexedClosureRAM.execute rom [.base (.constant .total 0)] state).register .total = 0 := rfl
  have hv : (IndexedClosureRAM.execute rom [.base (.constant .total 0)] state).register .value = state.register .value := rfl
  rw [hi, hv, Nat.zero_add]
  rfl

theorem nodes_value_eq (rom : ROM) (N q rowScratch stage : Nat) (nodes : List Nat)
    (fresh old : State) (hrow : fresh.heap rowScratch = 3 + stage * q)
    (hvalue : fresh.register .value = old.register .value) :
    (IndexedClosureRAM.execute rom (nodes.flatMap (nodeBlock N q rowScratch)) fresh).register .value =
      (IndexedClosureRAM.execute rom (nodes.flatMap (PA17StageMap001.nodeBlock N q stage)) old).register .value := by
  induction nodes generalizing fresh old with
  | nil => exact hvalue
  | cons node later ih =>
    rw [List.flatMap_cons, List.flatMap_cons, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
    apply ih
    · rw [nodeBlock_heap]
      exact hrow
    · rw [nodeBlock_value _ _ _ _ _ _ fresh hrow, PA17StageMap001.nodeBlock_value, hvalue]

theorem prepared_scan_result (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (rowScratch : Nat) (stage : Fin full.length) (state : State)
    (hrow : state.heap rowScratch = 3 + stage.val * q) :
    let cache := (prepareNormalization q full).indexed
    (IndexedClosureRAM.execute (givenTreeROM q full).semantic
      (scanProgram full.length q cache.nodes.size rowScratch) state).register .value =
      encodedNode cache (IndexedQuery.storedStageNode q full hq stage) := by
  intro cache
  have hN : full.length ≠ 0 := by have := stage.isLt; omega
  have hreference := PA17StageMap001.prepared_stageBlock_result q full hq 0 stage state
  dsimp only at hreference
  rw [PA17StageMap001.stageBlock_heap, Function.update_self] at hreference
  rw [scanProgram, ite_eq_right hN, IndexedClosureRAM.execute_append]
  exact (nodes_value_eq _ full.length q rowScratch stage.val (List.range cache.nodes.size)
    (IndexedClosureRAM.execute (givenTreeROM q full).semantic [.base (.constant .value 0)] state)
    (IndexedClosureRAM.execute (givenTreeROM q full).semantic [.base (.constant .value 0)] state)
    (by exact hrow) rfl).trans hreference

theorem nodes_value_eq_rom (rom referenceROM : ROM) (N q rowScratch stage : Nat) (nodes : List Nat)
    (hdiff : ∀ node ∈ nodes, PA17StageMap001.mismatch rom N q stage node =
      PA17StageMap001.mismatch referenceROM N q stage node)
    (fresh old : State) (hrow : fresh.heap rowScratch = 3 + stage * q)
    (hvalue : fresh.register .value = old.register .value) :
    (IndexedClosureRAM.execute rom (nodes.flatMap (nodeBlock N q rowScratch)) fresh).register .value =
      (IndexedClosureRAM.execute referenceROM (nodes.flatMap (PA17StageMap001.nodeBlock N q stage)) old).register .value := by
  induction nodes generalizing fresh old with
  | nil => exact hvalue
  | cons node later ih =>
    rw [List.flatMap_cons, List.flatMap_cons, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
    apply ih (fun other ho => hdiff other (List.mem_cons_of_mem _ ho))
    · rw [nodeBlock_heap]
      exact hrow
    · rw [nodeBlock_value _ _ _ _ _ _ fresh hrow, PA17StageMap001.nodeBlock_value,
        hdiff node List.mem_cons_self, hvalue]

theorem queryROM_mismatch (q : Nat) (full : List (Finset (Fin q))) (rawStage : Nat)
    (used : Finset (Fin q)) (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId) :
    PA17StageMap001.mismatch (queryROM q full rawStage used).semantic full.length q stage.val node.val =
      PA17StageMap001.mismatch (givenTreeROM q full).semantic full.length q stage.val node.val := by
  unfold PA17StageMap001.mismatch
  apply congrArg List.sum
  apply List.map_congr_left
  intro tool ht
  have htq : tool < q := List.mem_range.mp ht
  have hstage : 3 + stage.val * q + tool < (givenTreeROM q full).input.length := by
    rw [PA17QueryCounts008.givenTreeROM_input_length]
    have hm := Nat.mul_le_mul_right q (Nat.succ_le_of_lt stage.isLt)
    rw [Nat.succ_mul] at hm
    omega
  dsimp only [PA17StageMap001.difference]
  rw [PA17QueryCounts008.queryROM_tree_input_read q full rawStage used _ hstage,
    PA17QueryCounts008.queryROM_node_bit q full rawStage used node ⟨tool, htq⟩,
    UniformTreeMetadataRAM.givenTreeROM_node_bit q full node ⟨tool, htq⟩]

theorem prepared_query_scan_result (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (rawStage : Nat) (used : Finset (Fin q)) (rowScratch : Nat) (stage : Fin full.length) (state : State)
    (hrow : state.heap rowScratch = 3 + stage.val * q) :
    let cache := (prepareNormalization q full).indexed
    (IndexedClosureRAM.execute (queryROM q full rawStage used).semantic
      (scanProgram full.length q cache.nodes.size rowScratch) state).register .value =
      encodedNode cache (IndexedQuery.storedStageNode q full hq stage) := by
  intro cache
  have hN : full.length ≠ 0 := by have := stage.isLt; omega
  have hreference := PA17StageMap001.prepared_stageBlock_result q full hq 0 stage state
  dsimp only at hreference
  rw [PA17StageMap001.stageBlock_heap, Function.update_self] at hreference
  rw [scanProgram, ite_eq_right hN, IndexedClosureRAM.execute_append]
  apply Eq.trans (nodes_value_eq_rom _ _ full.length q rowScratch stage.val (List.range cache.nodes.size)
    (fun node hn => queryROM_mismatch q full rawStage used stage ⟨node, List.mem_range.mp hn⟩)
    (IndexedClosureRAM.execute (queryROM q full rawStage used).semantic [.base (.constant .value 0)] state)
    (IndexedClosureRAM.execute (givenTreeROM q full).semantic [.base (.constant .value 0)] state)
    (by exact hrow) rfl)
  exact hreference

theorem save_register (rom : ROM) (target : Nat) (source register : Register)
    (hne : register ≠ .index) (state : State) :
    (IndexedClosureRAM.execute rom (save target source) state).register register = state.register register :=
  Function.update_of_ne hne _ _

theorem readStage_old (rom : ROM) (N q size head : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (readStage N q size head) state).register .old =
      rom.read .input (3 + N * q + size * q) := rfl

theorem readStage_heap (rom : ROM) (N q size head : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (readStage N q size head) state).heap =
      Function.update state.heap (head + 3) (rom.read .input (3 + N * q + size * q)) := by
  rw [readStage, IndexedClosureRAM.execute_append, save_heap _ _ .old (by decide)]
  rfl

def rowArithmetic (q size : Nat) : List Op :=
  [.base (.constant .fresh 1), .base (.add .old .old .fresh), .base (.constant .total 0)] ++
    addLoop (stride q size) ++ [.base (.select .total .flag .total .address)]

theorem rowProgram_split (N q size head : Nat) :
    rowProgram N q size head = activeInit N ++ save (head + 2) .flag ++ rowArithmetic q size ++ save head .total := by
  simp only [rowProgram, rowArithmetic, List.append_assoc]

theorem rowArithmetic_heap (rom : ROM) (q size : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (rowArithmetic q size) state).heap = state.heap := by
  rw [rowArithmetic, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  change (IndexedClosureRAM.execute rom (addLoop (stride q size)) _).heap = _
  rw [addLoop_heap]
  rfl

theorem rowArithmetic_total (rom : ROM) (q size : Nat) (state : State) (hz : state.register .address = 0) :
    (IndexedClosureRAM.execute rom (rowArithmetic q size) state).register .total =
      if state.register .flag = 0 then 0 else (state.register .old + 1) * stride q size := by
  rw [rowArithmetic, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  change (if (IndexedClosureRAM.execute rom (addLoop (stride q size)) _).register .flag = 0
    then (IndexedClosureRAM.execute rom (addLoop (stride q size)) _).register .address
    else (IndexedClosureRAM.execute rom (addLoop (stride q size)) _).register .total) = _
  rw [addLoop_register _ _ _ .flag (by decide), addLoop_register _ _ _ .address (by decide), addLoop_total]
  change (if state.register .flag = 0 then state.register .address else 0 + stride q size * (state.register .old + 1)) = _
  rw [hz, Nat.zero_add]
  split_ifs <;> ring

theorem rowProgram_heap (rom : ROM) (N q size head : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (rowProgram N q size head) state).heap =
      Function.update (Function.update state.heap (head + 2) (if state.register .old < N then 1 else 0))
        head (if state.register .old < N then (state.register .old + 1) * stride q size else 0) := by
  rw [rowProgram_split, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append,
    save_heap _ _ .total (by decide), rowArithmetic_heap,
    rowArithmetic_total _ _ _ _ (by rfl), save_heap _ _ .flag (by decide)]
  change Function.update (Function.update state.heap (head + 2)
    ((IndexedClosureRAM.execute rom (activeInit N) state).register .flag)) head
      (if ((IndexedClosureRAM.execute rom (activeInit N) state).register .flag) = 0 then 0
        else (state.register .old + 1) * stride q size) = _
  rw [activeInit_flag]
  by_cases h : state.register .old < N <;> simp [h]

theorem scanNodes_heap (rom : ROM) (N q rowScratch : Nat) (nodes : List Nat) (state : State) :
    (IndexedClosureRAM.execute rom (nodes.flatMap (nodeBlock N q rowScratch)) state).heap = state.heap := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, nodeBlock_heap]

theorem scanProgram_heap (rom : ROM) (N q size rowScratch : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (scanProgram N q size rowScratch) state).heap = state.heap := by
  rw [scanProgram, IndexedClosureRAM.execute_append]
  by_cases hN : N = 0
  · rw [ite_eq_left hN]
    rfl
  · rw [ite_eq_right hN, scanNodes_heap]
    rfl

theorem set_heap (rom : ROM) (target value : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (set target value) state).heap = Function.update state.heap target value := by
  rw [set, execute_base, IndexedCellRAM.execute_constantBlock_heap]

theorem finish_heap (rom : ROM) (head : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (finish head) state).heap =
      Function.update (Function.update (Function.update (Function.update
        (Function.update state.heap (head + 1) (if state.heap (head + 2) = 0 then 0 else state.register .value))
          (head + 4) 0) (head + 5) 0) (head + 6) 0) (head + 7) 0 := by
  simp only [finish, IndexedClosureRAM.execute_append, set_heap, save_heap _ _ .value (by decide)]
  rfl

def active (N stage : Nat) : Nat := if stage < N then 1 else 0
def rowPointer (N q size stage : Nat) : Nat := if stage < N then (stage + 1) * stride q size else 0

def nodeWord (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (stage : Fin (full.length + 1)) : Nat :=
  if hs : stage.val < full.length then
    encodedNode (prepareNormalization q full).indexed (IndexedQuery.storedStageNode q full hq ⟨stage.val, hs⟩)
  else 0

def HeaderCorrect (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (stage : Fin (full.length + 1)) (head : Nat) (heap : Nat → Nat) : Prop :=
  let size := (prepareNormalization q full).indexed.nodes.size
  heap head = rowPointer full.length q size stage.val ∧
    heap (head + 1) = nodeWord q full hq stage ∧
    heap (head + 2) = active full.length stage.val ∧ heap (head + 3) = stage.val ∧
    ∀ offset < 4, heap (head + 4 + offset) = 0

theorem prepared_program_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (head : Nat) (state : State) :
    HeaderCorrect q full hq stage head (IndexedClosureRAM.execute (queryROM q full stage.val used).semantic
      (program full.length q (prepareNormalization q full).indexed.nodes.size head) state).heap := by
  let size := (prepareNormalization q full).indexed.nodes.size
  let rom := (queryROM q full stage.val used).semantic
  let a := IndexedClosureRAM.execute rom (readStage full.length q size head) state
  let b := IndexedClosureRAM.execute rom (rowProgram full.length q size head) a
  let c := IndexedClosureRAM.execute rom (stageStartProgram full.length q head) b
  let d := IndexedClosureRAM.execute rom (scanProgram full.length q size (head + 8)) c
  have haold : a.register .old = stage.val := (readStage_old rom _ _ _ _ state).trans (queryROM_stage q full stage.val used)
  have ha : a.heap = Function.update state.heap (head + 3) stage.val := by
    rw [readStage_heap, queryROM_stage]
  have hb : b.heap = Function.update (Function.update a.heap (head + 2) (active full.length stage.val))
      head (rowPointer full.length q size stage.val) := by
    rw [rowProgram_heap, haold]
    rfl
  have hb3 : b.heap (head + 3) = stage.val := by simp [hb, ha]
  have hc : c.heap = Function.update b.heap (head + 8) (3 + q * min stage.val (full.length - 1)) := by
    rw [stageStartProgram_heap, hb3]
  have hd : d.heap = c.heap := scanProgram_heap _ _ _ _ _ c
  have hd0 : d.heap head = rowPointer full.length q size stage.val := by simp [hd, hc, hb]
  have hd2 : d.heap (head + 2) = active full.length stage.val := by simp [hd, hc, hb]
  have hd3 : d.heap (head + 3) = stage.val := by simp [hd, hc, hb, ha]
  have hnode : (if d.heap (head + 2) = 0 then 0 else d.register .value) = nodeWord q full hq stage := by
    rw [hd2]
    by_cases hs : stage.val < full.length
    · have hmin : min stage.val (full.length - 1) = stage.val := Nat.min_eq_left (by omega)
      have hrow : c.heap (head + 8) = 3 + stage.val * q := by rw [hc, Function.update_self, hmin, Nat.mul_comm]
      have hv := prepared_query_scan_result q full hq stage.val used (head + 8) ⟨stage.val, hs⟩ c hrow
      change (if active full.length stage.val = 0 then 0 else d.register .value) = _
      rw [show active full.length stage.val = 1 from by simp [active, hs], ite_eq_right Nat.one_ne_zero,
        nodeWord, dite_eq_left hs]
      exact hv
    · simp [active, nodeWord, hs]
  simp only [program, IndexedClosureRAM.execute_append]
  change HeaderCorrect q full hq stage head (IndexedClosureRAM.execute rom (finish head) d).heap
  rw [finish_heap, hnode]
  constructor
  · simpa using hd0
  · constructor
    · simp
    · constructor
      · simpa using hd2
      · constructor
        · simpa using hd3
        · intro offset ho
          interval_cases offset <;> simp

theorem scanProgram_zero (q size rowScratch : Nat) : scanProgram 0 q size rowScratch = [.base (.constant .value 0)] := rfl

theorem save_length (target : Nat) (source : Register) : (save target source).length = 2 := rfl
theorem save_trace_length (target : Nat) (source : Register) : (trace (save target source)).length = 19 := rfl
theorem set_length (target value : Nat) : (set target value).length = 3 := rfl
theorem set_trace_length (target value : Nat) : (trace (set target value)).length = 27 := rfl
theorem addLoop_length (count : Nat) : (addLoop count).length = count := List.length_replicate

theorem addLoop_trace_length (count : Nat) : (trace (addLoop count)).length = 11 * count := by
  have ho : (Op.trace (.base (.add .total .total .old))).length = 11 := rfl
  simp only [addLoop, trace, List.length_flatMap, List.map_replicate, ho, List.sum_replicate, Nat.nsmul_eq_mul]
  omega

theorem nodeBlock_length (N q rowScratch node : Nat) : (nodeBlock N q rowScratch node).length = 11 * q + 3 := by
  have hb (tool : Nat) : (bitBlock N q rowScratch node tool).length = 11 := rfl
  have ht : (PA17StageMap001.nodeTail node).length = 2 := rfl
  simp only [nodeBlock, List.length_append, List.length_cons, List.length_nil, List.length_flatMap, hb, ht,
    List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

theorem nodeBlock_trace_length (N q rowScratch node : Nat) : (trace (nodeBlock N q rowScratch node)).length = 112 * q + 28 := by
  have hi : (trace [.base (.constant .total 0)]).length = 8 := rfl
  have hb (tool : Nat) : (trace (bitBlock N q rowScratch node tool)).length = 112 := rfl
  have ht : (trace (PA17StageMap001.nodeTail node)).length = 20 := rfl
  rw [nodeBlock, trace_append, trace_append, List.length_append, List.length_append, hi, ht,
    UniformNormalizationRAM.trace_flatMap_length]
  simp only [hb, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

theorem program_length (N q size head : Nat) :
    (program N q size head).length = 43 + stride q size + q + (if N = 0 then 0 else (11 * q + 3) * size) := by
  have hr : (readStage N q size head).length = 4 := rfl
  have ha : (activeInit N).length = 5 := rfl
  have hf : (finish head).length = 18 := rfl
  have hrow : (rowProgram N q size head).length = 13 + stride q size := by
    simp only [rowProgram, List.length_append, ha, save_length, addLoop_length, List.length_cons, List.length_nil]
    omega
  have hs : (stageStartProgram N q head).length = 7 + q := by
    simp only [stageStartProgram, List.length_append, save_length, addLoop_length, List.length_cons, List.length_nil]
    omega
  rw [program, List.length_append, List.length_append, List.length_append, List.length_append, hr, hrow, hs, hf,
    scanProgram, List.length_append]
  by_cases hN : N = 0
  · simp only [hN, ite_true, List.length_cons, List.length_nil]
    omega
  · simp only [hN, ite_false, List.length_cons, List.length_nil, List.length_flatMap,
      nodeBlock_length, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
    ring

theorem program_trace_length (N q size head : Nat) :
    (trace (program N q size head)).length =
      401 + 11 * stride q size + 11 * q + (if N = 0 then 0 else (112 * q + 28) * size) := by
  have hr : (trace (readStage N q size head)).length = 38 := rfl
  have ha : (trace (activeInit N)).length = 47 := rfl
  have hf : (trace (finish head)).length = 166 := rfl
  have hrow : (trace (rowProgram N q size head)).length = 124 + 11 * stride q size := by
    have hi : (trace [.base (.constant .fresh 1), .base (.add .old .old .fresh), .base (.constant .total 0)]).length = 27 := rfl
    have hm : (trace [.base (.select .total .flag .total .address)]).length = 12 := rfl
    simp only [rowProgram, trace_append, List.length_append, ha, save_trace_length, addLoop_trace_length, hi, hm]
    omega
  have hs : (trace (stageStartProgram N q head)).length = 65 + 11 * q := by
    have hi : (trace [.base (.constant .index (head + 3)), .base (.loadHeap .old .index),
      .base (.constant .fresh (N - 1)), .base (.minimum .old .old .fresh), .base (.constant .total 3)]).length = 46 := rfl
    simp only [stageStartProgram, trace_append, List.length_append, save_trace_length, addLoop_trace_length, hi]
    omega
  rw [program, trace_append, trace_append, trace_append, trace_append,
    List.length_append, List.length_append, List.length_append, List.length_append, hr, hrow, hs, hf,
    scanProgram, trace_append, List.length_append]
  have hi : (trace [.base (.constant .value 0)]).length = 8 := rfl
  rw [hi]
  by_cases hN : N = 0
  · simp only [hN, ite_true, trace, List.flatMap_nil, List.length_nil]
    omega
  · rw [ite_eq_right hN, UniformNormalizationRAM.trace_flatMap_length]
    simp only [hN, ite_false, nodeBlock_trace_length, List.map_const', List.sum_replicate,
      List.length_range, Nat.nsmul_eq_mul]
    ring

theorem program_trace_le (N q size head : Nat) (hsize : 0 < size) :
    (trace (program N q size head) ++ haltTrace).length ≤ 512 * queryWork q size := by
  rw [List.length_append, program_trace_length, haltTrace_length]
  have hs : (if N = 0 then 0 else (112 * q + 28) * size) ≤ (112 * q + 28) * size := by split_ifs <;> omega
  have hm : stride q size ≤ 2 * (q + 2) * size := by
    dsimp [stride]
    have hp := Nat.mul_le_mul_left (q + 2) (show size + 1 ≤ 2 * size from by omega)
    nlinarith
  have hq : q ≤ q * size := Nat.le_mul_of_pos_right q hsize
  dsimp [queryWork]
  nlinarith

theorem program_code_le (N q size head : Nat) (hsize : 0 < size) :
    (haltingWords (program N q size head)).length ≤ 256 * queryWork q size := by
  rw [haltingWords_length, program_length]
  have hs : (if N = 0 then 0 else (11 * q + 3) * size) ≤ (11 * q + 3) * size := by split_ifs <;> omega
  have hm : stride q size ≤ 2 * (q + 2) * size := by
    dsimp [stride]
    have hp := Nat.mul_le_mul_left (q + 2) (show size + 1 ≤ 2 * size from by omega)
    nlinarith
  have hq : q ≤ q * size := Nat.le_mul_of_pos_right q hsize
  dsimp [queryWork]
  nlinarith

theorem totalQueryCost_le (N q size head : Nat) (hsize : 0 < size) :
    totalQueryCost q (program N q size head) ≤ 1024 * queryWork q size := by
  have ht := program_trace_le N q size head hsize
  have hc := program_code_le N q size head hsize
  have hw : q + 1 ≤ queryWork q size := Nat.le_mul_of_pos_right (q + 1) hsize
  have hp : 0 < queryWork q size := Nat.mul_pos (by omega) hsize
  dsimp [totalQueryCost]
  omega

open UniformFreeTableSafety

theorem noStore_prefixFrame (rom : ROM) (ops : List Op) (address : Nat)
    (hn : ∀ op ∈ ops, PA17StageMap001.NoStore op) : PrefixFrame rom ops address := by
  intro state count _
  exact congrFun (PA17StageMap001.execute_noStore_heap rom _
    (fun op hm => hn op (List.mem_of_mem_take hm)) state) address

theorem noStore_append (left right : List Op)
    (hl : ∀ op ∈ left, PA17StageMap001.NoStore op) (hr : ∀ op ∈ right, PA17StageMap001.NoStore op) :
    ∀ op ∈ left ++ right, PA17StageMap001.NoStore op := by
  intro op hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hl op hm
  · exact hr op hm

theorem addLoop_noStore (count : Nat) : ∀ op ∈ addLoop count, PA17StageMap001.NoStore op := by
  intro op hm
  obtain ⟨_, rfl⟩ := List.mem_replicate.mp hm
  trivial

theorem bitBlock_noStore (N q rowScratch node tool : Nat) :
    ∀ op ∈ bitBlock N q rowScratch node tool, PA17StageMap001.NoStore op := by
  intro op hm
  simp only [bitBlock, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

theorem scanProgram_noStore (N q size rowScratch : Nat) :
    ∀ op ∈ scanProgram N q size rowScratch, PA17StageMap001.NoStore op := by
  rw [scanProgram]
  apply noStore_append
  · simp [PA17StageMap001.NoStore]
  · by_cases hN : N = 0
    · simp [hN]
    · rw [ite_eq_right hN]
      intro op hm
      obtain ⟨node, _, hm⟩ := List.mem_flatMap.mp hm
      simp only [nodeBlock, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatMap] at hm
      rcases hm with (rfl | ⟨tool, _, hm⟩) | hm
      · trivial
      · exact bitBlock_noStore N q rowScratch node tool op hm
      · simp only [PA17StageMap001.nodeTail, List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with rfl | rfl <;> trivial

theorem save_prefixFrame (rom : ROM) (target : Nat) (source : Register) (address : Nat) (hne : address ≠ target) :
    PrefixFrame rom (save target source) address := by
  intro state count hc
  change count ≤ 2 at hc
  interval_cases count <;>
    simp [save, IndexedClosureRAM.execute, Op.execute, Instruction.execute, hne]

theorem set_prefixFrame (rom : ROM) (target value address : Nat) (hne : address ≠ target) :
    PrefixFrame rom (set target value) address := by
  intro state count hc
  change count ≤ 3 at hc
  interval_cases count <;>
    simp [set, IndexedCellRAM.constantBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, hne]

theorem readStage_prefixFrame (rom : ROM) (N q size head address : Nat) (ha : address ≠ head + 3) :
    PrefixFrame rom (readStage N q size head) address := by
  rw [readStage]
  apply PrefixFrame.append
  · apply noStore_prefixFrame
    simp [PA17StageMap001.NoStore]
  · exact save_prefixFrame rom _ .old address ha

theorem rowProgram_prefixFrame (rom : ROM) (N q size head address : Nat)
    (h0 : address ≠ head) (h2 : address ≠ head + 2) : PrefixFrame rom (rowProgram N q size head) address := by
  rw [rowProgram_split]
  apply PrefixFrame.append
  · apply PrefixFrame.append
    · apply PrefixFrame.append
      · apply noStore_prefixFrame
        simp [activeInit, PA17StageMap001.NoStore]
      · exact save_prefixFrame rom _ .flag address h2
    · apply noStore_prefixFrame
      rw [rowArithmetic]
      apply noStore_append
      · apply noStore_append
        · simp [PA17StageMap001.NoStore]
        · exact addLoop_noStore _
      · simp [PA17StageMap001.NoStore]
  · exact save_prefixFrame rom _ .total address h0

theorem stageStart_prefixFrame (rom : ROM) (N q head address : Nat) (ha : address ≠ head + 8) :
    PrefixFrame rom (stageStartProgram N q head) address := by
  rw [stageStartProgram]
  apply PrefixFrame.append
  · apply PrefixFrame.append
    · apply noStore_prefixFrame
      simp [PA17StageMap001.NoStore]
    · exact noStore_prefixFrame rom _ address (addLoop_noStore _)
  · exact save_prefixFrame rom _ .total address ha

theorem finish_prefixFrame (rom : ROM) (head address : Nat)
    (ha : ∀ offset ≤ 8, address ≠ head + offset) : PrefixFrame rom (finish head) address := by
  rw [finish]
  apply PrefixFrame.append
  · apply PrefixFrame.append
    · apply PrefixFrame.append
      · apply PrefixFrame.append
        · apply PrefixFrame.append
          · apply noStore_prefixFrame
            simp [PA17StageMap001.NoStore]
          · exact save_prefixFrame rom _ .value address (ha 1 (by omega))
        · exact set_prefixFrame rom _ _ address (ha 4 (by omega))
      · exact set_prefixFrame rom _ _ address (ha 5 (by omega))
    · exact set_prefixFrame rom _ _ address (ha 6 (by omega))
  · exact set_prefixFrame rom _ _ address (ha 7 (by omega))

theorem program_prefixFrame (rom : ROM) (N q size head address : Nat)
    (ha : address < head ∨ head + 9 ≤ address) : PrefixFrame rom (program N q size head) address := by
  have hf (offset : Nat) (ho : offset ≤ 8) : address ≠ head + offset := by omega
  rw [program]
  apply PrefixFrame.append
  · apply PrefixFrame.append
    · apply PrefixFrame.append
      · apply PrefixFrame.append
        · exact readStage_prefixFrame rom N q size head address (hf 3 (by omega))
        · exact rowProgram_prefixFrame rom N q size head address (by simpa only [Nat.add_zero] using hf 0 (by omega)) (hf 2 (by omega))
      · exact stageStart_prefixFrame rom N q head address (hf 8 le_rfl)
    · exact noStore_prefixFrame rom _ address (scanProgram_noStore _ _ _ _)
  · exact finish_prefixFrame rom head address hf

theorem program_take_frame (rom : ROM) (N q size head count : Nat) (state : State)
    (address : Nat) (ha : address < head ∨ head + 9 ≤ address) :
    (IndexedClosureRAM.execute rom ((program N q size head).take count) state).heap address = state.heap address := by
  by_cases hc : count ≤ (program N q size head).length
  · exact program_prefixFrame rom N q size head address ha state count hc
  · rw [List.take_of_length_le (by omega)]
    simpa only [List.take_length] using
      program_prefixFrame rom N q size head address ha state (program N q size head).length le_rfl

theorem program_capacityThroughout (rom : PhysicalROM) (N q size head capWords : Nat)
    (hbase : capWords ≤ head) (state : State) (hcap : CapacityPrefixBounded q capWords state.heap) :
    CapacityThroughout q capWords rom (program N q size head) state := by
  intro count _ address ha
  rw [program_take_frame rom.semantic N q size head count state address (Or.inl (by omega))]
  exact hcap address ha

theorem prepared_halting_run (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (head : Nat) (state : State) (hpc : state.pc = 0) :
    let size := (prepareNormalization q full).indexed.nodes.size
    ∃ final operations,
      HaltingRuns (queryROM q full stage.val used).semantic (program full.length q size head) state final operations ∧
      HeaderCorrect q full hq stage head final.heap ∧
      (∀ address, address < head ∨ head + 9 ≤ address → final.heap address = state.heap address) ∧
      operations.length ≤ 512 * queryWork q size := by
  intro size
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hsize : 0 < size := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  refine ⟨_, _, IndexedClosureRAM.execute_halts _ _ state hpc,
    prepared_program_correct q full hq stage used head state, ?_, program_trace_le _ _ _ _ hsize⟩
  intro address ha
  simpa only [List.take_length] using program_take_frame (queryROM q full stage.val used).semantic full.length q size head
    (program full.length q size head).length state address ha

end PaperProofs.Structure.LaminarTree.PA17QueryHeader009

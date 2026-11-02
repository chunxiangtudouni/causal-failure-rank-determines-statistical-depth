module

public import PaperProofs.Structure.PA17_QueryTests_009
public import PaperProofs.Structure.PA17_QueryHeaderWord_022a

/-! Actual prefix register and access bounds for the dynamic budget tests.
Only values at addresses actually read by Tests009 are bounded. In particular,
unrelated protected heap words remain arbitrary, and VOID payloads use only
the original physical capacity bound. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17QueryTestsWord028

open IndexedRAM IndexedClosureRAM AlgorithmClaims
open PA17QueryTests009 PA17QueryHeaderWord022

structure Layout (B heapWords size q protectedLimit goodFlags badFlags : Nat) : Prop where
  protected_le : protectedLimit ≤ B
  protected_access : protectedLimit ≤ heapWords
  q_le : q ≤ B
  size_le : size ≤ B
  size_pos : 0 < size
  good_protected : protectedLimit ≤ goodFlags
  bad_protected : protectedLimit ≤ badFlags
  good_le : goodFlags + q + 2 ≤ B
  bad_le : badFlags + q + 2 ≤ B
  good_access : goodFlags + q + 2 ≤ heapWords
  bad_access : badFlags + q + 2 ≤ heapWords

structure ReadValuesBound (size q rowPointer countsBase parentBase nodePointer rowBase : Nat)
    (heap : Nat → Nat) : Prop where
  row_pointer : heap rowPointer = rowBase
  node_pointer : heap nodePointer ≤ size
  counts : ∀ node < size, heap (countsBase + node) ≤ q
  parents : ∀ encoded ≤ size, heap (parentBase + encoded) ≤ size
  row : ∀ budget : Fin (q + 2), ∀ index ≤ size,
    heap (rowBase + budget.val * (size + 1) + index) ≤ q

theorem ReadValuesBound.of_capacity (size q rowPointer countsBase parentBase nodePointer rowBase words : Nat)
    (heap : Nat → Nat) (hrow : heap rowPointer = rowBase) (hnode : heap nodePointer ≤ size)
    (hcounts : ∀ node < size, heap (countsBase + node) ≤ q)
    (hparents : ∀ encoded ≤ size, heap (parentBase + encoded) ≤ size)
    (htable : rowBase + (q + 2) * (size + 1) ≤ words)
    (hcapacity : CapacityPrefixBounded q words heap) :
    ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase heap := by
  refine ⟨hrow, hnode, hcounts, hparents, ?_⟩
  intro budget index hi
  exact hcapacity _ (rowWord_lt size q rowBase words htable budget index hi)

theorem ReadValuesBound.transfer (size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit : Nat)
    (hb : ReadBounds size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (heap heap' : Nat → Nat)
    (hv : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase heap)
    (hf : ∀ address < protectedLimit, heap' address = heap address) :
    ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase heap' := by
  constructor
  · rw [hf rowPointer hb.row_pointer]; exact hv.row_pointer
  · rw [hf nodePointer hb.node_pointer]; exact hv.node_pointer
  · intro node hn
    rw [hf (countsBase + node) (by have := hb.counts; omega)]
    exact hv.counts node hn
  · intro encoded he
    rw [hf (parentBase + encoded) (by have := hb.parents; omega)]
    exact hv.parents encoded he
  · intro budget index hi
    rw [hf _ (rowWord_lt size q rowBase protectedLimit hb.table budget index hi)]
    exact hv.row budget index hi

theorem acceptInit_numeric (B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q protectedLimit goodFlags badFlags)
    (hb : ReadBounds size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (budget : Fin (q + 2)) (state : State)
    (hv : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (acceptInit size rowPointer budget.val) state := by
  have ha := rowWord_lt size q rowBase protectedLimit hb.table budget 0 (Nat.zero_le _)
  simp only [Nat.add_zero] at ha
  have hvalue := hv.row budget 0 (Nat.zero_le _)
  simp only [Nat.add_zero] at hvalue
  have hp := hb.row_pointer
  have hB := hl.protected_le
  have hH := hl.protected_access
  have hq := hl.q_le
  have hone : 1 ≤ B := by have := hl.size_pos; have := hl.size_le; omega
  constructor
  · intro k hk r
    have hreg := hr r
    change k ≤ 8 at hk
    interval_cases k <;> cases r <;>
      simp [acceptInit, IndexedClosureRAM.execute, Op.execute, Instruction.execute, hv.row_pointer, Nat.add_assoc]
    all_goals (try split_ifs)
    all_goals omega
  · intro k hk
    change k < 8 at hk
    interval_cases k <;>
      simp [acceptInit, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, hv.row_pointer, Nat.add_assoc]
    all_goals omega

theorem acceptNode_numeric (B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q protectedLimit goodFlags badFlags)
    (hb : ReadBounds size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (budget : Fin (q + 2)) (node : Nat) (hn : node < size) (state : State)
    (hv : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (acceptNode size rowPointer countsBase budget.val node) state := by
  have ha := rowWord_lt size q rowBase protectedLimit hb.table budget (1 + node) (by omega)
  simp only [Nat.add_assoc] at ha
  have hvalue := hv.row budget (1 + node) (by omega)
  simp only [Nat.add_assoc] at hvalue
  have hcount := hv.counts node hn
  have hp := hb.row_pointer
  have hc := hb.counts
  have hB := hl.protected_le
  have hH := hl.protected_access
  have hq := hl.q_le
  constructor
  · intro k hk r
    have hreg := hr r
    change k ≤ 10 at hk
    interval_cases k <;> cases r <;>
      simp [acceptNode, IndexedClosureRAM.execute, Op.execute, Instruction.execute, hv.row_pointer, Nat.add_assoc]
    all_goals (try split_ifs)
    all_goals omega
  · intro k hk
    change k < 10 at hk
    interval_cases k <;>
      simp [acceptNode, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, hv.row_pointer, Nat.add_assoc]
    all_goals omega

theorem storeFlag_numeric (B heapWords : Nat) (rom : PhysicalROM) (target : Nat)
    (ht : target ≤ B) (ha : target < heapWords) (state : State) (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (storeFlag target) state := by
  constructor
  · intro k hk r
    have hreg := hr r
    change k ≤ 2 at hk
    interval_cases k <;> cases r <;>
      simp [storeFlag, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro k hk
    change k < 2 at hk
    interval_cases k <;> simp [storeFlag, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, ha]

theorem badInit_numeric (B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q protectedLimit goodFlags badFlags)
    (hb : ReadBounds size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (state : State) (hv : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (badInit nodePointer) state := by
  have hp := hb.node_pointer
  have hvn := hv.node_pointer
  have hB := hl.protected_le
  have hH := hl.protected_access
  have hs := hl.size_le
  have hone : 1 ≤ B := by have := hl.size_pos; omega
  constructor
  · intro k hk r
    have hreg := hr r
    change k ≤ 5 at hk
    interval_cases k <;> cases r <;>
      simp [badInit, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals (try split_ifs)
    all_goals omega
  · intro k hk
    change k < 5 at hk
    interval_cases k <;> simp [badInit, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits]
    all_goals omega

theorem badNode_numeric (B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q protectedLimit goodFlags badFlags)
    (hb : ReadBounds size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (budget : Fin (q + 2)) (state : State)
    (hv : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase state.heap)
    (hr : RegistersLE (2 * B) state) (hn : state.register .address ≤ size) (hone : state.register .total = 1) :
    NumericSafe (2 * B) heapWords rom (badNode size rowPointer countsBase parentBase budget.val) state := by
  have hnode : state.register .address - 1 < size := by have := hl.size_pos; omega
  have ha := rowWord_lt size q rowBase protectedLimit hb.table budget
    (1 + (state.register .address - 1)) (by omega)
  have hvalue := hv.row budget (1 + (state.register .address - 1)) (by omega)
  simp only [Nat.add_assoc] at ha hvalue
  have hcount := hv.counts (state.register .address - 1) hnode
  have hparent := hv.parents (state.register .address) hn
  have hp := hb.row_pointer
  have hc := hb.counts
  have hparents := hb.parents
  have hB := hl.protected_le
  have hH := hl.protected_access
  have hq := hl.q_le
  have hs := hl.size_le
  have hflag := hr .flag
  constructor
  · intro k hk r
    have hreg := hr r
    change k ≤ 18 at hk
    interval_cases k <;> cases r <;>
      simp [badNode, IndexedClosureRAM.execute, Op.execute, Instruction.execute, hv.row_pointer, hone, Nat.add_assoc]
    all_goals (try split_ifs)
    all_goals omega
  · intro k hk
    change k < 18 at hk
    interval_cases k <;>
      simp [badNode, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, hv.row_pointer, hone, Nat.add_assoc]
    all_goals omega

theorem acceptNodes_numeric (B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q protectedLimit goodFlags badFlags)
    (hb : ReadBounds size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (budget : Fin (q + 2)) (nodes : List Nat) (hn : ∀ node ∈ nodes, node < size) (state : State)
    (hv : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (nodes.flatMap (acceptNode size rowPointer countsBase budget.val)) state := by
  induction nodes generalizing state with
  | nil =>
    constructor
    · intro _ _; simpa [badLoop, IndexedClosureRAM.execute] using hr
    · intro k hk; simp at hk
  | cons node later ih =>
    rw [List.flatMap_cons]
    have hs := acceptNode_numeric B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit
      goodFlags badFlags rom hl hb budget node (hn node List.mem_cons_self) state hv hr
    apply NumericSafe.append _ _ _ _ _ _ hs
    apply ih (fun target ht => hn target (List.mem_cons_of_mem node ht))
    · rw [acceptNode_heap]; exact hv
    · exact hs.final _ _ _ _ _

theorem acceptProgram_numeric (B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q protectedLimit goodFlags badFlags)
    (hb : ReadBounds size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (budget : Fin (q + 2)) (state : State)
    (hv : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (acceptProgram size rowPointer countsBase budget.val) state := by
  have hi := acceptInit_numeric B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit
    goodFlags badFlags rom hl hb budget state hv hr
  rw [acceptProgram]
  apply NumericSafe.append _ _ _ _ _ _ hi
  apply acceptNodes_numeric B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit
    goodFlags badFlags rom hl hb budget (List.range size) (fun node hn => List.mem_range.mp hn)
  · rw [acceptInit_heap]; exact hv
  · exact hi.final _ _ _ _ _

theorem badLoop_numeric (B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q protectedLimit goodFlags badFlags)
    (hb : ReadBounds size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (budget : Fin (q + 2)) (fuel : Nat) (state : State)
    (hv : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase state.heap)
    (hr : RegistersLE (2 * B) state) (hn : state.register .address ≤ size) (hone : state.register .total = 1) :
    NumericSafe (2 * B) heapWords rom (badLoop size rowPointer countsBase parentBase budget.val fuel) state := by
  induction fuel generalizing state with
  | zero =>
    constructor
    · intro _ _; simpa [badLoop, IndexedClosureRAM.execute] using hr
    · intro k hk; simp [badLoop] at hk
  | succ fuel ih =>
    rw [badLoop_succ]
    have hs := badNode_numeric B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit
      goodFlags badFlags rom hl hb budget state hv hr hn hone
    apply NumericSafe.append _ _ _ _ _ _ hs
    apply ih
    · rw [badNode_heap]; exact hv
    · exact hs.final _ _ _ _ _
    · rw [badNode_address]; exact hv.parents (state.register .address) hn
    · rw [badNode_total]; exact hone

theorem badProgram_numeric (B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q protectedLimit goodFlags badFlags)
    (hb : ReadBounds size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (budget : Fin (q + 2)) (state : State)
    (hv : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (badProgram size rowPointer countsBase parentBase nodePointer budget.val) state := by
  have hi := badInit_numeric B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit
    goodFlags badFlags rom hl hb state hv hr
  rw [badProgram]
  apply NumericSafe.append _ _ _ _ _ _ hi
  apply badLoop_numeric B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit
    goodFlags badFlags rom hl hb budget size
  · exact hv
  · exact hi.final _ _ _ _ _
  · rw [badInit_address]; exact hv.node_pointer
  · exact badInit_total rom.semantic nodePointer state

theorem storeFlag_readValues (size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit target : Nat)
    (rom : ROM) (hb : ReadBounds size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (ht : protectedLimit ≤ target) (state : State)
    (hv : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase state.heap) :
    ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase
      (execute rom (storeFlag target) state).heap := by
  apply hv.transfer _ _ _ _ _ _ _ _ hb state.heap _
  intro address ha
  rw [storeFlag_heap, Function.update_of_ne (by omega)]

theorem budgetProgram_readValues (B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q protectedLimit goodFlags badFlags)
    (hb : ReadBounds size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (budget : Fin (q + 2)) (state : State)
    (hv : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase state.heap) :
    ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase
      (execute rom.semantic (budgetProgram size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget.val) state).heap := by
  apply hv.transfer _ _ _ _ _ _ _ _ hb state.heap _
  intro address ha
  have hg := hl.good_protected
  have hbad := hl.bad_protected
  have hf := budgetProgram_prefixFrame rom.semantic size rowPointer countsBase parentBase nodePointer goodFlags badFlags
    budget.val address (by omega) (by omega) state
    (budgetProgram size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget.val).length le_rfl
  simpa only [List.take_length] using hf

theorem budgetProgram_numeric (B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q protectedLimit goodFlags badFlags)
    (hb : ReadBounds size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (budget : Fin (q + 2)) (state : State)
    (hv : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom
      (budgetProgram size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget.val) state := by
  let accepted := execute rom.semantic (acceptProgram size rowPointer countsBase budget.val) state
  have h1 := acceptProgram_numeric B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit
    goodFlags badFlags rom hl hb budget state hv hr
  have hv1 : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase accepted.heap := by
    dsimp only [accepted]; rw [acceptProgram_heap]; exact hv
  have h2 := storeFlag_numeric B heapWords rom (goodFlags + budget.val)
    (by have := hl.good_le; have := budget.isLt; omega)
    (by have := hl.good_access; have := budget.isLt; omega) accepted (h1.final _ _ _ _ _)
  let goodStored := execute rom.semantic (storeFlag (goodFlags + budget.val)) accepted
  have hv2 : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase goodStored.heap :=
    storeFlag_readValues size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit _ rom.semantic hb
      (by have := hl.good_protected; omega) accepted hv1
  have h3 := badProgram_numeric B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit
    goodFlags badFlags rom hl hb budget goodStored hv2 (h2.final _ _ _ _ _)
  let tested := execute rom.semantic (badProgram size rowPointer countsBase parentBase nodePointer budget.val) goodStored
  have h4 := storeFlag_numeric B heapWords rom (badFlags + budget.val)
    (by have := hl.bad_le; have := budget.isLt; omega)
    (by have := hl.bad_access; have := budget.isLt; omega) tested (h3.final _ _ _ _ _)
  simp only [budgetProgram, List.append_assoc]
  exact NumericSafe.append _ _ _ _ _ _ h1
    (NumericSafe.append _ _ _ _ _ _ h2 (NumericSafe.append _ _ _ _ _ _ h3 h4))

theorem budgets_numeric (B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q protectedLimit goodFlags badFlags)
    (hb : ReadBounds size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (budgets : List (Fin (q + 2))) (state : State)
    (hv : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom
      (budgets.flatMap (fun budget => budgetProgram size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget.val)) state := by
  induction budgets generalizing state with
  | nil =>
    constructor
    · intro _ _; simpa [badLoop, IndexedClosureRAM.execute] using hr
    · intro k hk; simp at hk
  | cons budget later ih =>
    rw [List.flatMap_cons]
    have hs := budgetProgram_numeric B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit
      goodFlags badFlags rom hl hb budget state hv hr
    apply NumericSafe.append _ _ _ _ _ _ hs
    exact ih _ (budgetProgram_readValues B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit
      goodFlags badFlags rom hl hb budget state hv) (hs.final _ _ _ _ _)

theorem program_numeric (B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q protectedLimit goodFlags badFlags)
    (hb : ReadBounds size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (state : State)
    (hv : ReadValuesBound size q rowPointer countsBase parentBase nodePointer rowBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom
      (program size q rowPointer countsBase parentBase nodePointer goodFlags badFlags) state :=
  budgets_numeric B heapWords size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit
    goodFlags badFlags rom hl hb (List.finRange (q + 2)) state hv hr

end PaperProofs.Structure.LaminarTree.PA17QueryTestsWord028



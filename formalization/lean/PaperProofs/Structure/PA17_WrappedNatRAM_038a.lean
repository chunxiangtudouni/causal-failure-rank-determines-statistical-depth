module
public import PaperProofs.Structure.PA17_NatRAM_037
public import PaperProofs.Structure.PA17_PackedTranslator_034a
public import PaperProofs.Structure.PA17_DataFrame_039
import Mathlib.Tactic.Ring

/-! Concrete logical spill wrappers for the same three actual bodies.
Only seven appended index words and charged instructions are added. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17WrappedNatRAM038a

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022 PA17PackedTranslator034 PA17DataFrame039

def spillBase (N q size : Nat) : Nat := PA17QueryLayout014.heapWords N q size
def rollingSpillBase (q size : Nat) : Nat := PA17GivenWord031f.heapWords q size
def heapWords (N q size : Nat) : Nat := spillBase N q size + spillWords
def rollingHeapWords (q size : Nat) : Nat := rollingSpillBase q size + spillWords

def implementation : Implementation where
  buildProgram := fun N q size => logicalProgram (spillBase N q size) (PA17TableBuild005.buildProgram N q size)
  queryProgram := fun N q size => logicalProgram (spillBase N q size) (PA17Query019.program N q size)
  rollingProgram := fun N q size => logicalProgram (rollingSpillBase q size) (PA17Rolling018B.program N q size)
  capacityWords := PA17Implementation030.implementation.capacityWords
  indexWords := fun N q size => newIndexWords (PA17Implementation030.implementation.indexWords N q size)
  rollingCapacityWords := PA17Implementation030.implementation.rollingCapacityWords
  rollingIndexWords := fun N q size => newIndexWords (PA17Implementation030.implementation.rollingIndexWords N q size)

def constant : Nat := 65536

theorem constant_pos : 0 < constant := by decide

theorem implementation_heap (N q size : Nat) :
    implementation.capacityWords N q size + implementation.indexWords N q size = heapWords N q size := by
  rfl

theorem implementation_rollingHeap (N q size : Nat) :
    implementation.rollingCapacityWords N q size + implementation.rollingIndexWords N q size = rollingHeapWords q size := by
  rfl

theorem wipe_trace_length (spillBase : Nat) : (trace (wipe spillBase)).length = 149 := rfl

theorem logicalProgram_trace_length (spillBase : Nat) (body : List Op) :
    (trace (logicalProgram spillBase body)).length = (trace body).length + 298 := by
  simp only [logicalProgram, trace_append, List.length_append, wipe_trace_length]
  omega

theorem logicalProgram_code_length (spillBase : Nat) (body : List Op) :
    (haltingWords (logicalProgram spillBase body)).length = (haltingWords body).length + 160 := by
  rw [haltingWords_length, haltingWords_length, logicalProgram_length]
  omega

theorem logicalProgram_buildCost (spillBase : Nat) (rom : PhysicalROM) (body : List Op) :
    totalBuildCost rom (logicalProgram spillBase body) (spillBase + spillWords) = totalBuildCost rom body spillBase + 465 := by
  rw [totalBuildCost, totalBuildCost, logicalProgram_code_length, List.length_append, List.length_append,
    logicalProgram_trace_length]
  simp only [spillWords]
  omega

theorem logicalProgram_queryCost (q spillBase : Nat) (body : List Op) :
    totalQueryCost q (logicalProgram spillBase body) = totalQueryCost q body + 458 := by
  rw [totalQueryCost, totalQueryCost, logicalProgram_code_length, List.length_append, List.length_append,
    logicalProgram_trace_length]
  omega

theorem wipe_initial_dataEq (rom : ROM) (base : Nat) (heap : Nat → Nat) :
    DataEq (initial (wipeHeap base heap)) (execute rom (wipe base) (initial heap)) := by
  constructor
  · funext register
    rw [wipe_register]
    change 0 = if register = .flag ∨ register = .total then 0 else 0
    split_ifs <;> rfl
  · rw [wipe_heap]
    rfl

theorem wipe_initial_zero_dataEq (rom : ROM) (base : Nat) :
    DataEq (initial (fun _ => 0)) (execute rom (wipe base) (initial (fun _ => 0))) := by
  have hh : wipeHeap base (fun _ => 0) = fun _ => 0 := by
    funext address
    unfold wipeHeap
    split_ifs <;> rfl
  simpa only [hh] using wipe_initial_dataEq rom base (fun _ => 0)

theorem logicalProgram_numeric (B words base : Nat) (rom : PhysicalROM) (body : List Op)
    (hb : base + spillWords ≤ B) (ha : base + spillWords ≤ words) (state : State)
    (hr : RegistersLE (2 * B) state)
    (hbody : NumericSafe (2 * B) words rom body (execute rom.semantic (wipe base) state)) :
    NumericSafe (2 * B) words rom (logicalProgram base body) state := by
  have hw := wipe_numeric B words base rom hb ha state hr
  have hf := wipe_numeric B words base rom hb ha _ (hbody.final _ _ _ _ _)
  rw [logicalProgram]
  apply NumericSafe.append _ _ rom _ _ state (NumericSafe.append _ _ rom _ _ state hw hbody)
  rw [IndexedClosureRAM.execute_append]
  exact hf

theorem logicalProgram_capacityThroughout (q cap base : Nat) (rom : PhysicalROM) (body : List Op)
    (hb : cap ≤ base) (state : State) (hcap : CapacityPrefixBounded q cap state.heap)
    (hbody : CapacityThroughout q cap rom body (execute rom.semantic (wipe base) state)) :
    CapacityThroughout q cap rom (logicalProgram base body) state := by
  have hw := wipe_capacityThroughout q cap base rom hb state hcap
  have hf := wipe_capacityThroughout q cap base rom hb _ (by simpa only [List.take_length] using hbody _ le_rfl)
  rw [logicalProgram]
  apply UniformFreeTableSafety.capacityThroughout_append q cap rom _ _ state
    (UniformFreeTableSafety.capacityThroughout_append q cap rom _ _ state hw hbody)
  rw [IndexedClosureRAM.execute_append]
  exact hf

theorem logicalProgram_replyCorrect (q base : Nat) (rom : ROM) (body : List Op) (state : State)
    (answer : IndexedQuery.Reply q)
    (hr : ReplyCorrect q answer (execute rom body (execute rom (wipe base) state))) :
    ReplyCorrect q answer (execute rom (logicalProgram base body) state) := by
  rw [logicalProgram_execute]
  simpa only [ReplyCorrect, wipe_register, reduceCtorEq, or_self, ite_false] using hr

theorem logicalProgram_zero_heap (rom : ROM) (base : Nat) (body : List Op) (address : Nat) (ha : address < base) :
    (execute rom (logicalProgram base body) (initial (fun _ => 0))).heap address =
      (execute rom body (initial (fun _ => 0))).heap address := by
  rw [logicalProgram_execute, wipe_frame rom base _ address (Or.inl ha)]
  exact congrFun (execute_dataEq rom body _ _ (wipe_initial_zero_dataEq rom base)).2.symm address

theorem logicalProgram_zero_register (rom : ROM) (base : Nat) (body : List Op) (register : Register)
    (hf : register ≠ .flag) (ht : register ≠ .total) :
    (execute rom (logicalProgram base body) (initial (fun _ => 0))).register register =
      (execute rom body (initial (fun _ => 0))).register register := by
  simp only [logicalProgram_register, hf, ht, or_self, ite_false]
  exact congrFun (execute_dataEq rom body _ _ (wipe_initial_zero_dataEq rom base)).1.symm register

end PaperProofs.Structure.LaminarTree.PA17WrappedNatRAM038a

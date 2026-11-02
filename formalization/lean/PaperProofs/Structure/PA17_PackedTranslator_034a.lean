module

public import PaperProofs.Structure.PA17_QueryHeaderWord_022a
import Mathlib.Tactic.IntervalCases

/-! The logical seven-spill wrapper. Its two working registers are flag and
total; the other five registers, including every answer register, survive.
Both initial and final spill values are established by actual heap stores. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17PackedTranslator034

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022

def spillWords : Nat := 7

def newIndexWords (oldIndexWords : Nat) : Nat := oldIndexWords + spillWords

def wipeBlock (address : Nat) : List Op :=
  [.base (.constant .total address), .base (.storeHeap .total .flag)]

def wipe (spillBase : Nat) : List Op :=
  [.base (.constant .flag 0)] ++
    (List.range spillWords).flatMap (fun index => wipeBlock (spillBase + index)) ++
    [.base (.constant .total 0)]

def logicalProgram (spillBase : Nat) (body : List Op) : List Op := wipe spillBase ++ body ++ wipe spillBase

def wipeHeap (spillBase : Nat) (heap : Nat → Nat) (address : Nat) : Nat :=
  if spillBase ≤ address ∧ address < spillBase + spillWords then 0 else heap address

theorem spillWords_eq : spillWords = 7 := rfl

theorem wipe_length (spillBase : Nat) : (wipe spillBase).length = 16 := rfl

theorem logicalProgram_length (spillBase : Nat) (body : List Op) :
    (logicalProgram spillBase body).length = body.length + 32 := by
  simp only [logicalProgram, List.length_append, wipe_length]
  omega

theorem wipe_register (rom : ROM) (spillBase : Nat) (state : State) (register : Register) :
    (execute rom (wipe spillBase) state).register register =
      if register = .flag ∨ register = .total then 0 else state.register register := by
  cases register <;> rfl

theorem wipe_take_frame (rom : ROM) (spillBase : Nat) (state : State) (count : Nat)
    (hc : count ≤ (wipe spillBase).length) (address : Nat)
    (hout : address < spillBase ∨ spillBase + spillWords ≤ address) :
    (execute rom ((wipe spillBase).take count) state).heap address = state.heap address := by
  change count ≤ 16 at hc
  change address < spillBase ∨ spillBase + 7 ≤ address at hout
  interval_cases count <;>
    simp [wipe, spillWords, wipeBlock, List.range_succ, IndexedClosureRAM.execute, Op.execute,
      Instruction.execute, Function.update_apply]
  all_goals (try split_ifs)
  all_goals omega

theorem wipe_heap (rom : ROM) (spillBase : Nat) (state : State) :
    (execute rom (wipe spillBase) state).heap = wipeHeap spillBase state.heap := by
  funext address
  by_cases hin : spillBase ≤ address ∧ address < spillBase + 7
  · obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hin.1
    have ho : offset < 7 := by omega
    interval_cases offset <;>
      simp [wipe, spillWords, wipeBlock, List.range_succ, IndexedClosureRAM.execute,
        Op.execute, Instruction.execute, wipeHeap]
  · have hout : address < spillBase ∨ spillBase + spillWords ≤ address := by
      simp only [spillWords]
      omega
    have hf := wipe_take_frame rom spillBase state (wipe spillBase).length le_rfl address hout
    simpa only [List.take_length, wipeHeap, spillWords, hin, ite_false] using hf

theorem wipe_zero (rom : ROM) (spillBase : Nat) (state : State) (index : Nat) (hi : index < spillWords) :
    (execute rom (wipe spillBase) state).heap (spillBase + index) = 0 := by
  rw [wipe_heap]
  unfold wipeHeap
  split_ifs <;> omega

theorem wipe_frame (rom : ROM) (spillBase : Nat) (state : State) (address : Nat)
    (hout : address < spillBase ∨ spillBase + spillWords ≤ address) :
    (execute rom (wipe spillBase) state).heap address = state.heap address := by
  rw [wipe_heap]
  unfold wipeHeap
  split_ifs <;> omega

theorem wipe_pc (rom : ROM) (spillBase : Nat) (state : State) :
    (execute rom (wipe spillBase) state).pc = state.pc + 80 := by
  rw [IndexedClosureRAM.execute_pc, wipe_length]

theorem wipe_capacityThroughout (q capWords spillBase : Nat) (rom : PhysicalROM)
    (hbase : capWords ≤ spillBase) (state : State) (hcap : CapacityPrefixBounded q capWords state.heap) :
    CapacityThroughout q capWords rom (wipe spillBase) state := by
  intro count hc address ha
  rw [wipe_take_frame rom.semantic spillBase state count hc address (Or.inl (by omega))]
  exact hcap address ha

theorem logicalProgram_execute (rom : ROM) (spillBase : Nat) (body : List Op) (state : State) :
    execute rom (logicalProgram spillBase body) state =
      execute rom (wipe spillBase) (execute rom body (execute rom (wipe spillBase) state)) := by
  simp only [logicalProgram, IndexedClosureRAM.execute_append]

theorem logicalProgram_register (rom : ROM) (spillBase : Nat) (body : List Op) (state : State) (register : Register) :
    (execute rom (logicalProgram spillBase body) state).register register =
      if register = .flag ∨ register = .total then 0 else
        (execute rom body (execute rom (wipe spillBase) state)).register register := by
  rw [logicalProgram_execute, wipe_register]

theorem logicalProgram_spills_zero (rom : ROM) (spillBase : Nat) (body : List Op) (state : State)
    (index : Nat) (hi : index < spillWords) :
    (execute rom (logicalProgram spillBase body) state).heap (spillBase + index) = 0 := by
  rw [logicalProgram_execute]
  exact wipe_zero rom spillBase _ index hi

theorem wipe_numeric (B heapWords spillBase : Nat) (rom : PhysicalROM)
    (hbase : spillBase + spillWords ≤ B) (haccess : spillBase + spillWords ≤ heapWords)
    (state : State) (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (wipe spillBase) state := by
  simp only [spillWords] at hbase haccess
  constructor
  · intro count hc register
    have hv := hr register
    change count ≤ 16 at hc
    interval_cases count <;> cases register <;>
      simp [wipe, spillWords, wipeBlock, List.range_succ, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 16 at hc
    interval_cases count <;>
      simp [wipe, spillWords, wipeBlock, List.range_succ, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits]
    all_goals omega

end PaperProofs.Structure.LaminarTree.PA17PackedTranslator034

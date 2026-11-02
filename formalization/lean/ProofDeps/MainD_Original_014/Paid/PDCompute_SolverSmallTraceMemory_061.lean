module

public import Paid.PDCompute_SolverSmallPrefixMemory_060
public import Paid.PDCompute_SolverHeaderLoads_038

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot storeSlotResult)
open PDMenu.ComputeFrame

/-- Local instruction-prefix facts are transported to EVERY state of
the genuine fetched original-ISA trace, including its final state. -/
theorem linearExecute_trace_memory (program : Program) (input : List Cell) (code : List Instruction)
    (straight : StraightCode code) (before after : State) (base : ℕ)
    (fetched : FetchesCode program before.pc code) (run : linearExecute input code before=some after)
    (memory : ∀ count ≤ code.length, ∀ state,
      linearExecute input (code.take count) before=some state → HeaderMemory before state base) :
    ∃ trace : List State, trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 15*(code.length+1) ∧ ∀ state ∈ trace, HeaderMemory before state base := by
  obtain ⟨trace,hh,hl,hchain,ht,prefixes⟩ := linearExecute_trace_time program input code straight before after fetched run
  refine ⟨trace,hh,hl,hchain,ht,?_⟩
  intro state member
  have split := List.dropLast_append_getLast? after (by rw [hl]; simp)
  rw [← split] at member
  rcases List.mem_append.mp member with proper|last
  · obtain ⟨count,bound,execute⟩ := prefixes state proper
    exact memory count (Nat.le_of_lt bound) state execute
  · have eq : state=after := by simpa only [List.mem_singleton] using last
    subst state
    exact memory code.length (le_refl _) after (by simpa only [List.take_length] using run)

theorem Header.loadSlot_trace_memory {before : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (program : Program) (input : List Cell) (slot : ℕ) (target : Register)
    (inside : slot < headerWords) (hbase : before.register .fresh=.natural base)
    (fetched : FetchesCode program before.pc (loadSlot slot target)) :
    ∃ trace : List State, trace.head?=some before ∧ trace.getLast?=some (loadSlotResult before base slot target) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 60 ∧ ∀ state ∈ trace, HeaderMemory before state base := by
  apply linearExecute_trace_memory program input (loadSlot slot target) (loadSlot_straight slot target)
    before (loadSlotResult before base slot target) base fetched (header.loadSlot_execute input slot target inside hbase).1
  intro count bound state execute
  have facts := loadSlot_prefix_memory input before state base slot target hbase (header.live slot inside) count bound execute
  exact HeaderMemory.of_unchanged base facts.1 facts.2.1 facts.2.2

theorem Header.storeSlot_trace_memory {before : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (program : Program) (input : List Cell) (slot : ℕ) (source : Register)
    (inside : slot < headerWords) (hbase : before.register .fresh=.natural base) (different : source ≠ .address)
    (fetched : FetchesCode program before.pc (storeSlot slot source)) :
    ∃ trace : List State, trace.head?=some before ∧ trace.getLast?=some (storeSlotResult before base slot source) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 60 ∧ ∀ state ∈ trace, HeaderMemory before state base := by
  have straight : StraightCode (storeSlot slot source) := by
    intro instruction member
    simp only [storeSlot,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h <;> subst instruction <;> trivial
  apply linearExecute_trace_memory program input (storeSlot slot source) straight before (storeSlotResult before base slot source)
    base fetched (PDLower.CalibrationCompute.storeSlot_execute input before base slot source hbase different)
  intro count bound state execute
  exact storeSlot_prefix_memory input before state base slot source values header inside hbase different count bound execute

theorem minimumCompareCode_prefix_memory (input : List Cell) (before after : State) (base : ℕ)
    (values : ℕ → Cell) (candidate best : ℚ) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hc : values 28=.rational candidate) (hb : values 24=.rational best)
    (count : ℕ) (hcount : count ≤ 7)
    (hexec : linearExecute input (minimumCompareCode.take count) before=some after) :
    HeaderMemory before after base := by
  by_cases short : count < 7
  · have candidateLive := header.live 28 (by decide)
    have bestLive := header.live 24 (by decide)
    have candidateAt := (header.value 28 (by decide)).trans hc
    have bestAt := (header.value 24 (by decide)).trans hb
    interval_cases count <;>
      simp [minimumCompareCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
        hbase,candidateLive,bestLive,candidateAt,bestAt] at hexec <;> subst after <;>
      exact HeaderMemory.of_unchanged base rfl rfl rfl
  · have exactCount : count=7 := by omega
    subst count
    have full : linearExecute input minimumCompareCode before=some after := hexec
    rw [minimumCompareCode_execute input before base values candidate best header hbase hc hb] at full
    have eq := Option.some.inj full
    subst after
    have fields := minimumCompareResult_fields before base candidate best
    exact HeaderMemory.of_unchanged base fields.1 fields.2.1 fields.2.2.2.2.2

end PDCompute.Solver

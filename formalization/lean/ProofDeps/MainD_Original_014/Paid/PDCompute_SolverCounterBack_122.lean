module

public import Paid.PDCompute_SolverLinearPC_121
public import Paid.PDCompute_SolverAdvanceMemory_067
public import Paid.PDCompute_SolverHeaderFrame_099
public import Paid.PDCompute_SolverJump_096

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def counterBackCode (slot amount target : ℕ) : List Instruction := addNatSlot slot amount++[.jump target]

/-- The actual row/column increment and literal backedge, with the
requested proper-prefix PC interval as well as exact every-state memory. -/
theorem counterBack_trace_memory_pc (program : Program) (input : List Cell) (before : State)
    (base n k slot value amount target : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (inside : slot < headerWords) (hvalue : values slot=.natural value)
    (fetch : FetchesCode program before.pc (counterBackCode slot amount target)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 150 ∧ Header after base (Function.update values slot (.natural (value+amount))) ∧
      after.register .fresh=.natural base ∧ after.pc=target ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state ∈ trace,HeaderMemory before state base) ∧
      ∀ state ∈ trace.dropLast,before.pc ≤ state.pc ∧ state.pc < before.pc+(counterBackCode slot amount target).length := by
  let advanced:=addNatSlotResult before base slot value amount
  let returned:=jumpResult advanced target
  have run:=addNatSlot_execute input before base slot value amount hbase (header.live slot inside) ((header.value slot inside).trans hvalue)
  obtain ⟨incTrace,incHead,incLast,incChain,incTime,prefixes,pcRange⟩:=linearExecute_trace_closedPC program input
    (addNatSlot slot amount) (addNatSlot_straight slot amount) before advanced fetch.append_left run
  have incMemory : ∀ state ∈ incTrace,HeaderMemory before state base := by
    intro state member
    have split:=List.dropLast_append_getLast? advanced (by rw [incLast]; simp)
    rw [← split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,bound,execute⟩:=prefixes state proper
      exact addNatSlot_header_memory input before state base slot value amount values header inside hbase hvalue
        count (Nat.le_of_lt bound) execute
    · have same : state=advanced := List.mem_singleton.mp terminal
      subst state
      exact addNatSlot_header_memory input before advanced base slot value amount values header inside hbase hvalue
        (addNatSlot slot amount).length (le_refl _) (by simpa only [List.take_length] using run)
  have fields:=addNatSlotResult_fields before base slot value amount
  have jumpFetch : program[advanced.pc]?=some (.jump target) := by
    rw [fields.2.2.2.1]
    have branchFetch:=fetch.append_right
    have instruction:=branchFetch 0 (by change 0 < 1; decide)
    simpa only [addNatSlot_length,Nat.add_zero,List.getElem?_cons_zero] using instruction
  have control : step program input advanced=some returned := by unfold step; rw [jumpFetch]; rfl
  have appended:=chain_append_control program input incTrace advanced returned incChain incLast control
  have afterMemory : HeaderMemory before returned base :=
    (HeaderMemory.trace_last incMemory incLast).trans (HeaderMemory.of_unchanged base rfl rfl rfl)
  have nonempty : incTrace ≠ [] := by intro empty; simp only [empty,List.head?_nil,reduceCtorEq] at incHead
  refine ⟨incTrace++[returned],returned,?_,by simp,appended.1,?_,header.addNatSlot slot value amount,
    fields.2.2.1.trans hbase,rfl,afterMemory.frame n k,afterMemory.2.2,
    appendTrace_memory incTrace before returned base incMemory afterMemory,?_⟩
  · simpa only [List.head?_append_of_ne_nil _ nonempty] using incHead
  · have cost:=appended.2
    have incBound : time program incTrace ≤ 135 := incTime
    omega
  · intro state member
    have drop : (incTrace++[returned]).dropLast=incTrace := by simp
    rw [drop] at member
    have range:=pcRange state member
    have size : (counterBackCode slot amount target).length=9 := rfl
    rw [size]
    have incSize : (addNatSlot slot amount).length=8 := rfl
    rw [incSize] at range
    omega

end PDCompute.Solver

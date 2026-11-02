module

public import Paid.RootD27Core_InitializeSearch_064
public import Paid.PDLower_CoreSearch_LocatedLiterals_030
public import Paid.PDCompute_Pack_SlotBitTrace_064

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section

namespace PDCompute.CoreInitialize
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame PDROC.DataBits
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList loadSlot loadSlotResult linearExecute)
open RootD27.Core RootD27.Bits PDLower.CoreSearch

/-- Only the real inline caller and the shared fixed callee contain PCs. -/
def CalleePC (labels : RoutineLabels) (state : State) : Prop :=
  labels.solveEntry≤state.pc ∧ state.pc<labels.solveEntry+1+(solverCalleeCode .liveHeap (labels.solveEntry+1)).length

def ClosedPC (labels : RoutineLabels) (low high : ℕ) (state : State) : Prop :=
  (low≤state.pc ∧ state.pc≤high) ∨ CalleePC labels state

def ProperPC (labels : RoutineLabels) (low high : ℕ) (state : State) : Prop :=
  (low≤state.pc ∧ state.pc<high) ∨ CalleePC labels state

/-- The actual20 metadata instructions physically copy Lambda/J from
the prepared header. Arbitrary old scratch stays at the SAME budget. -/
theorem metadata_resources (program : Program) (input : List Cell) (before : State)
    (values : ℕ→Cell) (budget : ℕ) (header : Header before 0 values)
    (fresh : before.register .fresh=.natural 0) (safe : SafeBits before budget)
    (small : 7≤budget) (pcBits : natBits (before.pc+20)≤budget)
    (fetched : FetchesCode program before.pc (headerCode searchInitializeCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤315 ∧
      Header after 0 (searchInitializeValues values) ∧ after.register .fresh=.natural 0 ∧ after.pc=before.pc+20 ∧
      (∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧
      (∀ state∈trace,SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+20) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+20) := by
  have addressBits : 1+natBits headerWords≤budget :=
    (show 1+natBits headerWords≤7 by decide).trans small
  have bounded : ∀ command∈searchInitializeCommands,CopyConstantBound budget command := by
    intro command member
    simp only [searchInitializeCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same|same|same <;> subst command
    · exact (show (Cell.natural 1).bits≤7 by decide).trans small
    · change 1+ratEncodingBits 0≤budget
      norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
      omega
    · trivial
    · trivial
  obtain ⟨after,actual,afterHeader,afterFresh,afterPC⟩ :=
    PDLower.CoreSearch.Located.copyConstant_segment_bits searchInitializeCommands program input before values
      (searchInitializeValues values) budget searchInitialize_valid searchInitialize_targets header fresh
      (searchInitialize_eval values) safe bounded addressBits (by simpa only [searchInitialize_length] using pcBits)
      fetched before.pc (before.pc+20) (le_refl _) (by rw [searchInitialize_length])
  obtain ⟨trace,head,last,chain,cost,properties,proper⟩ := actual
  refine ⟨trace,after,head,last,chain,by simpa only [searchInitialize_length] using cost,
    afterHeader,afterFresh,by simpa only [searchInitialize_length] using afterPC,
    fun state member=>(properties state member).1.1,
    fun state member=>(properties state member).1.2,fun state member=>(properties state member).2,proper⟩

/-- A real three-op heap load copies the existing safe live penalty,
preserves the entire heap/live/output, and exposes proper fetched PCs. -/
theorem penalty_load_resources (program : Program) (input : List Cell) (before : State)
    (values : ℕ→Cell) (slot : ℕ) (penalty : ℚ) (budget : ℕ) (header : Header before 0 values)
    (inside : slot<headerWords) (fresh : before.register .fresh=.natural 0)
    (value : values slot=.rational penalty) (safe : SafeBits before budget) (small : 7≤budget)
    (pcBits : natBits (before.pc+3)≤budget)
    (fetched : FetchesCode program before.pc (loadSlot slot .total)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (loadSlotResult before 0 slot .total) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤60 ∧
      (loadSlotResult before 0 slot .total).register .total=.rational penalty ∧
      (loadSlotResult before 0 slot .total).register .fresh=.natural 0 ∧
      (∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+3) ∧
      (∀ state∈trace,SafeBits state budget) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+3) := by
  let code:=loadSlot slot .total
  let after:=loadSlotResult before 0 slot .total
  have run:=(header.loadSlot_execute input slot .total inside fresh).1
  have addressBits : 1+natBits (0+slot)≤budget :=
    (Nat.add_le_add_left (natBits_mono (by omega : 0+slot≤headerWords)) 1).trans
      ((show 1+natBits headerWords≤7 by decide).trans small)
  have properties (count : ℕ) (bound : count≤code.length) (state : State)
      (executed : linearExecute input (code.take count) before=some state) :
      (state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output) ∧ SafeBits state budget := by
    have countBound : count≤3 := bound
    exact ⟨loadSlot_prefix_memory input before state 0 slot .total fresh (header.live slot inside) count countBound executed,
      loadSlot_prefix_safe input before state 0 slot budget count .total safe fresh (header.live slot inside)
        addressBits pcBits countBound executed⟩
  obtain ⟨trace,head,last,chain,cost,prefixes,location⟩ := linearExecute_trace_closedPC program input code
    (loadSlot_straight slot .total) before after fetched run
  have allProperties : ∀ state∈trace,
      (state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output) ∧ SafeBits state budget := by
    intro state member
    have split:=List.dropLast_append_getLast? after (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,bound,executed⟩:=prefixes state proper
      exact properties count bound.le state executed
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact properties code.length (le_refl _) after (by simpa only [List.take_length] using run)
  refine ⟨trace,head,last,chain,cost,(header.loadSlot_execute input slot .total inside fresh).2.trans value,
    (loadSlotResult_fresh before 0 slot .total (by decide)).trans fresh,
    fun state member=>(allProperties state member).1,location,
    fun state member=>(allProperties state member).2,?_⟩
  intro state member
  obtain ⟨count,bound,executed⟩:=prefixes state member
  have straight : StraightCode (code.take count):=
    fun instruction member=>loadSlot_straight slot .total instruction (List.mem_of_mem_take member)
  have pc:=linearExecute_pc input _ straight before state executed
  simp only [List.length_take,Nat.min_eq_left bound.le] at pc
  change count<3 at bound
  omega

end PDCompute.CoreInitialize

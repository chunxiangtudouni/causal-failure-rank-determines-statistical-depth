module

public import Paid.RootD27Core_RetainedSavedCaller_054

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList linearExecute)

/-- Read the length REALLY saved by the actual copier, commit it to
the lower/upper metadata slot, and actually restore fresh0 for scalars. -/
def retainedCommitCode (slot : ℕ) : List Instruction :=
  [.constant .address (.natural 47),.load .index .address,
   .constant .address (.natural slot),.store .address .index,.constant .fresh (.natural 0)]

def retainedCommitResult (before : State) (slot count : ℕ) : State :=
  {before with
    register:=Function.update (Function.update (Function.update before.register .index (.natural count))
      .address (.natural slot)) .fresh (.natural 0)
    heap:=Function.update before.heap slot (.natural count)
    live:=insert slot before.live
    pc:=before.pc+5}

theorem retainedCommit_length (slot : ℕ) : (retainedCommitCode slot).length=5:=rfl

theorem retainedCommit_straight (slot : ℕ) : StraightCode (retainedCommitCode slot) := by
  simp [StraightCode,retainedCommitCode,StraightInstruction]

theorem retainedCommit_execute (input : List Cell) (before : State) (slot count : ℕ)
    (live : 47∈before.live) (value : before.heap 47=.natural count) :
    linearExecute input (retainedCommitCode slot) before=some (retainedCommitResult before slot count) := by
  simp [retainedCommitCode,retainedCommitResult,linearExecute,Instruction.execute,State.set,live,value,Cell.nat?,Nat.add_assoc]
  all_goals
    funext register
    cases register <;> simp

theorem retainedCommit_prefix_memory (input : List Cell) (before after : State) (slot count stepsTaken : ℕ)
    (live : 47∈before.live) (value : before.heap 47=.natural count) (bound : stepsTaken≤5)
    (executed : linearExecute input ((retainedCommitCode slot).take stepsTaken) before=some after) :
    RegionMemory before after {slot} := by
  interval_cases stepsTaken <;>
    simp [retainedCommitCode,linearExecute,Instruction.execute,State.set,live,value,Cell.nat?,Nat.add_assoc] at executed <;> subst after
  all_goals
    refine ⟨?_,?_,?_,rfl⟩
    · intro query outside
      have different : query≠slot:=by simpa only [Finset.mem_singleton] using outside
      simp_all
    · intro query member
      simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at member ⊢
      tauto
    · first
      | exact Finset.Subset.refl _
      | exact Finset.subset_insert _ _

theorem retainedCommit_actual (program : Program) (input : List Cell) (before : State) (slot count : ℕ)
    (saved : HeapList before 47 [.natural count])
    (fetched : FetchesCode program before.pc (retainedCommitCode slot)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (retainedCommitResult before slot count) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤90 ∧
      (∀ state∈trace,RegionMemory before state {slot}) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+5) ∧
      peakCells trace≤workingCells before+1 ∧
      HeapList (retainedCommitResult before slot count) slot [.natural count] := by
  have live : 47∈before.live:=by simpa only [Nat.add_zero] using saved.1 0 (by change 0<1;decide)
  have value:=PDLower.CalibrationCompute.HeapList.value saved 0 (by change 0<1;decide)
  change before.heap 47=.natural count at value
  have executed:=retainedCommit_execute input before slot count live value
  obtain ⟨trace,head,last,chain,cost,prefixes⟩:=linearExecute_trace_time program input _
    (retainedCommit_straight slot) before _ fetched executed
  have memory : ∀ state∈trace,RegionMemory before state {slot} := by
    intro state member
    have split:=List.dropLast_append_getLast? (retainedCommitResult before slot count) (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨stepsTaken,bound,actual⟩:=prefixes state proper
      exact retainedCommit_prefix_memory input before state slot count stepsTaken live value
        (by simpa only [retainedCommit_length] using bound.le) actual
    · have same : state=retainedCommitResult before slot count:=List.mem_singleton.mp terminal
      subst state
      exact retainedCommit_prefix_memory input before _ slot count 5 live value (le_refl _) (by
        rw [←retainedCommit_length slot,List.take_length]
        exact executed)
  have pcs : ∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+5 := by
    intro state member
    have split:=List.dropLast_append_getLast? (retainedCommitResult before slot count) (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨stepsTaken,bound,actual⟩:=prefixes state proper
      have straight : StraightCode ((retainedCommitCode slot).take stepsTaken) :=
        fun instruction inside=>retainedCommit_straight slot instruction (List.mem_of_mem_take inside)
      have pc:=linearExecute_pc input _ straight before state actual
      simp only [List.length_take,Nat.min_eq_left bound.le] at pc
      rw [retainedCommit_length] at bound
      omega
    · have same : state=retainedCommitResult before slot count:=List.mem_singleton.mp terminal
      subst state
      change before.pc≤before.pc+5 ∧ before.pc+5≤before.pc+5
      omega
  have stored : HeapList (retainedCommitResult before slot count) slot [.natural count] := by
    apply PDLower.CalibrationCompute.HeapList.of_values
    · intro offset inside
      have zero : offset=0:=by change offset<1 at inside;omega
      subst offset
      simp [retainedCommitResult]
    · intro offset inside
      have zero : offset=0:=by change offset<1 at inside;omega
      subst offset
      simp [retainedCommitResult]
  refine ⟨trace,head,last,chain,cost,memory,pcs,?_,stored⟩
  apply PDLower.CalibrationCompute.peakCells_le_of_forall
  intro state member
  simpa only [Finset.card_singleton] using (memory state member).workingCells_le

end RootD27.Core

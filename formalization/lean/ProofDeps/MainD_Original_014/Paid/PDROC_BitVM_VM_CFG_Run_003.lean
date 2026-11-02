module

public import Paid.PDROC_BitVM_VM_CFG_Run_002
public import Paid.PDROC_BitVM_VM_BoundaryBudget_Canonical_003
public import Paid.PDROC_BitVM_Kernel_NatInstruction_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Run

open Turing PDROC.BitVM.Common.IO PaperProofs.Paid.Computation

variable {Λ σ : Type}

/-- The arithmetic argument of Root096, isolated from its numerical
implementation imports so the actual Bool and rational TM origins are
not mixed. Every actual fetch pays at least one primitive, including HALT. -/
theorem trace_length_le_actual_time (code : Program) :
    ∀ states : List State, (∀ state ∈ states, ∃ instruction, code[state.pc]? = some instruction) →
      states.length ≤ time code states := by
  intro states
  induction states with
  | nil => intro _; simp only [List.length_nil, time, primitiveTrace, List.flatMap_nil]; exact Nat.le_refl 0
  | cons before tail ih =>
    intro fetches
    obtain ⟨instruction, fetched⟩ := fetches before List.mem_cons_self
    have later := ih (fun state member => fetches state (List.mem_cons_of_mem before member))
    have charged : 1 ≤ instruction.primitives.length := by
      simp only [Instruction.primitives, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
      omega
    have split : time code (before :: tail) = instruction.primitives.length + time code tail := by
      simp only [time, primitiveTrace, List.flatMap_cons, fetched, Option.map_some, Option.getD_some, List.length_append]
    rw [split]
    simp only [List.length_cons]
    omega

theorem runs_length_le_actual_time (code : Program) (input : List Cell) (states : List State) (final : State)
    (actual : Runs code input states final) : states.length ≤ time code states := by
  apply trace_length_le_actual_time code states
  intro state member
  have inside := Source.runs_pc_valid code input states final actual state member
  exact ⟨code[state.pc], Array.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩⟩

/-- Fixed-machine INTERNAL local contracts. C,d precede every input,
logical state, event history and old physical tape. The parent supplies
these from real FullCFG+Step/Resource adapters, not as paper premises. -/
def StepPolynomial (native : Λ → TM2.Stmt Alphabet Λ σ) (code : Program)
    (entry : State → NativeState Λ σ → Prop) (C d : ℕ) : Prop :=
  ∀ (input : List Cell) (current next : State) (instruction : Instruction)
    (events : List Log.HeapEvent) (physical : NativeState Λ σ),
    code[current.pc]? = some instruction → step code input current = some next → next.pc < code.size →
    Source.Ready input current events physical.stk → entry current physical →
    ∃ after : NativeState Λ σ, entry next after ∧
      Source.Ready input next (events ++ (Log.eventOf instruction current).toList) after.stk ∧
      ∃ path : ActualPath (TM2.step native) physical after,
        path.posts.length ≤ C * (Kernel.NatInstruction.dataSize physical.stk + (encodeBits input).length + 1)^d

def HaltPolynomial (native : Λ → TM2.Stmt Alphabet Λ σ) (code : Program)
    (entry : State → NativeState Λ σ → Prop) (C d : ℕ) : Prop :=
  ∀ (input : List Cell) (current : State) (events : List Log.HeapEvent) (physical : NativeState Λ σ),
    code[current.pc]? = some .halt → Source.Ready input current events physical.stk → entry current physical →
    ∃ after : NativeState Λ σ, TM2.step native after = none ∧ Source.Ready input current events after.stk ∧
      ∃ path : ActualPath (TM2.step native) physical after,
        path.posts.length ≤ C * (Kernel.NatInstruction.dataSize physical.stk + (encodeBits input).length + 1)^d

theorem boundary_size (code : Program) (input : List Cell) (states : List State) (final : State)
    (actual : Runs code input states final) (inputSize total budget : ℕ)
    (inputBound : (encodeBits input).length ≤ inputSize)
    (clock : time code states ≤ total) (peak : peakOperandBits states ≤ budget)
    (current : State) (events : List Log.HeapEvent) (contents : Stack → List Bool)
    (atBoundary : Boundary code states current events) (ready : Source.Ready input current events contents) :
    Kernel.NatInstruction.dataSize contents ≤ BoundaryBudget.boundaryBudget inputSize total budget := by
  have member := boundary_member code states current events atBoundary
  have history := boundary_history_bounds code states current events total budget atBoundary clock peak
  have output := BoundaryBudget.runs_output_bounds code input states final actual budget total peak clock current member
  have canonical := BoundaryBudget.canonical_dataSize input current events contents inputSize total budget ready
    (BoundaryBudget.state_bits_of_peak states budget peak current member) inputBound history.2.2 output.1 output.2.2
  simpa only [Kernel.NatInstruction.dataSize] using canonical

theorem local_base_bound (code : Program) (input : List Cell) (states : List State) (final : State)
    (actual : Runs code input states final) (inputSize total budget : ℕ)
    (inputBound : (encodeBits input).length ≤ inputSize)
    (clock : time code states ≤ total) (peak : peakOperandBits states ≤ budget)
    (current : State) (events : List Log.HeapEvent) (contents : Stack → List Bool)
    (atBoundary : Boundary code states current events) (ready : Source.Ready input current events contents) :
    Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1 ≤
      2 * BoundaryBudget.boundaryBudget inputSize total budget + 1 := by
  have data := boundary_size code input states final actual inputSize total budget inputBound clock peak current events contents atBoundary ready
  have inputEnv : inputSize ≤ BoundaryBudget.boundaryBudget inputSize total budget := by
    unfold BoundaryBudget.boundaryBudget
    nlinarith
  omega

/-- Actual whole-path construction with ONE uniform TBI environment.
The original Runs itself supplies member widths/output growth; prefix
history is the exact successive appended event list from EMPTY. -/
theorem runs_path_polynomial (native : Λ → TM2.Stmt Alphabet Λ σ) (code : Program)
    (entry : State → NativeState Λ σ → Prop) (C d : ℕ)
    (simulate : StepPolynomial native code entry C d) (finish : HaltPolynomial native code entry C d)
    (input : List Cell) (states : List State) (final : State) (actual : Runs code input states final)
    (boot : NativeState Λ σ) (inputSize total budget : ℕ)
    (inputBound : (encodeBits input).length ≤ inputSize)
    (clock : time code states ≤ total) (peak : peakOperandBits states ≤ budget)
    (startup : ∃ first : NativeState Λ σ, entry initial first ∧ Source.Ready input initial [] first.stk ∧
      ∃ path : ActualPath (TM2.step native) boot first,
        path.posts.length ≤ C * (2 * BoundaryBudget.boundaryBudget inputSize total budget + 1)^d) :
    ∃ terminal : NativeState Λ σ, TM2.step native terminal = none ∧
      Source.Ready input final (BoundaryBudget.actualHistory code states) terminal.stk ∧
      ∃ path : ActualPath (TM2.step native) boot terminal,
        path.posts.length ≤ (states.length + 1) * C *
          (2 * BoundaryBudget.boundaryBudget inputSize total budget + 1)^d := by
  let Q := C * (2 * BoundaryBudget.boundaryBudget inputSize total budget + 1)^d
  have uniformStep : StepQ native code input states entry Q := by
    intro current next instruction events physical atBoundary fetched executed valid ready related
    obtain ⟨after, nextRelated, nextReady, path, bounded⟩ :=
      simulate input current next instruction events physical fetched executed valid ready related
    have base := local_base_bound code input states final actual inputSize total budget inputBound clock peak
      current events physical.stk atBoundary ready
    refine ⟨after, nextRelated, nextReady, path, ?_⟩
    exact bounded.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left base d))
  have uniformHalt : HaltQ native code input states entry Q := by
    intro current events physical atBoundary fetched ready related
    obtain ⟨after, halted, nextReady, path, bounded⟩ := finish input current events physical fetched ready related
    have base := local_base_bound code input states final actual inputSize total budget inputBound clock peak
      current events physical.stk atBoundary ready
    refine ⟨after, halted, nextReady, path, ?_⟩
    exact bounded.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left base d))
  obtain ⟨terminal, halted, represented, path, bounded⟩ :=
    runs_path_Q native code input states final actual entry boot Q uniformStep uniformHalt startup
  refine ⟨terminal, halted, represented, path, ?_⟩
  simpa only [Q, Nat.mul_assoc] using bounded

/-- Exact original I,T,B; no supplied boundary/numeric growth oracle.
The frozen original trace-length≤actual primitive-time lemma is reused. -/
theorem runs_path_original_parameters (native : Λ → TM2.Stmt Alphabet Λ σ) (code : Program)
    (entry : State → NativeState Λ σ → Prop) (C d : ℕ)
    (simulate : StepPolynomial native code entry C d) (finish : HaltPolynomial native code entry C d)
    (input : List Cell) (states : List State) (final : State) (actual : Runs code input states final)
    (boot : NativeState Λ σ)
    (startup : ∃ first : NativeState Λ σ, entry initial first ∧ Source.Ready input initial [] first.stk ∧
      ∃ path : ActualPath (TM2.step native) boot first,
        path.posts.length ≤ C * (2 * BoundaryBudget.boundaryBudget (encodeBits input).length
          (time code states) (peakOperandBits states) + 1)^d) :
    ∃ terminal : NativeState Λ σ, TM2.step native terminal = none ∧
      Source.Ready input final (BoundaryBudget.actualHistory code states) terminal.stk ∧
      ∃ path : ActualPath (TM2.step native) boot terminal,
        path.posts.length ≤ (time code states + 1) * C *
          (2 * BoundaryBudget.boundaryBudget (encodeBits input).length (time code states) (peakOperandBits states) + 1)^d := by
  obtain ⟨terminal, halted, represented, path, bounded⟩ :=
    runs_path_polynomial native code entry C d simulate finish input states final actual boot
      (encodeBits input).length (time code states) (peakOperandBits states) (le_refl _) (le_refl _) (le_refl _) startup
  have length := runs_length_le_actual_time code input states final actual
  refine ⟨terminal, halted, represented, path, ?_⟩
  exact bounded.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right C (Nat.add_le_add_right length 1)))

end PDROC.BitVM.VM.CFG.Run

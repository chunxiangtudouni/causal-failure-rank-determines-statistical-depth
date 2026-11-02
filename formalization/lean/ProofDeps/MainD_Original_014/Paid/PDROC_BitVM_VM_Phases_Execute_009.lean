module

public import Paid.PDROC_BitVM_VM_Phases_Execute_008
public import Paid.PDROC_BitVM_VM_Phases_Occupancy_007
public import Paid.PDROC_BitVM_VM_Phases_Resources_002
public import Paid.PDROC_BitVM_VM_Phases_Polynomial_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Execute

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Common.IO

/-! Internal finite-eight-stage proof bookkeeping. P/Q bound the two
already selected actual source calls, not runtime inputs or paper
qualifications. Every other clock charges the real entry dataSize. -/

def phaseData (backend : ISA.RatBackend) (prepareCode coreCode : Program)
    (I P Q stage : ℕ) : ℕ :=
  Polynomial.dataAfter Resources.coefficient (Calls.globalPushCap backend prepareCode coreCode) I P Q stage

def phaseBudget (backend : ISA.RatBackend) (prepareCode coreCode : Program)
    (I P Q stage : ℕ) : ℕ :=
  Polynomial.stageBudget Resources.coefficient P Q stage (phaseData backend prepareCode coreCode I P Q stage)

def StageResult (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool)
    (post : (ISA.Stack → List Bool) → Prop) (I P Q stage : ℕ) : Prop :=
  ∃ returned : State backend prepareCode coreCode,
    returned.l = some (Kernel.CallFamily.returnLabel (LocalLabel backend prepareCode coreCode) phase) ∧
    post returned.stk ∧
    Kernel.NatInstruction.dataSize returned.stk ≤ phaseData backend prepareCode coreCode I P Q (stage + 1) ∧
    ∃ path : ActualPath (TM2.step (program backend prepareCode coreCode))
      (entryState backend prepareCode coreCode phase store contents) returned,
      path.posts.length + 1 ≤ phaseBudget backend prepareCode coreCode I P Q stage

/-- Occupancy is attached BEFORE selecting caller_path. The path, its
functional postcondition and endpoint-size certificate share one run. -/
theorem scheduled_call (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool)
    (post : (ISA.Stack → List Bool) → Prop) (I P Q stage : ℕ)
    (sized : Kernel.NatInstruction.dataSize contents ≤ phaseData backend prepareCode coreCode I P Q stage)
    (actual : Calls.CallerRun backend prepareCode coreCode phase store contents post
      (phaseBudget backend prepareCode coreCode I P Q stage)) :
    StageResult backend prepareCode coreCode phase store contents post I P Q stage := by
  obtain ⟨returned, label, represented, path, clock⟩ :=
    Calls.caller_path backend prepareCode coreCode phase store contents _ _
      (Calls.CallerRun.with_data_bound backend prepareCode coreCode phase store contents post _ actual)
  refine ⟨returned, label, represented.1, ?_, path, clock⟩
  change Kernel.NatInstruction.dataSize returned.stk ≤
    32 * (phaseData backend prepareCode coreCode I P Q stage +
      Calls.globalPushCap backend prepareCode coreCode * phaseBudget backend prepareCode coreCode I P Q stage)
  exact represented.2.trans (Nat.mul_le_mul_left 32 (Nat.add_le_add_right sized _))

/-- Six actual control calls use the common cubic certificate. Only
their proved clock is enlarged; no fresh semantic path is selected. -/
theorem control_call (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase)
    (store : Store backend prepareCode coreCode) (contents : ISA.Stack → List Bool)
    (post : (ISA.Stack → List Bool) → Prop) (bound I P Q stage : ℕ)
    (notPrepare : stage ≠ 2) (notCore : stage ≠ 6)
    (sized : Kernel.NatInstruction.dataSize contents ≤ phaseData backend prepareCode coreCode I P Q stage)
    (actual : Calls.CallerRun backend prepareCode coreCode phase store contents post bound)
    (clock : bound ≤ Resources.coefficient * (Kernel.NatInstruction.dataSize contents + 1)^3) :
    StageResult backend prepareCode coreCode phase store contents post I P Q stage := by
  have larger : bound ≤ phaseBudget backend prepareCode coreCode I P Q stage := by
    change bound ≤ Polynomial.stageBudget Resources.coefficient P Q stage
      (phaseData backend prepareCode coreCode I P Q stage)
    rw [Polynomial.stageBudget, ite_eq_right notPrepare, ite_eq_right notCore]
    exact clock.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right sized 1) 3))
  exact scheduled_call backend prepareCode coreCode phase store contents post I P Q stage sized
    (Calls.CallerRun.mono backend prepareCode coreCode phase store contents post bound _ actual larger)

theorem raw_data_size (bits : List Bool) : Kernel.NatInstruction.dataSize (rawContents bits) = bits.length := by
  classical
  unfold Kernel.NatInstruction.dataSize
  calc
    _ = ((rawContents bits) 0).length := by
      apply Finset.sum_eq_single (0 : ISA.Stack)
      · intro role _ different
        rw [rawContents_other bits role different]
        rfl
      · intro absent
        exact (absent (Finset.mem_univ _)).elim
    _ = bits.length := congrArg List.length (rawContents_zero bits)

/-- Appending a call then its single genuine return edge cancels the
call list's duplicated-head allowance. This applies to the final HALT
edge as well as to each real next-phase load/goto. -/
theorem append_stage {Config : Type*} {native : Config → Option Config} {first middle returned next : Config}
    (earlier : ActualPath native first middle) (callee : ActualPath native middle returned)
    (advance : ActualPath native returned next) (spent budget : ℕ)
    (earlierTime : earlier.posts.length ≤ spent) (calleeTime : callee.posts.length + 1 ≤ budget)
    (advanceTime : advance.posts.length = 1) :
    ((earlier.trans callee).trans advance).posts.length ≤ spent + budget := by
  change ((earlier.posts ++ callee.posts) ++ advance.posts).length ≤ spent + budget
  simp only [List.length_append]
  omega

theorem append_scheduled (backend : ISA.RatBackend) (prepareCode coreCode : Program) (I P Q stage : ℕ)
    {Config : Type*} {native : Config → Option Config} {first middle returned next : Config}
    (earlier : ActualPath native first middle) (callee : ActualPath native middle returned)
    (advance : ActualPath native returned next)
    (earlierTime : earlier.posts.length ≤ Polynomial.prefixBudget Resources.coefficient
      (Calls.globalPushCap backend prepareCode coreCode) I P Q stage)
    (calleeTime : callee.posts.length + 1 ≤ phaseBudget backend prepareCode coreCode I P Q stage)
    (advanceTime : advance.posts.length = 1) :
    ((earlier.trans callee).trans advance).posts.length ≤ Polynomial.prefixBudget Resources.coefficient
      (Calls.globalPushCap backend prepareCode coreCode) I P Q (stage + 1) :=
  append_stage earlier callee advance _ _ earlierTime calleeTime advanceTime

end PDROC.BitVM.VM.Phases.Execute

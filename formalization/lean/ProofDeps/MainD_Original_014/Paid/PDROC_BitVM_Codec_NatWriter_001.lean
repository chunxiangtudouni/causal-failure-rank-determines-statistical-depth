module

public import Paid.PDROC_BitVM_Kernel_Clear_006
public import Paid.PDROC_BitVM_Kernel_NatResult_001
public import Paid.PDROC_BitVM_Log_Header_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.NatWriter

open Turing

abbrev Stack := Fin 3
abbrev Alphabet (_ : Stack) := Bool
abbrev ClearState := TM2.Cfg Alphabet Unit (Option Bool)
abbrev ClearStatement := TM2.Stmt Alphabet Unit (Option Bool)

/-- Literal index-specialization of the already checked global clear.
Its semantics below come from global actual runs and genuine projection;
there is no second proof by induction of the clear macro. -/
def clearProgram (target : Stack) (_ : Unit) : ClearStatement :=
  .pop target (fun _ symbol => symbol)
    (.branch Option.isSome (.goto (fun _ => ())) .halt)

def proofEmbed : Stack ↪ Fin 32 :=
  ⟨fun role => if role = 0 then 0 else if role = 1 then 24 else 14, by
    intro left right equal
    fin_cases left <;> fin_cases right <;> simp_all⟩

/-- The inactive global extension is ONLY a proof witness used to project
the frozen global theorem. No extra stack/workspace enters local runtime. -/
def proofExtension (contents : Stack → List Bool) : Fin 32 → List Bool :=
  fun role => if role = 0 then contents 0 else if role = 24 then contents 1
    else if role = 14 then contents 2 else []

theorem proofExtension_slots (contents : Stack → List Bool) :
    PDROC.BitVM.Native.Lift.slots proofEmbed (proofExtension contents) = contents := by
  funext role
  fin_cases role <;> rfl

theorem global_clear_eq (target : Stack) :
    PDROC.BitVM.Kernel.Clear.program (proofEmbed target) =
      PDROC.BitVM.Native.Lift.machine proofEmbed (clearProgram target) := rfl

/-- The SAME actual global clear path, projected onto the three used
roles. Arbitrary local inactive data is preserved; no logical blankness
is substituted for genuine finite-stack emptiness. -/
theorem clear_runs (target : Stack) (contents : Stack → List Bool) (store : Option Bool) :
    ∃ run : List ClearState,
      run.head? = some (⟨some (), store, contents⟩ : ClearState) ∧
      run.IsChain (fun a b => TM2.step (clearProgram target) a = some b) ∧
      run.getLast? = some (⟨none, none, Function.update contents target []⟩ : ClearState) ∧
      TM2.step (clearProgram target) (⟨none, none, Function.update contents target []⟩ : ClearState) = none ∧
      run.length = (contents target).length + 2 ∧
      ∀ other, other ≠ target → (Function.update contents target []) other = contents other := by
  obtain ⟨globalRun, head, chain, last, _halt, length, _frame⟩ :=
    PDROC.BitVM.Kernel.Clear.runs (proofEmbed target) (proofExtension contents) store
  let project : PDROC.BitVM.Kernel.Clear.State → ClearState := PDROC.BitVM.Native.Lift.cfg proofEmbed
  have first : project (⟨some (), store, proofExtension contents⟩ : PDROC.BitVM.Kernel.Clear.State) =
      (⟨some (), store, contents⟩ : ClearState) := by
    change (⟨some (), store, PDROC.BitVM.Native.Lift.slots proofEmbed (proofExtension contents)⟩ :
      ClearState) = _
    rw [proofExtension_slots]
  have final : project (⟨none, none,
      Function.update (proofExtension contents) (proofEmbed target) []⟩ : PDROC.BitVM.Kernel.Clear.State) =
      (⟨none, none, Function.update contents target []⟩ : ClearState) := by
    change (⟨none, none, PDROC.BitVM.Native.Lift.slots proofEmbed
      (Function.update (proofExtension contents) (proofEmbed target) [])⟩ : ClearState) = _
    rw [PDROC.BitVM.Native.Lift.slots_update, proofExtension_slots]
  have actual : (globalRun.map project).IsChain
      (fun a b => TM2.step (clearProgram target) a = some b) := by
    apply List.isChain_map_of_isChain _ _ chain
    intro before after edge
    have same := PDROC.BitVM.Native.Lift.step_project proofEmbed (clearProgram target) before
    rw [← global_clear_eq, edge] at same
    exact same.symm
  have selected : proofExtension contents (proofEmbed target) = contents target :=
    congrFun (proofExtension_slots contents) target
  refine ⟨globalRun.map project, ?_, actual, ?_, rfl, ?_, ?_⟩
  · simp only [List.head?_map, head, Option.map_some, first]
  · simp only [List.getLast?_map, last, Option.map_some, final]
  · simp only [List.length_map, length, selected]
  · intro other different
    exact Function.update_of_ne different _ _

theorem clear_supports (target : Stack) : TM2.Supports (clearProgram target) Finset.univ := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    cases label
    simp [clearProgram, TM2.SupportsStmt]

end PDROC.BitVM.Codec.NatWriter

module

public import Paid.PDROC_BitVM_VM_CFG_Step_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Step

open Turing PDROC.BitVM.Common.IO PaperProofs.Paid.Computation

variable {I : Type} [DecidableEq I]
variable (Λ σ : I → Type)

theorem step_some
    (opcode : ∀ index, Λ index → TM2.Stmt Alphabet (Λ index) (σ index))
    (opcodeStart : ∀ index, Λ index) (opcodeInitial : ∀ index, σ index)
    (chooseNext : I → Store σ → Option I) (index next : I) (store : Store σ) (contents : Stack → List Bool)
    (run : List (TM2.Cfg Alphabet (Λ index) (σ index))) (final : TM2.Cfg Alphabet (Λ index) (σ index))
    (head : run.head? = some ⟨some (opcodeStart index), opcodeInitial index, contents⟩)
    (chain : run.IsChain (fun a b => TM2.step (opcode index) a = some b))
    (last : run.getLast? = some final) (halt : TM2.step (opcode index) final = none)
    (input : List Cell) (logical : PaperProofs.Paid.Computation.State) (events : List Log.HeapEvent)
    (observed : Source.Observables input logical events final.stk)
    (selected : chooseNext index (opcodeStore σ index store final.var) = some next) :
    ∃ path : ActualPath (TM2.step (machine Λ σ opcode opcodeStart opcodeInitial chooseNext))
      (atOpcode Λ σ index store contents)
      (atOpcode Λ σ next
        (cleanStore σ (metadataStore σ chooseNext index (opcodeStore σ index store final.var)))
        (Cleanup.cleaned final.stk)),
      Source.Ready input logical events (Cleanup.cleaned final.stk) ∧
      path.posts.length ≤ run.length + 20 * (Cleanup.dataSize final.stk + 1) + 8 := by
  obtain ⟨first, ready, savedChoice, firstLength⟩ :=
    opcode_cleanup_path Λ σ opcode opcodeStart opcodeInitial chooseNext index store contents
      run final head chain last halt input logical events observed
  let saved := metadataStore σ chooseNext index (opcodeStore σ index store final.var)
  let target := atOpcode Λ σ next (cleanStore σ saved) (Cleanup.cleaned final.stk)
  have edge : TM2.step (machine Λ σ opcode opcodeStart opcodeInitial chooseNext)
      (cleanReturned Λ σ saved final.stk) = some target :=
    Source.Dispatch.cleanup_return_some Λ σ Cleanup.Label CleanStore opcode opcodeStart opcodeInitial
      (Cleanup.program Unit) Cleanup.startLabel (none, ()) chooseNext next (cleanStore σ saved)
      (Cleanup.cleaned final.stk) (savedChoice.trans selected)
  let path := first.trans (ActualPath.single edge)
  refine ⟨path, ready, ?_⟩
  change (first.posts ++ [target]).length ≤ _
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- None takes the actual cleanup return to the metadata port and then
executes its real HALT. It is not a free source-PC termination or tape reset. -/
theorem step_none
    (opcode : ∀ index, Λ index → TM2.Stmt Alphabet (Λ index) (σ index))
    (opcodeStart : ∀ index, Λ index) (opcodeInitial : ∀ index, σ index)
    (chooseNext : I → Store σ → Option I) (index : I) (store : Store σ) (contents : Stack → List Bool)
    (run : List (TM2.Cfg Alphabet (Λ index) (σ index))) (final : TM2.Cfg Alphabet (Λ index) (σ index))
    (head : run.head? = some ⟨some (opcodeStart index), opcodeInitial index, contents⟩)
    (chain : run.IsChain (fun a b => TM2.step (opcode index) a = some b))
    (last : run.getLast? = some final) (halt : TM2.step (opcode index) final = none)
    (input : List Cell) (logical : PaperProofs.Paid.Computation.State) (events : List Log.HeapEvent)
    (observed : Source.Observables input logical events final.stk)
    (selected : chooseNext index (opcodeStore σ index store final.var) = none) :
    ∃ path : ActualPath (TM2.step (machine Λ σ opcode opcodeStart opcodeInitial chooseNext))
      (atOpcode Λ σ index store contents)
      (⟨none, cleanStore σ (metadataStore σ chooseNext index (opcodeStore σ index store final.var)),
        Cleanup.cleaned final.stk⟩ : State Λ σ),
      Source.Ready input logical events (Cleanup.cleaned final.stk) ∧
      path.posts.length ≤ run.length + 20 * (Cleanup.dataSize final.stk + 1) + 8 := by
  obtain ⟨first, ready, savedChoice, firstLength⟩ :=
    opcode_cleanup_path Λ σ opcode opcodeStart opcodeInitial chooseNext index store contents
      run final head chain last halt input logical events observed
  let saved := metadataStore σ chooseNext index (opcodeStore σ index store final.var)
  let marker : State Λ σ := ⟨some (Source.returnLabel (FamilyLabels Λ) .metadata), cleanStore σ saved, Cleanup.cleaned final.stk⟩
  let terminal : State Λ σ := ⟨none, cleanStore σ saved, Cleanup.cleaned final.stk⟩
  have toMarker : TM2.step (machine Λ σ opcode opcodeStart opcodeInitial chooseNext)
      (cleanReturned Λ σ saved final.stk) = some marker :=
    Source.Dispatch.cleanup_return_none Λ σ Cleanup.Label CleanStore opcode opcodeStart opcodeInitial
      (Cleanup.program Unit) Cleanup.startLabel (none, ()) chooseNext (cleanStore σ saved)
      (Cleanup.cleaned final.stk) (savedChoice.trans selected)
  have toHalt : TM2.step (machine Λ σ opcode opcodeStart opcodeInitial chooseNext) marker = some terminal :=
    Source.Dispatch.metadata_halt_edge Λ σ Cleanup.Label CleanStore opcode opcodeStart opcodeInitial
      (Cleanup.program Unit) Cleanup.startLabel (none, ()) chooseNext (cleanStore σ saved) (Cleanup.cleaned final.stk)
  let path := (first.trans (ActualPath.single toMarker)).trans (ActualPath.single toHalt)
  refine ⟨path, ready, ?_⟩
  change ((first.posts ++ [marker]) ++ [terminal]).length ≤ _
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

omit [DecidableEq I] in
theorem finite_control [Fintype I] [∀ index, Fintype (Λ index)] [∀ index, Fintype (σ index)] :
    Finite (Label Λ) ∧ Finite (Store σ) := ⟨inferInstance, inferInstance⟩

theorem supports [Fintype I] [∀ index, Fintype (Λ index)] [∀ index, Inhabited (Λ index)]
    (opcode : ∀ index, Λ index → TM2.Stmt Alphabet (Λ index) (σ index))
    (opcodeStart : ∀ index, Λ index) (opcodeInitial : ∀ index, σ index)
    (chooseNext : I → Store σ → Option I)
    (closed : ∀ index, TM2.Supports (opcode index) (Finset.univ : Finset (Λ index))) :
    TM2.Supports (machine Λ σ opcode opcodeStart opcodeInitial chooseNext) (Finset.univ : Finset (Label Λ)) :=
  Source.Dispatch.supports Λ σ Cleanup.Label CleanStore opcode opcodeStart opcodeInitial
    (Cleanup.program Unit) Cleanup.startLabel (none, ()) chooseNext closed (Cleanup.supports Unit)

end PDROC.BitVM.VM.CFG.Step

module

public import Paid.PDROC_BitVM_VM_CFG_Step_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Step

open Turing PDROC.BitVM.Common.IO PaperProofs.Paid.Computation

variable {I : Type} [DecidableEq I]
variable (Λ σ : I → Type)

/-- Genuine cleanup entry reset, then the SAME nine-clear/HALT path
mapped into the caller. Its local HALT reaches the caller cleanup return
port. Metadata is preserved in a distinct saved finite-store factor. -/
theorem cleanup_path
    (opcode : ∀ index, Λ index → TM2.Stmt Alphabet (Λ index) (σ index))
    (opcodeStart : ∀ index, Λ index) (opcodeInitial : ∀ index, σ index)
    (chooseNext : I → Store σ → Option I) (store : Store σ) (contents : Stack → List Bool) :
    ∃ path : ActualPath (TM2.step (machine Λ σ opcode opcodeStart opcodeInitial chooseNext))
      (atCleanup Λ σ store contents) (cleanReturned Λ σ store contents),
      path.posts.length ≤ 20 * (Cleanup.dataSize contents + 1) + 1 := by
  let localBefore : Cleanup.State Unit := ⟨some Cleanup.startLabel, (none, ()), contents⟩
  obtain ⟨localRun, localFinal, localHead, localChain, localLast, localHalt, localDone,
      localVars, localData, localFrame, localEmpty, localLength, localSpace⟩ :=
    Cleanup.runs Unit localBefore rfl
  obtain ⟨actual, returned, head, chain, last, label, data, vars, length⟩ :=
    Source.actual_entry_trace (FamilyLabels Λ) (FamilyStores σ)
      (Source.Dispatch.source Λ σ Cleanup.Label CleanStore opcode (Cleanup.program Unit))
      (Source.Dispatch.start Λ Cleanup.Label opcodeStart Cleanup.startLabel)
      (Source.Dispatch.initial σ CleanStore opcodeInitial (none, ()))
      (Source.Dispatch.resume Λ σ Cleanup.Label CleanStore chooseNext)
      .cleanup store contents localRun localFinal localHead localChain localLast localHalt
  have returnedEqual : returned = cleanReturned Λ σ store contents := by
    rcases returned with ⟨actualLabel, actualVars, actualData⟩
    change actualLabel = some (Source.returnLabel (FamilyLabels Λ) .cleanup) at label
    change actualData = localFinal.stk at data
    change actualVars = Kernel.CallFamily.split (FamilyStores σ) .cleanup
      (localFinal.var, fun other => store other.val) at vars
    have physicalData : actualData = Cleanup.cleaned contents := data.trans localData
    have finiteStore : actualVars = cleanStore σ store := by
      exact vars.trans (congrArg (fun value : CleanStore =>
        Kernel.CallFamily.split (FamilyStores σ) .cleanup (value, fun other => store other.val)) localVars)
    subst actualLabel
    rw [finiteStore, physicalData]
    rfl
  rw [returnedEqual] at last
  obtain ⟨path, bounded⟩ := path_of_trace _ actual _ _ head chain last
  refine ⟨path, ?_⟩
  change localRun.length ≤ 20 * (Cleanup.dataSize contents + 1) at localLength
  exact bounded.trans (length.le.trans (Nat.add_le_add_right localLength 1))

theorem clean_ready (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : Stack → List Bool)
    (observed : Source.Observables input logical events contents) :
    Source.Ready input logical events (Cleanup.cleaned contents) := by
  apply Source.ready_after_cleanup input logical events contents (Cleanup.cleaned contents) observed
  · exact Cleanup.cleaned_frame contents
  · exact Cleanup.cleaned_work contents

/-- Whole actual opcode→return load→cleanup entry/reset→cleanup return.
The finite selected value is computed from the ACTUAL returned opcode
store, saved by a real load, and preserved through real physical cleanup.
No selection or workspace value is an additional original paper input. -/
theorem opcode_cleanup_path
    (opcode : ∀ index, Λ index → TM2.Stmt Alphabet (Λ index) (σ index))
    (opcodeStart : ∀ index, Λ index) (opcodeInitial : ∀ index, σ index)
    (chooseNext : I → Store σ → Option I) (index : I) (store : Store σ) (contents : Stack → List Bool)
    (run : List (TM2.Cfg Alphabet (Λ index) (σ index))) (final : TM2.Cfg Alphabet (Λ index) (σ index))
    (head : run.head? = some ⟨some (opcodeStart index), opcodeInitial index, contents⟩)
    (chain : run.IsChain (fun a b => TM2.step (opcode index) a = some b))
    (last : run.getLast? = some final) (halt : TM2.step (opcode index) final = none)
    (input : List Cell) (logical : PaperProofs.Paid.Computation.State) (events : List Log.HeapEvent)
    (observed : Source.Observables input logical events final.stk) :
    ∃ path : ActualPath (TM2.step (machine Λ σ opcode opcodeStart opcodeInitial chooseNext))
      (atOpcode Λ σ index store contents)
      (cleanReturned Λ σ (metadataStore σ chooseNext index (opcodeStore σ index store final.var)) final.stk),
      Source.Ready input logical events
        (cleanReturned Λ σ (metadataStore σ chooseNext index (opcodeStore σ index store final.var)) final.stk).stk ∧
      Source.Dispatch.selected σ CleanStore
        (cleanReturned Λ σ (metadataStore σ chooseNext index (opcodeStore σ index store final.var)) final.stk).var =
          chooseNext index (opcodeStore σ index store final.var) ∧
      path.posts.length ≤ run.length + 20 * (Cleanup.dataSize final.stk + 1) + 4 := by
  obtain ⟨first, firstLength⟩ := opcode_path Λ σ opcode opcodeStart opcodeInitial chooseNext
    index store contents run final head chain last halt
  let returnedStore := opcodeStore σ index store final.var
  let saved := metadataStore σ chooseNext index returnedStore
  have transfer : TM2.step (machine Λ σ opcode opcodeStart opcodeInitial chooseNext)
      (opcodeReturned Λ σ index store final.var final.stk) = some (atCleanup Λ σ saved final.stk) :=
    Source.Dispatch.opcode_return_edge Λ σ Cleanup.Label CleanStore opcode opcodeStart opcodeInitial
      (Cleanup.program Unit) Cleanup.startLabel (none, ()) chooseNext index returnedStore final.stk
  obtain ⟨third, thirdLength⟩ := cleanup_path Λ σ opcode opcodeStart opcodeInitial chooseNext saved final.stk
  let path := (first.trans (ActualPath.single transfer)).trans third
  refine ⟨path, clean_ready input logical events final.stk observed, ?_, ?_⟩
  · change Source.Dispatch.selected σ CleanStore (cleanStore σ saved) = chooseNext index returnedStore
    rw [selected_cleanStore]
    exact Source.Dispatch.selected_set σ CleanStore (chooseNext index returnedStore) returnedStore
  · change ((first.posts ++ [atCleanup Λ σ saved final.stk]) ++ third.posts).length ≤ _
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

end PDROC.BitVM.VM.CFG.Step

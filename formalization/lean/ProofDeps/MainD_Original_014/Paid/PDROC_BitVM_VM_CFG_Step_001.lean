module

public import Paid.PDROC_BitVM_VM_Source_EntryRun_002
public import Paid.PDROC_BitVM_VM_Source_Dispatch_005
public import Paid.PDROC_BitVM_VM_Cleanup_002
public import Paid.PDROC_BitVM_VM_Source_Representation_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Step

open Turing PDROC.BitVM.Common.IO

abbrev Stack := Cleanup.Stack
abbrev Alphabet := Cleanup.Alphabet
abbrev CleanStore := Cleanup.Store Unit

variable {I : Type} [DecidableEq I]
variable (Λ σ : I → Type)

abbrev FamilyLabels := Source.Dispatch.LocalLabel Λ Cleanup.Label
abbrev FamilyStores := Source.Dispatch.LocalStore σ CleanStore
abbrev Label := Source.Dispatch.Label Λ Cleanup.Label
abbrev Store := Source.Dispatch.Store σ CleanStore
abbrev State := TM2.Cfg Alphabet (Label Λ) (Store σ)

def machine
    (opcode : ∀ index, Λ index → TM2.Stmt Alphabet (Λ index) (σ index))
    (opcodeStart : ∀ index, Λ index) (opcodeInitial : ∀ index, σ index)
    (chooseNext : I → Store σ → Option I) : Label Λ → TM2.Stmt Alphabet (Label Λ) (Store σ) :=
  Source.Dispatch.program Λ σ Cleanup.Label CleanStore opcode opcodeStart opcodeInitial
    (Cleanup.program Unit) Cleanup.startLabel (none, ()) chooseNext

def atOpcode (index : I) (store : Store σ) (contents : Stack → List Bool) : State Λ σ :=
  Source.entryState (FamilyLabels Λ) (FamilyStores σ) (.opcode index) store contents

def atCleanup (store : Store σ) (contents : Stack → List Bool) : State Λ σ :=
  Source.entryState (FamilyLabels Λ) (FamilyStores σ) .cleanup store contents

def opcodeStore (index : I) (store : Store σ) (value : σ index) : Store σ :=
  Kernel.CallFamily.split (FamilyStores σ) (.opcode index) (value, fun other => store other.val)

def opcodeReturned (index : I) (store : Store σ) (value : σ index) (contents : Stack → List Bool) : State Λ σ :=
  ⟨some (Source.returnLabel (FamilyLabels Λ) (.opcode index)), opcodeStore σ index store value, contents⟩

def cleanStore (store : Store σ) : Store σ :=
  Kernel.CallFamily.split (FamilyStores σ) .cleanup ((none, ()), fun other => store other.val)

def cleanReturned (store : Store σ) (contents : Stack → List Bool) : State Λ σ :=
  ⟨some (Source.returnLabel (FamilyLabels Λ) .cleanup), cleanStore σ store, Cleanup.cleaned contents⟩

def metadataStore (chooseNext : I → Store σ → Option I) (index : I) (store : Store σ) : Store σ :=
  Source.Dispatch.setSelected σ CleanStore (chooseNext index store) store

theorem selected_cleanStore (store : Store σ) :
    Source.Dispatch.selected σ CleanStore (cleanStore σ store) = Source.Dispatch.selected σ CleanStore store := by
  change (if same : (Source.Dispatch.Phase.metadata : Source.Dispatch.Phase I) = .cleanup
    then same.symm.rec (none, ()) else store .metadata) = store .metadata
  exact dite_eq_right (by intro same; cases same)

/-- Only proof data converts a selected list to an endpoint-sharing path.
The actual machine store contains none of this list or its length. -/
theorem path_of_trace {S : Type*} (step : S → Option S) (run : List S) (before after : S)
    (head : run.head? = some before) (chain : run.IsChain (fun a b => step a = some b))
    (last : run.getLast? = some after) :
    ∃ path : ActualPath step before after, path.posts.length ≤ run.length := by
  cases run with
  | nil => simp only [List.head?_nil, reduceCtorEq] at head
  | cons first rest =>
    have same : first = before := Option.some.inj head
    subst first
    refine ⟨⟨rest, chain, last⟩, ?_⟩
    change rest.length ≤ (before :: rest).length
    simp only [List.length_cons]
    omega

/-- The real outer entry reset and the SAME supplied actual opcode path.
Its local HALT becomes the actual opcode return port, preserving every
other finite-store factor and all the actual macro endpoint stacks. -/
theorem opcode_path
    (opcode : ∀ index, Λ index → TM2.Stmt Alphabet (Λ index) (σ index))
    (opcodeStart : ∀ index, Λ index) (opcodeInitial : ∀ index, σ index)
    (chooseNext : I → Store σ → Option I) (index : I) (store : Store σ) (contents : Stack → List Bool)
    (run : List (TM2.Cfg Alphabet (Λ index) (σ index))) (final : TM2.Cfg Alphabet (Λ index) (σ index))
    (head : run.head? = some ⟨some (opcodeStart index), opcodeInitial index, contents⟩)
    (chain : run.IsChain (fun a b => TM2.step (opcode index) a = some b))
    (last : run.getLast? = some final) (halt : TM2.step (opcode index) final = none) :
    ∃ path : ActualPath (TM2.step (machine Λ σ opcode opcodeStart opcodeInitial chooseNext))
      (atOpcode Λ σ index store contents) (opcodeReturned Λ σ index store final.var final.stk),
      path.posts.length ≤ run.length + 1 := by
  obtain ⟨actual, returned, actualHead, actualChain, actualLast, label, data, vars, length⟩ :=
    Source.actual_entry_trace (FamilyLabels Λ) (FamilyStores σ)
      (Source.Dispatch.source Λ σ Cleanup.Label CleanStore opcode (Cleanup.program Unit))
      (Source.Dispatch.start Λ Cleanup.Label opcodeStart Cleanup.startLabel)
      (Source.Dispatch.initial σ CleanStore opcodeInitial (none, ()))
      (Source.Dispatch.resume Λ σ Cleanup.Label CleanStore chooseNext)
      (.opcode index) store contents run final head chain last halt
  have returnedEqual : returned = opcodeReturned Λ σ index store final.var final.stk := by
    rcases returned with ⟨actualLabel, actualVars, actualData⟩
    change actualLabel = some (Source.returnLabel (FamilyLabels Λ) (.opcode index)) at label
    change actualData = final.stk at data
    change actualVars = opcodeStore σ index store final.var at vars
    subst actualLabel
    subst actualVars
    subst actualData
    rfl
  rw [returnedEqual] at actualLast
  obtain ⟨path, bounded⟩ := path_of_trace _ actual _ _ actualHead actualChain actualLast
  exact ⟨path, bounded.trans (Nat.le_of_eq length)⟩

end PDROC.BitVM.VM.CFG.Step

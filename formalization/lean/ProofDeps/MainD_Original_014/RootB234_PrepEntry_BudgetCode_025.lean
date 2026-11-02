module

public import RootB234_PrepEntry_BudgetField_023

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.Budget

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

abbrev Store (C : Type*) := Restore.Store (C × RawNative.NativeMemory)
abbrev BudgetContext (C : Type*) := Header.Store (WholeCopy.Store (C × RawNative.NativeMemory) × Alpha.NativeMemory)

inductive Label where
  | restore : Restore.Label → Label
  | copy : WholeCopy.Label → Label
  | raw : RawNative.Label → Label
  | budget : RootB234.PrepBudgetArchive.Label → Label
  | rewind : Rewind.Label → Label
  | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.restore default⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def rawIso (C : Type*) : RawNative.Store (Restore.Store C) ≃ Store C where
  toFun := fun m => (((((m.1.1.1.1.1,m.2),m.1.1.1.1.2.1,m.1.1.1.1.2.2),m.1.1.1.2),m.1.1.2),m.1.2)
  invFun := fun m => (((((m.1.1.1.1.1,m.1.1.1.2.1,m.1.1.1.2.2),m.1.1.2),m.1.2),m.2),m.1.1.1.1.2)
  left_inv := by rintro ⟨⟨⟨⟨⟨context,present,bit⟩,alpha⟩,natural⟩,header⟩,raw⟩; rfl
  right_inv := by rintro ⟨⟨⟨⟨⟨context,raw⟩,present,bit⟩,alpha⟩,natural⟩,header⟩; rfl

/-- The already allocated three NaturalExport Bool registers are reused
with their REAL current values. The budget source accepts arbitrary flags;
no new block, reset, Nat or Rat register is introduced at this splice. -/
def budgetIso (C : Type*) : RootB234.PrepBudgetArchive.Store (BudgetContext C) ≃ Store C :=
  HeaderNat.fieldIso (WholeCopy.Store (C × RawNative.NativeMemory) × Alpha.NativeMemory)

def restoreLabel (point : Restore.Label) : Label := if point=.done then .copy .boot else .restore point

def copyLabel (point : WholeCopy.Label) : Label := if point=.done then .raw 0 else .copy point

def rawLabel (point : RawNative.Label) : Label := if point=1 then .budget 0 else .raw point

def budgetLabel (point : RootB234.PrepBudgetArchive.Label) : Label := if point=4 then .rewind default else .budget point

def rewindLabel (point : Rewind.Label) : Label := if point=.done then .done else .rewind point

noncomputable def program (caller : Statement C) : Label → Statement C
  | .restore point => LabelMap.statement restoreLabel (Restore.program .halt point)
  | .copy point => LabelMap.statement copyLabel
    (StoreIso.statement (Restore.copyIso (C × RawNative.NativeMemory)) (WholeCopy.program .halt point))
  | .raw point => LabelMap.statement rawLabel (StoreIso.statement (rawIso C) (RawNative.program .halt point))
  | .budget point => LabelMap.statement budgetLabel
    (StoreIso.statement (budgetIso C) (RootB234.PrepBudgetArchive.program .halt point))
  | .rewind point => LabelMap.statement rewindLabel
    (StoreIso.statement (Restore.copyIso (C × RawNative.NativeMemory)) (Rewind.program .halt point))
  | .done => caller

def restoreCfg (before : Restore.State (C × RawNative.NativeMemory)) : State C :=
  LabelMap.configuration restoreLabel before

def copyCfg (before : WholeCopy.State (NJ.Store (C × RawNative.NativeMemory))) : State C :=
  LabelMap.configuration copyLabel (StoreIso.configuration (Restore.copyIso (C × RawNative.NativeMemory)) before)

def rawCfg (before : RawNative.State (Restore.Store C)) : State C :=
  LabelMap.configuration rawLabel (StoreIso.configuration (rawIso C) before)

def budgetCfg (before : RootB234.PrepBudgetArchive.State (BudgetContext C)) : State C :=
  LabelMap.configuration budgetLabel (StoreIso.configuration (budgetIso C) before)

def rewindCfg (before : Rewind.State (NJ.Store (C × RawNative.NativeMemory))) : State C :=
  LabelMap.configuration rewindLabel (StoreIso.configuration (Restore.copyIso (C × RawNative.NativeMemory)) before)

def entry (context : C) (bits : List Bool) : State C := restoreCfg (Restore.entry (context,default) bits)

def callerContext (memory : Store C) : C := memory.1.1.1.1.1

private theorem iso_path {Λ σ : Type*} [Inhabited Λ] (caller : Statement C)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (port : Λ) (halt : old port=.halt)
    (iso : σ ≃ Store C) (tag : Λ → Label)
    (run : List (TM2.Cfg RatInput.Alphabet Λ σ)) (before final : TM2.Cfg RatInput.Alphabet Λ σ)
    (first : run.head?=some before) (chain : run.IsChain (fun a b => TM2.step old a=some b))
    (last : run.getLast?=some final) (active : final.l=some port)
    (same : ∀ point,point≠port→program caller (tag point)=LabelMap.statement tag (StoreIso.statement iso (old point))) :
    (run.map (fun current => LabelMap.configuration tag (StoreIso.configuration iso current))).head?=
      some (LabelMap.configuration tag (StoreIso.configuration iso before)) ∧
    (run.map (fun current => LabelMap.configuration tag (StoreIso.configuration iso current))).IsChain
      (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map (fun current => LabelMap.configuration tag (StoreIso.configuration iso current))).getLast?=
      some (LabelMap.configuration tag (StoreIso.configuration iso final)) := by
  let isoProgram:=StoreIso.machine iso old
  have mappedStore:=StoreIso.actual_path_on iso old isoProgram run before final first chain last
    (by intro current member point selected; rfl)
  have stopped : isoProgram port=.halt := by
    change StoreIso.statement iso (old port)=.halt
    rw [halt]
    rfl
  have proper:=NativeMulLink.no_early_halt_port isoProgram port stopped _ _ mappedStore.2.1 mappedStore.2.2.1 active
  have mapped:=LabelMap.actual_path_on tag isoProgram (program caller)
    _ _ _ mappedStore.1 mappedStore.2.1 mappedStore.2.2.1 (by
      intro current member point selected
      exact same point (by intro equal; subst point; exact proper current member selected))
  have maps : (run.map (StoreIso.configuration iso)).map (LabelMap.configuration tag)=
      run.map (fun current => LabelMap.configuration tag (StoreIso.configuration iso current)) := by rw [List.map_map]; rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem restore_path (caller : Statement C) (run : List (Restore.State (C × RawNative.NativeMemory)))
    (before final : Restore.State (C × RawNative.NativeMemory)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (Restore.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map restoreCfg).head?=some (restoreCfg before) ∧
    (run.map restoreCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map restoreCfg).getLast?=some (restoreCfg final) := by
  have proper:=NativeMulLink.no_early_halt_port (Restore.program .halt) .done rfl run final chain last active
  have mapped:=LabelMap.actual_path_on restoreLabel (Restore.program .halt) (program caller)
    run before final first chain last (by
      intro current member point selected
      have different : point≠.done := by intro equal; subst point; exact proper current member selected
      simp only [restoreLabel,different,ite_false,program])
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem copy_path (caller : Statement C) (run : List (WholeCopy.State (NJ.Store (C × RawNative.NativeMemory))))
    (before final : WholeCopy.State (NJ.Store (C × RawNative.NativeMemory))) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (WholeCopy.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map copyCfg).head?=some (copyCfg before) ∧
    (run.map copyCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map copyCfg).getLast?=some (copyCfg final) := by
  exact iso_path caller (WholeCopy.program .halt) .done rfl (Restore.copyIso (C × RawNative.NativeMemory)) copyLabel run before final first chain last active
    (by intro point different; simp only [copyLabel,different,ite_false,program])

theorem raw_path (caller : Statement C) (run : List (RawNative.State (Restore.Store C)))
    (before final : RawNative.State (Restore.Store C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (RawNative.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some 1) :
    (run.map rawCfg).head?=some (rawCfg before) ∧
    (run.map rawCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map rawCfg).getLast?=some (rawCfg final) := by
  exact iso_path caller (RawNative.program .halt) 1 rfl (rawIso C) rawLabel run before final first chain last active
    (by intro point different; simp only [rawLabel,different,ite_false,program])

theorem budget_path (caller : Statement C) (run : List (RootB234.PrepBudgetArchive.State (BudgetContext C)))
    (before final : RootB234.PrepBudgetArchive.State (BudgetContext C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (RootB234.PrepBudgetArchive.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some 4) :
    (run.map budgetCfg).head?=some (budgetCfg before) ∧
    (run.map budgetCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map budgetCfg).getLast?=some (budgetCfg final) := by
  exact iso_path caller (RootB234.PrepBudgetArchive.program .halt) 4 rfl (budgetIso C) budgetLabel run before final first chain last active
    (by intro point different; simp only [budgetLabel,different,ite_false,program])

theorem rewind_path (caller : Statement C) (run : List (Rewind.State (NJ.Store (C × RawNative.NativeMemory))))
    (before final : Rewind.State (NJ.Store (C × RawNative.NativeMemory))) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (Rewind.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map rewindCfg).head?=some (rewindCfg before) ∧
    (run.map rewindCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map rewindCfg).getLast?=some (rewindCfg final) := by
  exact iso_path caller (Rewind.program .halt) .done rfl (Restore.copyIso (C × RawNative.NativeMemory)) rewindLabel run before final first chain last active
    (by intro point different; simp only [rewindLabel,different,ite_false,program])

end RootB234.PrepEntry.Budget

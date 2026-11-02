module

public import RootB234_PrepEntry_NJPublic_011
public import B23_4_RatWordPrep_SeqCmp_WholeCopyPublic_045
public import B23_4_RatWordPrep_SeqCmp_RewindRun_056

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.Restore

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

abbrev Store (C : Type*) := NJ.Store (WholeCopy.Store C)

inductive Label where
  | copy : WholeCopy.Label → Label
  | prep : NJ.Label → Label
  | rewind : Rewind.Label → Label
  | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.copy .boot⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def copyIso (C : Type*) : WholeCopy.Store (NJ.Store C) ≃ Store C where
  toFun := fun m => ((((m.1.1.1.1,m.2.1,m.2.2),m.1.1.1.2),m.1.1.2),m.1.2)
  invFun := fun m => ((((m.1.1.1.1,m.1.1.2),m.1.2),m.2),m.1.1.1.2.1,m.1.1.1.2.2)
  left_inv := by rintro ⟨⟨⟨⟨context,alpha⟩,natural⟩,header⟩,present,bit⟩; rfl
  right_inv := by rintro ⟨⟨⟨⟨context,present,bit⟩,alpha⟩,natural⟩,header⟩; rfl

def copyLabel (point : WholeCopy.Label) : Label := if point=.done then .prep default else .copy point

def prepLabel (point : NJ.Label) : Label := if point=.done then .rewind default else .prep point

def rewindLabel (point : Rewind.Label) : Label := if point=.done then .done else .rewind point

def program (caller : Statement C) : Label → Statement C
  | .copy point => LabelMap.statement copyLabel (StoreIso.statement (copyIso C) (WholeCopy.program .halt point))
  | .prep point => LabelMap.statement prepLabel (NJ.program .halt point)
  | .rewind point => LabelMap.statement rewindLabel (StoreIso.statement (copyIso C) (Rewind.program .halt point))
  | .done => caller

def copyCfg (before : WholeCopy.State (NJ.Store C)) : State C :=
  LabelMap.configuration copyLabel (StoreIso.configuration (copyIso C) before)

def prepCfg (before : NJ.State (WholeCopy.Store C)) : State C := LabelMap.configuration prepLabel before

def rewindCfg (before : Rewind.State (NJ.Store C)) : State C :=
  LabelMap.configuration rewindLabel (StoreIso.configuration (copyIso C) before)

def entry (context : C) (bits : List Bool) : State C :=
  ⟨some (.copy .boot),((((context,false,false),default),default),default),
    fun slot => if slot=0 then bits else []⟩

def callerContext (memory : Store C) : C := memory.1.1.1.1

theorem copy_path (caller : Statement C) (run : List (WholeCopy.State (NJ.Store C)))
    (before final : WholeCopy.State (NJ.Store C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (WholeCopy.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map copyCfg).head?=some (copyCfg before) ∧
    (run.map copyCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map copyCfg).getLast?=some (copyCfg final) := by
  let old:=WholeCopy.program (C := NJ.Store C) .halt
  let isoProgram:=StoreIso.machine (copyIso C) old
  have iso:=StoreIso.actual_path_on (copyIso C) old isoProgram run before final first chain last
    (by intro current member point selected; rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram .done rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on copyLabel isoProgram (program caller)
    _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      have notDone : point≠.done := by intro same; subst point; exact proper current member selected
      simp only [copyLabel,notDone,ite_false,program]
      rfl)
  have maps : (run.map (StoreIso.configuration (copyIso C))).map (LabelMap.configuration copyLabel)=run.map copyCfg := by
    rw [List.map_map]
    rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem rewind_path (caller : Statement C) (run : List (Rewind.State (NJ.Store C)))
    (before final : Rewind.State (NJ.Store C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (Rewind.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map rewindCfg).head?=some (rewindCfg before) ∧
    (run.map rewindCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map rewindCfg).getLast?=some (rewindCfg final) := by
  let old:=Rewind.program (C := NJ.Store C) .halt
  let isoProgram:=StoreIso.machine (copyIso C) old
  have iso:=StoreIso.actual_path_on (copyIso C) old isoProgram run before final first chain last
    (by intro current member point selected; rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram .done rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on rewindLabel isoProgram (program caller)
    _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      have notDone : point≠.done := by intro same; subst point; exact proper current member selected
      simp only [rewindLabel,notDone,ite_false,program]
      rfl)
  have maps : (run.map (StoreIso.configuration (copyIso C))).map (LabelMap.configuration rewindLabel)=run.map rewindCfg := by
    rw [List.map_map]
    rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem prep_path (caller : Statement C) (trace : List (NJ.State (WholeCopy.Store C)))
    (before final : NJ.State (WholeCopy.Store C)) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (NJ.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some .done) :
    (trace.map prepCfg).head?=some (prepCfg before) ∧
    (trace.map prepCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map prepCfg).getLast?=some (prepCfg final) := by
  have proper:=NativeMulLink.no_early_halt_port (NJ.program .halt) .done rfl trace final chain last active
  have mapped:=LabelMap.actual_path_on prepLabel (NJ.program .halt) (program caller)
    trace before final first chain last (by
      intro current member point selected
      have notDone : point≠.done := by intro same; subst point; exact proper current member selected
      simp only [prepLabel,notDone,ite_false,program])
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

end RootB234.PrepEntry.Restore

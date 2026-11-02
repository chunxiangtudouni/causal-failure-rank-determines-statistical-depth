module
public import RootB236_Controller_RankMerge_Public006
public import RootB236_Controller_ResumeErase_Public006

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
abbrev Stack := Fin 16
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := BestUpdate.Store
abbrev CopyPhase := Fin 3
inductive Label where
  | control : Fin 22 → Label
  | copy : CopyPhase → B23_4_RatWordPrep.WholeCopy.Label → Label
  | select : SelectErase.Label → Label
  | resume : ResumeErase.Label → Label
  | best : BestUpdate.Label → Label
  | merge : RankMerge.Label → Label
  deriving DecidableEq
instance : Fintype Label where
  elems := (Finset.univ.image Label.control) ∪
    ((Finset.univ.product Finset.univ).image (fun pair : CopyPhase×B23_4_RatWordPrep.WholeCopy.Label => Label.copy pair.1 pair.2)) ∪
    (Finset.univ.image Label.select) ∪ (Finset.univ.image Label.resume) ∪
    (Finset.univ.image Label.best) ∪ (Finset.univ.image Label.merge)
  complete := by intro point;cases point <;> simp
instance : Inhabited Label := ⟨.control 0⟩
abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Store C)
variable {C : Type*}
def entry : Label := .control 0
def pushGood : Label := .control 14
def pushBad : Label := .control 15
def popFrame : Label := .control 16
def rootDone : Label := .control 17
def returnedGood : Label := .copy 1 .boot
def returnedBad : Label := .best 0
def Boundary (point : Label) : Prop := point=pushGood ∨ point=pushBad ∨ point=popFrame ∨ point=rootDone
instance (point : Label) : Decidable (Boundary point) := by unfold Boundary;infer_instance
/-- Ten literal work roles; no runtime natural chooses a bank. -/
def clearSlot (phase : Fin 10) : Stack :=
  if phase=0 then 3 else if phase=1 then 5 else if phase=2 then 6 else if phase=3 then 7 else
    if phase=4 then 8 else if phase=5 then 9 else if phase=6 then 10 else if phase=7 then 12 else
      if phase=8 then 14 else 15
def capture (memory : Store C) (value : Option Bool) : Store C :=
  (memory.1,value.isSome,value.getD false,memory.2.2.2)
def copyRoles (phase : CopyPhase) : Stack ≃ Stack :=
  if phase=0 then (Equiv.swap 0 11).trans ((Equiv.swap 2 6).trans (Equiv.swap 3 12)) else
    if phase=1 then (Equiv.swap 0 15).trans ((Equiv.swap 2 10).trans (Equiv.swap 3 12)) else
      (Equiv.swap 0 2).trans ((Equiv.swap 0 15).trans (Equiv.swap 3 12))
def copyReturn (phase : CopyPhase) : Label :=
  if phase=0 then .control 12 else if phase=1 then .control 18 else .control 21
def copyMap (phase : CopyPhase) : B23_4_RatWordPrep.WholeCopy.Label → Label
  | .done => copyReturn phase
  | point => .copy phase point
def selectMap : SelectErase.Label → Label
  | .found => pushBad | .empty => .merge RankMerge.entry | point => .select point
def resumeMap : ResumeErase.Label → Label
  | .body .found => pushBad | .body .empty => .merge RankMerge.entry | point => .resume point
def bestMap (point : BestUpdate.Label) : Label := if point=BestUpdate.done then .control 19 else .best point
def mergeMap (point : RankMerge.Label) : Label := if point=RankMerge.done then .control 20 else .merge point
def badRoles : Stack ≃ Stack := Equiv.swap 10 15

def program (good bad pop finish : Statement C) : Label → Statement C
  | .control point =>
    if within : point.val<10 then
      .pop (clearSlot ⟨point.val,within⟩) BestUpdate.capturePresent (.branch (fun memory => memory.2.1)
        (.goto (fun _ => .control point)) (.goto (fun _ => .control ⟨point.val+1,by have bound:=point.isLt;omega⟩)))
    else if point=10 then .pop 13 capture (.push 13 (fun _ => false) (.goto (fun _ => .control 11)))
    else if point=11 then .pop 0 BestUpdate.capturePresent (.branch (fun memory => memory.2.1)
      (.goto (fun _ => .copy 0 .boot)) (.goto (fun _ => .copy 2 .boot)))
    else if point=12 then .pop 6 BestUpdate.capturePresent (.branch (fun memory => memory.2.1)
      (.pop 0 capture (.push 7 (fun memory => memory.2.2.1) (.goto (fun _ => .control 12))))
      (.goto (fun _ => .control 13)))
    else if point=13 then .pop 7 capture (.branch (fun memory => memory.2.1)
      (.push 3 (fun memory => memory.2.2.1) (.goto (fun _ => .control 13))) (.goto (fun _ => pushGood)))
    else if point=14 then good else if point=15 then bad else if point=16 then pop else if point=17 then finish
    else if point=18 then .pop 15 BestUpdate.capturePresent (.branch (fun memory => memory.2.1)
      (.goto (fun _ => .control 18)) (.goto (fun _ => .select SelectErase.entry)))
    else if point=19 then .pop 15 BestUpdate.capturePresent (.branch (fun memory => memory.2.1)
      (.goto (fun _ => .control 19)) (.goto (fun _ => .resume .clear)))
    else if point=20 then .pop 9 capture (.branch (fun memory => memory.2.1)
      (.push 15 (fun memory => memory.2.2.1) (.goto (fun _ => .control 20))) (.goto (fun _ => .control 21)))
    else .pop 13 capture (.peek 13 BestUpdate.capturePresent (.push 13 (fun memory => memory.2.2.1)
      (.branch (fun memory => memory.2.1) (.goto (fun _ => popFrame)) (.goto (fun _ => rootDone)))))
  | .copy phase point => LabelMap.statement (copyMap phase) (StackIso.statement (copyRoles phase)
      (StoreIso.statement BestUpdate.storeIso (B23_4_RatWordPrep.WholeCopy.program .halt point)))
  | .select point => LabelMap.statement selectMap
      (StoreIso.statement BestUpdate.storeIso (SelectErase.source (C:=C×Ordering) point))
  | .resume point => LabelMap.statement resumeMap
      (StoreIso.statement BestUpdate.storeIso (ResumeErase.source (C:=C×Ordering) point))
  | .best point => LabelMap.statement bestMap (StackIso.statement badRoles (BestUpdate.program .halt point))
  | .merge point => LabelMap.statement mergeMap (RankMerge.program .halt point)

def source : Label → Statement C := program .halt .halt .halt .halt
private theorem closed (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro memory;exact Finset.mem_univ (target memory)
  | halt => trivial
theorem supports (good bad pop finish : Statement C) :
    TM2.Supports (program good bad pop finish) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun point _ => closed (program good bad pop finish point)⟩
theorem finite_store [Finite C] : Finite (Store C) := inferInstance

theorem copy_code (good bad pop finish : Statement C) (phase : CopyPhase) (point : B23_4_RatWordPrep.WholeCopy.Label)
    (proper : point≠.done) : program good bad pop finish (copyMap phase point)=
      LabelMap.statement (copyMap phase) (StackIso.statement (copyRoles phase)
        (StoreIso.statement BestUpdate.storeIso (B23_4_RatWordPrep.WholeCopy.program .halt point))) := by
  cases point <;> first | rfl | exact False.elim (proper rfl)
theorem select_code (good bad pop finish : Statement C) (point : SelectErase.Label)
    (nf : point≠.found) (ne : point≠.empty) : program good bad pop finish (selectMap point)=
      LabelMap.statement selectMap (StoreIso.statement BestUpdate.storeIso (SelectErase.source (C:=C×Ordering) point)) := by
  cases point <;> first | rfl | exact False.elim (nf rfl) | exact False.elim (ne rfl)
theorem resume_code (good bad pop finish : Statement C) (point : ResumeErase.Label)
    (nf : point≠ResumeErase.foundPort) (ne : point≠ResumeErase.emptyPort) : program good bad pop finish (resumeMap point)=
      LabelMap.statement resumeMap (StoreIso.statement BestUpdate.storeIso (ResumeErase.source (C:=C×Ordering) point)) := by
  cases point with
  | clear => rfl
  | body point => cases point <;> first | rfl | exact False.elim (nf rfl) | exact False.elim (ne rfl)
theorem best_code (good bad pop finish : Statement C) (point : BestUpdate.Label) (proper : point≠BestUpdate.done) :
    program good bad pop finish (bestMap point)=LabelMap.statement bestMap (StackIso.statement badRoles (BestUpdate.program .halt point)) := by
  simp only [bestMap,proper,ite_false,program]
theorem merge_code (good bad pop finish : Statement C) (point : RankMerge.Label) (proper : point≠RankMerge.done) :
    program good bad pop finish (mergeMap point)=LabelMap.statement mergeMap (RankMerge.program .halt point) := by
  simp only [mergeMap,proper,ite_false,program]
end RootB236.Controller.DFSDriver

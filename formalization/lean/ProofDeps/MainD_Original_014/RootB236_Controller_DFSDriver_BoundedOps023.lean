module
public import RootB236_Controller_DFSDriver_BoundedCall022

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing RootB23.GenericRank PaperProofs.Structure
open PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}
variable {q : Nat}
attribute [local irreducible] pushProfile actionProfile nodeProfile

theorem bounded_select (finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (limit skip bound cap : Nat) (best : CodeBest q) (frame : List Bool) (eligible remaining : Finset (Fin q))
    (fields : FieldsBound bg bound) (limitBound : limit≤bound) (widthBound : q≤bound)
    (skipBound : skip≤limit) (bestBound : bestCode best≤limit) (room : frame.length≤cap) :
    ∃ steps final,BoundedRun finish (peak C bound cap)
      (state (.inl (.select SelectErase.entry)) memory (firstBank bg limit skip best frame eligible remaining)) final steps ∧
      ScanResult bg memory.1 memory.2.2.2 limit skip best frame remaining (genericRankCandidates q eligible remaining) final ∧
      steps≤localTime bound cap := by
  obtain ⟨steps,final,run,outcome,time⟩:=select_current finish bg memory limit skip best frame eligible remaining
  have beforeFields:=first_fields_bound bg bound limit skip best frame eligible remaining fields limitBound
    (skipBound.trans limitBound) (bestBound.trans limitBound) widthBound
  have beforeBound:=complete_bank_bound _ bound cap (hasCode best) frame beforeFields rfl room
  have small : steps≤localTime bound cap := by dsimp only [localTime,entryCap];omega
  exact ⟨steps,final,atom run bound cap beforeBound small,outcome,small⟩

theorem bounded_resume (finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (limit skip bound cap : Nat) (best : CodeBest q) (frame : List Bool) (remaining : Finset (Fin q))
    (bits current : List Bool) (oldTool k : Nat) (tools : List (Fin q))
    (extent : k+bits.length=q) (pending : ControllerCandidate.pending k bits=tools.map Fin.val)
    (fields : FieldsBound bg bound) (limitBound : limit≤bound) (widthBound : q≤bound)
    (skipBound : skip≤limit) (bestBound : bestCode best≤limit) (room : frame.length≤cap)
    (currentBound : current.length≤q) (toolBound : oldTool≤q) :
    ∃ steps final,BoundedRun finish (peak C bound cap) (state (.inl (.resume .clear)) memory
      (scanBank bg limit skip best frame bits current (EraseSem.mask remaining) oldTool k)) final steps ∧
      ScanResult bg memory.1 memory.2.2.2 limit skip best frame remaining tools final ∧ steps≤localTime bound cap := by
  obtain ⟨steps,final,run,outcome,time⟩:=resume_current finish bg memory limit skip best frame remaining bits current oldTool k tools extent pending
  have beforeFields:=scan_fields_bound bg bound limit skip best frame bits current (EraseSem.mask remaining) oldTool k fields limitBound
    (skipBound.trans limitBound) (bestBound.trans limitBound) widthBound (by omega) (currentBound.trans widthBound)
    (mask_length_le remaining widthBound) (toolBound.trans widthBound) (by omega)
  have beforeBound:=complete_bank_bound _ bound cap (hasCode best) frame beforeFields rfl room
  have small : steps≤localTime bound cap := by dsimp only [localTime,entryCap];omega
  exact ⟨steps,final,atom run bound cap beforeBound small,outcome,small⟩

theorem bounded_update (finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (limit skip bound cap : Nat) (best : CodeBest q) (frame : List Bool) (remaining : Finset (Fin q))
    (bits : List Bool) (tool : Fin q) (rank : Nat) (extent : tool.val+1+bits.length=q)
    (fields : FieldsBound bg bound) (limitBound : limit≤bound) (widthBound : q≤bound)
    (skipBound : skip≤limit) (bestBound : bestCode best≤limit) (rankBound : rank≤limit) (room : frame.length≤cap) :
    ∃ steps finalMemory,BoundedRun finish (peak C bound cap)
      (state (.inl returnedBad) memory (bestInput bg limit skip best frame bits (EraseSem.mask (remaining.erase tool))
        (EraseSem.mask remaining) tool.val (tool.val+1) rank))
      (state (.inl (.resume .clear)) finalMemory (scanBank bg limit skip (updateCode best tool rank) frame bits
        (EraseSem.mask (remaining.erase tool)) (EraseSem.mask remaining) tool.val (tool.val+1))) steps ∧
      finalMemory.1=memory.1 ∧ steps≤localTime bound cap := by
  obtain ⟨steps,finalMemory,path,context,time⟩:=update_path .halt .halt .halt .halt bg memory limit skip best frame bits
    (EraseSem.mask (remaining.erase tool)) (EraseSem.mask remaining) tool (tool.val+1) rank
  have run:=core_path finish path
  rw [core_state,core_state] at run
  change Run finish (state (.inl returnedBad) _ _) (state (.inl (.resume .clear)) _ _) _ at run
  let before:=bestInput bg limit skip best frame bits (EraseSem.mask (remaining.erase tool))
    (EraseSem.mask remaining) tool.val (tool.val+1) rank
  have beforeFields : FieldsBound before bound := updated_fields_bound bg bound limit skip best frame bits
    (EraseSem.mask (remaining.erase tool)) (EraseSem.mask remaining) tool.val (tool.val+1) rank fields limitBound
    (skipBound.trans limitBound) (bestBound.trans limitBound) widthBound (by omega)
    (mask_length_le _ widthBound) (mask_length_le _ widthBound) (Nat.le_of_lt tool.isLt |>.trans widthBound)
    (by omega) (rankBound.trans limitBound)
  have beforeBound:=complete_bank_bound before bound cap (hasCode best) frame beforeFields rfl room
  have scaleBound:=best_scale_bound bg limit skip best frame bits (EraseSem.mask (remaining.erase tool))
    (EraseSem.mask remaining) tool.val (tool.val+1) rank (entryCap bound cap) beforeBound
  have small : steps≤localTime bound cap := by dsimp only [localTime,entryCap] at *;omega
  exact ⟨steps,finalMemory,atom run bound cap beforeBound small,context,small⟩

structure BoundedComplete (limit skip : Nat) (best : CodeBest q) (tail archive : List Bool) (remaining : Finset (Fin q))
    (context : C) (bound : Nat) (final : State C) : Prop extends Completed limit skip best tail context final where
  fields : FieldsBound final.stk bound
  archive : final.stk 1=archive
  limit_saved : final.stk 2=unary limit
  remaining_saved : final.stk 4=EraseSem.mask remaining
  width_saved : final.stk 11=unary q

theorem bounded_merge (finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (limit skip bound cap : Nat) (best : CodeBest q) (frame : List Bool) (remaining : Finset (Fin q))
    (fields : FieldsBound bg bound) (limitBound : limit≤bound) (widthBound : q≤bound)
    (skipBound : skip≤limit) (bestBound : bestCode best≤limit) (room : frame.length≤cap) :
    ∃ steps final,BoundedRun finish (peak C bound cap)
      (state (.inl (.merge RankMerge.entry)) memory
        (scanBank bg limit skip best frame [] (EraseSem.mask remaining) (EraseSem.mask remaining) 0 q)) final steps ∧
      BoundedComplete limit skip best frame (bg 1) remaining memory.1 bound final ∧ steps≤localTime bound cap := by
  let slots:=scanBank bg limit skip best frame [] (EraseSem.mask remaining) (EraseSem.mask remaining) 0 q
  obtain ⟨steps,finalMemory,path,context,time⟩:=scan_nil_path .halt .halt .halt .halt slots memory
    limit (bestCode best) skip (hasCode best) frame rfl rfl rfl rfl rfl rfl rfl
  have run:=core_path finish path
  rw [core_state,core_state,core_return] at run
  change Run finish (state (.inl (.merge RankMerge.entry)) memory slots) _ _ at run
  have slotFields : FieldsBound slots bound := scan_fields_bound bg bound limit skip best frame [] (EraseSem.mask remaining)
    (EraseSem.mask remaining) 0 q fields limitBound (skipBound.trans limitBound) (bestBound.trans limitBound) widthBound
    (Nat.zero_le _) (mask_length_le remaining widthBound) (mask_length_le remaining widthBound) (Nat.zero_le _) widthBound
  have beforeBound:=complete_bank_bound slots bound cap (hasCode best) frame slotFields rfl room
  have small : steps≤localTime bound cap := by dsimp only [localTime,entryCap];omega
  have finalFields:=merge_bank_bound slots bound limit (bestCode best) skip slotFields limitBound (skipBound.trans limitBound)
  refine ⟨steps,_,atom run bound cap beforeBound small,⟨⟨rfl,context,rfl,rfl,rfl⟩,finalFields,rfl,rfl,rfl,?_⟩,small⟩
  change unary (EraseSem.mask remaining).length=unary q
  rw [EraseSem.mask_length]
end RootB236.Controller.DFSDriver.Machine

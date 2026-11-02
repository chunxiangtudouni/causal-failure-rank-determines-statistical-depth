module
public import RootB236_Controller_DFSDriver_Data009
public import RootB236_Controller_DFSDriver_Frames011

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
open scoped BigOperators
variable {C : Type*} {q : Nat}

/-- Stable scalar banks are bounded by original data size;13 alone contains nested frames. -/
def FieldsBound (before : Stack → List Bool) (bound : Nat) : Prop := ∀ slot,slot≠13 → (before slot).length≤bound

theorem unary_length_le {n bound : Nat} (bounded : n≤bound) : (unary n).length≤bound := by
  simpa only [unary,RankCompare.unary,List.length_replicate] using bounded

theorem reverse_length_le {data : List Bool} {bound : Nat} (bounded : data.length≤bound) : data.reverse.length≤bound := by
  simpa only [List.length_reverse] using bounded

theorem mask_length_le {bound : Nat} (data : Finset (Fin q)) (bounded : q≤bound) : (EraseSem.mask data).length≤bound := by
  simpa only [EraseSem.mask_length] using bounded

theorem mass_prefix_bound (before : Stack → List Bool) (bound n : Nat) (bounded : FieldsBound before bound) :
    B23_6.DFSFrame.massPrefix before n≤n*bound := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have field:=bounded (B23_6.DFSFrame.field (B23_6.DFSFrame.rom n)) (B23_6.DFSFrame.field_ne13 _)
    simp only [B23_6.DFSFrame.massPrefix,Nat.succ_mul]
    omega

/-- The old tail occurs exactly once. This is the depth increment, not a step-count recurrence. -/
theorem frame_length_bound (parent : Stack → List Bool) (bound : Nat) (kind flag : Bool) (tail : List Bool)
    (bounded : FieldsBound parent bound) (spool : parent 13=flag::tail) :
    (B23_6.DFSFrame.framePrefix parent kind 14).length≤tail.length+28*bound+30 := by
  have size:=(B23_6.DFSFrame.Public.spool_exact parent kind).2
  change (false::B23_6.DFSFrame.framePrefix parent kind 14).length=(parent 13).length+2*B23_6.DFSFrame.massPrefix parent 14+30 at size
  rw [spool] at size
  simp only [List.length_cons] at size
  have mass:=mass_prefix_bound parent bound 14 bounded
  omega

theorem push_fields_bound (parent : Stack → List Bool) (bound : Nat) (kind : Bool) (bounded : FieldsBound parent bound) :
    FieldsBound (B23_6.DFSFrame.pushBank kind parent) bound := by
  intro slot outside
  fin_cases slot
  all_goals first | exact bounded _ (by decide) | exact Nat.zero_le bound | exact False.elim (outside rfl)

theorem restore_fields_bound (parent : Stack → List Bool) (bound : Nat) (rank : List Bool)
    (bounded : FieldsBound parent bound) (rankBound : rank.length≤bound) :
    FieldsBound (B23_6.DFSFrame.restoreBank parent rank) bound := by
  intro slot outside
  by_cases last : slot=15
  · subst slot;exact rankBound
  · change (Function.update parent 15 rank slot).length≤bound
    rw [Function.update_of_ne last]
    exact bounded slot outside

theorem complete_bank_bound (before : Stack → List Bool) (bound cap : Nat) (flag : Bool) (tail : List Bool)
    (fields : FieldsBound before bound) (spool : before 13=flag::tail) (room : tail.length≤cap) :
    ∀ slot,(before slot).length≤bound+cap+1 := by
  intro slot
  by_cases frame : slot=13
  · subst slot;rw [spool,List.length_cons];omega
  · exact (fields slot frame).trans (by omega)

theorem depth_room (parent : Stack → List Bool) (bound cap depth : Nat) (kind flag : Bool) (tail : List Bool)
    (fields : FieldsBound parent bound) (spool : parent 13=flag::tail)
    (room : tail.length+(depth+1)*(28*bound+30)≤cap) :
    (B23_6.DFSFrame.framePrefix parent kind 14).length+depth*(28*bound+30)≤cap := by
  have size:=frame_length_bound parent bound kind flag tail fields spool
  rw [Nat.add_mul] at room
  omega

theorem clean_fields_bound (before : Stack → List Bool) (bound : Nat) (bounded : FieldsBound before bound) :
    FieldsBound (cleanBank before) bound := by
  intro slot outside
  fin_cases slot
  all_goals first | exact bounded _ (by decide) | exact Nat.zero_le bound | exact False.elim (outside rfl)

theorem node_fields_bound (bg : Stack → List Bool) (bound : Nat) (input : List Bool) (limit : Nat)
    (remaining : List Bool) (q : Nat) (frame : List Bool) (bounded : FieldsBound bg bound)
    (inputBound : input.length≤bound) (limitBound : limit≤bound) (remainingBound : remaining.length≤bound) (widthBound : q≤bound) :
    FieldsBound (nodeBank bg input limit remaining q frame) bound := by
  intro slot outside
  fin_cases slot
  all_goals first | exact inputBound | exact unary_length_le limitBound |
    exact remainingBound | exact unary_length_le widthBound |
    exact bounded _ (by decide) | exact False.elim (outside rfl)

theorem ready_fields_bound (bg : Stack → List Bool) (bound : Nat) (input bits : List Bool) (limit : Nat)
    (remaining : List Bool) (q : Nat) (frame : List Bool) (bounded : FieldsBound bg bound)
    (inputBound : input.length≤bound) (bitsBound : bits.length≤bound) (limitBound : limit≤bound)
    (remainingBound : remaining.length≤bound) (widthBound : q≤bound) :
    FieldsBound (readyBank bg input bits limit remaining q frame) bound := by
  have cleaned:=clean_fields_bound _ bound (node_fields_bound bg bound input limit remaining q frame bounded inputBound limitBound remainingBound widthBound)
  intro slot outside
  by_cases eligible : slot=3
  · subst slot;exact bitsBound
  · change (Function.update (cleanBank (nodeBank bg input limit remaining q frame)) (3:Stack) bits slot).length≤bound
    rw [Function.update_of_ne eligible]
    exact cleaned slot outside

theorem tool_code_bound (best : CodeBest q) : (toolCode best).length≤q := by
  cases best with
  | none => exact Nat.zero_le q
  | some pair =>
    rcases pair with ⟨tool,rank⟩
    simpa only [toolCode,unary,RankCompare.unary,List.length_replicate] using Nat.le_of_lt tool.isLt

theorem data_fields_bound (bg : Stack → List Bool) (bound limit skip : Nat) (best : CodeBest q) (frame : List Bool)
    (bounded : FieldsBound bg bound) (limitBound : limit≤bound) (skipBound : skip≤bound)
    (bestBound : bestCode best≤bound) (widthBound : q≤bound) : FieldsBound (dataBank bg limit skip best frame) bound := by
  intro slot outside
  fin_cases slot
  all_goals first | exact bounded _ (by decide) | exact Nat.zero_le bound |
    exact unary_length_le limitBound |
    exact unary_length_le skipBound |
    exact unary_length_le bestBound |
    exact (tool_code_bound best).trans widthBound | exact False.elim (outside rfl)

theorem clear_cost_bound (before : Stack → List Bool) (bound : Nat) (bounded : FieldsBound before bound) : clearCost before≤10*bound+10 := by
  have a:=bounded 3 (by decide);have b:=bounded 5 (by decide);have c:=bounded 6 (by decide);have d:=bounded 7 (by decide)
  have e:=bounded 8 (by decide);have f:=bounded 9 (by decide);have g:=bounded 10 (by decide);have h:=bounded 12 (by decide)
  have i:=bounded 14 (by decide);have j:=bounded 15 (by decide)
  dsimp only [clearCost];omega
end RootB236.Controller.DFSDriver.Machine

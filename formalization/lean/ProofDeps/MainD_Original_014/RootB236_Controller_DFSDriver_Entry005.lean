module
public import RootB236_Controller_DFSDriver_NodePaths004

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}
def cleanBank (slots : Stack → List Bool) : Stack → List Bool :=
  fun slot => if slot=3 then [] else if slot=5 then [] else if slot=6 then [] else if slot=7 then [] else
    if slot=8 then [] else if slot=9 then [] else if slot=10 then [] else if slot=12 then [] else
      if slot=14 then [] else if slot=15 then [] else slots slot
def clearCost (slots : Stack → List Bool) : Nat :=
  (slots 3).length+(slots 5).length+(slots 6).length+(slots 7).length+(slots 8).length+
    (slots 9).length+(slots 10).length+(slots 12).length+(slots 14).length+(slots 15).length+10

theorem clear_all (good bad pop finish : Statement C) (slots : Stack → List Bool) (memory : Store C) :
    Path good bad pop finish (state entry memory slots)
      (state (.control 10) (memory.1,false,memory.2.2.1,memory.2.2.2) (cleanBank slots)) (clearCost slots) := by
  let s0:=slots
  let after : Store C := (memory.1,false,memory.2.2.1,memory.2.2.2)
  let s1:=Function.update s0 (3:Stack) ([]:List Bool)
  let s2:=Function.update s1 (5:Stack) ([]:List Bool)
  let s3:=Function.update s2 (6:Stack) ([]:List Bool)
  let s4:=Function.update s3 (7:Stack) ([]:List Bool)
  let s5:=Function.update s4 (8:Stack) ([]:List Bool)
  let s6:=Function.update s5 (9:Stack) ([]:List Bool)
  let s7:=Function.update s6 (10:Stack) ([]:List Bool)
  let s8:=Function.update s7 (12:Stack) ([]:List Bool)
  let s9:=Function.update s8 (14:Stack) ([]:List Bool)
  let s10:=Function.update s9 (15:Stack) ([]:List Bool)
  have h0:=clear_path good bad pop finish 0 s0 memory (s0 3) rfl
  have h1:=clear_path good bad pop finish 1 s1 after (s1 5) rfl
  have h2:=clear_path good bad pop finish 2 s2 after (s2 6) rfl
  have h3:=clear_path good bad pop finish 3 s3 after (s3 7) rfl
  have h4:=clear_path good bad pop finish 4 s4 after (s4 8) rfl
  have h5:=clear_path good bad pop finish 5 s5 after (s5 9) rfl
  have h6:=clear_path good bad pop finish 6 s6 after (s6 10) rfl
  have h7:=clear_path good bad pop finish 7 s7 after (s7 12) rfl
  have h8:=clear_path good bad pop finish 8 s8 after (s8 14) rfl
  have h9:=clear_path good bad pop finish 9 s9 after (s9 15) rfl
  have whole:=h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9)))))))))
  have finalBank : s10=cleanBank slots := by funext slot;fin_cases slot <;> rfl
  change Path good bad pop finish (state entry memory slots) (state (.control 10) after s10) _ at whole
  rw [finalBank] at whole
  convert whole using 1
  dsimp [clearCost,clearSlot,s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10]
  norm_num [Function.update_apply]; omega

theorem reset_flag (good bad pop finish : Statement C) (slots : Stack → List Bool) (memory : Store C) :
    TM2.step (program good bad pop finish) (state (.control 10) memory slots)=
      some (state (.control 11) (capture memory (slots 13).head?)
        (Function.update slots 13 (false::(slots 13).tail))) := by
  change some (⟨_,_,_⟩ : State C)=_
  congr 1;congr 1;funext slot
  by_cases same : slot=13
  · subst slot;simp only [Function.update_self]
  · simp only [Function.update_of_ne same]

theorem marker_code (good bad pop finish : Statement C) : program good bad pop finish (.control 11)=
    .pop 0 BestUpdate.capturePresent (.branch (fun memory => memory.2.1)
      (.goto (fun _ => .copy 0 .boot)) (.goto (fun _ => .copy 2 .boot))) := rfl
theorem marker_present (good bad pop finish : Statement C) (slots : Stack → List Bool) (memory : Store C)
    (marker : Bool) (tail : List Bool) (present : slots 0=marker::tail) :
    TM2.step (program good bad pop finish) (state (.control 11) memory slots)=
      some (state (.copy 0 .boot) (memory.1,true,memory.2.2.1,memory.2.2.2) (Function.update slots 0 tail)) := by
  change some (TM2.stepAux (program good bad pop finish (.control 11)) memory slots)=_
  rw [marker_code]
  simp only [TM2.stepAux,BestUpdate.capturePresent,present,List.head?_cons,List.tail_cons,
    Option.isSome_some,Bool.cond_true,state]
theorem marker_empty (good bad pop finish : Statement C) (slots : Stack → List Bool) (memory : Store C)
    (empty : slots 0=[]) :
    TM2.step (program good bad pop finish) (state (.control 11) memory slots)=
      some (state (.copy 2 .boot) (memory.1,false,memory.2.2.1,memory.2.2.2) (Function.update slots 0 [])) := by
  change some (TM2.stepAux (program good bad pop finish (.control 11)) memory slots)=_
  rw [marker_code]
  simp only [TM2.stepAux,BestUpdate.capturePresent,empty,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.cond_false,state]

def nodeBank (bg : Stack → List Bool) (stream : List Bool) (limit : Nat) (remaining : List Bool)
    (q : Nat) (frame : List Bool) : Stack → List Bool :=
  fun slot => if slot=0 then stream else if slot=2 then unary limit else if slot=4 then remaining else
    if slot=11 then unary q else if slot=13 then frame else bg slot

def readyBank (bg : Stack → List Bool) (stream eligible : List Bool) (limit : Nat) (remaining : List Bool)
    (q : Nat) (frame : List Bool) : Stack → List Bool :=
  Function.update (cleanBank (nodeBank bg stream limit remaining q frame)) 3 eligible

/-- Actual entry cleanup and flag production. The old frame tail is retained once, including empty root13. -/
theorem entry_path (good bad pop finish : Statement C) (slots : Stack → List Bool) (memory : Store C) :
    Path good bad pop finish (state entry memory slots)
      (state (.control 11) (capture (memory.1,false,memory.2.2.1,memory.2.2.2) (slots 13).head?)
        (Function.update (cleanBank slots) 13 (false::(slots 13).tail))) (clearCost slots+1) := by
  have cleaned:=clear_all good bad pop finish slots memory
  have reset : Path good bad pop finish
      (state (.control 10) (memory.1,false,memory.2.2.1,memory.2.2.2) (cleanBank slots))
      (state (.control 11) (capture (memory.1,false,memory.2.2.1,memory.2.2.2) (slots 13).head?)
        (Function.update (cleanBank slots) 13 (false::(slots 13).tail))) 1 :=
    Path.step (inside_control _ _ _ (Or.inl (by decide))) (reset_flag good bad pop finish _ _) .refl
  exact cleaned.trans reset
end RootB236.Controller.DFSDriver

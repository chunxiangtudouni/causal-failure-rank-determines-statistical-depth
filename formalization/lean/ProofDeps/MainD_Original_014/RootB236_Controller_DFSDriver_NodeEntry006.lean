module
public import RootB236_Controller_DFSDriver_Entry005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}

theorem entry_node (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (input : List Bool) (limit : Nat) (remaining : List Bool) (q : Nat) (frame : List Bool) :
    Path good bad pop finish (state entry memory (nodeBank bg input limit remaining q frame))
      (state (.control 11) (capture memory frame.head?)
        (cleanBank (nodeBank bg input limit remaining q (false::frame.tail))))
      (clearCost (nodeBank bg input limit remaining q frame)+1) := by
  have raw:=entry_path good bad pop finish (nodeBank bg input limit remaining q frame) memory
  have bankEq : Function.update (cleanBank (nodeBank bg input limit remaining q frame)) 13
      (false::(nodeBank bg input limit remaining q frame 13).tail)=
        cleanBank (nodeBank bg input limit remaining q (false::frame.tail)) := by
    funext slot;fin_cases slot <;> rfl
  rw [bankEq] at raw
  exact raw

theorem qcopy_row (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (bits suffix : List Bool) (limit : Nat) (remaining : List Bool) (q : Nat) (frame : List Bool)
    (width : bits.length=q) :
    Path good bad pop finish
      (state (.copy 0 .boot) memory (cleanBank (nodeBank bg (bits++suffix) limit remaining q frame)))
      (state pushGood (memory.1,false,false,memory.2.2.2) (readyBank bg suffix bits limit remaining q frame)) (4*q+5) := by
  subst q
  let slots:=cleanBank (nodeBank bg (bits++suffix) limit remaining bits.length frame)
  have copied:=copy_current good bad pop finish 0 slots memory (unary bits.length) [] []
  rw [show (unary bits.length).reverse++[]=unary bits.length from BestUpdate.unary_reverse bits.length] at copied
  have inputBank : copyBank 0 slots (unary bits.length) [] []=slots := by funext slot;fin_cases slot <;> rfl
  have outputBank : copyBank 0 slots (unary bits.length) (unary bits.length) []=
      rowBank slots (bits++suffix) [] bits.length [] := by funext slot;fin_cases slot <;> rfl
  change Path good bad pop finish (state _ _ _) (state _ _ _) _ at copied
  rw [inputBank,outputBank] at copied
  have read:=row_path good bad pop finish slots (memory.1,true,true,memory.2.2.2) bits suffix
  have finalBank : rowBank slots suffix bits 0 []=readyBank bg suffix bits limit remaining bits.length frame := by
    funext slot;fin_cases slot <;> rfl
  rw [finalBank] at read
  have whole:=copied.trans read
  simpa only [copyMap,copyReturn,unary,RankCompare.unary,List.length_replicate,
    show 2*bits.length+3+(2*bits.length+2)=4*bits.length+5 by omega] using whole

/-- Complete real nonterminal entry, including q0 marker/EOF distinction. -/
theorem call_cons_path (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (bits suffix : List Bool) (limit : Nat) (remaining : List Bool) (q : Nat) (frame : List Bool)
    (width : bits.length=q) :
    Path good bad pop finish
      (state entry memory (nodeBank bg (true::(bits++suffix)) limit remaining q frame))
      (state pushGood (memory.1,false,false,memory.2.2.2)
        (readyBank bg suffix bits limit remaining q (false::frame.tail)))
      (clearCost (nodeBank bg (true::(bits++suffix)) limit remaining q frame)+4*q+7) := by
  have initialized:=entry_node good bad pop finish bg memory (true::(bits++suffix)) limit remaining q frame
  let middle:=cleanBank (nodeBank bg (true::(bits++suffix)) limit remaining q (false::frame.tail))
  let mem:=capture memory frame.head?
  have marked:=marker_present good bad pop finish middle mem true (bits++suffix) rfl
  have bankEq : Function.update middle 0 (bits++suffix)=cleanBank (nodeBank bg (bits++suffix) limit remaining q (false::frame.tail)) := by
    funext slot;fin_cases slot <;> rfl
  rw [bankEq] at marked
  have tail:=qcopy_row good bad pop finish bg (mem.1,true,mem.2.2.1,mem.2.2.2) bits suffix limit remaining q (false::frame.tail) width
  have whole:=initialized.trans (Path.step (inside_control _ mem middle (Or.inl (by decide))) marked tail)
  convert whole using 1 <;> first | rfl | omega

/-- Actual terminal production copies the physical global limit; it does not compute N in the store. -/
theorem terminal_copy (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (limit : Nat) (remaining : List Bool) (q : Nat) (frame : List Bool) :
    Path good bad pop finish
      (state (.copy 2 .boot) memory (cleanBank (nodeBank bg [] limit remaining q frame)))
      (state (.control 21) (memory.1,true,true,memory.2.2.2)
        (Function.update (cleanBank (nodeBank bg [] limit remaining q frame)) 15 (unary limit))) (2*limit+3) := by
  let slots:=cleanBank (nodeBank bg [] limit remaining q frame)
  have copied:=copy_current good bad pop finish 2 slots memory (unary limit) [] []
  rw [show (unary limit).reverse++[]=unary limit from BestUpdate.unary_reverse limit] at copied
  have inputBank : copyBank 2 slots (unary limit) [] []=slots := by funext slot;fin_cases slot <;> rfl
  have outputBank : copyBank 2 slots (unary limit) (unary limit) []=Function.update slots 15 (unary limit) := by
    funext slot;fin_cases slot <;> rfl
  change Path good bad pop finish (state _ _ _) (state _ _ _) _ at copied
  rw [inputBank,outputBank] at copied
  simpa only [copyMap,copyReturn,show (2:CopyPhase)≠0 by decide,show (2:CopyPhase)≠1 by decide,ite_false,unary,RankCompare.unary,List.length_replicate] using copied

theorem call_nil_path (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (limit : Nat) (remaining : List Bool) (q : Nat) (frame : List Bool) :
    Path good bad pop finish (state entry memory (nodeBank bg [] limit remaining q frame))
      (state (if frame.tail.isEmpty then rootDone else popFrame)
        (memory.1,!frame.tail.isEmpty,false,memory.2.2.2)
        (Function.update (cleanBank (nodeBank bg [] limit remaining q (false::frame.tail))) 15 (unary limit)))
      (clearCost (nodeBank bg [] limit remaining q frame)+2*limit+6) := by
  have initialized:=entry_node good bad pop finish bg memory [] limit remaining q frame
  let slots:=cleanBank (nodeBank bg [] limit remaining q (false::frame.tail))
  let mem:=capture memory frame.head?
  have marked:=marker_empty good bad pop finish slots mem rfl
  have unchanged : Function.update slots 0 []=slots := by funext slot;fin_cases slot <;> rfl
  rw [unchanged] at marked
  have copied:=terminal_copy good bad pop finish bg (mem.1,false,mem.2.2.1,mem.2.2.2) limit remaining q (false::frame.tail)
  let finalSlots:=Function.update slots 15 (unary limit)
  have probed:=return_probe good bad pop finish finalSlots (mem.1,true,true,mem.2.2.2) false frame.tail rfl
  have last : Path good bad pop finish (state (.control 21) (mem.1,true,true,mem.2.2.2) finalSlots)
      (state (if frame.tail.isEmpty then rootDone else popFrame) (mem.1,!frame.tail.isEmpty,false,mem.2.2.2) finalSlots) 1 :=
    Path.step (inside_control _ _ _ (Or.inr (by decide))) probed .refl
  have whole:=initialized.trans (Path.step (inside_control _ mem slots (Or.inl (by decide))) marked (copied.trans last))
  convert whole using 1 <;> first | rfl | omega
end RootB236.Controller.DFSDriver

module

public import PSTR_WordBool_RatPair_Restore_001

/-! Exact physical bank ports for the four paid field loops and one
whole-source restore. The arrays here are theorem states, never control. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Collector

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

theorem actual_field (caller : Statement C) (later second : Bool) (background : Stack → List Bool)
    (context : C) (sx sy : Bool) (formatter : WordNatIO.Store) (mode : Bool) (digits : List Bool)
    (bit flag : Bool) (copied source scratch xn xd yn yd : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some (state background
        (if later then (if second then 5 else 4) else (if second then 2 else 1)) context sx sy (bit,flag,mode) formatter
        (PSTRTMRawNat010.leftBlocks digits++false::false::source)
        (PSTRSymbolicNaturalExport.backups copied++true::scratch) xn xd yn yd) ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some (state background
        (if later then (if second then 6 else 5) else (if second then 3 else 2)) context sx sy (false,false,mode) formatter
        source
        (PSTRSymbolicNaturalExport.backups
          (false::false::((PSTRTMRawNat010.leftBlocks digits).reverse++copied))++true::scratch)
        (if later then xn else if second then xn else digits.reverse++xn)
        (if later then xd else if second then digits.reverse++xd else xd)
        (if later then (if second then yn else digits.reverse++yn) else yn)
        (if later then (if second then digits.reverse++yd else yd) else yd)) ∧
      trace.length=digits.length+2 := by
  let oldNum:=if later then yn else xn
  let oldDen:=if later then yd else xd
  let oldBackground:=fieldBackground later background xn xd yn yd
  let old:=RatInput.fieldTrace second oldBackground ((context,sx,sy),formatter) mode digits bit flag
    copied source scratch oldNum oldDen (background 13)
  have path:=field_path caller later second oldBackground context sx sy formatter mode digits bit flag
    copied source scratch oldNum oldDen (background 13)
  refine ⟨old.map (fieldConfiguration later),?_,path.2.1,?_,path.2.2.2⟩
  · have first:=path.1
    change _=some (fieldConfiguration later (RatInput.state (fieldBackground later background xn xd yn yd) _ _ _ _ _ _ _ _)) at first
    rw [field_configuration] at first
    cases later <;> cases second <;> exact first
  · have last:=path.2.2.1
    change _=some (fieldConfiguration later (RatInput.state (fieldBackground later background xn xd yn yd) _ _ _ _ _ _ _ _)) at last
    rw [field_configuration] at last
    cases later <;> cases second <;> exact last

theorem actual_restore (caller : Statement C) (background : Stack → List Bool)
    (context : C) (sx sy : Bool) (formatter : WordNatIO.Store) (bit flag mode : Bool)
    (copied source scratch xn xd yn yd : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some (state background 6 context sx sy (bit,flag,mode) formatter source
        (PSTRSymbolicNaturalExport.backups copied++true::scratch) xn xd yn yd) ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some (state background 7 context sx sy
        (PSTRSymbolicNaturalExport.finalBit copied bit,true,mode) formatter
        (copied.reverse++source) scratch xn xd yn yd) ∧
      trace.length=copied.length+2 := by
  let oldBackground:=bank background [] [] xn xd yn yd
  let old:=RatInput.restoreTrace oldBackground ((context,sx,sy),formatter) bit flag mode
    copied source scratch yn yd (background 13)
  have path:=restore_path caller oldBackground context sx sy formatter bit flag mode
    copied source scratch yn yd (background 13)
  refine ⟨old.map restoreConfiguration,?_,path.2.1,?_,path.2.2.2⟩
  · have first:=path.1
    dsimp only [oldBackground] at first
    rw [restore_configuration] at first
    exact first
  · have last:=path.2.2.1
    dsimp only [oldBackground] at last
    rw [restore_configuration] at last
    exact last

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Collector

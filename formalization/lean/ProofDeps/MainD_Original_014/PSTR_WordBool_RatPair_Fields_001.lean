module

public import PSTR_WordBool_RatPair_Code_001

/-! Genuine frozen field-copy traces, transported only by fixed stack,
store and label maps. Every proper field point really executes its source. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Collector

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

theorem field_proper (second : Bool) (background : Stack → List Bool) (context : C)
    (mode : Bool) (digits : List Bool) (bit flag : Bool)
    (copied source scratch numerator denominator raw : List Bool) :
    ∀ current ∈ (RatInput.fieldTrace second background context mode digits bit flag
      copied source scratch numerator denominator raw).dropLast,
      current.l=some (if second then 2 else 1) := by
  induction digits generalizing bit flag copied numerator denominator with
  | nil =>
    intro current member
    have same : current=RatInput.state background (if second then 2 else 1) context (bit,flag,mode)
        (false::false::source) (PSTRSymbolicNaturalExport.backups copied++true::scratch) numerator denominator raw := by
      simpa only [RatInput.fieldTrace,List.dropLast_cons_cons,List.dropLast_singleton,List.mem_singleton] using member
    subst current
    rfl
  | cons digit later ih =>
    intro current member
    rw [RatInput.fieldTrace,List.dropLast_cons_of_ne_nil (RatInput.field_nonempty _ _ _ _ _ _ _ _ _ _ _ _ _)] at member
    rcases List.mem_cons.mp member with rfl|laterMember
    · rfl
    · exact ih digit true (digit::true::copied) _ _ current laterMember

theorem program_field (caller : Statement C) (later second : Bool) :
    program caller (fieldLabel later (if second then 2 else 1))=fieldBody later second := by
  cases later <;> cases second <;> rfl

theorem field_path (caller : Statement C) (later second : Bool) (background : Stack → List Bool)
    (context : C) (sx sy : Bool) (formatter : WordNatIO.Store) (mode : Bool) (digits : List Bool)
    (bit flag : Bool) (copied source scratch numerator denominator raw : List Bool) :
    let old:=RatInput.fieldTrace second background ((context,sx,sy),formatter) mode digits bit flag
      copied source scratch numerator denominator raw
    (old.map (fieldConfiguration later)).head?=some (fieldConfiguration later
      (RatInput.state background (if second then 2 else 1) ((context,sx,sy),formatter) (bit,flag,mode)
        (PSTRTMRawNat010.leftBlocks digits++false::false::source)
        (PSTRSymbolicNaturalExport.backups copied++true::scratch) numerator denominator raw)) ∧
    (old.map (fieldConfiguration later)).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (old.map (fieldConfiguration later)).getLast?=some (fieldConfiguration later
      (RatInput.state background (if second then 3 else 2) ((context,sx,sy),formatter) (false,false,mode) source
        (PSTRSymbolicNaturalExport.backups
          (false::false::((PSTRTMRawNat010.leftBlocks digits).reverse++copied))++true::scratch)
        (if second then numerator else digits.reverse++numerator)
        (if second then digits.reverse++denominator else denominator) raw)) ∧
    (old.map (fieldConfiguration later)).length=digits.length+2 := by
  let old:=RatInput.fieldTrace second background ((context,sx,sy),formatter) mode digits bit flag
    copied source scratch numerator denominator raw
  let roles:=fieldRoles later
  let exchange:=RatInput.Encoder.exchange (C × Bool × Bool)
  let sourceProgram:=RatInput.program (C:=(C × Bool × Bool) × WordNatIO.Store) .halt
  let stackProgram:=fun point=>StackIso.statement roles (sourceProgram point)
  let storeProgram:=StoreIso.machine exchange stackProgram
  have oldChain:=RatInput.field_chain .halt second background ((context,sx,sy),formatter) mode digits bit flag
    copied source scratch numerator denominator raw
  have stackChain:=StackIso.chain_configuration_on roles sourceProgram stackProgram old oldChain
    (by intro current member point selected;rfl)
  have storeChain:=StoreIso.chain_configuration_on exchange stackProgram storeProgram
    (old.map (StackIso.configuration roles)) stackChain
    (by intro current member point selected;rfl)
  have mapped:=LabelMap.chain_configuration_on (fieldLabel later) storeProgram (program caller)
    ((old.map (StackIso.configuration roles)).map (StoreIso.configuration exchange)) storeChain (by
      intro current member point selected
      rw [←List.map_dropLast] at member
      obtain ⟨middle,middleMember,rfl⟩:=List.mem_map.mp member
      rw [←List.map_dropLast] at middleMember
      obtain ⟨small,smallMember,rfl⟩:=List.mem_map.mp middleMember
      have position:=field_proper second background ((context,sx,sy),formatter) mode digits bit flag
        copied source scratch numerator denominator raw small smallMember
      change small.l=some point at selected
      have same : point=(if second then 2 else 1):=Option.some.inj (selected.symm.trans position)
      subst point
      exact program_field caller later second)
  have maps : ((old.map (StackIso.configuration roles)).map (StoreIso.configuration exchange)).map
      (LabelMap.configuration (fieldLabel later))=old.map (fieldConfiguration later) := by
    rw [List.map_map,List.map_map]
    rfl
  rw [maps] at mapped
  refine ⟨?_,?_,?_,?_⟩
  · rw [List.head?_map,RatInput.field_head,Option.map_some]
  · exact mapped
  · rw [List.getLast?_map,RatInput.field_last,Option.map_some]
  · rw [List.length_map,RatInput.field_length]

def fieldBackground (later : Bool) (background : Stack → List Bool) (xn xd yn yd : List Bool) : Stack → List Bool :=
  StackIso.slots (fieldRoles later).symm (bank background [] [] xn xd yn yd)

theorem field_configuration (later : Bool) (background : Stack → List Bool) (point : RatInput.Label)
    (context : C) (sx sy : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (source scratch xn xd yn yd numerator denominator : List Bool) :
    fieldConfiguration later
      (RatInput.state (fieldBackground later background xn xd yn yd) point ((context,sx,sy),formatter) memory
        source scratch numerator denominator (background 13))=
      state background (fieldLabel later point) context sx sy memory formatter source scratch
        (if later then xn else numerator) (if later then xd else denominator)
        (if later then numerator else yn) (if later then denominator else yd) := by
  change (⟨some (fieldLabel later point),(((context,sx,sy),memory),formatter),_⟩:State C)=_
  congr 1
  funext slot
  cases later <;> fin_cases slot <;> rfl

theorem restore_configuration (background : Stack → List Bool) (point : RatInput.Label)
    (context : C) (sx sy : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (source scratch xn xd yn yd : List Bool) :
    restoreConfiguration (RatInput.state (bank background [] [] xn xd yn yd) point
      ((context,sx,sy),formatter) memory source scratch yn yd (background 13))=
      state background (restoreLabel point) context sx sy memory formatter source scratch xn xd yn yd := by
  change (⟨some (restoreLabel point),(((context,sx,sy),memory),formatter),_⟩:State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Collector

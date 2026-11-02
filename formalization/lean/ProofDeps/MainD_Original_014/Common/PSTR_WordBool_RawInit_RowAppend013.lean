module

public import Common.PSTR_WordBool_RawInit_RowEnd012
public import Common.PSTR_WordBool_Emit33_Core001
public import Common.PSTR_SYM_Carry_042

/-! ONE finite table carries a real finite entry bit through the actual
presence-driven output-end search and selects the matching frozen Emit33
entry. Both append values use this one code and one common final HALT.
The future source decoder must populate the finite bit entry by reading
the source; this internal port is not a raw-input oracle. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.RowAppend

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMSeq005

def savedBit (bit : Bool) : Fin 8 := if bit then 1 else 0
def rowLabel (label : Fin 280) : Fin 365 := ⟨label.val,by omega⟩
def emitLabel (label : Fin 85) : Fin 365 := ⟨280+label.val,by omega⟩
def entry (bit : Bool) : Fin 365 := rowLabel (PSTRSymbolicCarry.carryLabel (0 : Fin 35) (savedBit bit))
def haltPort : Fin 365 := emitLabel Emit33.haltPort

def machine : Machine 364 := fun label symbol =>
  if inside : label.val < 280 then
    let q : Fin 280 := ⟨label.val,inside⟩
    match PSTRSymbolicCarry.carryMachine RowEnd.machine q symbol with
    | none => some (emitLabel (Emit33.entry false ((PSTRSymbolicCarry.savedLabel (states:=34) q).val == 1)),
        .write symbol)
    | some (next,op) => some (rowLabel next,op)
  else
    let q : Fin 85 := ⟨label.val-280,by omega⟩
    match Emit33.code q symbol with
    | none => none
    | some (next,op) => some (emitLabel next,op)

def rowCfg (bit : Bool) (cfg : MachineState 34) : MachineState 364 :=
  ⟨rowLabel (PSTRSymbolicCarry.carryLabel cfg.q (savedBit bit)),cfg.Tape⟩
def emitCfg (cfg : MachineState 84) : MachineState 364 := ⟨emitLabel cfg.q,cfg.Tape⟩

theorem row_lookup (q : Fin 280) (symbol : Bool) :
    machine (rowLabel q) symbol =
      match PSTRSymbolicCarry.carryMachine RowEnd.machine q symbol with
      | none => some (emitLabel (Emit33.entry false ((PSTRSymbolicCarry.savedLabel (states:=34) q).val == 1)),
          .write symbol)
      | some (next,op) => some (rowLabel next,op) := by
  simp only [machine,rowLabel,q.isLt,↓reduceDIte,Fin.eta]

theorem emit_lookup (q : Fin 85) (symbol : Bool) :
    machine (emitLabel q) symbol =
      match Emit33.code q symbol with
      | none => none
      | some (next,op) => some (emitLabel next,op) := by
  have outside : ¬280+q.val < 280 := by omega
  simp only [machine,emitLabel,outside,↓reduceDIte,Nat.add_sub_cancel_left,Fin.eta]

theorem row_step (bit : Bool) (cfg : MachineState 34) :
    TM0.step machine (rowCfg bit cfg) =
      match TM0.step RowEnd.machine cfg with
      | none => some (emitCfg ⟨Emit33.entry false bit,cfg.Tape⟩)
      | some next => some (rowCfg bit next) := by
  cases cfg with
  | mk q tape =>
    simp only [TM0.step,rowCfg]
    rw [row_lookup]
    simp only [PSTRSymbolicCarry.carryMachine,PSTRSymbolicRelabel.relabelMachine,TM0.Machine.map,
      PSTRSymbolicCarry.original_carry,PSTRSymbolicCarry.saved_carry,PSTRSymbolicRelabel.boolIdentity,id_eq]
    have recovered : ((savedBit bit).val == 1) = bit := by cases bit <;> rfl
    rw [recovered]
    cases action : RowEnd.machine q tape.head with
    | none => simp only [Option.map_none,Option.map_some,emitCfg,Tape.write_self]
    | some pair =>
      obtain ⟨next,op⟩ := pair
      cases op <;> rfl

theorem emit_step (cfg : MachineState 84) :
    TM0.step machine (emitCfg cfg) = (TM0.step Emit33.code cfg).map emitCfg := by
  cases cfg with
  | mk q tape =>
    simp only [TM0.step,emitCfg]
    rw [emit_lookup]
    cases action : Emit33.code q tape.head with
    | none => rfl
    | some pair =>
      obtain ⟨next,op⟩ := pair
      cases op <;> rfl

theorem blank_writer_input (left : List Bool) :
    Tape.mk₂ left [] = Tape.mk₂ left (List.replicate 33 false ++ []) := by
  have blank : ListBlank.mk ([] : List Bool) = ListBlank.mk (List.replicate 33 false) :=
    Quotient.sound (Or.inl ⟨33,rfl⟩)
  simp only [List.append_nil]
  change Tape.mk' (ListBlank.mk left) (ListBlank.mk ([] : List Bool)) =
    Tape.mk' (ListBlank.mk left) (ListBlank.mk (List.replicate 33 false))
  rw [blank]

theorem actual (bit : Bool) (left bits : List Bool) (inputLength : Nat) :
    ∃ path,
      RunsFrom machine ⟨entry bit,Tape.mk₂ left (RowEnd.rows bits)⟩ path
        ⟨haltPort,Tape.mk₂ ((RowEnd.rows (bits ++ [bit])).reverse ++ left) []⟩ ∧
      path.length = 33*(bits.length+1)+70 ∧
      ∀ clock, visitedSpace machine inputLength (path.take clock) ≤ inputLength+66*(bits.length+1)+141 := by
  obtain ⟨rowTrace,rowRun,rowTime,_rowSpace⟩ := RowEnd.actual left bits inputLength
  let outputLeft := (RowEnd.rows bits).reverse ++ left
  obtain ⟨emitTrace,emitRun,emitTime⟩ := Emit33.runs_list false bit outputLeft
    (List.replicate 33 false) [] (by simp)
  have emitStart : emitTrace.head? =
      some ⟨Emit33.entry false bit,(RowEnd.finish left bits).Tape⟩ := by
    rw [emitRun.1]
    change some (⟨Emit33.entry false bit,Tape.mk₂ outputLeft (List.replicate 33 false ++ [])⟩ : MachineState 84) = _
    rw [← blank_writer_input]
    rfl
  let path := rowTrace.map (rowCfg bit) ++ emitTrace.map emitCfg
  let final := emitCfg ⟨Emit33.haltPort,Tape.mk₂ ((rowBits false bit).reverse ++ outputLeft) []⟩
  have rowChain : (rowTrace.map (rowCfg bit)).IsChain
      (fun before after => TM0.step machine before = some after) := by
    apply (List.isChain_map _).mpr
    exact rowRun.2.1.imp (fun before after edge => by simp only [row_step,edge])
  have emitChain : (emitTrace.map emitCfg).IsChain
      (fun before after => TM0.step machine before = some after) := by
    apply (List.isChain_map _).mpr
    exact emitRun.2.1.imp (fun before after edge => by simp only [emit_step,edge,Option.map_some])
  have chain : path.IsChain (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append rowChain emitChain
    intro before beforeLast after afterHead
    simp only [List.getLast?_map,rowRun.2.2.1,Option.map_some,Option.mem_some_iff] at beforeLast
    simp only [List.head?_map,emitStart,Option.map_some,Option.mem_some_iff] at afterHead
    subst before
    subst after
    simp only [row_step,rowRun.2.2.2]
  have run : RunsFrom machine ⟨entry bit,Tape.mk₂ left (RowEnd.rows bits)⟩ path final := by
    refine ⟨?_,chain,?_,?_⟩
    · simp only [path,List.head?_append,List.head?_map,rowRun.1,Option.map_some,Option.some_or]
      rfl
    · simp only [path,final,List.getLast?_append,List.getLast?_map,emitRun.2.2.1,Option.map_some,Option.some_or]
    · simp only [final,emit_step,emitRun.2.2.2,Option.map_none]
  have finalEq : final = ⟨haltPort,Tape.mk₂ ((RowEnd.rows (bits ++ [bit])).reverse ++ left) []⟩ := by
    simp only [final,emitCfg,haltPort,outputLeft,RowEnd.rows,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.reverse_append,List.append_assoc]
  have length : path.length = 33*(bits.length+1)+70 := by
    simp only [path,List.length_append,List.length_map,rowTime,emitTime]
  rw [finalEq] at run
  refine ⟨path,run,length,?_⟩
  intro clock
  have space := PSTRTMTrace002.visitedSpace_le machine inputLength (path.take clock)
  have short := List.length_take_le' clock path
  omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.RowAppend

module

public import Common.PSTR_WordBool_RawInit_MarkSeek014

/-! The append bit is now obtained by the program itself from the real
source payload cell. One finite380-control table selects, marks, seeks,
finds the output end and writes the matching33-cell row. No bit is passed
through an external entry choice. The selected flag remains for return. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.MarkAppend

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMSeq005

def markLabel (q : Fin 15) : Fin 380 := ⟨q.val,by omega⟩
def appendLabel (q : Fin 365) : Fin 380 := ⟨15+q.val,by omega⟩
def saved (q : Fin 15) : Bool := decide (8 ≤ q.val)
def haltPort : Fin 380 := appendLabel RowAppend.haltPort

def machine : Machine 379 := fun label symbol =>
  if inside : label.val < 15 then
    let q : Fin 15 := ⟨label.val,inside⟩
    match MarkSeek.machine q symbol with
    | none => some (appendLabel (RowAppend.entry (saved q)),.write symbol)
    | some (next,op) => some (markLabel next,op)
  else
    let q : Fin 365 := ⟨label.val-15,by omega⟩
    match RowAppend.machine q symbol with
    | none => none
    | some (next,op) => some (appendLabel next,op)

def markCfg (cfg : MachineState 14) : MachineState 379 := ⟨markLabel cfg.q,cfg.Tape⟩
def appendCfg (cfg : MachineState 364) : MachineState 379 := ⟨appendLabel cfg.q,cfg.Tape⟩

theorem mark_lookup (q : Fin 15) (symbol : Bool) :
    machine (markLabel q) symbol =
      match MarkSeek.machine q symbol with
      | none => some (appendLabel (RowAppend.entry (saved q)),.write symbol)
      | some (next,op) => some (markLabel next,op) := by
  simp only [machine,markLabel,q.isLt,↓reduceDIte,Fin.eta]

theorem append_lookup (q : Fin 365) (symbol : Bool) :
    machine (appendLabel q) symbol =
      match RowAppend.machine q symbol with
      | none => none
      | some (next,op) => some (appendLabel next,op) := by
  have outside : ¬15+q.val < 15 := by omega
  simp only [machine,appendLabel,outside,↓reduceDIte,Nat.add_sub_cancel_left,Fin.eta]

theorem mark_step (cfg : MachineState 14) :
    TM0.step machine (markCfg cfg) =
      match TM0.step MarkSeek.machine cfg with
      | none => some (appendCfg ⟨RowAppend.entry (saved cfg.q),cfg.Tape⟩)
      | some next => some (markCfg next) := by
  cases cfg with
  | mk q tape =>
    simp only [TM0.step,markCfg]
    rw [mark_lookup]
    cases action : MarkSeek.machine q tape.head with
    | none => simp only [Option.map_none,Option.map_some,appendCfg,Tape.write_self]
    | some pair => obtain ⟨next,op⟩ := pair; cases op <;> rfl

theorem append_step (cfg : MachineState 364) :
    TM0.step machine (appendCfg cfg) = (TM0.step RowAppend.machine cfg).map appendCfg := by
  cases cfg with
  | mk q tape =>
    simp only [TM0.step,appendCfg]
    rw [append_lookup]
    cases action : RowAppend.machine q tape.head with
    | none => rfl
    | some pair => obtain ⟨next,op⟩ := pair; cases op <;> rfl

def sourceLeft (left higher : List Bool) (bit : Bool) (gap : Nat) : List Bool :=
  List.replicate gap false ++ false :: true :: MarkSeek.selectedLeft left higher bit

def initial (left higher : List Bool) (bit : Bool) (gap : Nat) (bits : List Bool) : MachineState 379 :=
  ⟨0,Tape.mk₂ (false :: left)
    (bit :: (MarkSeek.pairs higher ++ true :: false :: (List.replicate gap false ++ RowEnd.rows bits)))⟩

def final (left higher : List Bool) (bit : Bool) (gap : Nat) (bits : List Bool) : MachineState 379 :=
  ⟨haltPort,Tape.mk₂ ((RowEnd.rows (bits ++ [bit])).reverse ++ sourceLeft left higher bit gap) []⟩

theorem actual (left higher : List Bool) (bit : Bool) (gap : Nat) (bits : List Bool) (inputLength : Nat) :
    ∃ path, RunsFrom machine (initial left higher bit gap bits) path (final left higher bit gap bits) ∧
      path.length = 2*higher.length+gap+33*(bits.length+1)+77 ∧
      ∀ clock, visitedSpace machine inputLength (path.take clock) ≤
        inputLength+4*higher.length+2*gap+66*(bits.length+1)+155 := by
  let rowTail := (RowEnd.rows bits).tail
  have rowHead : true :: rowTail = RowEnd.rows bits := by rfl
  obtain ⟨markTrace,markRun,markTime,_markSpace⟩ := MarkSeek.actual left higher bit gap rowTail inputLength
  obtain ⟨appendTrace,appendRun,appendTime,_appendSpace⟩ :=
    RowAppend.actual bit (sourceLeft left higher bit gap) bits inputLength
  have appendStart : appendTrace.head? = some
      ⟨RowAppend.entry bit,(MarkSeek.finish left higher bit gap rowTail).Tape⟩ := by
    rw [appendRun.1]
    change some (⟨RowAppend.entry bit,Tape.mk₂ (sourceLeft left higher bit gap) (RowEnd.rows bits)⟩ : MachineState 364) = _
    simp only [MarkSeek.finish,MarkSeek.state,sourceLeft,rowHead]
  let path := markTrace.map markCfg ++ appendTrace.map appendCfg
  have chain : path.IsChain (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append
    · apply (List.isChain_map _).mpr
      exact markRun.2.1.imp (fun before after edge => by simp only [mark_step,edge])
    · apply (List.isChain_map _).mpr
      exact appendRun.2.1.imp (fun before after edge => by simp only [append_step,edge,Option.map_some])
    · intro before beforeLast after afterHead
      simp only [List.getLast?_map,markRun.2.2.1,Option.map_some,Option.mem_some_iff] at beforeLast
      simp only [List.head?_map,appendStart,Option.map_some,Option.mem_some_iff] at afterHead
      subst before
      subst after
      simp only [mark_step,markRun.2.2.2]
      cases bit <;> rfl
  have length : path.length = 2*higher.length+gap+33*(bits.length+1)+77 := by
    simp only [path,List.length_append,List.length_map,markTime,appendTime]
    omega
  refine ⟨path,⟨?_,chain,?_,?_⟩,length,?_⟩
  · simp only [path,List.head?_append,List.head?_map,markRun.1,Option.map_some,Option.some_or]
    simp only [markCfg,MarkSeek.initial,initial,markLabel,rowHead]
    rfl
  · simp only [path,List.getLast?_append,List.getLast?_map,appendRun.2.2.1,Option.map_some,Option.some_or]
    rfl
  · change TM0.step machine (appendCfg
      ⟨RowAppend.haltPort,Tape.mk₂ ((RowEnd.rows (bits ++ [bit])).reverse ++ sourceLeft left higher bit gap) []⟩) = none
    simp only [append_step,appendRun.2.2.2,Option.map_none]
  · intro clock
    have space := PSTRTMTrace002.visitedSpace_le machine inputLength (path.take clock)
    have short := List.length_take_le' clock path
    omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.MarkAppend

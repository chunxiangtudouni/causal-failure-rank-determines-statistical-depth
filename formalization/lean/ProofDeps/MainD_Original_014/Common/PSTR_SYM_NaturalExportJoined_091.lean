module

public import Common.PSTR_SYM_NaturalExportFinite_090
public import Common.PSTR_WordVM_LabelMap_029
public import Common.PSTR_WordBool_StoreIso_048
public import Common.PSTR_WordBool_NativeTrace_006

/-! One fixed six-label actual TM2 source:020 parser at0,086 exporter
at1..5. The parser's real gotoReturn1 enters the exporter. Product-store
exchange and label maps are fixed compilation, with all stacks unchanged. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport.Joined

open Turing PaperProofs.Common.Native.PSTRWordVM PaperProofs.Common.Native.PSTRWordBool

abbrev GlobalLabel := Fin 6
abbrev GlobalMemory (C : Type*) := (C × PSTRSymbolicDualStack.Store) × Store
abbrev GlobalState (C : Type*) := TM2.Cfg Alphabet GlobalLabel (GlobalMemory C)
abbrev ParserState (C : Type*) := TM2.Cfg Alphabet (Fin 2) (GlobalMemory C)

def oldLabel (label : Fin 2) : GlobalLabel := ⟨label.val,by omega⟩

def exportLabel (label : Label) : GlobalLabel := label.succ

def exportIndex (label : GlobalLabel) : Label := ⟨(label.val+4)%5,Nat.mod_lt _ (by decide)⟩

def exchange (C : Type*) : ((C × Store) × PSTRSymbolicDualStack.Store) ≃ GlobalMemory C :=
  StoreIso.exchange C Store PSTRSymbolicDualStack.Store

noncomputable def parserProgram {C : Type*} : Fin 2 → TM2.Stmt Alphabet (Fin 2) (GlobalMemory C) :=
  StoreIso.machine (exchange C) (PSTRSymbolicDualStack.program .halt)

noncomputable def combinedProgram {C : Type*} (label : GlobalLabel) : TM2.Stmt Alphabet GlobalLabel (GlobalMemory C) :=
  if label = 0 then LabelMap.statement oldLabel (parserProgram 0)
  else LabelMap.statement exportLabel (program (exportIndex label))

theorem old_zero : oldLabel 0 = 0 := rfl

theorem old_one : oldLabel 1 = 1 := rfl

theorem export_zero : exportLabel 0 = 1 := rfl

theorem combined_parser {C : Type*} :
    combinedProgram (C := C) 0 = LabelMap.statement oldLabel (parserProgram 0) := rfl

theorem combined_export {C : Type*} (label : Label) :
    combinedProgram (C := C) (exportLabel label) = LabelMap.statement exportLabel (program label) := by
  fin_cases label <;> rfl

theorem parser_halt {C : Type*} : parserProgram (C := C) 1 = .halt := rfl

theorem parser_stopped_step {C : Type*} (before : ParserState C) (stopped : before.l = none) :
    TM2.step parserProgram before = none := by
  cases before with
  | mk position memory bank =>
    change position = none at stopped
    subst position
    rfl

theorem parser_active_step {C : Type*} (before : ParserState C) (point : Fin 2)
    (active : before.l = some point) :
    TM2.step parserProgram before = some (TM2.stepAux (parserProgram point) before.var before.stk) := by
  cases before with
  | mk position memory bank =>
    change position = some point at active
    subst position
    rfl

theorem parser_path_active {C : Type*} (path : List (ParserState C)) (final : ParserState C)
    (chain : path.IsChain (fun before after => TM2.step parserProgram before = some after))
    (last : path.getLast? = some final) (active : final.l = some 1) :
    ∀ current ∈ path, current.l ≠ none := by
  induction path with
  | nil => intro current present; cases present
  | cons first rest ih =>
    cases rest with
    | nil =>
      have same : first = final := Option.some.inj last
      subst first
      intro current present
      have same := List.mem_singleton.mp present
      subst current
      rw [active]
      intro impossible
      cases impossible
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      have tailLast : (next :: rest).getLast? = some final := last
      intro current present
      rcases List.mem_cons.mp present with same | later
      · subst current
        intro stopped
        have noStep : TM2.step parserProgram first = none := parser_stopped_step first stopped
        rw [noStep] at edge
        cases edge
      · exact ih tailChain tailLast current later

theorem parser_proper {C : Type*} (path : List (ParserState C)) (final : ParserState C)
    (chain : path.IsChain (fun before after => TM2.step parserProgram before = some after))
    (last : path.getLast? = some final) (active : final.l = some 1) :
    ∀ current ∈ path.dropLast, current.l = some 0 := by
  induction path with
  | nil => intro current present; cases present
  | cons first rest ih =>
    cases rest with
    | nil => intro current present; cases present
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      have tailLast : (next :: rest).getLast? = some final := last
      rw [List.dropLast_cons_cons]
      intro current present
      rcases List.mem_cons.mp present with same | later
      · subst current
        have nextActive := parser_path_active (next :: rest) final tailChain tailLast active next (List.mem_cons_self)
        cases position : first.l with
        | none =>
          rw [parser_stopped_step first position] at edge
          cases edge
        | some point =>
          fin_cases point
          · rfl
          · have nextStopped : next.l = none := by
              have actual := parser_active_step first 1 position
              rw [parser_halt] at actual
              have equal := Option.some.inj (actual.symm.trans edge)
              exact (congrArg TM2.Cfg.l equal).symm
            exact False.elim (nextActive nextStopped)
      · exact ih tailChain tailLast current later

theorem parser_lift {C : Type*} (path : List (ParserState C)) (final : ParserState C)
    (chain : path.IsChain (fun before after => TM2.step parserProgram before = some after))
    (last : path.getLast? = some final) (active : final.l = some 1) :
    (path.map (LabelMap.configuration oldLabel)).IsChain
      (fun before after => TM2.step (combinedProgram (C := C)) before = some after) := by
  apply LabelMap.chain_configuration_on oldLabel parserProgram combinedProgram path chain
  intro current present point position
  have zero := parser_proper path final chain last active current present
  have same : point = 0 := Option.some.inj (position.symm.trans zero)
  subst point
  exact combined_parser

theorem getter_lift {C : Type*} (path : List (State (C × PSTRSymbolicDualStack.Store)))
    (chain : path.IsChain (fun before after => TM2.step program before = some after)) :
    (path.map (LabelMap.configuration exportLabel)).IsChain
      (fun before after => TM2.step (combinedProgram (C := C)) before = some after) := by
  apply LabelMap.chain_configuration_on exportLabel program combinedProgram path chain
  intro _current _present point _position
  exact combined_export point

theorem combined_pushes {C : Type*} (label : GlobalLabel) :
    AuxWorkspace.pushes (combinedProgram (C := C) label) ≤ 7 := by
  by_cases zero : label = 0
  · subst label
    rw [combined_parser,LabelMap.statement_pushes]
    change AuxWorkspace.pushes (StoreIso.statement (exchange C) (PSTRSymbolicDualStack.program .halt 0)) ≤ 7
    rw [StoreIso.statement_pushes,PSTRSymbolicDualStack.body_at_entry]
    exact (show AuxWorkspace.pushes (VirtualReturn.statement (C := C × Store)
      (PSTRSymbolicDualStack.source ())) = 2 from
        PaperProofs.Common.Native.PSTRWordVM.VirtualBool.pushes PSTRSymbolicDualStream.dualMachine).le.trans (by decide)
  · rw [combinedProgram,ite_eq_right zero,LabelMap.statement_pushes]
    exact source_pushes _

theorem combined_actions {C : Type*} (label : GlobalLabel) :
    ScannerClock.actions (combinedProgram (C := C) label) ≤ 9 := by
  by_cases zero : label = 0
  · subst label
    rw [combined_parser,LabelMap.statement_actions]
    change ScannerClock.actions (StoreIso.statement (exchange C) (PSTRSymbolicDualStack.program .halt 0)) ≤ 9
    rw [StoreIso.statement_actions,PSTRSymbolicDualStack.body_at_entry]
    exact (show ScannerClock.actions (VirtualReturn.statement (C := C × Store)
      (PSTRSymbolicDualStack.source ())) = 4 from
        PaperProofs.Common.Native.PSTRWordVM.VirtualBool.actions PSTRSymbolicDualStream.dualMachine).le.trans (by decide)
  · rw [combinedProgram,ite_eq_right zero,LabelMap.statement_actions]
    exact source_actions _

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport.Joined

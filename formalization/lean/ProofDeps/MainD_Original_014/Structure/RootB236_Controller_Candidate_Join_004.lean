module
public import Structure.RootB236_Controller_Candidate_Resources_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
@[expose] public section
namespace RootB236.ControllerCandidate
open Turing
open PaperProofs.Common.Native
open PSTRWordBool PSTRWordVM
abbrev Label := Sum Bitwise.Label ScanLabel
abbrev Statement := TM2.Stmt Alphabet Label Store
abbrev State := TM2.Cfg Alphabet Label Store
def andLabels (label : Bitwise.Label) : Label := if label=3 then .inr .clear else .inl label
def scanLabels : ScanLabel → Label := Sum.inr
def andEmbed : Bitwise.State → State := LabelMap.configuration andLabels
def scanEmbed : ScanState → State := LabelMap.configuration scanLabels

/-- Fixed code. The AND return3 is statically identified with clear, not HALTed. -/
def program (found empty : Statement) : Label → Statement
  | .inl label => LabelMap.statement andLabels (Bitwise.program false .halt label)
  | .inr .found => found
  | .inr .empty => empty
  | .inr label => LabelMap.statement scanLabels (scanner label)
def source : Label → Statement := program .halt .halt
def scanBackground (bg : Stack → List Bool) (q : Nat) : Stack → List Bool :=
  Bitwise.cells bg [] [] [] (unary q) []
def Owned (point : Stack) : Prop :=
  point=3 ∨ point=4 ∨ point=5 ∨ point=6 ∨ point=7 ∨ point=11 ∨ point=12

theorem supports_statement (body : Statement) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ iy ino => exact ⟨iy,ino⟩
  | goto target => intro memory; exact Finset.mem_univ (target memory)
  | halt => trivial
theorem supports (found empty : Statement) :
    TM2.Supports (program found empty) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun label _ => supports_statement (program found empty label)⟩

theorem and_agrees (label : Bitwise.Label) (proper : label≠3) :
    source (andLabels label)=LabelMap.statement andLabels (Bitwise.program false .halt label) := by
  simp only [andLabels,proper,ite_false,source,program]
theorem scan_agrees (found empty : Statement) (label : ScanLabel) (proper : Proper label) :
    program found empty (scanLabels label)=LabelMap.statement scanLabels (scanner label) := by
  cases label <;> simp_all [Proper,scanLabels,program]

theorem active_path {Λ σ : Type*} (machine : Λ → TM2.Stmt Alphabet Λ σ)
    (trace : List (TM2.Cfg Alphabet Λ σ)) (final : TM2.Cfg Alphabet Λ σ)
    (chain : trace.IsChain (fun a b => TM2.step machine a=some b))
    (last : trace.getLast?=some final) (active : final.l≠none) :
    ∀ current∈trace, current.l≠none := by
  induction trace with
  | nil => simp
  | cons head tail ih =>
    cases tail with
    | nil =>
      have same : head=final := Option.some.inj last
      subst head
      simpa only [List.mem_singleton] using fun current (same : current=final) => same ▸ active
    | cons next tail =>
      obtain ⟨edge,rest⟩:=List.isChain_cons_cons.mp chain
      have later:=ih rest last
      intro current member
      rcases List.mem_cons.mp member with same | member
      · subst current
        intro stopped
        cases head with
        | mk location memory slots =>
          change location=none at stopped
          subst location
          cases edge
      · exact later current member

theorem no_early_halt_port {Λ σ : Type*} (machine : Λ → TM2.Stmt Alphabet Λ σ)
    (port : Λ) (code : machine port=.halt) (trace : List (TM2.Cfg Alphabet Λ σ))
    (final : TM2.Cfg Alphabet Λ σ)
    (chain : trace.IsChain (fun a b => TM2.step machine a=some b))
    (last : trace.getLast?=some final) (active : final.l≠none) :
    ∀ current∈trace.dropLast, current.l≠some port := by
  induction trace with
  | nil => simp
  | cons head tail ih =>
    cases tail with
    | nil => simp
    | cons next tail =>
      obtain ⟨edge,rest⟩:=List.isChain_cons_cons.mp chain
      have later:=ih rest last
      intro current member
      rw [List.dropLast_cons_cons] at member
      rcases List.mem_cons.mp member with same | member
      · subst current
        intro entered
        cases head with
        | mk location memory slots =>
          change location=some port at entered
          subst location
          have endpoint : TM2.stepAux (machine port) memory slots=next := Option.some.inj edge
          have stopped : next.l=none := by rw [←endpoint,code];rfl
          exact active_path machine (next::tail) final rest last active next List.mem_cons_self stopped
      · exact later current member

theorem source_counts (label : Label) :
    ScannerClock.actions (source label)≤5 ∧ AuxWorkspace.pushes (source label)≤2 := by
  cases label with
  | inl label =>
    by_cases last : label=3
    · subst label; norm_num [source,program,Bitwise.program,LabelMap.statement,ScannerClock.actions,AuxWorkspace.pushes]
    · simpa only [source,program,LabelMap.statement_actions,LabelMap.statement_pushes] using
        And.intro (Bitwise.program_actions false .halt label last) (Bitwise.program_pushes false .halt label last)
  | inr label =>
    cases label <;> norm_num [source,program,scanner,LabelMap.statement,ScannerClock.actions,AuxWorkspace.pushes]

theorem scan_background_bound (bg : Stack → List Bool) (q : Nat) (point : Stack) :
    (scanBackground bg q point).length≤mass bg+q := by
  have original : (bg point).length≤mass bg := Bitwise.background_point_le bg point
  simp only [scanBackground,Bitwise.cells]
  split_ifs <;> first | omega | (simp only [List.length_nil,unary,List.length_replicate];omega)

theorem and_scan_boundary (bg : Stack → List Bool) (pairs : List (Bool×Bool))
    (cursor : bg 6=[]) :
    andEmbed (Bitwise.state bg 3 (false,false) (Bitwise.outputs false pairs) [] [] (unary pairs.length) [])=
      scanEmbed (state (scanBackground bg pairs.length) .clear (false,false)
        (Bitwise.outputs false pairs) (bg 5) (unary 0) []) := by
  change (⟨some (.inr .clear),(false,false),_⟩ : State)=_
  congr 1
  funext point
  fin_cases point <;> simp [state,cells,scanBackground,Bitwise.state,Bitwise.cells,unary,cursor]

/-- One fixed actual source: first AND has cursor0; continuation is a separate API. -/
theorem actual_first (bg : Stack → List Bool) (mem : Store) (pairs : List (Bool×Bool))
    (cursor : bg 6=[]) :
    ∃ (trace : List State) (final : State),
      trace.head?=some (andEmbed (Bitwise.state bg 0 mem (pairs.map Prod.fst) (pairs.map Prod.snd)
        [] (unary pairs.length) [])) ∧
      trace.IsChain (fun a b => TM2.step source a=some b) ∧ trace.getLast?=some final ∧
      trace.length≤12*((bg 5).length+pairs.length+1) ∧
      (∃ scanFinal, Outcome (scanBackground bg pairs.length) (Bitwise.outputs false pairs) 0 scanFinal ∧
        final=scanEmbed scanFinal) ∧
      ∀ current∈trace, ∀ point, (current.stk point).length≤2*mass bg+3*pairs.length+2 := by
  let old:=Bitwise.actualTrace false bg mem pairs
  have oldRun:=Bitwise.actual_run false .halt bg mem pairs
  have noPort:=no_early_halt_port (Bitwise.program false .halt) 3 (by norm_num [Bitwise.program])
    old _ oldRun.2.1 oldRun.2.2.1 (by simp [Bitwise.state])
  have mapped:=LabelMap.actual_path_on andLabels (Bitwise.program false .halt) source old _ _
    oldRun.1 oldRun.2.1 oldRun.2.2.1 (fun current member label atLabel =>
      and_agrees label (fun eqn => noPort current member (eqn ▸ atLabel)))
  let first:=old.map andEmbed
  have firstHead : first.head?=some (andEmbed (Bitwise.state bg 0 mem
      (pairs.map Prod.fst) (pairs.map Prod.snd) [] (unary pairs.length) [])) := mapped.1
  have firstChain:=mapped.2.1
  have firstLast:=mapped.2.2.1
  have firstLength : first.length=old.length := mapped.2.2.2.1
  let nextBg:=scanBackground bg pairs.length
  let bits:=Bitwise.outputs false pairs
  have bitsLength : bits.length=pairs.length := by simp [bits,Bitwise.outputs]
  obtain ⟨scanTrace,scanFinal,head,chain,last,time,outcome,bounds,interior,_charge⟩:=
    actual_resume_trace nextBg (false,false) bits (bg 5) 0
  have mappedScan:=LabelMap.actual_path_on scanLabels scanner source scanTrace _ _ head chain last
    (fun current member label atLabel => scan_agrees .halt .halt label
      (by obtain ⟨actualLabel,equal,proper⟩:=interior current member
          have same : label=actualLabel := Option.some.inj (atLabel.symm.trans equal)
          exact same ▸ proper))
  let later:=scanTrace.map scanEmbed
  have boundary:=and_scan_boundary bg pairs cursor
  have laterHead : later.head?=some (andEmbed (Bitwise.state bg 3 (false,false) bits [] [] (unary pairs.length) [])) := by
    rw [boundary]
    exact mappedScan.1
  obtain ⟨laterTail,laterEq⟩:=List.head?_eq_some_iff.mp laterHead
  have laterChain : (andEmbed (Bitwise.state bg 3 (false,false) bits [] [] (unary pairs.length) [])::laterTail).IsChain
      (fun a b => TM2.step source a=some b) := laterEq ▸ mappedScan.2.1
  refine ⟨first++laterTail,scanEmbed scanFinal,?_,?_,?_,?_,⟨scanFinal,outcome,rfl⟩,?_⟩
  · rw [List.head?_append,firstHead];rfl
  · exact NativeTrace.join_chain first _ laterTail firstLast firstChain laterChain
  · exact (NativeTrace.join_last first _ laterTail firstLast).trans (laterEq ▸ mappedScan.2.2.1)
  · have tailLength : laterTail.length+1=scanTrace.length := by
      have same:=congrArg List.length laterEq
      have mappedLength : later.length=scanTrace.length := mappedScan.2.2.2.1
      simp only [List.length_cons] at same
      omega
    have beforeLength : first.length=3*pairs.length+4 := firstLength.trans oldRun.2.2.2
    simp only [List.length_append]
    omega
  · intro current member point
    rcases List.mem_append.mp member with before | after
    · obtain ⟨original,inOld,same⟩:=List.mem_map.mp before
      subst current
      have bound:=Bitwise.work_stack_bound bg _ original (Bitwise.actual_bound false bg mem pairs original inOld) point
      change (original.stk point).length≤_
      have oldSize : (bg point).length≤mass bg := Bitwise.background_point_le bg point
      omega
    · have memberLater : current∈later := by rw [laterEq];exact List.mem_cons_of_mem _ after
      obtain ⟨original,inScan,same⟩:=List.mem_map.mp memberLater
      subst current
      have bound:=(bounds original inScan).1 point
      have bgBound:=scan_background_bound bg pairs.length point
      have oldResult : (bg 5).length≤mass bg := Bitwise.background_point_le bg 5
      change (original.stk point).length≤_
      dsimp [nextBg] at bound
      omega
end RootB236.ControllerCandidate

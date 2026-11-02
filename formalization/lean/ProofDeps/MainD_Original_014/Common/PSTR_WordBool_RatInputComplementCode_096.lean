module

public import Common.PSTR_WordBool_RatInputOriginalRun_095

/-! Fixed whole original-front/encoder/RawSub/output program. The encoder's
last active port is exactly the already-frozen native callee's reset entry. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput.Complement

open Turing PSTRWordVM RationalControllerComputation
open PA17TMRatArithmeticAddSubController075 PA17TMRatArithmeticAddSubFull079

abbrev CalleeFlags := BoolOnStacks.Store controllerCap
abbrev Reader := RatOutput.Store
abbrev Store (C : Type*) := RatOutput.Link.Store (Original.Store C) controllerCap

inductive Label where
  | front : Original.Label→Label
  | native : RatOutput.Link.Label→Label
  | done : Label
  deriving DecidableEq,Fintype

instance : Inhabited Label:=⟨.front (.prior 0)⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def storeMap (C : Type*) : Original.Store ((C×CalleeFlags)×Reader)≃Store C where
  toFun v:=(((((v.1.1.1.1.1,v.1.1.2),v.1.2),v.2),v.1.1.1.1.2),v.1.1.1.2)
  invFun v:=(((((v.1.1.1.1.1,v.1.2),v.2),v.1.1.1.1.2),v.1.1.1.2),v.1.1.2)
  left_inv _:=rfl
  right_inv _:=rfl

def frontLabel (point : Original.Label) : Label := if point=.done then .native 1 else .front point
def nativeLabel (point : RatOutput.Link.Label) : Label := if point=10 then .done else .native point

noncomputable def program (caller : Statement C) : Label→Statement C
  | .front point=>LabelMap.statement frontLabel (StoreIso.statement (storeMap C)
      (Original.program (C:=(C×CalleeFlags)×Reader) .halt point))
  | .native point=>LabelMap.statement nativeLabel (RatOutput.Link.program subMachine .halt point)
  | .done=>caller

def frontConfiguration (before : Original.State ((C×CalleeFlags)×Reader)) : State C :=
  LabelMap.configuration frontLabel (StoreIso.configuration (storeMap C) before)

def nativeConfiguration (before : RatOutput.Link.State (Original.Store C) controllerCap) : State C :=
  LabelMap.configuration nativeLabel before

def initial (context : C) (native : CalleeFlags) (reader : Reader) (bits : List Bool) : State C :=
  frontConfiguration (Original.initial ((context,native),reader) bits)

theorem program_front (caller : Statement C) (point : Original.Label) (proper : point≠.done) :
    program caller (frontLabel point)=LabelMap.statement frontLabel (StoreIso.statement (storeMap C)
      (Original.program (C:=(C×CalleeFlags)×Reader) .halt point)) := by
  simp only [frontLabel,proper,ite_false,program]

theorem front_path (caller : Statement C) (trace : List (Original.State ((C×CalleeFlags)×Reader)))
    (before final : Original.State ((C×CalleeFlags)×Reader))
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (Original.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some .done) :
    (trace.map frontConfiguration).head?=some (frontConfiguration before) ∧
    (trace.map frontConfiguration).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (trace.map frontConfiguration).getLast?=some (frontConfiguration final) := by
  let old:=Original.program (C:=(C×CalleeFlags)×Reader) .halt
  let isoProgram:=StoreIso.machine (storeMap C) old
  have iso:=StoreIso.actual_path_on (storeMap C) old isoProgram trace before final first chain last
    (by intro current member point selected;rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram .done rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on frontLabel isoProgram (program caller) _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
    intro current member point selected
    exact program_front caller point (by intro same;subst point;exact proper current member selected))
  have maps : (trace.map (StoreIso.configuration (storeMap C))).map (LabelMap.configuration frontLabel)=
      trace.map frontConfiguration := by rw [List.map_map];rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem program_native (caller : Statement C) (point : RatOutput.Link.Label) (proper : point≠10) :
    program caller (nativeLabel point)=LabelMap.statement nativeLabel (RatOutput.Link.program subMachine .halt point) := by
  simp only [nativeLabel,proper,ite_false,program]

theorem native_path (caller : Statement C) (trace : List (RatOutput.Link.State (Original.Store C) controllerCap))
    (before final : RatOutput.Link.State (Original.Store C) controllerCap)
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (RatOutput.Link.program subMachine .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some 10) :
    (trace.map nativeConfiguration).head?=some (nativeConfiguration before) ∧
    (trace.map nativeConfiguration).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (trace.map nativeConfiguration).getLast?=some (nativeConfiguration final) := by
  have proper:=NativeMulLink.no_early_halt_port (RatOutput.Link.program subMachine .halt) 10 rfl trace final chain last active
  have mapped:=LabelMap.actual_path_on nativeLabel (RatOutput.Link.program subMachine .halt) (program caller)
    trace before final first chain last (by
      intro current member point selected
      exact program_native caller point (by intro same;subst point;exact proper current member selected))
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem program_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point)≤15 := by
  cases point with
  | front point =>
    rw [program,LabelMap.statement_actions,StoreIso.statement_actions]
    exact Original.program_actions point
  | native point =>
    rw [program,LabelMap.statement_actions]
    by_cases done : point=10
    · subst point;exact Nat.zero_le _
    · exact (RatOutput.Link.program_actions subMachine .halt point done).trans (by decide)
  | done => exact Nat.zero_le _

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point)≤15 := by
  cases point with
  | front point =>
    rw [program,LabelMap.statement_pushes,StoreIso.statement_pushes]
    exact Original.program_pushes point
  | native point =>
    rw [program,LabelMap.statement_pushes]
    by_cases done : point=10
    · subst point;exact Nat.zero_le _
    · exact (RatOutput.Link.program_pushes subMachine .halt point done).trans (by decide)
  | done => exact Nat.zero_le _

end PaperProofs.Common.Native.PSTRWordBool.RatInput.Complement


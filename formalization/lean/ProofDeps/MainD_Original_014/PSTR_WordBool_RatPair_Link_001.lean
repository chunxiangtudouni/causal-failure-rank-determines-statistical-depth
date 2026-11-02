module

public import PSTR_WordBool_RatPair_Resources_001
public import PSTR_WordBool_RatPair_Serialize_Run_002

/-! One fixed whole double-packet encoder. Collector's active return is
exactly the serializer's paid boot; caller continuation executes last. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Link

open Turing PSTRWordVM RationalControllerComputation

inductive Label where
  | collect : Collector.Label → Label
  | serialize : Serializer.Label → Label
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.collect 0⟩

abbrev Stack := RatInput.Stack
abbrev Store (C : Type*) := Collector.Store C
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def collectLabel (point : Collector.Label) : Label :=
  if point=7 then .serialize (.boot false) else .collect point

def serializeLabel (point : Serializer.Label) : Label := .serialize point

def done : Label := .serialize .done

def program (caller : Statement C) : Label → Statement C
  | .collect point => LabelMap.statement collectLabel (Collector.program (C:=C) .halt point)
  | .serialize point => if point=.done then caller else
      LabelMap.statement serializeLabel (Serializer.program2 (C:=C) .halt point)

def collectConfiguration (before : Collector.State C) : State C :=
  LabelMap.configuration collectLabel before
def serializeConfiguration (before : Serializer.State C) : State C :=
  LabelMap.configuration serializeLabel before

theorem program_collect (caller : Statement C) (point : Collector.Label) (proper : point≠7) :
    program caller (collectLabel point)=LabelMap.statement collectLabel (Collector.program .halt point) := by
  simp only [collectLabel,proper,ite_false,program]

theorem program_serialize (caller : Statement C) (point : Serializer.Label) (proper : point≠.done) :
    program caller (serializeLabel point)=LabelMap.statement serializeLabel (Serializer.program2 .halt point) := by
  simp only [serializeLabel,program,proper,ite_false]

theorem collect_path (caller : Statement C) (trace : List (Collector.State C))
    (before final : Collector.State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (Collector.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some 7) :
    (trace.map collectConfiguration).head?=some (collectConfiguration before) ∧
    (trace.map collectConfiguration).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (trace.map collectConfiguration).getLast?=some (collectConfiguration final) := by
  have proper:=NativeMulLink.no_early_halt_port (Collector.program .halt) 7 rfl trace final chain last active
  have mapped:=LabelMap.actual_path_on collectLabel (Collector.program .halt) (program caller) trace before final
    first chain last (by
      intro current member point selected
      exact program_collect caller point (by intro same;subst point;exact proper current member selected))
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem serialize_path (caller : Statement C) (trace : List (Serializer.State C))
    (before final : Serializer.State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (Serializer.program2 .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some .done) :
    (trace.map serializeConfiguration).head?=some (serializeConfiguration before) ∧
    (trace.map serializeConfiguration).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (trace.map serializeConfiguration).getLast?=some (serializeConfiguration final) := by
  have proper:=NativeMulLink.no_early_halt_port (Serializer.program2 .halt) .done rfl trace final chain last active
  have mapped:=LabelMap.actual_path_on serializeLabel (Serializer.program2 .halt) (program caller) trace before final
    first chain last (by
      intro current member point selected
      exact program_serialize caller point (by intro same;subst point;exact proper current member selected))
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

def clean (background : Stack → List Bool) : Stack → List Bool :=
  Serializer.bank background [] [] [] [] [] [] [] [] []

def initial (background : Stack → List Bool) (source scratch : List Bool) : Stack → List Bool :=
  Collector.bank (clean background) source scratch [] [] [] []

def entry (background : Stack → List Bool) (context : C) (oldX oldY : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (sx sy : Bool)
    (xn xd yn yd tail scratch : List Bool) : State C :=
  collectConfiguration (Collector.state (clean background) 0 context oldX oldY memory formatter
    (Collector.packets sx sy xn xd yn yd tail) scratch [] [] [] [])

def finalContents (background : Stack → List Bool) (source scratch output : List Bool) : Stack → List Bool :=
  Serializer.bank (initial background source scratch) [] [] [] [] [] [] output [] []

theorem shared_configuration (background : Stack → List Bool) (context : C) (sx sy : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (source scratch xn xd yn yd : List Bool) :
    collectConfiguration (Collector.state (clean background) 7 context sx sy memory formatter
      source scratch xn.reverse xd.reverse yn.reverse yd.reverse)=
      serializeConfiguration (Serializer.entry (initial background source scratch) context sx sy
        memory formatter xn xd yn yd) := by
  change (⟨some (.serialize (.boot false)),(((context,sx,sy),memory),formatter),_⟩:State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Link

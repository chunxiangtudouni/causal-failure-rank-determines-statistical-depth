module

public import Common.PSTR_WordBool_ContextLift_041
public meta import Lean.Elab.Tactic.Omega

/-! Actual two-work-stack Unit-label callee embedding for the parent's
NativeMul/BoolOnStacks consumer. The ENTIRE old terminal statement step,
including its final push of the current head bit, executes. Only its HALT
leaf becomes a real gotoReturn and None-end becomes ACTIVE return1.
All code/types are chosen before data; native clock uses NEW syntax. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.VirtualReturn

open Turing

abbrev SmallStack := PSTRWordBool.PushPop.Stack
abbrev SmallAlphabet := PSTRWordBool.PushPop.Alphabet
abbrev Stack := Fin 16
abbrev Label := Fin 2
abbrev Alphabet (_ : Stack) := Bool
abbrev SmallStatement (σ : Type*) := TM2.Stmt SmallAlphabet Unit σ
abbrev SmallState (σ : Type*) := TM2.Cfg SmallAlphabet Unit σ
abbrev Statement (C σ : Type*) := TM2.Stmt Alphabet Label (C × σ)
abbrev State (C σ : Type*) := TM2.Cfg Alphabet Label (C × σ)

variable {C σ : Type*}

def role (point : SmallStack) : Stack := ⟨point.val, by omega⟩

def slots (background : Stack → List Bool) (small : SmallStack → List Bool) : Stack → List Bool :=
  fun point => if point = 0 then small 0 else if point = 1 then small 1 else background point

theorem slots_role (background : Stack → List Bool) (small : SmallStack → List Bool) (point : SmallStack) :
    slots background small (role point) = small point := by
  fin_cases point <;> rfl

theorem slots_frame (background : Stack → List Bool) (small : SmallStack → List Bool) (point : Stack)
    (notR : point ≠ 0) (notL : point ≠ 1) : slots background small point = background point := by
  simp only [slots, notR, notL, ite_false]

theorem slots_update (background : Stack → List Bool) (small : SmallStack → List Bool)
    (point : SmallStack) (value : List Bool) :
    Function.update (slots background small) (role point) value =
      slots background (Function.update small point value) := by
  fin_cases point <;> funext current <;> fin_cases current <;> rfl

/-- This is ACTUAL syntax: terminal HALT is replaced by a charged goto1.
The source Unit goto always returns to the actual entry0. -/
def core : SmallStatement σ → TM2.Stmt Alphabet Label σ
  | .push point value next => .push (role point) value (core next)
  | .peek point value next => .peek (role point) value (core next)
  | .pop point value next => .pop (role point) value (core next)
  | .load value next => .load value (core next)
  | .branch test yes no => .branch test (core yes) (core no)
  | .goto _ => .goto (fun _ => 0)
  | .halt => .goto (fun _ => 1)

def coreConfiguration (background : Stack → List Bool) (small : SmallState σ) : TM2.Cfg Alphabet Label σ :=
  ⟨some (if small.l.isSome then 0 else 1), small.var, slots background small.stk⟩

def statement (code : SmallStatement σ) : Statement C σ := PSTRWordBool.ContextLift.statement (core code)

def configuration (context : C) (background : Stack → List Bool) (small : SmallState σ) : State C σ :=
  PSTRWordBool.ContextLift.configuration context (coreConfiguration background small)

def program (source : Unit → SmallStatement σ) (caller : Statement C σ) (point : Label) : Statement C σ :=
  if point = 0 then statement (source ()) else caller

theorem core_stepAux (code : SmallStatement σ) (memory : σ) (small : SmallStack → List Bool)
    (background : Stack → List Bool) :
    TM2.stepAux (core code) memory (slots background small) =
      coreConfiguration background (TM2.stepAux code memory small) := by
  induction code generalizing memory small with
  | push point value next ih =>
    simp only [core, TM2.stepAux, slots_role]
    rw [slots_update]
    exact ih _ _
  | peek point value next ih =>
    simp only [core, TM2.stepAux, slots_role]
    exact ih _ _
  | pop point value next ih =>
    simp only [core, TM2.stepAux, slots_role]
    rw [slots_update]
    exact ih _ _
  | load value next ih =>
    simp only [core, TM2.stepAux]
    exact ih _ _
  | branch test yes no ihYes ihNo =>
    cases choice : test memory
    · simpa only [core, TM2.stepAux, choice, Bool.cond_false] using ihNo memory small
    · simpa only [core, TM2.stepAux, choice, Bool.cond_true] using ihYes memory small
  | goto target => rfl
  | halt => rfl

theorem stepAux_configuration (code : SmallStatement σ) (context : C) (memory : σ)
    (small : SmallStack → List Bool) (background : Stack → List Bool) :
    TM2.stepAux (statement code) (context, memory) (slots background small) =
      configuration context background (TM2.stepAux code memory small) := by
  change TM2.stepAux (PSTRWordBool.ContextLift.statement (core code)) (context, memory) (slots background small) =
    PSTRWordBool.ContextLift.configuration context (coreConfiguration background (TM2.stepAux code memory small))
  rw [PSTRWordBool.ContextLift.stepAux_configuration, core_stepAux]

/-- The real source edge supplies the proper-entry fact. If before were
None, TM2.step would be none. No original caller execution oracle is added. -/
theorem step_configuration (source : Unit → SmallStatement σ) (caller : Statement C σ)
    (context : C) (background : Stack → List Bool) (before after : SmallState σ)
    (edge : TM2.step source before = some after) :
    TM2.step (program source caller) (configuration context background before) =
      some (configuration context background after) := by
  rcases before with ⟨position, memory, small⟩
  cases position with
  | none => cases edge
  | some point =>
    cases point
    have same : TM2.stepAux (source ()) memory small = after := Option.some.inj edge
    change some (TM2.stepAux (statement (source ())) (context, memory) (slots background small)) = _
    rw [stepAux_configuration, same]

theorem core_pushes (code : SmallStatement σ) :
    PSTRWordBool.AuxWorkspace.pushes (core code) = PSTRWordBool.AuxWorkspace.pushes code := by
  induction code with
  | push _ _ _ ih => exact congrArg (· + 1) ih
  | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact congrArg₂ max yes no
  | goto _ | halt => rfl

theorem core_actions (code : SmallStatement σ) :
    PSTRWordBool.ScannerClock.actions (core code) = PSTRWordBool.ScannerClock.actions code := by
  induction code with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih => exact congrArg (· + 1) ih
  | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact congrArg₂ max yes no
  | goto _ | halt => rfl

theorem statement_pushes (code : SmallStatement σ) :
    PSTRWordBool.AuxWorkspace.pushes (statement (C := C) code) = PSTRWordBool.AuxWorkspace.pushes code := by
  rw [statement, PSTRWordBool.ContextLift.statement_pushes, core_pushes]

theorem statement_actions (code : SmallStatement σ) :
    PSTRWordBool.ScannerClock.actions (statement (C := C) code) = PSTRWordBool.ScannerClock.actions code := by
  rw [statement, PSTRWordBool.ContextLift.statement_actions, core_actions]

def coreSnapshot (background : Stack → List Bool)
    (small : PSTRWordBool.AuxWorkspace.Snapshot (Γ := SmallAlphabet) (σ := σ)) :
    PSTRWordBool.AuxWorkspace.Snapshot (Γ := Alphabet) (σ := σ) := (small.1, slots background small.2)

def snapshot (context : C) (background : Stack → List Bool)
    (small : PSTRWordBool.AuxWorkspace.Snapshot (Γ := SmallAlphabet) (σ := σ)) :
    PSTRWordBool.AuxWorkspace.Snapshot (Γ := Alphabet) (σ := C × σ) := ((context, small.1), slots background small.2)

theorem core_nodes (code : SmallStatement σ) (memory : σ) (small : SmallStack → List Bool)
    (background : Stack → List Bool) :
    PSTRWordBool.AuxWorkspace.nodes (core code) memory (slots background small) =
      (PSTRWordBool.AuxWorkspace.nodes code memory small).map (coreSnapshot background) := by
  induction code generalizing memory small with
  | push point value next ih =>
    simp only [core, PSTRWordBool.AuxWorkspace.nodes, slots_role, slots_update, List.map_cons, coreSnapshot]
    exact congrArg (List.cons (memory, slots background small)) (ih _ _)
  | peek point value next ih =>
    simp only [core, PSTRWordBool.AuxWorkspace.nodes, slots_role, List.map_cons, coreSnapshot]
    exact congrArg (List.cons (memory, slots background small)) (ih _ _)
  | pop point value next ih =>
    simp only [core, PSTRWordBool.AuxWorkspace.nodes, slots_role, slots_update, List.map_cons, coreSnapshot]
    exact congrArg (List.cons (memory, slots background small)) (ih _ _)
  | load value next ih =>
    simp only [core, PSTRWordBool.AuxWorkspace.nodes, List.map_cons, coreSnapshot]
    exact congrArg (List.cons (memory, slots background small)) (ih _ _)
  | branch test yes no ihYes ihNo =>
    cases choice : test memory
    · simpa only [core, PSTRWordBool.AuxWorkspace.nodes, choice, Bool.false_eq_true, ite_false,
        List.map_cons, coreSnapshot] using congrArg (List.cons (memory, slots background small)) (ihNo memory small)
    · simpa only [core, PSTRWordBool.AuxWorkspace.nodes, choice, ite_true, List.map_cons, coreSnapshot]
        using congrArg (List.cons (memory, slots background small)) (ihYes memory small)
  | goto target => rfl
  | halt => rfl

theorem nodes_configuration (code : SmallStatement σ) (context : C) (memory : σ)
    (small : SmallStack → List Bool) (background : Stack → List Bool) :
    PSTRWordBool.AuxWorkspace.nodes (statement code) (context, memory) (slots background small) =
      (PSTRWordBool.AuxWorkspace.nodes code memory small).map (snapshot context background) := by
  rw [statement, PSTRWordBool.ContextLift.nodes_configuration, core_nodes, List.map_map]
  rfl

theorem path_configuration (source : Unit → SmallStatement σ) (caller : Statement C σ)
    (context : C) (background : Stack → List Bool) (path : List (SmallState σ))
    (first final : SmallState σ) (head : path.head? = some first)
    (chain : path.IsChain (fun before after => TM2.step source before = some after))
    (last : path.getLast? = some final) :
    (path.map (configuration context background)).head? = some (configuration context background first) ∧
    (path.map (configuration context background)).IsChain
      (fun before after => TM2.step (program source caller) before = some after) ∧
    (path.map (configuration context background)).getLast? = some (configuration context background final) ∧
    (path.map (configuration context background)).length = path.length ∧
    ∀ current ∈ path.map (configuration context background), current.var.1 = context ∧
      ∀ point, point ≠ 0 → point ≠ 1 → current.stk point = background point := by
  refine ⟨?_, ?_, ?_, List.length_map _, ?_⟩
  · simp only [List.head?_map, head, Option.map_some]
  · apply (List.isChain_map (configuration context background)).mpr
    exact List.IsChain.imp (fun before after edge => step_configuration source caller context background before after edge) chain
  · simp only [List.getLast?_map, last, Option.map_some]
  · intro current present
    obtain ⟨small, _, rfl⟩ := List.mem_map.mp present
    exact ⟨rfl, fun point notR notL => slots_frame background small.stk point notR notL⟩

theorem none_of_stopped (source : Unit → SmallStatement σ) (final : SmallState σ)
    (stopped : TM2.step source final = none) : final.l = none := by
  rcases final with ⟨position, memory, small⟩
  cases position with
  | none => rfl
  | some point => cases stopped

theorem returned (context : C) (background : Stack → List Bool) (final : SmallState σ)
    (stopped : final.l = none) : (configuration context background final).l = some 1 := by
  rcases final with ⟨position, memory, small⟩
  change position = none at stopped
  subst position
  rfl

theorem boundary_frame (context : C) (background : Stack → List Bool) (small : SmallState σ) :
    (configuration context background small).var.1 = context ∧
    ∀ point, point ≠ 0 → point ≠ 1 → (configuration context background small).stk point = background point :=
  ⟨rfl, fun point notR notL => slots_frame background small.stk point notR notL⟩

theorem internal_frame (code : SmallStatement σ) (context : C) (memory : σ)
    (small : SmallStack → List Bool) (background : Stack → List Bool) :
    ∀ current ∈ PSTRWordBool.AuxWorkspace.nodes (statement code) (context, memory) (slots background small),
      current.1.1 = context ∧ ∀ point, point ≠ 0 → point ≠ 1 → current.2 point = background point := by
  intro current present
  rw [nodes_configuration] at present
  obtain ⟨old, _, rfl⟩ := List.mem_map.mp present
  exact ⟨rfl, fun point notR notL => slots_frame background old.2 point notR notL⟩

/-- Native finite-control applicability must instantiate C and sigma as
fixed finite types BEFORE all data (e.g. C=WordVM64, sigma=Fin983×Bool). -/
abbrev control_finite [Fintype C] [Fintype σ] : Fintype (C × σ) := inferInstance

def enter [Inhabited σ] : Statement C σ :=
  .load (fun memory => (memory.1, (default : σ))) (.goto (fun _ => 0))

theorem caller_step (source : Unit → SmallStatement σ) (caller : Statement C σ)
    (memory : C × σ) (bankSlots : Stack → List Bool) :
    TM2.step (program source caller) ⟨some 1, memory, bankSlots⟩ = some (TM2.stepAux caller memory bankSlots) := rfl

theorem enter_step [Inhabited σ] (source : Unit → SmallStatement σ) (memory : C × σ)
    (bankSlots : Stack → List Bool) :
    TM2.step (program source enter) ⟨some 1, memory, bankSlots⟩ =
      some ⟨some 0, (memory.1, (default : σ)), bankSlots⟩ := rfl

def occupiedSlots (bankSlots : Stack → List Bool) : Nat :=
  (bankSlots 0).length + (bankSlots 1).length + (bankSlots 2).length + (bankSlots 3).length +
  (bankSlots 4).length + (bankSlots 5).length + (bankSlots 6).length + (bankSlots 7).length +
  (bankSlots 8).length + (bankSlots 9).length + (bankSlots 10).length + (bankSlots 11).length +
  (bankSlots 12).length + (bankSlots 13).length + (bankSlots 14).length + (bankSlots 15).length

def outside (background : Stack → List Bool) : Nat :=
  (background 2).length + (background 3).length + (background 4).length + (background 5).length +
  (background 6).length + (background 7).length + (background 8).length + (background 9).length +
  (background 10).length + (background 11).length + (background 12).length + (background 13).length +
  (background 14).length + (background 15).length

theorem occupied_slots (background : Stack → List Bool) (small : SmallStack → List Bool) :
    occupiedSlots (slots background small) = outside background + (small 0).length + (small 1).length := by
  unfold occupiedSlots slots outside
  dsimp
  omega

theorem internal_occupied (code : SmallStatement σ) (context : C) (memory : σ)
    (small : SmallStack → List Bool) (background : Stack → List Bool) :
    ∀ current ∈ PSTRWordBool.AuxWorkspace.nodes (statement code) (context, memory) (slots background small),
      occupiedSlots current.2 ≤ outside background +
        2 * ((small 0).length + (small 1).length + PSTRWordBool.AuxWorkspace.pushes code) := by
  intro current present
  rw [nodes_configuration] at present
  obtain ⟨old, member, rfl⟩ := List.mem_map.mp present
  change occupiedSlots (slots background old.2) ≤ _
  rw [occupied_slots]
  have initial : ∀ point : SmallStack, (small point).length ≤ (small 0).length + (small 1).length := by
    intro point
    fin_cases point
    · exact Nat.le_add_right _ _
    · exact Nat.le_add_left _ _
  have rightBound := PSTRWordBool.AuxWorkspace.node_bound code memory small _ initial old member 0
  have leftBound := PSTRWordBool.AuxWorkspace.node_bound code memory small _ initial old member 1
  omega

theorem represented_tape (context : C) (background : Stack → List Bool) (small : SmallState σ) :
    Tape.mk' (ListBlank.mk ((configuration context background small).stk 1))
      (ListBlank.mk ((configuration context background small).stk 0)) =
    Tape.mk' (ListBlank.mk (small.stk 1)) (ListBlank.mk (small.stk 0)) := rfl

theorem statement_supports (code : Statement C σ) : TM2.SupportsStmt (Finset.univ : Finset Label) code := by
  induction code with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes, no⟩
  | goto _ => intro memory; exact Finset.mem_univ _
  | halt => trivial

theorem supports (source : Unit → SmallStatement σ) (caller : Statement C σ) :
    TM2.Supports (program source caller) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _, fun point _ => statement_supports (program source caller point)⟩

end PaperProofs.Common.Native.PSTRWordVM.VirtualReturn

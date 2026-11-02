module

public import Paid.PDROC_BitVM_Codec_FieldOps_016
public import Paid.PDROC_BitVM_Codec_Output_List_004
public import Paid.PDROC_BitVM_Kernel_CellRead_027

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Codec.OutputInstruction

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal
open PDROC.BitVM.Codec.FieldOps (Path)

abbrev Stack := RatMarshal.Stack
abbrev Alphabet := RatMarshal.Alphabet
abbrev Store := OutputList.EmitStore × Unit
abbrev Label := Fin 5 ⊕ (PDROC.BitVM.Kernel.CellRead.Label ⊕ OutputList.EmitLabel)
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def control (label : Fin 5) : Label := .inl label
def readerLabels (label : PDROC.BitVM.Kernel.CellRead.Label) : Label := .inr (.inl label)
def emitLabels (label : OutputList.EmitLabel) : Label := .inr (.inr label)
def clearedStore : Store := ((none, ()), ())
def clearIso : (Option Bool × (Unit × Unit)) ≃ Store := (Equiv.prodAssoc _ _ _).symm

/-- The globally fixed output roles: native source, reverse output,
copy scratch, unary actual emission ticks. -/
def emitEmbedding : OutputList.EmitStack ↪ Stack where
  toFun := fun role => if role = 0 then 0 else if role = 1 then 22 else if role = 2 then 24 else 23
  inj' := by
    intro a b same
    have values := congrArg Fin.val same
    fin_cases a <;> fin_cases b <;> simp at values ⊢

theorem emit_outside (other : Stack) (not0 : other ≠ 0) (not22 : other ≠ 22)
    (not24 : other ≠ 24) (not23 : other ≠ 23) : ∀ role, other ≠ emitEmbedding role := by
  intro role
  fin_cases role
  · exact not0
  · exact not22
  · exact not24
  · exact not23

theorem register_outside (reg : Register) : ∀ role, registerSlot reg ≠ emitEmbedding role := by
  intro role same
  have values := congrArg Fin.val same
  have bounds := registerSlot_bounds reg
  fin_cases role
  · exact RatMarshal.source_not_right reg same
  · change (registerSlot reg).val = 22 at values
    omega
  · exact RatMarshal.register_not_left reg same
  · change (registerSlot reg).val = 23 at values
    omega


def clearStatement (slot : Stack) (start finish : Label) : Statement :=
  StoreIso.statement clearIso (Inline.statement (τ := Unit × Unit) (fun _ : Unit => start) finish
    (PDROC.BitVM.Kernel.Clear.program slot ()))

/-- One original output: real old-work cleanup, exact whole Cell read,
actual reverse-byte copy plus one TRUE tick, then actual source cleanup.
The whole-list finalizer is not part of this per-emission machine. -/
def program (source : Register) : Label → Statement
  | .inl index =>
    if index = 0 then .load (fun _ => clearedStore) (.goto (fun _ => control 1))
    else if index = 1 then clearStatement 0 (control 1) (control 2)
    else if index = 2 then clearStatement 24 (control 2) (readerLabels 0)
    else if index = 3 then clearStatement 0 (control 3) (control 4)
    else .load (fun _ => clearedStore) .halt
  | .inr (.inl label) => StoreIso.statement clearIso
      (Inline.statement (τ := Unit × Unit) readerLabels (emitLabels 0)
        (PDROC.BitVM.Kernel.CellRead.program source label))
  | .inr (.inr label) => Inline.statement (τ := Unit) emitLabels (control 3)
      (Lift.machine emitEmbedding OutputList.emitProgram label)

def before (contents : Stack → List Bool) (saved : Store) : State := ⟨some (control 0), saved, contents⟩

theorem state_at_label (state : State) (label : Label) (position : state.l = some label) :
    state = (⟨some label, state.var, state.stk⟩ : State) := by
  rcases state with ⟨oldLabel, saved, contents⟩
  change oldLabel = some label at position
  subst oldLabel
  rfl

theorem supports (source : Register) : TM2.Supports (program source) Finset.univ := by
  have every : ∀ code : Statement, TM2.SupportsStmt Finset.univ code := by
    intro code
    induction code with
    | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
    | branch _ _ _ yes no => exact ⟨yes, no⟩
    | goto _ => exact fun _ => Finset.mem_univ _
    | halt => trivial
  exact ⟨Finset.mem_univ _, fun label _ => every (program source label)⟩

theorem reset_step (source : Register) (contents : Stack → List Bool) (saved : Store) :
    TM2.step (program source) (before contents saved) =
      some (⟨some (control 1), clearedStore, contents⟩ : State) := rfl

theorem finish_step (source : Register) (contents : Stack → List Bool) (saved : Store) :
    TM2.step (program source) (⟨some (control 4), saved, contents⟩ : State) =
      some (⟨none, clearedStore, contents⟩ : State) := rfl

def clearSlot (stage : Fin 3) : Stack := ![0, 24, 0] stage
def clearStart (stage : Fin 3) : Label := ![control 1, control 2, control 3] stage
def clearFinish (stage : Fin 3) : Label := ![control 2, readerLabels 0, control 4] stage
def clearCfg (stage : Fin 3) (source : PDROC.BitVM.Kernel.Clear.State) : State :=
  StoreIso.cfg clearIso (Inline.cfg (fun _ : Unit => clearStart stage) (clearFinish stage) ((), ()) source)

theorem clear_agrees (source : Register) (stage : Fin 3) (label : Unit) :
    program source (clearStart stage) = StoreIso.statement clearIso
      (Inline.statement (τ := Unit × Unit) (fun _ : Unit => clearStart stage) (clearFinish stage)
        (PDROC.BitVM.Kernel.Clear.program (clearSlot stage) label)) := by
  cases label
  fin_cases stage <;> rfl

theorem clear_call (source : Register) (stage : Fin 3) (contents : Stack → List Bool) (saved : Option Bool) :
    ∃ path : Path (program source)
      (⟨some (clearStart stage), ((saved, ()), ()), contents⟩ : State)
      (⟨some (clearFinish stage), clearedStore, Function.update contents (clearSlot stage) []⟩ : State),
      path.states.length = (contents (clearSlot stage)).length + 2 := by
  obtain ⟨run, head, chain, last, _halt, length, _frame⟩ :=
    PDROC.BitVM.Kernel.Clear.runs (clearSlot stage) contents saved
  let localPath : Path (PDROC.BitVM.Kernel.Clear.program (clearSlot stage))
      (⟨some (), saved, contents⟩ : PDROC.BitVM.Kernel.Clear.State)
      (⟨none, none, Function.update contents (clearSlot stage) []⟩ : PDROC.BitVM.Kernel.Clear.State) :=
    ⟨run, head, chain, last⟩
  have edge : ∀ a b, TM2.step (PDROC.BitVM.Kernel.Clear.program (clearSlot stage)) a = some b →
      TM2.step (program source) (clearCfg stage a) = some (clearCfg stage b) := by
    intro a b actual
    exact FieldOps.iso_inline_edge clearIso (fun _ : Unit => clearStart stage) (clearFinish stage) ((), ())
      (PDROC.BitVM.Kernel.Clear.program (clearSlot stage)) (program source)
      (clear_agrees source stage) a b actual
  exact ⟨localPath.transport (clearCfg stage) edge, (localPath.transport_length (clearCfg stage) edge).trans length⟩

def readerCfg (source : PDROC.BitVM.Kernel.CellRead.State) : State :=
  StoreIso.cfg clearIso (Inline.cfg readerLabels (emitLabels 0) ((), ()) source)

theorem reader_call (source : Register) (logical : PaperProofs.Paid.Computation.State)
    (contents : Stack → List Bool)
    (represented : ∀ reg, contents (registerSlot reg) = encodeCellBits (logical.register reg))
    (empty0 : contents 0 = []) (empty24 : contents 24 = []) :
    ∃ ready : State, ∃ path : Path (program source)
      (⟨some (readerLabels 0), clearedStore, contents⟩ : State) ready,
      ready.l = some (emitLabels 0) ∧ ready.var = clearedStore ∧
      ready.stk 0 = encodeCellBits (logical.register source) ∧ ready.stk 24 = [] ∧
      (∀ other, other ≠ 0 → other ≠ 24 → ready.stk other = contents other) ∧
      path.states.length = 2 * (encodeCellBits (logical.register source)).length + 3 := by
  obtain ⟨run, after, head, chain, last, _halt, halted, store, regs, word, scratch, length, frame⟩ :=
    PDROC.BitVM.Kernel.CellRead.runs logical source [] contents represented empty0 empty24
  let localPath : Path (PDROC.BitVM.Kernel.CellRead.program source) (PDROC.BitVM.Kernel.CellRead.before contents) after :=
    ⟨run, head, chain, last⟩
  have edge : ∀ a b, TM2.step (PDROC.BitVM.Kernel.CellRead.program source) a = some b →
      TM2.step (program source) (readerCfg a) = some (readerCfg b) := by
    intro a b actual
    exact FieldOps.iso_inline_edge clearIso readerLabels (emitLabels 0) ((), ())
      (PDROC.BitVM.Kernel.CellRead.program source) (program source) (by intro label; rfl) a b actual
  refine ⟨readerCfg after, localPath.transport readerCfg edge, ?_, ?_, ?_, scratch, ?_, ?_⟩
  · change some (after.l.map readerLabels |>.getD (emitLabels 0)) = _
    rw [halted]
    rfl
  · change ((after.var, ()), ()) = clearedStore
    rw [store]
    rfl
  · change after.stk 0 = encodeCellBits (logical.register source)
    simpa only [List.append_nil] using word
  · intro other not0 not24
    by_cases same : other = registerSlot source
    · subst other
      exact (regs source).trans (represented source).symm
    · apply frame other
      intro role
      fin_cases role
      · exact same
      · exact not0
      · exact not24
  · exact (localPath.transport_length readerCfg edge).trans length

def emitCfg (source : TM2.Cfg Alphabet OutputList.EmitLabel OutputList.EmitStore) : State :=
  Inline.cfg emitLabels (control 3) () source

/-- A real fixed four-role Lift of the already-frozen emitter. The
arbitrary previous reverse-output/ticks are actual caller stacks. -/
theorem emit_call (source : Register) (word : List Bool) (contents : Stack → List Bool)
    (actualWord : contents 0 = word) (emptyScratch : contents 24 = []) :
    ∃ ready : State, ∃ path : Path (program source)
      (⟨some (emitLabels 0), clearedStore, contents⟩ : State) ready,
      ready.l = some (control 3) ∧ ready.var = clearedStore ∧
      ready.stk 0 = word ∧ ready.stk 24 = [] ∧
      ready.stk 22 = word.reverse ++ contents 22 ∧ ready.stk 23 = true :: contents 23 ∧
      (∀ other, other ≠ 0 → other ≠ 22 → other ≠ 24 → other ≠ 23 → ready.stk other = contents other) ∧
      path.states.length = 2 * word.length + 4 := by
  obtain ⟨run, head, chain, last, _halt, length, _source, _output, _scratch, _ticks⟩ :=
    OutputList.emit_runs word (contents 22) (contents 23)
  cases run with
  | nil => simp only [List.head?_nil, reduceCtorEq] at head
  | cons start rest =>
    have same : start = OutputList.emitBefore word (contents 22) (contents 23) := Option.some.inj head
    subst start
    let rawBefore : TM2.Cfg Alphabet OutputList.EmitLabel OutputList.EmitStore := ⟨some 0, (none, ()), contents⟩
    have view : Lift.cfg emitEmbedding rawBefore = OutputList.emitBefore word (contents 22) (contents 23) := by
      have data : Lift.slots emitEmbedding contents = OutputList.emitSlots word (contents 22) [] (contents 23) := by
        funext role
        fin_cases role
        · exact actualWord
        · rfl
        · exact emptyScratch
        · rfl
      change (⟨some 0, (none, ()), Lift.slots emitEmbedding contents⟩ : OutputList.EmitState) = _
      rw [data]
      rfl
    obtain ⟨posts, after, size, actual, actualLast, finalView, outside⟩ :=
      Lift.path emitEmbedding OutputList.emitProgram rawBefore
        (OutputList.emitBefore word (contents 22) (contents 23))
        (OutputList.emitAfter word (contents 22) (contents 23)) rest view chain last
    let localPath : Path (Lift.machine emitEmbedding OutputList.emitProgram) rawBefore after :=
      ⟨rawBefore :: posts, rfl, actual, actualLast⟩
    have edge : ∀ a b, TM2.step (Lift.machine emitEmbedding OutputList.emitProgram) a = some b →
        TM2.step (program source) (emitCfg a) = some (emitCfg b) := by
      intro a b actual
      exact Inline.step_edge emitLabels (control 3) (Lift.machine emitEmbedding OutputList.emitProgram)
        (program source) (by intro label; rfl) a b () actual
    have finalLabel : after.l = none := congrArg TM2.Cfg.l finalView
    have finalStore : after.var = (none, ()) := congrArg TM2.Cfg.var finalView
    have selected : ∀ role, after.stk (emitEmbedding role) =
        (OutputList.emitAfter word (contents 22) (contents 23)).stk role := by
      intro role
      exact congrArg (fun state : OutputList.EmitState => state.stk role) finalView
    refine ⟨emitCfg after, localPath.transport emitCfg edge, ?_, ?_, selected 0, selected 2,
      selected 1, selected 3, ?_, ?_⟩
    · change some (after.l.map emitLabels |>.getD (control 3)) = _
      rw [finalLabel]
      rfl
    · change (after.var, ()) = clearedStore
      rw [finalStore]
      rfl
    · intro other not0 not22 not24 not23
      exact outside other (emit_outside other not0 not22 not24 not23)
    · have sameLength : localPath.states.length = 2 * word.length + 4 := by
        change posts.length + 1 = _
        simp only [List.length_cons] at length
        omega
      exact (localPath.transport_length emitCfg edge).trans sameLength

end PDROC.BitVM.Codec.OutputInstruction

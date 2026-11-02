module

public import Paid.PDROC_BitVM_Log_Capture_005
public import Paid.PDROC_BitVM_Log_Header_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

/-! A real Nat-field subroutine for copying Cell fields. It reuses the
literal capture header/payload code and its exact state witnesses, but ends
at a real halt BEFORE address normalization. This permits several fields
to accumulate in reverse order on stack6; no decoded Nat enters sigma. -/

namespace PDROC.BitVM.Log.CellField

open Turing

abbrev Stack := Capture.Stack
abbrev Label := Capture.Label
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := Capture.Store
abbrev State := Capture.State
abbrev Statement := Capture.Statement

def program (label : Label) : Statement :=
  if label = 0 then Capture.readHeader else if label = 1 then Capture.readPayload else .halt

theorem header_chain (width : ℕ) (input ticks archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (Capture.headerTrace other width input ticks archive captured store).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction width generalizing ticks archive captured store with
  | zero =>
    apply List.isChain_cons_cons.mpr
    refine ⟨?_, List.isChain_singleton _⟩
    exact Capture.header_false input ticks archive captured other store
  | succ width ih =>
    change (_ :: Capture.headerTrace other width input (true :: ticks) (true :: archive)
      (true :: captured) (Query.setRecord store (some true))).IsChain _
    apply List.IsChain.cons (ih (true :: ticks) (true :: archive) (true :: captured) _)
    intro after member
    rw [Capture.headerTrace_head] at member
    have equal := Option.mem_some_iff.mp member
    subst after
    exact Capture.header_true (List.replicate width true ++ false :: input)
      ticks archive captured other store

theorem payload_chain (digits suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (Capture.payloadTrace other digits suffix archive captured store).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction digits generalizing archive captured store with
  | nil =>
    apply List.isChain_cons_cons.mpr
    refine ⟨?_, List.isChain_singleton _⟩
    exact Capture.payload_done suffix archive captured other store
  | cons bit digits ih =>
    change (_ :: Capture.payloadTrace other digits suffix (bit :: archive) (bit :: captured)
      (Query.setRecord store (some bit))).IsChain _
    apply List.IsChain.cons (ih (bit :: archive) (bit :: captured) _)
    intro after member
    rw [Capture.payloadTrace_head] at member
    have equal := Option.mem_some_iff.mp member
    subst after
    exact Capture.payload_bit bit (digits ++ suffix) (List.replicate digits.length true)
      archive captured other store

theorem prefix_chain (digits suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (Capture.scanTrace digits suffix archive captured other store).IsChain
      (fun before after => TM2.step program before = some after) := by
  apply TwoStack.join_chain _ _
    (Capture.state (some 1) (Query.setRecord store (some false)) (digits ++ suffix)
      (List.replicate digits.length true)
      (false :: (List.replicate digits.length true ++ archive))
      (false :: (List.replicate digits.length true ++ captured)) other)
  · exact header_chain digits.length (digits ++ suffix) [] archive captured other store
  · exact payload_chain digits suffix
      (false :: (List.replicate digits.length true ++ archive))
      (false :: (List.replicate digits.length true ++ captured)) other
      (Query.setRecord store (some false))
  · simp only [Capture.headerTrace_last, List.append_nil]
  · exact Capture.payloadTrace_head digits suffix
      (false :: (List.replicate digits.length true ++ archive))
      (false :: (List.replicate digits.length true ++ captured)) other
      (Query.setRecord store (some false))

theorem supports : TM2.Supports program (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label <;> simp [program, Capture.readHeader, Capture.readPayload, TM2.SupportsStmt]

/-- One source field is copied by real reads and a real halt. Old copied
bytes, query, output and all caller-extra flags are preserved as data. -/
theorem field_runs (digits suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    ∃ (run : List State) (after : State),
      run.head? = some (Capture.state (some 0) store (Header.natWord digits ++ suffix)
        [] archive captured other) ∧
      run.IsChain (fun before after => TM2.step program before = some after) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧ after.var = (none, store.2) ∧
      after.stk = Capture.slots suffix [] ((Header.natWord digits).reverse ++ archive)
        ((Header.natWord digits).reverse ++ captured) other ∧
      run.length = 2 * digits.length + 4 := by
  let frontTrace := Capture.scanTrace digits suffix archive captured other store
  let ready := Capture.state (some 2) (Query.setRecord store none) suffix []
    ((Header.natWord digits).reverse ++ archive) ((Header.natWord digits).reverse ++ captured) other
  let after := Capture.state none (Query.setRecord store none) suffix []
    ((Header.natWord digits).reverse ++ archive) ((Header.natWord digits).reverse ++ captured) other
  have head : frontTrace.head? = some (Capture.state (some 0) store (Header.natWord digits ++ suffix)
      [] archive captured other) := Capture.scan_trace_head digits suffix archive captured other store
  have last : frontTrace.getLast? = some ready := Capture.scan_trace_last digits suffix archive captured other store
  let run := frontTrace ++ [after]
  have chain : run.IsChain (fun a b => TM2.step program a = some b) := by
    have frontChain : frontTrace.IsChain (fun a b => TM2.step program a = some b) :=
      prefix_chain digits suffix archive captured other store
    apply frontChain.append (List.isChain_singleton _)
    intro before hb next hn
    simp only [last, Option.mem_some_iff] at hb
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst before
    subst next
    rfl
  refine ⟨run, after, ?_, chain, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · change (frontTrace ++ [after]).head? = _
    simp only [List.head?_append, head, Option.some_or]
  · exact List.getLast?_append_cons frontTrace after []
  · simp only [run, frontTrace, List.length_append, List.length_cons, List.length_nil,
      Capture.scan_trace_length]

open PaperProofs.Paid.Computation PaperProofs.Paid.Parameters in
theorem official_field_runs (value : ℕ) (suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    ∃ (run : List State) (after : State),
      run.head? = some (Capture.state (some 0) store (encodeNatBits value ++ suffix)
        [] archive captured other) ∧
      run.IsChain (fun before after => TM2.step program before = some after) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧ after.var = (none, store.2) ∧
      after.stk = Capture.slots suffix [] ((encodeNatBits value).reverse ++ archive)
        ((encodeNatBits value).reverse ++ captured) other ∧
      run.length = 2 * natBits value + 4 := by
  simpa only [Header.natWord_digits, Header.digits_length] using
    field_runs (Header.digits value) suffix archive captured other store

end PDROC.BitVM.Log.CellField

/- The skip side is a separate real finite program in this same execution
module. It reads the actual Cell tag/sign and calls the already proved
ordinary Nat scanner on one natural field or two rational fields. -/

namespace PDROC.BitVM.Log.CellSkip

open Turing

abbrev Stack := Query.Stack
abbrev Label := Fin 4 ⊕ (Fin 4 ⊕ (Fin 4 ⊕ Fin 4))
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := Query.Store
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def startLabel : Label := .inl 0
def signLabel : Label := .inl 1
def doneLabel : Label := .inl 2
def invalidLabel : Label := .inl 3
def naturalLabel (label : Header.Label) : Label := .inr (.inl label)
def numeratorLabel (label : Header.Label) : Label := .inr (.inr (.inl label))
def denominatorLabel (label : Header.Label) : Label := .inr (.inr (.inr label))

def headerEmbed : Header.Stack ↪ Stack where
  toFun := fun index => ⟨index.val, by have := index.isLt; omega⟩
  inj' := by
    intro left right equal
    apply Fin.ext
    exact congrArg (fun index : Stack => index.val) equal

def headerCode (labels : Header.Label → Label) (returnLabel : Label) (label : Header.Label) : Statement :=
  Native.Inline.statement (τ := Query.Extra) labels returnLabel
    (Native.Lift.statement headerEmbed (Header.program label))

def tagCode : Statement :=
  .pop 0 Query.setRecord
    (.branch (fun store => store.1.isSome)
      (.push 2 (fun store => store.1.getD false)
        (.branch (fun store => store.1.getD false)
          (.goto (fun _ => signLabel)) (.goto (fun _ => naturalLabel 0))))
      (.goto (fun _ => invalidLabel)))

def signCode : Statement :=
  .pop 0 Query.setRecord
    (.branch (fun store => store.1.isSome)
      (.push 2 (fun store => store.1.getD false) (.goto (fun _ => numeratorLabel 0)))
      (.goto (fun _ => invalidLabel)))

def program : Label → Statement
  | .inl control => if control = 0 then tagCode else if control = 1 then signCode else .halt
  | .inr (.inl label) => headerCode naturalLabel doneLabel label
  | .inr (.inr (.inl label)) => headerCode numeratorLabel (denominatorLabel 0) label
  | .inr (.inr (.inr label)) => headerCode denominatorLabel doneLabel label

theorem header_supports (labels : Header.Label → Label) (returnLabel : Label) (label : Header.Label) :
    TM2.SupportsStmt (Finset.univ : Finset Label) (headerCode labels returnLabel label) := by
  apply Native.Inline.supports_statement labels returnLabel
    (Finset.univ : Finset Header.Label) (Finset.univ : Finset Label)
  · intro sourceLabel _; exact Finset.mem_univ _
  · exact Finset.mem_univ _
  · apply Native.Lift.supports_statement
    exact Header.supports.2 label (Finset.mem_univ _)

theorem supports : TM2.Supports program (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    rcases label with control | (natural | (numerator | denominator))
    · fin_cases control <;> simp [program, tagCode, signCode, TM2.SupportsStmt]
    · exact header_supports naturalLabel doneLabel natural
    · exact header_supports numeratorLabel (denominatorLabel 0) numerator
    · exact header_supports denominatorLabel doneLabel denominator

def slots (input ticks archive : List Bool) (other : Stack → List Bool) : Stack → List Bool :=
  fun stack => if stack = 0 then input else if stack = 1 then ticks else if stack = 2 then archive else other stack

def state (label : Option Label) (store : Store) (input ticks archive : List Bool)
    (other : Stack → List Bool) : State := ⟨label, store, slots input ticks archive other⟩

theorem update_input (input ticks archive replacement : List Bool) (other : Stack → List Bool) :
    Function.update (slots input ticks archive other) 0 replacement = slots replacement ticks archive other := by
  funext stack; fin_cases stack <;> simp [slots]

theorem update_archive (input ticks archive replacement : List Bool) (other : Stack → List Bool) :
    Function.update (slots input ticks archive other) 2 replacement = slots input ticks replacement other := by
  funext stack; fin_cases stack <;> simp [slots]

theorem tag_false (input ticks archive : List Bool) (other : Stack → List Bool) (store : Store) :
    TM2.step program (state (some startLabel) store (false :: input) ticks archive other) =
      some (state (some (naturalLabel 0)) (Query.setRecord store (some false))
        input ticks (false :: archive) other) := by
  change (some ⟨some (naturalLabel 0), Query.setRecord store (some false),
    Function.update (Function.update (slots (false :: input) ticks archive other) 0 input)
      2 (false :: archive)⟩ : Option State) = _
  rw [update_input, update_archive]
  rfl

theorem tag_true (input ticks archive : List Bool) (other : Stack → List Bool) (store : Store) :
    TM2.step program (state (some startLabel) store (true :: input) ticks archive other) =
      some (state (some signLabel) (Query.setRecord store (some true))
        input ticks (true :: archive) other) := by
  change (some ⟨some signLabel, Query.setRecord store (some true),
    Function.update (Function.update (slots (true :: input) ticks archive other) 0 input)
      2 (true :: archive)⟩ : Option State) = _
  rw [update_input, update_archive]
  rfl

theorem sign_bit (bit : Bool) (input ticks archive : List Bool) (other : Stack → List Bool) (store : Store) :
    TM2.step program (state (some signLabel) store (bit :: input) ticks archive other) =
      some (state (some (numeratorLabel 0)) (Query.setRecord store (some bit))
        input ticks (bit :: archive) other) := by
  change (some ⟨some (numeratorLabel 0), Query.setRecord store (some bit),
    Function.update (Function.update (slots (bit :: input) ticks archive other) 0 input)
      2 (bit :: archive)⟩ : Option State) = _
  rw [update_input, update_archive]
  rfl

theorem done_halt (input ticks archive : List Bool) (other : Stack → List Bool) (store : Store) :
    TM2.step program (state (some doneLabel) store input ticks archive other) =
      some (state none store input ticks archive other) := rfl

theorem halted (input ticks archive : List Bool) (other : Stack → List Bool) (store : Store) :
    TM2.step program (state none store input ticks archive other) = none := rfl

end PDROC.BitVM.Log.CellSkip

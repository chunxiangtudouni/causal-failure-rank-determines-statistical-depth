module

public import Common.PSTR_WordBool_NativeMulPort_056
public import Common.PSTR_WordBool_NatWordCaller_055
public import Common.PSTR_WordBool_StoreIso_048
public import Common.PSTR_WordVM_LabelMap_029

/-! One fixed joint finite program: native body0, paid initialization1,
and the actual reader at2..9. Native return goes to reader entry2.
The final caller9 is not executed by the component. All control-store
reassociation is static; runtime width/values never occur in control. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.NativeMulLink

open Turing

abbrev Stack := Fin 16
abbrev Label := Fin 10
abbrev Alphabet (_ : Stack) := Bool
abbrev Store (C : Type*) := (C × NativeMulPort.OldStore) × NatWordIO.Store
abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Store C)

variable {C : Type*}

def exchange (C : Type*) : ((C × NatWordIO.Store) × NativeMulPort.OldStore) ≃ Store C :=
  StoreIso.exchange C NatWordIO.Store NativeMulPort.OldStore

def nativePort (point : PSTRWordVM.VirtualReturn.Label) : Label :=
  if point = 0 then 0 else 2

def readerPort (point : NatWordIO.Label) : Label := ⟨point.val + 2, by omega⟩

def nativeBody : Statement C :=
  PSTRWordVM.LabelMap.statement nativePort
    (StoreIso.statement (exchange C)
      (PSTRWordVM.VirtualReturn.statement (C := C × NatWordIO.Store) (NativeMulPort.source ())))

def enterBody : Statement C :=
  .load (fun memory => ((memory.1.1, (default : NativeMulPort.OldStore)), memory.2))
    (.goto (fun _ => 0))

def program (caller : Statement C) (point : Label) : Statement C :=
  if point.val = 0 then nativeBody else
  if point.val = 1 then enterBody else
  if point.val = 9 then caller else
    PSTRWordVM.LabelMap.statement readerPort
      (ContextLift.statement (C := C × NativeMulPort.OldStore)
        (NatWordIO.program .halt ⟨point.val - 2, by omega⟩))

theorem program_native (caller : Statement C) : program caller 0 = nativeBody := rfl
theorem program_enter (caller : Statement C) : program caller 1 = enterBody := rfl
theorem program_caller (caller : Statement C) : program caller 9 = caller := rfl

theorem native_port_zero : nativePort 0 = 0 := rfl
theorem native_port_one : nativePort 1 = 2 := rfl

theorem program_reader (caller : Statement C) (point : NatWordIO.Label) (internal : point ≠ 7) :
    program caller (readerPort point) = PSTRWordVM.LabelMap.statement readerPort
      (ContextLift.statement (C := C × NativeMulPort.OldStore) (NatWordIO.program .halt point)) := by
  fin_cases point
  all_goals first | exact False.elim (internal rfl) | rfl

theorem enter_step (caller : Statement C) (context : C) (oldMemory : NativeMulPort.OldStore)
    (readerMemory : NatWordIO.Store) (slots : Stack → List Bool) :
    TM2.step (program caller) ⟨some 1, ((context, oldMemory), readerMemory), slots⟩ =
      some ⟨some 0, ((context, (default : NativeMulPort.OldStore)), readerMemory), slots⟩ := rfl

theorem no_early_halt_port {K Λ σ : Type*} {Γ : K → Type*} [DecidableEq K]
    (machine : Λ → TM2.Stmt Γ Λ σ) (port : Λ) (atPort : machine port = .halt)
    (trace : List (TM2.Cfg Γ Λ σ)) (final : TM2.Cfg Γ Λ σ)
    (chain : trace.IsChain (fun before after => TM2.step machine before = some after))
    (last : trace.getLast? = some final) (active : final.l = some port) :
    ∀ current ∈ trace.dropLast, current.l ≠ some port := by
  induction trace with
  | nil => simp
  | cons before rest ih =>
    cases rest with
    | nil => simp
    | cons next rest =>
      obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
      intro current present
      rw [List.dropLast_cons_cons] at present
      rcases List.mem_cons.mp present with same | later
      · subst current
        intro selected
        have stopped : TM2.step machine before = some (⟨none, before.var, before.stk⟩ : TM2.Cfg Γ Λ σ) := by
          cases before with
          | mk label memory slots =>
            change label = some port at selected
            subst label
            change some (TM2.stepAux (machine port) memory slots) = _
            rw [atPort]
            rfl
        rw [stopped] at edge
        have nextStopped := (Option.some.inj edge).symm
        cases rest with
        | nil =>
          have nextFinal : next = final := Option.some.inj last
          have inactive : final.l = none := by rw [← nextFinal, nextStopped]
          rw [inactive] at active
          cases active
        | cons after rest =>
          have impossible := (List.isChain_cons_cons.mp tailChain).1
          rw [nextStopped] at impossible
          cases impossible
      · exact ih tailChain last current later

end PaperProofs.Common.Native.PSTRWordBool.NativeMulLink

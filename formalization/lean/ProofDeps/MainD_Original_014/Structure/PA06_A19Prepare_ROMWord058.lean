module

public import Structure.PA06_A19Prepare_ROM_001
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

/-! Physical execution under the existing ROMPrefix relation. Only actual
old in-range loads are used. No ROM size, allocation or word width changes.
Candidate until strict validation. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareROMWord058

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims PA06A19PrepareROM001

theorem access_of_prefix {bits : Nat} {old new : PhysicalROM}
    (hprefix : ROMPrefix old new) (H : Nat) (state : WordState bits) (op : PackingOp)
    (safe : packingAccessFits old H state op) : packingAccessFits new H state op := by
  cases op with
  | base instruction => exact accessFits_of_romPrefix hprefix H _ instruction safe
  | arithmetic operation target left right => trivial
  | jumpIfZero condition target => trivial

theorem execute_eq_of_prefix {bits : Nat} {old new : PhysicalROM}
    (hprefix : ROMPrefix old new) (H : Nat) (state : WordState bits) (op : PackingOp)
    (safe : packingAccessFits old H state op) :
    packingExecuteOp new op state = packingExecuteOp old op state := by
  cases op with
  | arithmetic operation target left right => rfl
  | jumpIfZero condition target => rfl
  | base op =>
    cases op with
    | subtract target left right => rfl
    | base instruction =>
      cases instruction <;> try rfl
      case loadROM region target pointer =>
        have ha : (state.register pointer).toNat < (old.words region).length := safe
        have he := hprefix.read_eq region (state.register pointer).toNat ha
        change (new.words region).getD (state.register pointer).toNat 0 =
          (old.words region).getD (state.register pointer).toNat 0 at he
        simp only [packingExecuteOp, wordOp, wordInstruction, he]

theorem step_eq_of_prefix {bits : Nat} {old new : PhysicalROM}
    (hprefix : ROMPrefix old new) (H : Nat) (program : List PackingOp)
    (state : WordState bits) (op : PackingOp)
    (decoded : PackingOp.decode (fetch program state) = some op)
    (safe : packingAccessFits old H state op) :
    packingStep new ((packingCode program).map (BitVec.ofNat bits)) state =
      packingStep old ((packingCode program).map (BitVec.ofNat bits)) state := by
  cases active : state.halted with
  | true => simp only [packingStep, active, ite_true]
  | false =>
    change (if state.halted then state else
      match PackingOp.decode (fetch program state) with
      | none => {state with halted := true}
      | some instruction => packingExecuteOp new instruction state) =
      (if state.halted then state else
      match PackingOp.decode (fetch program state) with
      | none => {state with halted := true}
      | some instruction => packingExecuteOp old instruction state)
    simp only [active, Bool.false_eq_true, ite_false, decoded]
    exact execute_eq_of_prefix hprefix H state op safe

/-- A component producer supplies this premise from its own actual
prefixes. It is never an extra original-controller caller assumption. -/
theorem run_eq_of_prefix {bits : Nat} {old new : PhysicalROM}
    (hprefix : ROMPrefix old new) (H : Nat) (program : List PackingOp)
    (before : WordState bits) (count : Nat)
    (safe : ∀ clock < count, ∃ op,
      PackingOp.decode (fetch program (packingRun old program clock before)) = some op ∧
        packingAccessFits old H (packingRun old program clock before) op) :
    packingRun new program count before = packingRun old program count before := by
  revert safe
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
    intro safe
    have beforeEq := ih (fun clock hc => safe clock (by omega))
    rw [packingRun_succ, packingRun_succ, beforeEq]
    obtain ⟨op, decoded, access⟩ := safe count (by omega)
    exact step_eq_of_prefix hprefix H program _ op decoded access

end PaperProofs.Structure.LaminarTree.PA06A19PrepareROMWord058

module

public import PaperProofs.Structure.RawIncidenceLaminarRAM
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED same-length replacement of the original first10 checker
instructions. The q0 branch occurs immediately after the actual raw header
loads, before any stage-pair loop. The remaining whole code is retained
byte-for-byte at its original offsets. handlerPC is a fixed WORD address. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawIncidenceLaminarRAM RawTreePreprocessingClaims

def lead (handlerPC : Nat) : List PackingOp :=
  [.base (.base (.constant .address 0)),
   .base (.base (.loadROM .input .total .address)),
   .base (.base (.storeHeap .address .total)),
   .base (.base (.constant .address 1)),
   .base (.base (.loadROM .input .total .address)),
   .base (.base (.storeHeap .address .total)),
   .base (.base (.constant .index handlerPC))]

def branch : PackingOp := .jumpIfZero .total .index

def restore : List PackingOp :=
  [.base (.base (.constant .value 1)), .base (.base (.constant .address 2))]

def head (handlerPC : Nat) : List PackingOp := lead handlerPC ++ [branch] ++ restore

def program (handlerPC : Nat) (old : List PackingOp) : List PackingOp :=
  head handlerPC ++ old.drop 10

theorem lead_length (handlerPC : Nat) : (lead handlerPC).length = 7 := rfl

theorem head_length (handlerPC : Nat) : (head handlerPC).length = 10 := rfl

theorem lead_noJump (handlerPC : Nat) : ∀ op ∈ lead handlerPC, NoJump op := by
  simp [lead, NoJump]

theorem program_length (handlerPC : Nat) (old : List PackingOp) (bound : 10 ≤ old.length) :
    (program handlerPC old).length = old.length := by
  simp only [program, List.length_append, head_length, List.length_drop]
  omega

theorem program_drop10 (handlerPC : Nat) (old : List PackingOp) :
    (program handlerPC old).drop 10 = old.drop 10 := rfl

theorem program_take10 (handlerPC : Nat) (old : List PackingOp) :
    (program handlerPC old).take 10 = head handlerPC := rfl

theorem head_first_six (handlerPC : Nat) : (head handlerPC).take 6 = checker.take 6 := rfl

theorem program_lead_slice (handlerPC : Nat) (old : List PackingOp) :
    0 + (lead handlerPC).length + 1 ≤ (program handlerPC old).length ∧
      (∀ position (hp : position < (lead handlerPC).length),
        (program handlerPC old)[0 + position]'(by
          simp only [lead_length] at hp
          simp only [program, List.length_append, head_length]
          omega) = (lead handlerPC)[position]) ∧
      (program handlerPC old)[0 + (lead handlerPC).length]'(by
        simp only [program, List.length_append, head_length, lead_length]
        omega) = branch := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [program, List.length_append, head_length, lead_length]
    omega
  · intro position hp
    rw [lead_length] at hp
    interval_cases position <;> rfl
  · rfl

end PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079

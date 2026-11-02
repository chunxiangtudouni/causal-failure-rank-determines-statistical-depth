module

public import Structure.PA17_TM_RatArithmetic_Parse_002c

/-! A fixed Bool TM0 scans genuine original Natural Datums and stops on
the first TRUE tag. The real whole-field parser is embedded with one extra
test label. Its HALT becomes an actual write-self transition back to test;
there is no reset, host list-length loop, EOF search or allocator. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLocator

open Turing
open PA17TMRatArithmeticParse002

def embedLabel (label : Fin 18) : Fin 19 := ⟨label.val + 1, by omega⟩

def embedCfg (state : MachineState 17) : MachineState 18 :=
  ⟨embedLabel state.q, state.Tape⟩

def scanState (label : Fin 19) (left right : List Bool) : MachineState 18 :=
  ⟨label, Tape.mk₂ left right⟩

/-- Nineteen fixed labels, independent of all field values and counts. -/
def scanMachine : Machine 18 := fun label symbol =>
  if initial : label.val = 0 then
    if symbol then none else some (1, .move .right)
  else
    match streamMachine ⟨label.val - 1, by omega⟩ symbol with
    | none => some (0, .write symbol)
    | some (next, instruction) => some (embedLabel next, instruction)

theorem scan_step_embed (state : MachineState 17) :
    TM0.step scanMachine (embedCfg state) =
      match TM0.step streamMachine state with
      | none => some ⟨0, state.Tape⟩
      | some after => some (embedCfg after) := by
  cases state with
  | mk label tape =>
    unfold TM0.step scanMachine embedCfg embedLabel
    simp only [show ¬ label.val + 1 = 0 by omega, ↓reduceDIte,
      Nat.add_sub_cancel, Fin.eta]
    cases action : streamMachine label tape.head with
    | none => simp [Tape.write_self]
    | some value =>
      obtain ⟨next, instruction⟩ := value
      cases instruction <;> rfl

theorem scan_false_step (left right : List Bool) :
    TM0.step scanMachine (scanState 0 left (false :: right)) =
      some (embedCfg (streamState 0 (false :: left) right)) := by
  simp [TM0.step, scanMachine, scanState, embedCfg, embedLabel,
    streamState, Tape.mk₂]

theorem scan_true_halt (left right : List Bool) :
    TM0.step scanMachine (scanState 0 left (true :: right)) = none := by
  simp [TM0.step, scanMachine, scanState, Tape.mk₂]

def naturalPrefix (numbers : List Nat) : List Bool :=
  numbers.flatMap (fun number => encodeDatum (.natural number))

/-- Exact in-place archive from consuming one FALSE tag and real raw Nat.
The original tag remains as an actual left FALSE guard. -/
def naturalLeft (left : List Bool) (number : Nat) : List Bool :=
  false :: (PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse ++ false :: left)

def scanArchive (left : List Bool) (numbers : List Nat) : List Bool :=
  numbers.foldl naturalLeft left

def scanTrace (left : List Bool) : List Nat → List Bool → List (MachineState 18)
  | [], suffix => [scanState 0 left (true :: suffix)]
  | number :: later, suffix =>
    scanState 0 left (encodeDatum (.natural number) ++ naturalPrefix later ++ true :: suffix) ::
      ((streamTrace (false :: left) [] (PSTRTMNatValue017.rawPayload number)
        (naturalPrefix later ++ true :: suffix)).map embedCfg ++
        scanTrace (naturalLeft left number) later suffix)

def scanFinal (left : List Bool) (numbers : List Nat) (suffix : List Bool) : MachineState 18 :=
  scanState 0 (scanArchive left numbers) (true :: suffix)

theorem naturalPrefix_cons (number : Nat) (later : List Nat) :
    naturalPrefix (number :: later) = encodeDatum (.natural number) ++ naturalPrefix later := rfl

theorem scanArchive_cons (left : List Bool) (number : Nat) (later : List Nat) :
    scanArchive left (number :: later) = scanArchive (naturalLeft left number) later := rfl

theorem scanTrace_head (left : List Bool) (numbers : List Nat) (suffix : List Bool) :
    (scanTrace left numbers suffix).head? =
      some (scanState 0 left (naturalPrefix numbers ++ true :: suffix)) := by
  cases numbers <;> rfl

theorem scanTrace_nonempty (left : List Bool) (numbers : List Nat) (suffix : List Bool) :
    scanTrace left numbers suffix ≠ [] := by
  intro empty
  have first := scanTrace_head left numbers suffix
  simp [empty] at first

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLocator


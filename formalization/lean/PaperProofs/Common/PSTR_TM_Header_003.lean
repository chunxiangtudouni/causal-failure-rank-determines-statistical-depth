module
public import PaperProofs.Common.PSTR_TM_Codec_001
public import PaperProofs.Common.PSTR_TM_Trace_002

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMHeader003
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrace002

/-- A single-state Boolean TM. Its only transition moves right over true;
false is a genuine halt. Code is fixed before every numeric input. -/
def headerMachine : Machine 0 := fun _ symbol =>
  if symbol then some (0, Turing.TM0.Stmt.move Turing.Dir.right) else none

def headerState (left right : List Bool) : MachineState 0 :=
  ⟨0, Turing.Tape.mk₂ left right⟩

def headerTrace : Nat → List Bool → List Bool → List (MachineState 0)
  | 0, left, tail => [headerState left (false :: tail)]
  | n + 1, left, tail =>
    headerState left (List.replicate (n + 1) true ++ false :: tail) ::
      headerTrace n (true :: left) tail

theorem header_step (left right : List Bool) :
    Turing.TM0.step headerMachine (headerState left (true :: right)) =
      some (headerState (true :: left) right) := by
  simp [Turing.TM0.step, headerMachine, headerState, Turing.Tape.mk₂,
    Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk, Turing.ListBlank.cons_mk]

theorem header_halt (left tail : List Bool) :
    Turing.TM0.step headerMachine (headerState left (false :: tail)) = none := by
  simp [Turing.TM0.step, headerMachine, headerState, Turing.Tape.mk₂,
    Turing.ListBlank.head_mk]

theorem headerTrace_head (n : Nat) (left tail : List Bool) :
    (headerTrace n left tail).head? =
      some (headerState left (List.replicate n true ++ false :: tail)) := by
  cases n <;> rfl

theorem headerTrace_length (n : Nat) (left tail : List Bool) :
    (headerTrace n left tail).length = n + 1 := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih => simp only [headerTrace, List.length_cons, ih]

theorem headerTrace_chain (n : Nat) (left tail : List Bool) :
    (headerTrace n left tail).IsChain (fun a b => Turing.TM0.step headerMachine a = some b) := by
  induction n generalizing left with
  | zero => exact .singleton _
  | succ n ih =>
    cases n with
    | zero =>
      simp only [headerTrace, List.isChain_cons_cons, List.isChain_singleton, and_true]
      simpa using header_step left (false :: tail)
    | succ n =>
      apply List.isChain_cons_cons.mpr
      constructor
      · simpa only [List.replicate_succ, List.cons_append] using
          header_step left (List.replicate (n + 1) true ++ false :: tail)
      · exact ih (true :: left)

theorem replicate_push (n : Nat) (left : List Bool) :
    List.replicate n true ++ true :: left = List.replicate (n + 1) true ++ left := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] using ih

theorem headerTrace_last (n : Nat) (left tail : List Bool) :
    (headerTrace n left tail).getLast? =
      some (headerState (List.replicate n true ++ left) (false :: tail)) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
    have hne : headerTrace n (true :: left) tail ≠ [] := by
      have := headerTrace_length n (true :: left) tail
      intro h
      simp [h] at this
    rw [headerTrace, List.getLast?_cons_of_ne_nil hne, ih, replicate_push]

/-- Actual finite-control TM run on the self-delimiting numeric header.
The tape retains its payload and arbitrary suffix, and final HALT is real. -/
theorem header_runs (n : Nat) (tail : List Bool) :
    Runs headerMachine (List.replicate n true ++ false :: tail) (headerTrace n [] tail)
      (headerState (List.replicate n true) (false :: tail)) := by
  apply runs_of_chain
  · simpa [Turing.TM0.init, Turing.Tape.mk₁, headerState] using headerTrace_head n [] tail
  · exact headerTrace_chain n [] tail
  · simpa using headerTrace_last n [] tail
  · exact header_halt _ _

/-- A fixed Bool TM removes the true length header and returns the entire
false delimiter/payload/suffix with a linear actual trace and visited space. -/
theorem header_computes (n : Nat) (tail : List Bool) :
    computes headerMachine (List.replicate n true ++ false :: tail) (false :: tail)
      (n + 1) (3 * n + tail.length + 4) := by
  refine ⟨headerTrace n [] tail, headerState (List.replicate n true) (false :: tail),
    header_runs n tail, ?_, ?_, ?_⟩
  · simp [headerState, Turing.Tape.mk₂]
  · exact (headerTrace_length n [] tail).le
  · have h := visitedSpace_le headerMachine (List.replicate n true ++ false :: tail).length
      (headerTrace n [] tail)
    simp only [headerTrace_length, List.length_append, List.length_replicate, List.length_cons] at h ⊢
    omega

/-- This machine is applied directly to the ORIGINAL B23 binary encoding,
not a new unary-numeric input. The unary part is only its bit-length header. -/
theorem encodeNat_header_computes (value : Nat) (suffix : List Bool) :
    let payload := List.ofFn (fun position : Fin (natBits value) => value.testBit position.val)
    computes headerMachine (encodeNat value ++ suffix) (false :: (payload ++ suffix))
      (natBits value + 1) (4 * natBits value + suffix.length + 4) := by
  dsimp only
  have h := header_computes (natBits value)
    (List.ofFn (fun position : Fin (natBits value) => value.testBit position.val) ++ suffix)
  convert h using 1
  · simp [encodeNat, List.append_assoc]
  · simp only [List.length_append, List.length_ofFn]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMHeader003



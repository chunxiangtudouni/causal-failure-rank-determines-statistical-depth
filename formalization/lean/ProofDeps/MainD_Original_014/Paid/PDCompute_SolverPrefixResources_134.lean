module

public import Paid.PDCompute_SolverPaddingScalars_133

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)

/-- Prefix analysis of literal straight macros. A real trace is obtained
only after providing genuine FetchesCode and StraightCode, as in121. -/
def CodePrefixResources (input : List Cell) (code : List Instruction) (before : State) (region : Finset ℕ) (budget : ℕ) : Prop :=
  ∀ count ≤ code.length, ∀ after,linearExecute input (code.take count) before=some after →
    RegionMemory before after region ∧ RootD27.Bits.SafeBits after budget

theorem CodePrefixResources.full {input : List Cell} {code : List Instruction} {before after : State}
    {region : Finset ℕ} {budget : ℕ} (resources : CodePrefixResources input code before region budget)
    (execute : linearExecute input code before=some after) :
    RegionMemory before after region ∧ RootD27.Bits.SafeBits after budget :=
  resources code.length (le_refl _) after (by simpa only [List.take_length] using execute)

/-- Prefixes are split by actual successful execution of the first
macro. Concrete callers prove both macro resource predicates and the
literal execution; this theorem is not a machine oracle. -/
theorem CodePrefixResources.append {input : List Cell} {first second : List Instruction} {before middle : State}
    {region : Finset ℕ} {budget : ℕ} (left : CodePrefixResources input first before region budget)
    (right : CodePrefixResources input second middle region budget)
    (execute : linearExecute input first before=some middle) :
    CodePrefixResources input (first++second) before region budget := by
  intro count bound after executed
  by_cases short : count ≤ first.length
  · rw [List.take_append_of_le_length short] at executed
    exact left count short after executed
  · have full := left.full execute
    have split : (first++second).take count=first++second.take (count-first.length) := by
      rw [List.take_append,List.take_of_length_le (by omega)]
    rw [split,PDLower.CalibrationCompute.linearExecute_append,execute,Option.bind_some] at executed
    have tailBound : count-first.length ≤ second.length := by rw [List.length_append] at bound; omega
    have later:=right (count-first.length) tailBound after executed
    exact ⟨full.1.trans later.1,later.2⟩

end PDCompute.Solver

module
public import Paid.PDCompute_Pack_ArithmeticMemory_009

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver
open PDLower.CalibrationCompute (linearExecute linearExecute_append)

/-- Compose the already proved actual-prefix footprints of two literal
fragments. The first success is proved by its real execute lemma at use. -/
theorem header_prefix_append (input : List Cell) (first later : List Instruction)
    (before middle : State) (base : ℕ)
    (firstRun : linearExecute input first before=some middle)
    (firstMemory : ∀ count≤first.length,∀ after,
      linearExecute input (first.take count) before=some after → HeaderMemory before after base)
    (laterMemory : ∀ count≤later.length,∀ after,
      linearExecute input (later.take count) middle=some after → HeaderMemory middle after base) :
    ∀ count≤(first++later).length,∀ after,
      linearExecute input ((first++later).take count) before=some after → HeaderMemory before after base := by
  intro count bound after execute
  by_cases short : count≤first.length
  · rw [List.take_append_of_le_length short] at execute
    exact firstMemory count short after execute
  · have enough : first.length≤count := by omega
    rw [List.take_append,List.take_of_length_le enough,linearExecute_append,firstRun,Option.bind_some] at execute
    have head:=firstMemory first.length (le_refl _) middle (by simpa only [List.take_length] using firstRun)
    have tail:=laterMemory (count-first.length) (by rw [List.length_append] at bound;omega) after execute
    exact head.trans tail

end PDCompute.Pack

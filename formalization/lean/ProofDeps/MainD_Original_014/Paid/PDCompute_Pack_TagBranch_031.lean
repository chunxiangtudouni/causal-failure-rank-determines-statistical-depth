module
public import Paid.PDCompute_Pack_EntryValues_030
public import Paid.PDCompute_Pack_Fetch_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

def emissionPC (origin : ℕ) (entry : MenuEntry) : ℕ := match entry.action with
  | .test _ _ => origin+165
  | _ => origin+140
def tagBranchResult (before : State) (origin : ℕ) (entry : MenuEntry) : State := {before with pc:=emissionPC origin entry}

/-- Actual tag conditional. The only tested value is the result of the
real2-tag arithmetic already established by the read-entry fragment. -/
theorem tag_branch_step (program : Program) (input : List Cell) (origin : ℕ) (before : State) (entry : MenuEntry)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+139)
    (value : before.register .value=.natural (2-entryTag entry)) :
    step program input before=some (tagBranchResult before origin entry) := by
  have fetch : program[before.pc]?=some (.branchZero .value (origin+165) (origin+140)) := by
    rw [pc]
    exact entry_test_fetch program origin code
  simp only [step,fetch]
  obtain ⟨action,observation,repairs,failure⟩:=entry
  cases action <;> simp [Instruction.execute,value,entryTag,tagBranchResult,emissionPC,Cell.nat?]

theorem tag_branch_memory (before : State) (origin : ℕ) (entry : MenuEntry) (base : ℕ) :
    HeaderMemory before (tagBranchResult before origin entry) base :=
  HeaderMemory.of_unchanged base rfl rfl rfl

end PDCompute.Pack

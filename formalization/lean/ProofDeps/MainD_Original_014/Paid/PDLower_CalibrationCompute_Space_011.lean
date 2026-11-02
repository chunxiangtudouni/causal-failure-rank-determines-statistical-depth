module

public import Paid.PDLower_CalibrationCompute_Header_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem workspace_card (base M : ℕ) : (workspace base M).card = workspaceSize M := by
  unfold workspace
  rw [Finset.card_image_of_injective _ (by intro a b eq; exact Nat.add_left_cancel eq),Finset.card_range]

theorem Frame.live_subset {before after : State} {base M : ℕ} (frame : Frame before after base M) :
    after.live ⊆ before.live ∪ workspace base M := by
  intro address member
  by_cases inside : address ∈ workspace base M
  · exact Finset.mem_union.mpr (Or.inr inside)
  · exact Finset.mem_union.mpr (Or.inl ((frame.2 address inside).mp member))

theorem Frame.live_card_le {before after : State} {base M : ℕ} (frame : Frame before after base M) :
    after.live.card ≤ before.live.card+workspaceSize M := by
  calc
    _ ≤ (before.live ∪ workspace base M).card := Finset.card_le_card frame.live_subset
    _ ≤ before.live.card+(workspace base M).card := Finset.card_union_le _ _
    _ = _ := by rw [workspace_card]

theorem Frame.workingCells_le {before after : State} {base M : ℕ} (frame : Frame before after base M)
    (extra : List Cell) (output : after.output = before.output++extra) :
    workingCells after ≤ workingCells before+workspaceSize M+extra.length := by
  have live := frame.live_card_le
  simp only [workingCells,output,List.length_append]
  omega

theorem peakCells_le_of_forall (trace : List State) (bound : ℕ)
    (each : ∀ state ∈ trace,workingCells state ≤ bound) : peakCells trace ≤ bound := by
  have fold (values : List ℕ) : ∀ initial,initial ≤ bound → (∀ value ∈ values,value ≤ bound) →
      values.foldl max initial ≤ bound := by
    induction values with
    | nil => intro initial start _; exact start
    | cons value values ih =>
      intro initial start valuesBound
      exact ih (max initial value) (max_le start (valuesBound value (by simp)))
        (fun x member => valuesBound x (by simp only [List.mem_cons]; exact Or.inr member))
  apply fold (trace.map workingCells) 0 (Nat.zero_le _)
  intro value member
  obtain ⟨state,inTrace,eq⟩ := List.mem_map.mp member
  subst value
  exact each state inTrace

theorem peakCells_le_of_frames (trace : List State) (before : State) (base M : ℕ)
    (states : ∀ state ∈ trace,Frame before state base M ∧
      ∃ extra,state.output = before.output++extra ∧ extra.length ≤ rowWidth M) :
    peakCells trace ≤ workingCells before+workspaceSize M+rowWidth M := by
  apply peakCells_le_of_forall
  intro state member
  obtain ⟨frame,extra,output,length⟩ := states state member
  exact (frame.workingCells_le extra output).trans (by omega)

theorem standalone_peakCells_le (trace : List State) (before : State) (base M : ℕ)
    (inputRecords : workingCells before ≤ registers.length+rowWidth M)
    (states : ∀ state ∈ trace,Frame before state base M ∧
      ∃ extra,state.output = before.output++extra ∧ extra.length ≤ rowWidth M) :
    peakCells trace ≤ 38*(M+1) := by
  have peak := peakCells_le_of_frames trace before base M states
  have records := standaloneRecordEnvelope M
  omega

end PDLower.CalibrationCompute

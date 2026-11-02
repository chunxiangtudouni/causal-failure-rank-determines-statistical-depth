module

public import Paid.PDCompute_SolverABI_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

/-- Fixed six-cell WORKING representation. The returned original encoding
is separately serialized, so no fixed-width output format is substituted. -/
def denseEncodeEntry (entry : MenuEntry) : List Cell :=
  let action := match entry.action with
    | .finish => [.natural 0,.natural 0,.natural 0]
    | .abandon => [.natural 1,.natural 0,.natural 0]
    | .test level bad => [.natural 2,.natural level,.natural (if bad=.repair then 1 else 0)]
  action++[.rational entry.observation,.rational entry.repairs,.rational entry.failure]

def packDenseEntry : List Cell → List Cell
  | [tag,level,bad,observation,repairs,failure] =>
      if tag=.natural 2 then [tag,level,bad,observation,repairs,failure]
      else [tag,observation,repairs,failure]
  | _ => []

theorem denseEncodeEntry_length (entry : MenuEntry) : (denseEncodeEntry entry).length=entryWords := by
  obtain ⟨action,observation,repairs,failure⟩ := entry
  cases action <;> rfl

theorem packDenseEntry_exact (entry : MenuEntry) : packDenseEntry (denseEncodeEntry entry)=encodeEntry entry := by
  obtain ⟨action,observation,repairs,failure⟩ := entry
  cases action <;> simp [denseEncodeEntry,packDenseEntry,encodeEntry,encodeAction]

theorem encodeEntry_length_le (entry : MenuEntry) : (encodeEntry entry).length ≤ 6 := by
  obtain ⟨action,observation,repairs,failure⟩ := entry
  cases action <;> simp [encodeEntry,encodeAction]

theorem encodeEntries_length_le (entries : List MenuEntry) :
    (entries.flatMap encodeEntry).length ≤ 6*entries.length := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      have h := encodeEntry_length_le entry
      omega

theorem encodeRow_length_le (row : MenuRow) : (encodeRow row).length ≤ 1+6*row.size := by
  have h := encodeEntries_length_le row.toList
  simp only [Array.length_toList] at h
  simp only [encodeRow,encodeList,List.length_cons]
  omega

theorem encodeRows_length_le (rows : List MenuRow) (k : ℕ)
    (hrows : ∀ row ∈ rows, row.size ≤ k+1) :
    (rows.flatMap encodeRow).length ≤ rows.length*(1+6*(k+1)) := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      have hr := encodeRow_length_le row
      have hs := hrows row (by simp)
      have ht := ih (fun r hm => hrows r (by simp only [List.mem_cons]; exact Or.inr hm))
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      nlinarith

theorem encodeTable_length_le (table : MenuTable) (n k : ℕ) (hn : table.size ≤ n+1)
    (hrows : ∀ row ∈ table, row.size ≤ k+1) : (encodeTable table).length ≤ resultCapacity n k := by
  have h := encodeRows_length_le table.toList k (by simpa only [Array.mem_toList_iff] using hrows)
  simp only [Array.length_toList] at h
  have h' := h.trans (Nat.mul_le_mul_right _ hn)
  simp only [encodeTable,encodeList,List.length_cons,resultCapacity]
  omega

theorem cellBase_succ_column (base k row column : ℕ) :
    cellBase base k row (column+1)=cellBase base k row column+entryWords := by
  unfold cellBase
  ring

theorem denseCell_mem_workspace (base n k row column offset : ℕ) (hr : row ≤ n)
    (hc : column ≤ k) (hoff : offset < entryWords) :
    cellBase base k row column+offset ∈ workspace base n k := by
  have hrow := Nat.mul_le_mul_right (k+1) hr
  have hindex : row*(k+1)+column < entryCount n k := by unfold entryCount; nlinarith
  apply Finset.mem_image.mpr
  refine ⟨headerWords+entryWords*(row*(k+1)+column)+offset, ?_, ?_⟩
  · apply Finset.mem_range.mpr
    unfold workspaceSize resultCapacity
    unfold entryWords at hoff ⊢
    omega
  · unfold cellBase tableBase
    omega

end PDCompute.Solver

module
public import Paid.PDCompute_SolverDenseLayout_006

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver

/-- Fixed live header scratch. Original argument slots1,3,4 are retained. -/
def rowRemaining : ℕ := 40
def columnRemaining : ℕ := 41
def sourceCursor : ℕ := 42
def outputCursor : ℕ := 43
def outputStart : ℕ := 44
def columnsPerRow : ℕ := 47
def entryStart : ℕ := 24

def headerRegion (base : ℕ) : Finset ℕ := (Finset.range headerWords).image (base+·)
def resultRegion (base n k : ℕ) : Finset ℕ :=
  (Finset.range (resultCapacity n k)).image (resultBase base n k+·)
def writeRegion (base n k : ℕ) : Finset ℕ := headerRegion base ∪ resultRegion base n k

def actionSlots (action : MenuAction) : List ℕ := match action with
  | .test _ _ => [24,25,26,27,28,29]
  | _ => [24,27,28,29]

/-- Select actual dense cells; this is the source indexing lemma only,
not an execution shortcut or precomputed serialized-output assumption. -/
theorem selected_dense_is_original (entry : MenuEntry) :
    (actionSlots entry.action).map (fun slot =>
      (denseEncodeEntry entry)[slot-entryStart]?.getD (.natural 0))=encodeEntry entry := by
  obtain ⟨action,observation,repairs,failure⟩ := entry
  cases action <;> rfl

theorem original_entry_length (entry : MenuEntry) :
    (encodeEntry entry).length=(actionSlots entry.action).length := by
  rw [←selected_dense_is_original,List.length_map]

theorem original_entry_length_pos (entry : MenuEntry) : 4 ≤ (encodeEntry entry).length := by
  rw [original_entry_length]
  cases entry.action <;> norm_num [actionSlots]

theorem selected_slots_inside (action : MenuAction) :
    ∀ slot ∈ actionSlots action, entryStart ≤ slot ∧ slot < entryStart+6 := by
  cases action <;> simp [actionSlots,entryStart]

theorem dense_before_result (base n k row column offset : ℕ)
    (hr : row≤n) (hc : column≤k) (hoff : offset<entryWords) :
    cellBase base k row column+offset<resultBase base n k := by
  have hi : row*(k+1)+column<PDCompute.Solver.entryCount n k := by unfold PDCompute.Solver.entryCount; nlinarith
  unfold cellBase resultBase
  unfold entryWords at hoff ⊢
  omega

theorem result_after_header (base n k : ℕ) : base+headerWords≤resultBase base n k := by
  unfold resultBase tableBase
  omega

theorem dense_outside_writeRegion (base n k row column offset : ℕ)
    (hr : row≤n) (hc : column≤k) (hoff : offset<entryWords) :
    cellBase base k row column+offset ∉ writeRegion base n k := by
  have lower : base+headerWords≤cellBase base k row column+offset := by
    unfold cellBase tableBase
    omega
  have upper:=dense_before_result base n k row column offset hr hc hoff
  intro member
  rcases Finset.mem_union.mp member with header|result
  · obtain ⟨index,inside,eq⟩:=Finset.mem_image.mp header
    have bound:=Finset.mem_range.mp inside
    omega
  · obtain ⟨index,_,eq⟩:=Finset.mem_image.mp result
    omega

theorem encoding_capacity (table : MenuTable) (n k : ℕ)
    (rows : table.size=n+1) (columns : ∀ row∈table,row.size=k+1) :
    (encodeTable table).length≤resultCapacity n k :=
  encodeTable_length_le table n k rows.le (fun row member=>(columns row member).le)

end PDCompute.Pack

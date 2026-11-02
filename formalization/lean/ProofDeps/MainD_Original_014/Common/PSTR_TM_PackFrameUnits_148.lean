module
public import Common.PSTR_TM_PackRepairFrame_147
public import Common.PSTR_TM_PackZeroA_041
public import Common.PSTR_TM_PackZeroB_042

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackFrameUnits148
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036

def Safe (trace : List (MachineState 193)) : Prop :=
  ∀ configuration∈trace,PSTRTMPackFrameCode146.Outside configuration

theorem small (q : Fin 194) (hq : q.val<145) (left right : List Bool) :
    PSTRTMPackFrameCode146.Outside (state q left right) := Or.inl hq

theorem large (q : Fin 194) (hq : 186≤q.val) (left right : List Bool) :
    PSTRTMPackFrameCode146.Outside (state q left right) := Or.inr hq

theorem nil_safe : Safe [] := by intro configuration h; simp at h

theorem cons_safe (first : MachineState 193) (tail : List (MachineState 193))
    (hf : PSTRTMPackFrameCode146.Outside first) (ht : Safe tail) : Safe (first::tail) := by
  intro configuration hm
  rcases List.mem_cons.mp hm with he|he
  · subst configuration; exact hf
  · exact ht _ he

theorem singleton_safe (configuration : MachineState 193)
    (h : PSTRTMPackFrameCode146.Outside configuration) : Safe [configuration] :=
  cons_safe _ _ h nil_safe

theorem append_safe (first second : List (MachineState 193)) (hf : Safe first) (hs : Safe second) :
    Safe (first++second) := by
  intro configuration hm
  rcases List.mem_append.mp hm with hm|hm
  · exact hf _ hm
  · exact hs _ hm

theorem glue_safe (first second : List (MachineState 193)) (hf : Safe first) (hs : Safe second) :
    Safe (PSTRTMOverlap132.glue first second) := by
  intro configuration hm
  rcases List.mem_append.mp hm with hm|hm
  · exact hf _ (List.mem_of_mem_dropLast hm)
  · exact hs _ hm

theorem align_safe (trace : List (MachineState 134)) : Safe (trace.map liftAlign) := by
  intro configuration hm
  obtain ⟨old,_,he⟩ := List.mem_map.mp hm
  subst configuration
  exact PSTRTMPackFrameCode146.align_outside old

theorem dispatch_safe (bit : Bool) (left right : List Bool) :
    Safe (PSTRTMPackColumns038.dispatchTrace bit left right) := by
  cases bit <;> intro configuration hm
  all_goals
    simp only [PSTRTMPackColumns038.dispatchTrace,PSTRTMPackColumns038.dispatchFlag,
      List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl
  all_goals (apply small; decide)

theorem column_safe (a b : Bool) (left first tail : List Bool) :
    Safe (PSTRTMPackColumns038.columnTrace a b left first tail) := by
  apply append_safe _ _ (dispatch_safe _ _ _)
  apply append_safe _ _ (align_safe _)
  apply singleton_safe
  apply small
  decide

theorem endA_safe (bit : Bool) (left tail : List Bool) :
    Safe (PSTRTMPackZeroA041.endATrace bit left tail) := by
  cases bit <;> intro configuration hm
  all_goals
    simp only [PSTRTMPackZeroA041.endATrace,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals (apply small; decide)

theorem zeroA_safe (bit : Bool) (left tail : List Bool) :
    Safe (PSTRTMPackZeroA041.zeroATrace bit left tail) := by
  apply append_safe _ _ (endA_safe _ _ _)
  apply append_safe _ _ (align_safe _)
  apply singleton_safe
  apply small
  decide

theorem zeroB_tail_safe (bit : Bool) (left first : List Bool) :
    Safe (PSTRTMPackZeroB042.tailTrace bit left first) := by
  apply append_safe
  · apply singleton_safe; apply large; decide
  · apply append_safe _ _ (align_safe _)
    apply singleton_safe; apply small; decide

theorem zeroB_safe (bit : Bool) (left first : List Bool) :
    Safe (PSTRTMPackZeroB042.zeroBTrace bit left first) :=
  append_safe _ _ (dispatch_safe _ _ _) (append_safe _ _ (align_safe _) (zeroB_tail_safe _ _ _))

theorem clearFront_safe (left : List Bool) : Safe (PSTRTMPackFinishFrame143.clearFront left) := by
  intro configuration hm
  simp only [PSTRTMPackFinishFrame143.clearFront,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals (apply small; decide)

theorem clearBack_safe (left : List Bool) : Safe (PSTRTMPackFinishFrame143.clearBack left) := by
  intro configuration hm
  simp only [PSTRTMPackFinishFrame143.clearBack,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | (apply small; decide) | (apply large; decide)

theorem clear_safe (left : List Bool) : Safe (PSTRTMPackFinishFrame143.clearTrace left) :=
  glue_safe _ _ (clearFront_safe _) (clearBack_safe _)

theorem rewind_safe (archive previous right : List Bool) :
    Safe (PSTRTMPackFinishFrame143.rewindTrace archive previous right) := by
  induction previous generalizing right with
  | nil =>
    apply cons_safe
    · apply large; decide
    · apply singleton_safe; apply large; decide
  | cons bit previous ih =>
    apply cons_safe
    · apply large; decide
    · apply cons_safe
      · apply large; decide
      · exact ih _

theorem finish_safe (archive previous : List Bool) :
    Safe (PSTRTMPackFinishFrame143.finishTrace archive previous) :=
  append_safe _ _ (clear_safe _) (rewind_safe _ _ _)

/-- These existing physical units never enter the replaced padding label
range. Their SAME full traces are therefore valid for146, for all actual
left data, not just blank tape. The new padding is proved separately147. -/
theorem column_chain (a b : Bool) (left first tail : List Bool) :
    (PSTRTMPackColumns038.columnTrace a b left first tail).IsChain
      (fun before after => Turing.TM0.step PSTRTMPackFrameCode146.packMachine before=some after) :=
  PSTRTMPackFrameCode146.transfer_chain _ (column_safe _ _ _ _ _) (PSTRTMPackColumns038.column_chain _ _ _ _ _)

theorem zeroA_chain (bit : Bool) (left tail : List Bool) :
    (PSTRTMPackZeroA041.zeroATrace bit left tail).IsChain
      (fun before after => Turing.TM0.step PSTRTMPackFrameCode146.packMachine before=some after) :=
  PSTRTMPackFrameCode146.transfer_chain _ (zeroA_safe _ _ _) (PSTRTMPackZeroA041.zeroA_chain _ _ _)

theorem zeroB_chain (bit : Bool) (left first : List Bool) :
    (PSTRTMPackZeroB042.zeroBTrace bit left first).IsChain
      (fun before after => Turing.TM0.step PSTRTMPackFrameCode146.packMachine before=some after) :=
  PSTRTMPackFrameCode146.transfer_chain _ (zeroB_safe _ _ _) (PSTRTMPackZeroB042.zeroB_chain _ _ _)

theorem finish_chain (archive previous : List Bool) :
    (PSTRTMPackFinishFrame143.finishTrace archive previous).IsChain
      (fun before after => Turing.TM0.step PSTRTMPackFrameCode146.packMachine before=some after) :=
  PSTRTMPackFrameCode146.transfer_chain _ (finish_safe _ _) (PSTRTMPackFinishFrame143.finish_chain _ _)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackFrameUnits148

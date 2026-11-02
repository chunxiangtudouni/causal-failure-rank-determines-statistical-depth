module

public import Paid.PDLower_CalibrationCompute_BootstrapCellTrace_041
public import Paid.PDLower_CalibrationCompute_HeapAppend_042

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- Proof-side fragments of the ORIGINAL fixed standalone program. -/
def StandaloneSegment (input : List Cell) (before after : State) (budget : ℕ) : Prop :=
  ∃ trace : List State, trace.head?=some before ∧ trace.getLast?=some after ∧
    trace.IsChain (fun first later => step calibrate input first=some later) ∧
    time calibrate trace≤budget

theorem StandaloneSegment.trans {input : List Cell} {before middle after : State} {first later : ℕ}
    (earlier : StandaloneSegment input before middle first)
    (following : StandaloneSegment input middle after later) :
    StandaloneSegment input before after (first+later) := by
  obtain ⟨left,lh,ll,lc,lt⟩ := earlier
  obtain ⟨right,rh,rl,rc,rt⟩ := following
  refine ⟨PDMenu.ComputeFrame.joinTrace left right,?_,?_,
    PDMenu.ComputeFrame.joinTrace_chain _ _ _ _ middle lc rc ll rh,?_⟩
  · cases left with
    | nil => cases lh
    | cons head tail =>
      cases tail with
      | nil =>
        have hm : head=middle := Option.some.inj ll
        have hb : head=before := Option.some.inj lh
        exact rh.trans (congrArg some (hm.symm.trans hb))
      | cons next rest => exact lh
  · have nonempty : right≠[] := by intro eq; rw [eq] at rh; cases rh
    exact (List.getLast?_append_of_ne_nil left.dropLast nonempty).trans rl
  · exact (PDMenu.ComputeFrame.joinTrace_time_le _ left right middle ll).trans (Nat.add_le_add lt rt)

theorem StandaloneSegment.mono {input : List Cell} {before after : State} {first later : ℕ}
    (run : StandaloneSegment input before after first) (bound : first≤later) :
    StandaloneSegment input before after later := by
  obtain ⟨trace,head,last,chain,cost⟩ := run
  exact ⟨trace,head,last,chain,cost.trans bound⟩

theorem standalone_oneStep (input : List Cell) (before after : State)
    (actual : step calibrate input before=some after) : StandaloneSegment input before after 30 := by
  refine ⟨[before,after],rfl,rfl,?_,?_⟩
  · simpa only [List.isChain_cons_cons,List.isChain_singleton,and_true] using actual
  · exact (PDMenu.ComputeFrame.time_le_length calibrate [before,after]).trans (by simp only [List.length_cons,List.length_nil]; omega)

theorem bootstrapCopy_segment (input : List Cell) (before : State) (source destination remaining : ℕ) (value : Cell)
    (position : before.pc=mainStart+13)
    (old : before.register .old=.natural source) (address : before.register .address=.natural destination)
    (flag : before.register .flag=.natural remaining) (data : input[source]?=some value) :
    StandaloneSegment input before
      {bootstrapCopyResult before source destination remaining value with pc:=mainStart+12} 120 :=
  bootstrapCopy_trace input before source destination remaining value position old address flag data

end PDLower.CalibrationCompute

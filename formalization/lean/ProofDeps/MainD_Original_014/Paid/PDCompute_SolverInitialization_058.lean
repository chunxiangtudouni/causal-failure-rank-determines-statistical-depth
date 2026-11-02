module

public import Paid.RootD27Endpoint_HeaderInit_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

theorem workspace_zero_subset (base n k : ℕ) : workspace base 0 0 ⊆ workspace base n k := by
  have bound : workspaceSize 0 0 ≤ workspaceSize n k := by
    unfold workspaceSize headerWords entryWords entryCount resultCapacity
    nlinarith
  intro address member
  obtain ⟨offset,inside,rfl⟩ := Finset.mem_image.mp member
  refine Finset.mem_image.mpr ⟨offset,Finset.mem_range.mpr ?_,rfl⟩
  exact (Finset.mem_range.mp inside).trans_le bound

theorem Frame.enlarge {before after : State} {base n k largeN largeK : ℕ}
    (frame : Frame before after base n k) (included : workspace base n k ⊆ workspace base largeN largeK) :
    Frame before after base largeN largeK :=
  ⟨fun address outside => frame.1 address (fun inside => outside (included inside)),
    fun address outside => frame.2 address (fun inside => outside (included inside))⟩

/-- The exact generic producer from Root is adapted to ANY standalone
solver dimensions. All actual incoming register cells are saved by the
real code; there is no prefilled header or live-disjointness premise. -/
theorem solver_header_initialization (program : Program) (input : List Cell) (origin : ℕ)
    (before : State) (base n k : ℕ) (hpc : before.pc=origin)
    (hbase : before.register .fresh=.natural base)
    (hprologue : FetchesCode program before.pc solverPrologue)
    (hlead : FetchesCode program (origin+16) RootD27.Endpoint.paddingLeadCode)
    (hloop : FetchesCode program (origin+19) (baseRowCode (origin+19))) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤2460 ∧
      Header after base (initializedHeaderValues (solverPrologueResult before base) base) ∧
      (∀ slot (inside : slot<6), after.heap (base+slot)=
        (savedArguments before)[slot]'(by change slot<6; exact inside)) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+37 ∧
      Frame before after base n k ∧ after.output=before.output := by
  obtain ⟨trace,after,hh,hl,hchain,ht,header,afterBase,afterPC,frame,afterOutput⟩ :=
    RootD27.Endpoint.header_initialization_actual program input origin before base hpc hbase hprologue hlead hloop
  refine ⟨trace,after,hh,hl,hchain,ht,header,?_,afterBase,afterPC,
    frame.enlarge (workspace_zero_subset base n k),afterOutput⟩
  intro slot inside
  have represented := header.value slot (by change slot<48; omega)
  simp only [initializedHeaderValues,ite_eq_left inside] at represented
  exact represented.trans (PDLower.CalibrationCompute.HeapList.value (solverPrologue_arguments before base) slot
    (by change slot<6; exact inside))

end PDCompute.Solver

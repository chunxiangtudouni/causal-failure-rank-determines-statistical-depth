module

public import Paid.RootD27Endpoint_Padding_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (storeSlot)

theorem prologue_straight : StraightCode solverPrologue := by
  simp [StraightCode,solverPrologue,storeSlot,StraightInstruction]

/-- The complete original scalar entry really saves its six registers and
allocates all48 header cells before any header arithmetic is invoked. This
phase does not require a preinitialized header or fresh disjoint workspace. -/
theorem header_initialization_actual (program : Program) (input : List Cell) (origin : ℕ)
    (before : State) (base : ℕ) (hpc : before.pc=origin)
    (hbase : before.register .fresh=.natural base)
    (hprologue : FetchesCode program before.pc solverPrologue)
    (hlead : FetchesCode program (origin+16) paddingLeadCode)
    (hloop : FetchesCode program (origin+19) (baseRowCode (origin+19))) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤2460 ∧
      Header after base (initializedHeaderValues (solverPrologueResult before base) base) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+37 ∧
      PDCompute.Solver.Frame before after base 0 0 ∧ after.output=before.output := by
  let middle:=solverPrologueResult before base
  obtain ⟨lead,hlh,hll,hlc,hlt,_⟩ :=
    linearExecute_trace_time program input solverPrologue prologue_straight before middle
      hprologue (solverPrologue_execute input before base hbase)
  have hmPC : middle.pc=origin+16 := by
    change (solverPrologueResult before base).pc=origin+16
    rw [solverPrologue_pc,hpc]
  have hf : FetchesCode program middle.pc paddingLeadCode := by rw [hmPC]; exact hlead
  have hl : FetchesCode program ((origin+16)+3) (baseRowCode ((origin+16)+3)) := by
    have he : (origin+16)+3=origin+19 := by omega
    rw [he]
    exact hloop
  have firstSix : ∀ slot<6, base+slot∈middle.live := by
    intro slot inside
    exact (solverPrologue_arguments before base).1 slot inside
  obtain ⟨later,after,hrh,hrl,hrc,hrt,header,hb,hp,frame,hout⟩ :=
    padding_actual program input (origin+16) middle base hmPC
      ((solverPrologue_base before base).trans hbase) firstSix hf hl
  have leadTime : time program lead≤255 := hlt
  have joined:=joinTrace_spec program input lead later before middle after 255 2205
    hlh hll hrh hrl hlc hrc leadTime hrt
  refine ⟨joinTrace lead later,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2,header,hb,?_,?_,?_⟩
  · omega
  · exact (solverPrologue_frame before base 0 0).trans frame
  · exact hout.trans (solverPrologue_output before base)

end RootD27.Endpoint

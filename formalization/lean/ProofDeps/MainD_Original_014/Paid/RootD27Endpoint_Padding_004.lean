module

public import Paid.RootD27Endpoint_Code_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

def paddingLeadCode : List Instruction := paddingSetup++[.constant .flag (.natural 1)]

def paddingLeadResult (before : State) (base : ℕ) : State :=
  let a:=({before with pc:=before.pc+4}).set .address (.natural (base+6))
  let b:=a.set .index (.natural 7)
  b.set .flag (.natural 1)

theorem paddingLead_straight : StraightCode paddingLeadCode := by
  intro instruction member
  simp only [paddingLeadCode,paddingSetup,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at member
  rcases member with (h|h|h)|h <;> subst instruction <;> trivial

theorem paddingLead_execute (input : List Cell) (before : State) (base : ℕ)
    (hbase : before.register .fresh=.natural base) :
    linearExecute input paddingLeadCode before=some (paddingLeadResult before base) := by
  simp [paddingLeadCode,paddingSetup,paddingLeadResult,linearExecute,Instruction.execute,
    State.set,NatOp.eval,Cell.nat?,hbase,Nat.add_assoc]

theorem paddingLead_pc (before : State) (base : ℕ) :
    (paddingLeadResult before base).pc=before.pc+4 := rfl

theorem paddingLead_live (before : State) (base : ℕ) :
    (paddingLeadResult before base).live=before.live := rfl

theorem paddingLead_heap (before : State) (base : ℕ) :
    (paddingLeadResult before base).heap=before.heap := rfl

theorem paddingLead_output (before : State) (base : ℕ) :
    (paddingLeadResult before base).output=before.output := rfl

theorem paddingLead_registers (before : State) (base : ℕ) :
    (paddingLeadResult before base).register .fresh=before.register .fresh ∧
    (paddingLeadResult before base).register .address=.natural (base+6) ∧
    (paddingLeadResult before base).register .index=.natural 7 ∧
    (paddingLeadResult before base).register .flag=.natural 1 := by
  simp [paddingLeadResult,State.set]

/-- Actual four-instruction setup followed by the fixed seven-row write
loop. Existing live cells inside the workspace are permitted. All original
six saved arguments are retained; no desired cache is assumed here. -/
theorem padding_actual (program : Program) (input : List Cell) (origin : ℕ)
    (before : State) (base : ℕ) (hpc : before.pc=origin)
    (hbase : before.register .fresh=.natural base)
    (hfirst : ∀ slot<6, base+slot∈before.live)
    (hlead : FetchesCode program before.pc paddingLeadCode)
    (hloop : FetchesCode program (origin+3) (baseRowCode (origin+3))) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤2205 ∧
      Header after base (initializedHeaderValues before base) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+21 ∧
      PDCompute.Solver.Frame before after base 0 0 ∧ after.output=before.output := by
  let middle:=paddingLeadResult before base
  obtain ⟨lead,hlh,hll,hlc,hlt,_⟩ :=
    linearExecute_trace_time program input paddingLeadCode paddingLead_straight
      before middle hlead (paddingLead_execute input before base hbase)
  have fields:=paddingLead_registers before base
  have hmPC : middle.pc=(origin+3)+1 := by
    change before.pc+4=(origin+3)+1
    omega
  have hmlive : ∀ slot<6, base+slot∈middle.live := hfirst
  obtain ⟨later,after,hrh,hrl,hrc,hrt,header,hb,hp,frame,hout⟩ :=
    initializeHeaderLoop program input (origin+3) hloop middle base 0 0 hmPC
      (fields.1.trans hbase) fields.2.1 fields.2.2.1 fields.2.2.2 hmlive
  have hlbound : time program lead≤75 := hlt
  have joined:=joinTrace_spec program input lead later before middle after 75 2130
    hlh hll hrh hrl hlc hrc hlbound hrt
  refine ⟨joinTrace lead later,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2,header,hb,?_,?_,hout⟩
  · omega
  · have trivialFrame : PDCompute.Solver.Frame before middle base 0 0 :=
      ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩
    exact trivialFrame.trans frame

end RootD27.Endpoint

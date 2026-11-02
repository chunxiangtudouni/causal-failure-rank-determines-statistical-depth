module

public import Paid.PDLower_CalibrationCompute_StandaloneSegment_057

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def bootstrapStartCode : List Instruction :=
  [.constant .address (.natural 0),.loadInput .total .address,
   .constant .address (.natural 1),.loadInput .index .address,
   .constant .address (.natural 2),.loadInput .value .address,
   .constant .old (.natural 2),.natOp .multiply .flag .total .old,
   .constant .old (.natural 3),.natOp .add .flag .flag .old,
   .constant .address (.natural 0),.constant .old (.natural 3)]

def bootstrapStartResult (before : State) (P : Parameters) : State :=
  {before with
    pc:=before.pc+12,
    register:=Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update before.register .total (.natural P.certificate.M))
              .index (.natural P.certificate.Q))
            .value (.rational P.certificate.gamma))
          .old (.natural 3))
        .flag (.natural (P.certificate.M*2+3)))
      .address (.natural 0)}

theorem bootstrapStart_execute (P : Parameters) (before : State) :
    linearExecute (calibrationInput P) bootstrapStartCode before=some (bootstrapStartResult before P) := by
  simp [bootstrapStartCode,linearExecute,calibrationInput,Instruction.execute,State.set,NatOp.eval,
    Cell.nat?,bootstrapStartResult,Nat.add_assoc]
  funext register
  cases register <;> simp

theorem bootstrapStart_straight : PDMenu.ComputeFrame.StraightCode bootstrapStartCode := by
  intro instruction member
  simp only [bootstrapStartCode,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq <;> subst instruction <;> trivial

theorem bootstrapStart_fetch (offset : ℕ) (inside : offset<bootstrapStartCode.length) :
    calibrate[mainStart+offset]?=bootstrapStartCode[offset]? := by
  rw [calibrate_bootstrap_fetch]
  have bound : offset<12 := inside
  interval_cases offset <;> rfl

/-- Original readonly M,Q,gamma are actually loaded before the original
endpoint-copy loop; none is a literal parameter of the fixed program. -/
theorem bootstrapStart_segment (P : Parameters) (before : State) (position : before.pc=mainStart) :
    StandaloneSegment (calibrationInput P) before (bootstrapStartResult before P) 195 := by
  have fetch : PDMenu.ComputeFrame.FetchesCode calibrate before.pc bootstrapStartCode := by
    intro offset inside
    rw [position]
    exact bootstrapStart_fetch offset inside
  obtain ⟨trace,head,last,length,chain,_prefix⟩ :=
    PDMenu.ComputeFrame.linearExecute_trace calibrate (calibrationInput P) bootstrapStartCode bootstrapStart_straight
      before (bootstrapStartResult before P) fetch (bootstrapStart_execute P before)
  refine ⟨trace,head,last,chain,?_⟩
  have size : trace.length=13 := length
  exact (PDMenu.ComputeFrame.time_le_length calibrate trace).trans (by omega)

end PDLower.CalibrationCompute

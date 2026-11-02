module
public import Paid.PDCompute_Nat_EntryResources_015
public import Paid.PDCompute_Nat_SelectedPointerBits_018

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

/-- The source comes from the actual entry register. Real cache cursors,
including the M+1 terminating scan cursor and pair offset, are paid once
by the original scale; no workspace bound is imposed on ROM addresses. -/
theorem originalControlBudget_cursor (caller : State) (incoming source : ℕ) (P : Parameters) (fee penalty : ℚ)
    (n k origin span level extra : ℕ) (initial : RootD27.Bits.SafeBits caller incoming)
    (address : caller.register .address=.natural source) (bounded : level≤P.certificate.M+1) (small : extra≤2) :
    1+natBits (source+(1+2*level)+extra)≤originalControlBudget incoming P fee penalty n k origin span := by
  have sourceBits:=initial.register .address
  rw [address] at sourceBits
  change 1+natBits source≤ incoming at sourceBits
  have first:=Nat.mul_le_mul_right (2*(P.certificate.M+1)+2) (by omega : 1≤n+1)
  simp only [one_mul] at first
  have second:=Nat.mul_le_mul_left ((n+1)*(2*(P.certificate.M+1)+2)) (by omega : 1≤maximumMenuBits P fee+1)
  simp only [mul_one] at second
  have weight : P.certificate.M+1≤solverBitScale P fee penalty n k:=by unfold solverBitScale;omega
  have levelBits : natBits level≤P.certificate.M+2:=
    (natBits_mono bounded).trans (Nat.add_le_add_right (Nat.log2_le_self _) 1)
  have product:=natBits_mul_le 2 level
  have shift:=natBits_add_le 1 (2*level)
  have sourceAdd:=natBits_add_le source (1+2*level)
  have extraAdd:=natBits_add_le (source+(1+2*level)) extra
  have extraBits:=(natBits_mono small)
  have one : natBits 1=1:=by decide
  have two : natBits 2=2:=by decide
  unfold originalControlBudget
  omega

/-- Actual079 selected-pointer on the SAME entry-carried global budget.
All new scalar/address and PC premises are discharged from true source,
selected level and literal located code. Arbitrary old scratch is carried. -/
theorem selectedPointer_trace_original (mode : ReaderMode) (origin : ℕ) (input : List Cell)
    (P : Parameters) (fee penalty : ℚ) (caller before : State) (base n k source level : ℕ) (values : ℕ → Cell)
    (callerFresh : caller.register .fresh=.natural base) (callerSource : caller.register .address=.natural source)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hsource : values 0=.natural source) (hlevel : values 23=.natural level) (bounded : level≤P.certificate.M)
    (safe : RootD27.Bits.SafeBits before (originalControlBudget (PDCompute.Pack.initialBits caller) P fee penalty n k origin (solverCalleeCode mode origin).length))
    (fetch : FetchesCode (solverLocatedProgram mode origin) before.pc selectedPointerCode) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (selectedPointerResult before base source level) ∧
      trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧ time (solverLocatedProgram mode origin) trace≤225 ∧
      Header (selectedPointerResult before base source level) base (Function.update values 39 (.natural (source+(1+2*level)))) ∧
      Frame before (selectedPointerResult before base source level) base n k ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state
        (originalControlBudget (PDCompute.Pack.initialBits caller) P fee penalty n k origin (solverCalleeCode mode origin).length) := by
  have context:=controlContext_originalScale caller (PDCompute.Pack.initialBits caller) base n k origin (solverCalleeCode mode origin).length P fee penalty
    (PDCompute.Pack.initialBits_safe caller) callerFresh
  have targetBits:=originalControlBudget_cursor caller (PDCompute.Pack.initialBits caller) source P fee penalty n k origin (solverCalleeCode mode origin).length level 0
    (PDCompute.Pack.initialBits_safe caller) callerSource (by omega) (by decide)
  simp only [Nat.add_zero] at targetBits
  exact selectedPointer_trace_resources _ input before base source level n k _ values header fresh hsource hlevel safe context.header targetBits
    (SolverControlContext.block (before:=before) context selectedPointerCode (by rw [selectedPointerCode_length];decide) fetch) fetch

end PDCompute.NatControl

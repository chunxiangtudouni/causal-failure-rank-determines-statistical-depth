module

public import Paid.RootD27Core_ResourceEnvelope_093
public import Paid.PDROC_D27Prepare_Resources_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits

attribute [local irreducible] PolynomialBound

/-- The actual original numerical core scale is polynomial in the
ORIGINAL variable-gamma input expression, including all fee bits. -/
theorem sourceCoreScale_original_polynomial :
    PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>sourceCoreScale x.1 x.2) := by
  have hs:=PDROC.D27Prepare.Resources.size_pos
  have base:=PolynomialBound.size PDROC.D27Prepare.Resources.size
  have data:=PDROC.D27Prepare.Resources.dataWeight_polynomial
  let c (n : ℕ):=PolynomialBound.constant PDROC.D27Prepare.Resources.size n
  have stages : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.certificate.stages) :=
    base.mono (by intro x;unfold PDROC.D27Prepare.Resources.size variableGammaSize rawSize;omega)
  have tools : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.tools) :=
    stages.mono (fun x=>x.1.tools_lt_stages.le)
  have levels : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.certificate.M) :=
    data.mono (by intro x;unfold PDROC.D27Prepare.Resources.dataWeight PDROC.D27Prepare.Resources.countWeight;omega)
  have rows : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.certificate.Q) :=
    data.mono (by intro x;unfold PDROC.D27Prepare.Resources.dataWeight PDROC.D27Prepare.Resources.countWeight;omega)
  have rounds : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.bisectionBudget x.2) :=
    data.mono (by intro x;unfold PDROC.D27Prepare.Resources.dataWeight numericalSize;omega)
  have m1:=levels.add (c 1) hs
  have search:=(((rounds.add (c 2) hs).mul (stages.add (c 1) hs)).mul (tools.add (c 1) hs)).mul m1
  have calibration:=rows.mul (m1.mul m1)
  simpa only [sourceCoreScale,pow_two,Nat.mul_assoc] using search.add calibration hs

theorem sourceRecordSpace_original_polynomial :
    PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>sourceRecordSpace x.1) := by
  have hs:=PDROC.D27Prepare.Resources.size_pos
  have base:=PolynomialBound.size PDROC.D27Prepare.Resources.size
  have data:=PDROC.D27Prepare.Resources.dataWeight_polynomial
  let c (n : ℕ):=PolynomialBound.constant PDROC.D27Prepare.Resources.size n
  have stages : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.certificate.stages) :=
    base.mono (by intro x;unfold PDROC.D27Prepare.Resources.size variableGammaSize rawSize;omega)
  have tools : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.tools) :=
    stages.mono (fun x=>x.1.tools_lt_stages.le)
  have levels : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.certificate.M) :=
    data.mono (by intro x;unfold PDROC.D27Prepare.Resources.dataWeight PDROC.D27Prepare.Resources.countWeight;omega)
  exact ((stages.add (c 1) hs).mul (tools.add (c 1) hs)).add (levels.add (c 1) hs) hs

/-- One envelope for the proved raw preparation, numerical core time,
working records, complete operand budget and physical raw input length.
The constants/degree precede every P/fee. Actual VM execution remains a
separate required producer; this theorem supplies no execution oracle. -/
def vmEnvelope (prepareConstant prepareDegree pcUpper : ℕ) (P : Parameters) (fee : ℚ) : ℕ :=
  prepareConstant*(variableGammaSize P fee)^prepareDegree+
    300000*sourceCoreScale P fee+512*sourceRecordSpace P+
    PDCompute.CoreGlobalBudget.budget P fee pcUpper+24*variableGammaSize P fee+1

theorem vmEnvelope_original_uniform (prepareConstant prepareDegree pcUpper : ℕ) :
    ∃ C degree : ℕ,0<C ∧ ∀ (P : Parameters) (fee : ℚ),
      vmEnvelope prepareConstant prepareDegree pcUpper P fee≤C*(variableGammaSize P fee)^degree := by
  have hs:=PDROC.D27Prepare.Resources.size_pos
  let c (n : ℕ):=PolynomialBound.constant PDROC.D27Prepare.Resources.size n
  have prep : PolynomialBound PDROC.D27Prepare.Resources.size
      (fun x=>prepareConstant*(PDROC.D27Prepare.Resources.size x)^prepareDegree) := by
    unfold PolynomialBound
    exact ⟨prepareConstant+1,prepareDegree,by omega,fun x=>
      Nat.mul_le_mul_right ((PDROC.D27Prepare.Resources.size x)^prepareDegree) (by omega)⟩
  have cost:=(c 300000).mul sourceCoreScale_original_polynomial
  have space:=(c 512).mul sourceRecordSpace_original_polynomial
  have bits:=PDCompute.CoreGlobalBudget.budget_original_polynomial pcUpper
  have input:=(c 24).mul (PolynomialBound.size PDROC.D27Prepare.Resources.size)
  have bound:=(((((prep.add cost hs).add space hs).add bits hs).add input hs).add (c 1) hs)
  unfold PolynomialBound at bound
  obtain ⟨C,degree,positive,bounded⟩:=bound
  exact ⟨C,degree,positive,fun P fee=>bounded (P,fee)⟩

/-- Every actually fetched RAM instruction charges at least its real
five-word fetch. Thus transition-count bounds follow from the original
primitive time on the SAME valid trace, including the fetched HALT. -/
theorem trace_length_le_actual_time (program : Program) :
    ∀ trace : List State,(∀ state∈trace,∃ instruction,program[state.pc]?=some instruction) →
      trace.length≤time program trace := by
  intro trace
  induction trace with
  | nil => intro _;simp only [List.length_nil,time,primitiveTrace,List.flatMap_nil];exact Nat.le_refl 0
  | cons before tail ih =>
    intro fetches
    obtain ⟨instruction,fetched⟩:=fetches before (List.mem_cons_self)
    have later:=ih (fun state member=>fetches state (List.mem_cons_of_mem before member))
    have charged : 1 ≤ instruction.primitives.length := by
      simp only [Instruction.primitives,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
      omega
    have split : time program (before::tail)=instruction.primitives.length+time program tail := by
      simp only [time,primitiveTrace,List.flatMap_cons,fetched,Option.map_some,Option.getD_some,List.length_append]
    rw [split]
    simp only [List.length_cons]
    omega

theorem runs_length_le_actual_time (program : Program) (input : List Cell) (trace : List State) (final : State)
    (run : Runs program input trace final) : trace.length≤time program trace := by
  apply trace_length_le_actual_time program trace
  intro state member
  have inside:=PDROC.D27Prepare.Resources.runs_pc_lt program input trace final run state member
  exact ⟨program[state.pc],Array.getElem?_eq_some_iff.mpr ⟨inside,rfl⟩⟩

end RootD27.Core

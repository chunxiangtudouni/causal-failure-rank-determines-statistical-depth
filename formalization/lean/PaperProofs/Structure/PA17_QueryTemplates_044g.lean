module
public import PaperProofs.Structure.PA17_QueryTemplates_044f
public import PaperProofs.Structure.PA17_UniformGenerator_035e

/-! Static compiler certificates for the exact whole-query source templates.
These are finite syntactic checks; all target instructions are generated
from dimensions by the actual fixed-template compiler. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PaperProofs.Structure.LaminarTree.PA17QueryTemplates044g
open PA17UniformGenerator035b PA17UniformGenerator035d PA17ProgramTemplates041 PA17QueryTemplates044f

def exprBelowDec (limit : Nat) : (expression : Expr) → Decidable (expression.Below limit)
  | .constant _ => isTrue True.intro
  | .cell address => by change Decidable (address < limit); infer_instance
  | .input _ => isTrue True.intro
  | .binary _ left right => by
    letI := exprBelowDec limit left
    letI := exprBelowDec limit right
    change Decidable (left.Below limit ∧ right.Below limit)
    infer_instance

def exprInputsDec (limit : Nat) : (expression : Expr) → Decidable (expression.InputsBelow limit)
  | .constant _ | .cell _ => isTrue True.intro
  | .input address => by change Decidable (address < limit); infer_instance
  | .binary _ left right => by
    letI := exprInputsDec limit left
    letI := exprInputsDec limit right
    change Decidable (left.InputsBelow limit ∧ right.InputsBelow limit)
    infer_instance

@[instance_reducible] def scopedDec (scope : Finset Nat) : (template : Template) → Decidable (template.WellScoped scope)
  | .empty => isTrue True.intro
  | .word expression => by change Decidable (expression.cells ⊆ scope); infer_instance
  | .append left right => by
    letI := scopedDec scope left
    letI := scopedDec scope right
    change Decidable (left.WellScoped scope ∧ right.WellScoped scope)
    infer_instance
  | .repeat counter bound body => by
    letI := scopedDec (insert counter scope) body
    change Decidable (counter ∉ scope ∧ bound.cells ⊆ scope ∧ body.WellScoped (insert counter scope))
    infer_instance

@[instance_reducible] def belowDec (stack : Nat) : (template : Template) → Decidable (template.Below stack)
  | .empty => isTrue True.intro
  | .word expression => exprBelowDec stack expression
  | .append left right => by
    letI := belowDec stack left
    letI := belowDec stack right
    change Decidable (left.Below stack ∧ right.Below stack)
    infer_instance
  | .repeat counter bound body => by
    letI := exprBelowDec stack bound
    letI := belowDec stack body
    change Decidable (counter < stack ∧ bound.Below stack ∧ body.Below stack)
    infer_instance

@[instance_reducible] def stackDec (stack output : Nat) : (template : Template) → Decidable (template.StackFits stack output)
  | .empty => isTrue True.intro
  | .word expression => by change Decidable (stack + expression.size ≤ output); infer_instance
  | .append left right => by
    letI := stackDec stack output left
    letI := stackDec stack output right
    change Decidable (left.StackFits stack output ∧ right.StackFits stack output)
    infer_instance
  | .repeat _ bound body => by
    letI := stackDec stack output body
    change Decidable (stack + bound.size ≤ output ∧ body.StackFits stack output)
    infer_instance

@[instance_reducible] def inputsDec (limit : Nat) : (template : Template) → Decidable (template.InputsBelow limit)
  | .empty => isTrue True.intro
  | .word expression => exprInputsDec limit expression
  | .append left right => by
    letI := inputsDec limit left
    letI := inputsDec limit right
    change Decidable (left.InputsBelow limit ∧ right.InputsBelow limit)
    infer_instance
  | .repeat _ bound body => by
    letI := exprInputsDec limit bound
    letI := inputsDec limit body
    change Decidable (bound.InputsBelow limit ∧ body.InputsBelow limit)
    infer_instance

attribute [local instance] scopedDec belowDec stackDec inputsDec

@[instance_reducible] def avoidsDec (cursor : Nat) : (template : Template) →
    Decidable (PA17UniformGenerator035e.CountersAvoid cursor template)
  | .empty | .word _ => isTrue True.intro
  | .append left right => by
    letI := avoidsDec cursor left
    letI := avoidsDec cursor right
    change Decidable (PA17UniformGenerator035e.CountersAvoid cursor left ∧ PA17UniformGenerator035e.CountersAvoid cursor right)
    infer_instance
  | .repeat counter _ body => by
    letI := avoidsDec cursor body
    change Decidable (counter ≠ cursor ∧ PA17UniformGenerator035e.CountersAvoid cursor body)
    infer_instance

attribute [local instance] avoidsDec

theorem query_wellScoped : queryProgram.codeTemplate.WellScoped ∅ := by decide
theorem query_below : queryProgram.codeTemplate.Below 64 := by decide
theorem query_stackFits : queryProgram.codeTemplate.StackFits 64 1024 := by decide
theorem query_inputsBelow : queryProgram.codeTemplate.InputsBelow 3 := by decide

theorem wrapped_wellScoped : wrappedQuery.codeTemplate.WellScoped ∅ := by decide
theorem wrapped_below : wrappedQuery.codeTemplate.Below 64 := by decide
theorem wrapped_stackFits : wrappedQuery.codeTemplate.StackFits 64 1024 := by decide
theorem wrapped_inputsBelow : wrappedQuery.codeTemplate.InputsBelow 3 := by decide

theorem query_parentScoped : queryProgram.codeTemplate.WellScoped (insert 3 {1, 2}) := by decide
theorem wrapped_parentScoped : wrappedQuery.codeTemplate.WellScoped (insert 3 {1, 2}) := by decide
theorem query_countersAvoid : PA17UniformGenerator035e.CountersAvoid 0 queryProgram.codeTemplate := by decide
theorem wrapped_countersAvoid : PA17UniformGenerator035e.CountersAvoid 0 wrappedQuery.codeTemplate := by decide

end PaperProofs.Structure.LaminarTree.PA17QueryTemplates044g

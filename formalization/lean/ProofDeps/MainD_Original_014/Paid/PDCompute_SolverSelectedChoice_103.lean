module

public import Paid.PDCompute_SolverHeaderBlock_102
public import Paid.PDCompute_SolverSelectedRuntime_081
public import Paid.PDCompute_SolverTerminalFields_095
public import Paid.PDCompute_SolverSelectedFacts_082
public import Paid.PDCompute_SolverRatBranch_098

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

/-- The original strict outer comparison, executed by the fixed ISA.
Both code paths are literal parts of one input-independent program. -/
def selectedChoiceCode (mode : ReaderMode) (origin : ℕ) : List Instruction :=
  choiceCode (rationalBranchCode .less 28 24) (fun _ => selectedTestingCode mode) (fun _ => []) origin

def selectedChoiceValues (_mode : ReaderMode) (P : Parameters) (values : ℕ → Cell) (fee penalty score : ℚ)
    (previous : MenuRow) (tools source level : ℕ) : ℕ → Cell :=
  if score < penalty then selectedTestingValues P values fee penalty previous tools source level else values

theorem selectedChoice_trace_memory (mode : ReaderMode) (program : Program) (input : List Cell)
    (P : Parameters) (fee penalty score : ℚ) (previous : MenuRow) (tools source level : ℕ)
    (before : State) (base n k : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (hlevel : values 23=.natural level) (bound : level ≤ P.certificate.M)
    (hscore : values 28=.rational score) (hpenalty : values 24=.rational penalty)
    (hgo : values 10=.rational (previous.getD tools abandonEntry).observation)
    (hgr : values 11=.rational (previous.getD tools abandonEntry).repairs)
    (hgf : values 12=.rational (previous.getD tools abandonEntry).failure)
    (hbo : values 31=.rational (P.menuBadBranch fee penalty previous tools).2.observation)
    (hbr : values 32=.rational (P.menuBadBranch fee penalty previous tools).2.repairs)
    (hbf : values 33=.rational (P.menuBadBranch fee penalty previous tools).2.failure)
    (hb : values 34=.natural (if (P.menuBadBranch fee penalty previous tools).1=.repair then 1 else 0))
    (fetch : FetchesCode program before.pc (selectedChoiceCode mode before.pc)) :
    HeaderBlockRun program input before base n k
      (selectedChoiceValues mode P values fee penalty score previous tools source level)
      (before.pc+(selectedChoiceCode mode before.pc).length) 3300 := by
  let guard:=rationalBranchCode .less 28 24
  let first : ℕ → List Instruction:=fun _ => selectedTestingCode mode
  let second : ℕ → List Instruction:=fun _ => []
  have size : ∀ a b,(guard a b).length=8 := by intro a b; rfl
  have codeFetch : FetchesCode program before.pc (choiceCode guard first second before.pc) := fetch
  have guarded : HeaderBlockRun program input before base n k values
      (if decide (score < penalty) then choiceFirstPC before.pc else choiceSecondPC first before.pc) 135 := by
    exact rationalBranch_trace_memory program input before base n k 28 24
      (choiceSecondPC first before.pc) (choiceFirstPC before.pc) score penalty .less values
      header (by decide) (by decide) hscore hpenalty hbase
      (choice_guard_fetch guard first second program before.pc codeFetch)
  have firstRun : ∀ state : State, decide (score < penalty)=true → state.pc=choiceFirstPC before.pc →
      Header state base values → state.register .fresh=.natural base → HeaderMemory before state base →
      FetchesCode program state.pc (first (choiceFirstPC before.pc)) →
      HeaderBlockRun program input state base n k (selectedTestingValues P values fee penalty previous tools source level)
        (choiceFirstPC before.pc+(first (choiceFirstPC before.pc)).length) 3120 := by
    intro state _ statePC stateHeader stateBase memory stateFetch
    have stateSource:=EndpointSource.frame_of_avoids mode input P source base n k before state hsource avoids (memory.frame n k)
    obtain ⟨trace,after,head,last,chain,timeBound,afterHeader,_,afterBase,afterPC,frame,output,allMemory⟩:=
      selectedTesting_trace_memory mode program input P fee penalty previous tools source level state base n k values
        stateHeader stateBase stateSource avoids hsourceValue hlevel bound hgo hgr hgf hbo hbr hbf hb stateFetch
    exact ⟨trace,after,head,last,chain,timeBound,afterHeader,afterBase,by simpa only [statePC] using afterPC,
      frame,output,allMemory⟩
  have secondRun : ∀ state : State, decide (score < penalty)=false → state.pc=choiceSecondPC first before.pc →
      Header state base values → state.register .fresh=.natural base → HeaderMemory before state base →
      FetchesCode program state.pc (second (choiceSecondPC first before.pc)) →
      HeaderBlockRun program input state base n k values (choiceEndPC first second before.pc) 15 := by
    intro state _ statePC stateHeader stateBase _ _
    simpa only [choiceEndPC,second,List.length_nil,Nat.add_zero,statePC] using
      HeaderBlockRun.empty program input state base n k values stateHeader stateBase
  have run:=choice_compose_memory guard first second size program input before base n k before.pc 3120 15
    values (selectedTestingValues P values fee penalty previous tools source level) values (decide (score < penalty))
    codeFetch guarded firstRun secondRun
  have endPC:=choiceCode_end guard first second size before.pc
  simpa only [selectedChoiceValues,selectedChoiceCode,guard,first,second,decide_eq_true_eq,← endPC] using run

theorem selectedChoiceValues_dense (mode : ReaderMode) (P : Parameters) (values : ℕ → Cell)
    (fee penalty score : ℚ) (previous : MenuRow) (tools source level : ℕ)
    (abandon : DenseFields values abandonEntry) :
    DenseFields (selectedChoiceValues mode P values fee penalty score previous tools source level)
      (if score < penalty then P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level else abandonEntry) := by
  by_cases less : score < penalty
  · simp only [selectedChoiceValues,less,ite_true,DenseFields,selectedTestingValues]
    exact testingFieldsValues_original P _ fee penalty previous tools level
  · simpa only [selectedChoiceValues,less,ite_false] using abandon

end PDCompute.Solver

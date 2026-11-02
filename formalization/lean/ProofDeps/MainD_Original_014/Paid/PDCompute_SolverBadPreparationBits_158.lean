module

public import Paid.PDCompute_SolverObjectiveBits_157

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

theorem badPreparationCommands_evaluated_bits (values : ℕ → Cell) (fee penalty : ℚ) (entry : MenuEntry) (S L T budget : ℕ)
    (initial : HeaderValueBits values budget) (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (hobs : values 16=.rational entry.observation) (hrep : values 17=.rational entry.repairs) (hfail : values 18=.rational entry.failure)
    (observation : ratEncodingBits entry.observation≤S) (repairs : ratEncodingBits entry.repairs≤S) (failure : ratEncodingBits entry.failure≤S)
    (feeBits : ratEncodingBits fee≤L) (penaltyBits : ratEncodingBits penalty≤T)
    (room : 1+16*(2*(S+3)+L+T+1)≤budget) : HeaderEvaluatedBits budget badPreparationCommands values := by
  let R:=2*(S+3)
  have fields : S≤R := by dsimp only [R]; omega
  have roomR : 1+16*(R+L+T+1)≤budget := room
  have oneSize : ratEncodingBits (1:ℚ)=3 := by norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have zeroSize : ratEncodingBits (0:ℚ)=3 := by norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have repaired : ratEncodingBits (1+entry.repairs)≤R := by
    have add:=ratEncodingBits_add_le (1:ℚ) entry.repairs
    rw [oneSize] at add
    dsimp only [R]
    omega
  have numbers:=solverObjective_intermediate_bits (repairEntry entry) fee penalty R L T (observation.trans fields) repaired (failure.trans fields) feeBits penaltyBits
  have feeRepair : ratEncodingBits (fee*(1+entry.repairs))≤16*(R+L+T+1) := numbers.1
  have subtotal : ratEncodingBits (entry.observation+fee*(1+entry.repairs))≤16*(R+L+T+1) := numbers.2.1
  have penaltyFailure : ratEncodingBits (penalty*entry.failure)≤16*(R+L+T+1) := numbers.2.2.1
  have score : ratEncodingBits ((repairEntry entry).objective fee penalty)≤16*(R+L+T+1) := numbers.2.2.2
  let one:=Function.update values 40 (.rational entry.observation)
  let two:=Function.update one 29 (.rational 1)
  let three:=Function.update two 41 (.rational (1+entry.repairs))
  let four:=Function.update three 42 (.rational entry.failure)
  let five:=Function.update four 29 (.rational (fee*(1+entry.repairs)))
  let six:=Function.update five 30 (.rational (penalty*entry.failure))
  let seven:=Function.update six 28 (.rational (entry.observation+fee*(1+entry.repairs)))
  let eight:=Function.update seven 28 (.rational ((repairEntry entry).objective fee penalty))
  let nine:=Function.update eight 31 (.rational 0)
  let ten:=Function.update nine 32 (.rational 0)
  let eleven:=Function.update ten 33 (.rational 1)
  let twelve:=Function.update eleven 34 (.natural 0)
  let thirteen:=Function.update twelve 22 (.rational penalty)
  let fourteen:=Function.update thirteen 24 (.rational penalty)
  have oneBits : HeaderValueBits one budget := initial.update (by change 1+ratEncodingBits entry.observation≤budget; omega)
  have twoBits : HeaderValueBits two budget := oneBits.update (by change 1+ratEncodingBits (1:ℚ)≤budget; omega)
  have threeBits : HeaderValueBits three budget := twoBits.update (by change 1+ratEncodingBits (1+entry.repairs)≤budget; omega)
  have fourBits : HeaderValueBits four budget := threeBits.update (by change 1+ratEncodingBits entry.failure≤budget; omega)
  have fiveBits : HeaderValueBits five budget := fourBits.update (by change 1+ratEncodingBits (fee*(1+entry.repairs))≤budget; omega)
  have sixBits : HeaderValueBits six budget := fiveBits.update (by change 1+ratEncodingBits (penalty*entry.failure)≤budget; omega)
  have sevenBits : HeaderValueBits seven budget := sixBits.update (by change 1+ratEncodingBits (entry.observation+fee*(1+entry.repairs))≤budget; omega)
  have eightBits : HeaderValueBits eight budget := sevenBits.update (by change 1+ratEncodingBits ((repairEntry entry).objective fee penalty)≤budget; omega)
  have nineBits : HeaderValueBits nine budget := eightBits.update (by change 1+ratEncodingBits (0:ℚ)≤budget; omega)
  have tenBits : HeaderValueBits ten budget := nineBits.update (by change 1+ratEncodingBits (0:ℚ)≤budget; omega)
  have elevenBits : HeaderValueBits eleven budget := tenBits.update (by change 1+ratEncodingBits (1:ℚ)≤budget; omega)
  have twelveBits : HeaderValueBits twelve budget := elevenBits.update (by change 1+natBits 0≤budget; norm_num [natBits]; omega)
  have thirteenBits : HeaderValueBits thirteen budget := twelveBits.update (by change 1+ratEncodingBits penalty≤budget; omega)
  have fourteenBits : HeaderValueBits fourteen budget := thirteenBits.update (by change 1+ratEncodingBits penalty≤budget; omega)
  refine ⟨one,?_,oneBits,two,?_,twoBits,three,?_,threeBits,four,?_,fourBits,five,?_,fiveBits,six,?_,sixBits,seven,?_,sevenBits,
    eight,?_,eightBits,nine,?_,nineBits,ten,?_,tenBits,eleven,?_,elevenBits,twelve,?_,twelveBits,thirteen,?_,thirteenBits,fourteen,?_,fourteenBits,True.intro⟩
  all_goals simp [HeaderCommand.eval,one,two,three,four,five,six,seven,eight,nine,ten,eleven,twelve,thirteen,fourteen,
    hfee,hpenalty,hobs,hrep,hfail,Cell.rat?,RatOp.eval,repairEntry,MenuEntry.objective]

/-- Actual original fourteen-command repaired-candidate preparation.
All abandoned and repaired fields, temporary objectives and literals
have same-budget bits at EVERY original instruction prefix. -/
theorem badPreparation_trace_bits (program : Program) (input : List Cell) (before : State) (base n k budget S L T : ℕ)
    (values : ℕ → Cell) (fee penalty : ℚ) (entry : MenuEntry) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (hobs : values 16=.rational entry.observation) (hrep : values 17=.rational entry.repairs) (hfail : values 18=.rational entry.failure)
    (observation : ratEncodingBits entry.observation≤S) (repairs : ratEncodingBits entry.repairs≤S) (failure : ratEncodingBits entry.failure≤S)
    (feeBits : ratEncodingBits fee≤L) (penaltyBits : ratEncodingBits penalty≤T) (room : 1+16*(2*(S+3)+L+T+1)≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+(headerCode badPreparationCommands).length)≤budget)
    (fetch : FetchesCode program before.pc (headerCode badPreparationCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤2475 ∧
      Header after base (badPreparationValues values fee penalty entry) ∧ after.register .fresh=.natural base ∧
      after.pc=before.pc+(headerCode badPreparationCommands).length ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have bounded:=badPreparationCommands_evaluated_bits values fee penalty entry S L T budget (HeaderValueBits.of_safe header safe)
    hfee hpenalty hobs hrep hfail observation repairs failure feeBits penaltyBits room
  have commandCost : 165*(badPreparationCommands.length+1)=2475 := rfl
  simpa only [commandCost] using headerCode_trace_bits badPreparationCommands program input before base n k budget values
    (badPreparationValues values fee penalty entry) badPreparationCommands_valid header fresh
    (badPreparationCommands_eval values fee penalty entry hfee hpenalty hobs hrep hfail) safe bounded addressBits pcBits fetch

end PDCompute.Solver

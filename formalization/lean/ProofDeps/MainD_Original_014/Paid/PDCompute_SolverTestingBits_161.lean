module

public import Paid.PDCompute_SolverSequenceBits_155
public import Paid.PDCompute_SolverScalarBits_152
public import Paid.PDCompute_SolverTestingFields_074

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

theorem testingFieldsCommands_evaluated_bits (values : ℕ → Cell) (error charge : ℚ) (good bad : MenuEntry)
    (level repairFlag L S budget : ℕ) (initial : HeaderValueBits values budget)
    (he : values 26=.rational error) (hc : values 27=.rational charge)
    (hgo : values 10=.rational good.observation) (hgr : values 11=.rational good.repairs) (hgf : values 12=.rational good.failure)
    (hbo : values 31=.rational bad.observation) (hbr : values 32=.rational bad.repairs) (hbf : values 33=.rational bad.failure)
    (hl : values 23=.natural level) (hb : values 34=.natural repairFlag)
    (errorBits : ratEncodingBits error≤L) (chargeBits : ratEncodingBits charge≤L)
    (goBits : ratEncodingBits good.observation≤S) (grBits : ratEncodingBits good.repairs≤S) (gfBits : ratEncodingBits good.failure≤S)
    (boBits : ratEncodingBits bad.observation≤S) (brBits : ratEncodingBits bad.repairs≤S) (bfBits : ratEncodingBits bad.failure≤S)
    (room : 1+64*(L+S+1)≤budget) : HeaderEvaluatedBits budget testingFieldsCommands values := by
  have observation:=solverCandidate_intermediate_bits error charge good.observation bad.observation L S errorBits chargeBits goBits boBits
  have repairs:=solverCandidate_intermediate_bits error charge good.repairs bad.repairs L S errorBits chargeBits grBits brBits
  have failure:=solverCandidate_intermediate_bits error charge good.failure bad.failure L S errorBits chargeBits gfBits bfBits
  have levelBits : (.natural level : Cell).bits≤budget := by simpa only [hl] using initial 23 (by decide)
  have repairBits : (.natural repairFlag : Cell).bits≤budget := by simpa only [hb] using initial 34 (by decide)
  let a:=Function.update values 29 (.rational 1)
  let b:=Function.update a 29 (.rational (1-error))
  let c:=Function.update b 43 (.rational ((1-error)*good.observation))
  let d:=Function.update c 30 (.rational (error*bad.observation))
  let e:=Function.update d 43 (.rational ((1-error)*good.observation+error*bad.observation))
  let f:=Function.update e 43 (.rational (charge+((1-error)*good.observation+error*bad.observation)))
  let g:=Function.update f 44 (.rational ((1-error)*good.repairs))
  let h:=Function.update g 30 (.rational (error*bad.repairs))
  let i:=Function.update h 44 (.rational ((1-error)*good.repairs+error*bad.repairs))
  let j:=Function.update i 45 (.rational ((1-error)*good.failure))
  let l:=Function.update j 30 (.rational (error*bad.failure))
  let m:=Function.update l 45 (.rational ((1-error)*good.failure+error*bad.failure))
  let o:=Function.update m 40 (.natural 2)
  let p:=Function.update o 41 (.natural level)
  let q:=Function.update p 42 (.natural repairFlag)
  have aBits : HeaderValueBits a budget := initial.update (by change 1+ratEncodingBits (1:ℚ)≤budget; omega)
  have bBits : HeaderValueBits b budget := aBits.update (by change 1+ratEncodingBits (1-error)≤budget; omega)
  have cBits : HeaderValueBits c budget := bBits.update (by change 1+ratEncodingBits ((1-error)*good.observation)≤budget; omega)
  have dBits : HeaderValueBits d budget := cBits.update (by change 1+ratEncodingBits (error*bad.observation)≤budget; omega)
  have eBits : HeaderValueBits e budget := dBits.update (by change 1+ratEncodingBits ((1-error)*good.observation+error*bad.observation)≤budget; omega)
  have fBits : HeaderValueBits f budget := eBits.update (by change 1+ratEncodingBits (charge+((1-error)*good.observation+error*bad.observation))≤budget; omega)
  have gBits : HeaderValueBits g budget := fBits.update (by change 1+ratEncodingBits ((1-error)*good.repairs)≤budget; omega)
  have hBits : HeaderValueBits h budget := gBits.update (by change 1+ratEncodingBits (error*bad.repairs)≤budget; omega)
  have iBits : HeaderValueBits i budget := hBits.update (by change 1+ratEncodingBits ((1-error)*good.repairs+error*bad.repairs)≤budget; omega)
  have jBits : HeaderValueBits j budget := iBits.update (by change 1+ratEncodingBits ((1-error)*good.failure)≤budget; omega)
  have lBits : HeaderValueBits l budget := jBits.update (by change 1+ratEncodingBits (error*bad.failure)≤budget; omega)
  have mBits : HeaderValueBits m budget := lBits.update (by change 1+ratEncodingBits ((1-error)*good.failure+error*bad.failure)≤budget; omega)
  have oBits : HeaderValueBits o budget := mBits.update (by change 1+natBits 2≤budget; norm_num [natBits]; omega)
  have pBits : HeaderValueBits p budget := oBits.update levelBits
  have qBits : HeaderValueBits q budget := pBits.update repairBits
  refine ⟨a,?_,aBits,b,?_,bBits,c,?_,cBits,d,?_,dBits,e,?_,eBits,f,?_,fBits,g,?_,gBits,h,?_,hBits,i,?_,iBits,j,?_,jBits,
    l,?_,lBits,m,?_,mBits,o,?_,oBits,p,?_,pBits,q,?_,qBits,True.intro⟩
  all_goals simp [HeaderCommand.eval,a,b,c,d,e,f,g,h,i,j,l,m,o,p,q,he,hc,hgo,hgr,hgf,hbo,hbr,hbf,hl,hb,Cell.rat?,RatOp.eval]

/-- SAME original130-op actual selected-testing fields, ALL temporary
and output six cells have numerical same-budget guards discharged. -/
theorem testingFields_trace_bits (program : Program) (input : List Cell) (before : State) (base n k budget L S : ℕ)
    (values : ℕ → Cell) (error charge : ℚ) (good bad : MenuEntry) (level repairFlag : ℕ)
    (header : Header before base values) (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (he : values 26=.rational error) (hc : values 27=.rational charge)
    (hgo : values 10=.rational good.observation) (hgr : values 11=.rational good.repairs) (hgf : values 12=.rational good.failure)
    (hbo : values 31=.rational bad.observation) (hbr : values 32=.rational bad.repairs) (hbf : values 33=.rational bad.failure)
    (hl : values 23=.natural level) (hb : values 34=.natural repairFlag)
    (errorBits : ratEncodingBits error≤L) (chargeBits : ratEncodingBits charge≤L)
    (goBits : ratEncodingBits good.observation≤S) (grBits : ratEncodingBits good.repairs≤S) (gfBits : ratEncodingBits good.failure≤S)
    (boBits : ratEncodingBits bad.observation≤S) (brBits : ratEncodingBits bad.repairs≤S) (bfBits : ratEncodingBits bad.failure≤S)
    (room : 1+64*(L+S+1)≤budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (pcBits : natBits (before.pc+130)≤budget) (fetch : FetchesCode program before.pc (headerCode testingFieldsCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤2640 ∧
      Header after base (testingFieldsValues values error charge good bad level repairFlag) ∧ after.register .fresh=.natural base ∧
      after.pc=before.pc+130 ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have bounded:=testingFieldsCommands_evaluated_bits values error charge good bad level repairFlag L S budget (HeaderValueBits.of_safe header safe)
    he hc hgo hgr hgf hbo hbr hbf hl hb errorBits chargeBits goBits grBits gfBits boBits brBits bfBits room
  have codeLength : (headerCode testingFieldsCommands).length=130 := rfl
  have commandCost : 165*(testingFieldsCommands.length+1)=2640 := rfl
  simpa only [codeLength,commandCost] using headerCode_trace_bits testingFieldsCommands program input before base n k budget values
    (testingFieldsValues values error charge good bad level repairFlag) testingFieldsCommands_valid header fresh
    (testingFieldsCommands_eval values error charge good bad level repairFlag he hc hgo hgr hgf hbo hbr hbf hl hb) safe bounded addressBits pcBits fetch

end PDCompute.Solver

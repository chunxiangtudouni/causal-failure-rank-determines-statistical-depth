module

public import Paid.PDCompute_SolverEndpointFrame_033

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute linearExecute_append storeSlot storeSlotResult)
open PDMenu.ComputeFrame

def endpointHeaderCode (mode : ReaderMode) : List Instruction :=
  endpointPairCode mode++storeSlot 26 .total++storeSlot 27 .value

def endpointHeaderResult (before : State) (base address : ℕ) (error charge : ℚ) : State :=
  storeSlotResult (storeSlotResult (endpointPairResult before address error charge) base 26 .total) base 27 .value

theorem endpointHeaderCode_length (mode : ReaderMode) : (endpointHeaderCode mode).length=10 := rfl

theorem endpointHeaderCode_straight (mode : ReaderMode) : StraightCode (endpointHeaderCode mode) := by
  intro instruction member
  simp only [endpointHeaderCode,List.mem_append] at member
  rcases member with (member|member)|member
  · exact endpointPairCode_straight mode instruction member
  all_goals
    simp only [storeSlot,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h <;> subst instruction <;> trivial

theorem endpointHeaderCode_execute (mode : ReaderMode) (input : List Cell) (P : Parameters)
    (before : State) (base source index : ℕ) (hsource : EndpointSource mode input P source before)
    (hindex : index ≤ P.certificate.M) (hbase : before.register .fresh=.natural base)
    (haddress : before.register .address=.natural (source+(1+2*index))) :
    linearExecute input (endpointHeaderCode mode) before=
      some (endpointHeaderResult before base (source+(1+2*index))
        (P.cachedEndpoint P.endpointCache index).error (P.cachedEndpoint P.endpointCache index).charge) := by
  let paired := endpointPairResult before (source+(1+2*index))
    (P.cachedEndpoint P.endpointCache index).error (P.cachedEndpoint P.endpointCache index).charge
  let first := storeSlotResult paired base 26 .total
  have hp := endpointPairCode_original mode input P before source index hsource hindex haddress
  change linearExecute input (endpointPairCode mode) before=some paired at hp
  have hbp : paired.register .fresh=.natural base := by simp [paired,endpointPairResult,hbase]
  have hbf : first.register .fresh=.natural base := by simpa [first,storeSlotResult] using hbp
  have hf := PDLower.CalibrationCompute.storeSlot_execute input paired base 26 .total hbp (by decide)
  change linearExecute input (storeSlot 26 .total) paired=some first at hf
  have hl := PDLower.CalibrationCompute.storeSlot_execute input first base 27 .value hbf (by decide)
  change _=some (storeSlotResult first base 27 .value)
  simp only [endpointHeaderCode,linearExecute_append,hp,Option.bind_some,hf,hl]

theorem endpointHeaderResult_header (before : State) (base address : ℕ) (error charge : ℚ)
    (values : ℕ → Cell) (header : Header before base values) :
    Header (endpointHeaderResult before base address error charge) base
      (Function.update (Function.update values 26 (.rational error)) 27 (.rational charge)) := by
  let paired := endpointPairResult before address error charge
  let first := storeSlotResult paired base 26 .total
  have hp : Header paired base values := header
  have hf : Header first base (Function.update values 26 (.rational error)) := by
    apply Header.update hp 26 (.rational error)
    · simp [first,storeSlotResult,paired,endpointPairResult]
    · intro cell member
      exact Finset.mem_insert_of_mem member
  apply Header.update hf 27 (.rational charge)
  · simp [endpointHeaderResult,first,paired,storeSlotResult,endpointPairResult]
  · intro cell member
    exact Finset.mem_insert_of_mem member

theorem endpointHeaderResult_frame (before : State) (base address n k : ℕ) (error charge : ℚ) :
    Frame before (endpointHeaderResult before base address error charge) base n k := by
  let paired := endpointPairResult before address error charge
  let first := storeSlotResult paired base 26 .total
  have hf : Frame before first base n k := by
    apply slotWrite_frame before first base 26 n k (.rational error) (by decide)
    · simp [first,storeSlotResult,paired,endpointPairResult]
    · rfl
  apply hf.trans
  apply slotWrite_frame first _ base 27 n k (.rational charge) (by decide)
  · simp [endpointHeaderResult,first,paired,storeSlotResult,endpointPairResult]
  · rfl

end PDCompute.Solver

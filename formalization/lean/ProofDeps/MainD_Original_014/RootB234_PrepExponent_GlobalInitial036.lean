module

public import RootB234_PrepExponent_GlobalArithmetic035

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.Global
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

theorem pair_packets (x y : Rat) (tail : List Bool) :
    RatInput.Encoder.packet x (RatInput.Encoder.packet y tail)=RatPair.input x y tail :=
  RatPair.two_packet_format x y tail

theorem literal_pair_step (caller : Statement C) (site : MulSite) (background : Stack → List Bool)
    (memory : Store C) (cache exponent tail : List Bool) (value : Rat) :
    TM2.step (program caller) (state (.literal site) memory
      (bank background cache exponent (RatInput.Encoder.packet value tail) [] [] []))=
      some (state (.mul site default) memory (bank background cache exponent (RatPair.input 2 value tail) [] [] [])) := by
  have step := literal_step caller site memory (bank background cache exponent (RatInput.Encoder.packet value tail) [] [] [])
  rw [bank_update15] at step
  have cells : bank background cache exponent (RatInput.Encoder.packet value tail) [] [] [] 15=
      RatInput.Encoder.packet value tail := rfl
  have packet : RatInput.Encoder.packet (2 : Rat) []++RatInput.Encoder.packet value tail=RatPair.input 2 value tail :=
    (RatPair.packet_append 2 (RatInput.Encoder.packet value tail)).symm.trans (pair_packets 2 value tail)
  rw [cells,packet] at step
  exact step

theorem packet_layout (caller : Statement C) (site : PacketSite) (before after : State C)
    (value : Rat) (tail : List Bool) (active : before.l=some (.packet site 0))
    (source : before.stk (packetRoles site 15)=RatInput.Encoder.packet value tail)
    (temporary : before.stk (packetRoles site 4)=[])
    (endpoint : state (packetNext site) (before.var.1,false,false)
      (RatPacketTransport.atBank (packetRoles site) before.stk
        (if packetCopy site then RatInput.Encoder.packet value tail else tail) []
        (RatInput.Encoder.packet value (before.stk (packetRoles site 2))))=after) :
    ∃ part : Segment caller before after,part.trace.length ≤ 3*RatInput.Encoder.fieldSize value+14 := by
  obtain ⟨part,count⟩ := packet_from_state caller before site value tail active source temporary
  exact ⟨⟨part.trace,part.first,part.chain,part.last.trans (congrArg some endpoint)⟩,count⟩

theorem park15_actual (caller : Statement C) (site : PacketSite)
    (roles : packetRoles site=QLoop.parkRoles) (copy : packetCopy site=false)
    (background : Stack → List Bool) (memory : Store C) (cache exponent left right : List Bool) (value : Rat) :
    ∃ part : Segment caller
      (state (.packet site 0) memory (bank background cache exponent (RatInput.Encoder.packet value []) left right []))
      (state (packetNext site) (memory.1,false,false) (bank background (RatInput.Encoder.packet value cache) exponent [] left right [])),
      part.trace.length ≤ 3*RatInput.Encoder.fieldSize value+14 := by
  refine packet_layout caller site _ _ value [] rfl ?_ ?_ ?_
  · rw [roles];rfl
  · rw [roles];rfl
  · unfold state
    rw [roles,copy]
    congr 1
    funext slot
    fin_cases slot <;> rfl

theorem pull12_actual (caller : Statement C) (site : PacketSite)
    (roles : packetRoles site=QLoop.discardRoles) (copy : packetCopy site=false)
    (background : Stack → List Bool) (memory : Store C) (tail exponent input right : List Bool) (value : Rat) :
    ∃ part : Segment caller
      (state (.packet site 0) memory (bank background (RatInput.Encoder.packet value tail) exponent input [] right []))
      (state (packetNext site) (memory.1,false,false)
        (bank background tail exponent input (RatInput.Encoder.packet value []) right [])),
      part.trace.length ≤ 3*RatInput.Encoder.fieldSize value+14 := by
  refine packet_layout caller site _ _ value tail rfl ?_ ?_ ?_
  · rw [roles];rfl
  · rw [roles];rfl
  · unfold state
    rw [roles,copy]
    congr 1
    funext slot
    fin_cases slot <;> rfl

theorem copy7_actual (caller : Statement C) (site : PacketSite)
    (roles : packetRoles site=QLoop.copyRoles) (copy : packetCopy site=true)
    (background : Stack → List Bool) (memory : Store C) (tail exponent input left right : List Bool) (value : Rat) :
    ∃ part : Segment caller
      (state (.packet site 0) memory (bank background (RatInput.Encoder.packet value tail) exponent input left right []))
      (state (packetNext site) (memory.1,false,false)
        (bank background (RatInput.Encoder.packet value tail) exponent (RatInput.Encoder.packet value input) left right [])),
      part.trace.length ≤ 3*RatInput.Encoder.fieldSize value+14 := by
  refine packet_layout caller site _ _ value tail rfl ?_ ?_ ?_
  · rw [roles];rfl
  · rw [roles];rfl
  · unfold state
    rw [roles,copy]
    congr 1
    funext slot
    fin_cases slot <;> rfl

theorem pullQ_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (tail exponent input left : List Bool) (value : Rat) :
    ∃ part : Segment caller
      (state (.packet .pullQ 0) memory (bank background (RatInput.Encoder.packet value tail) exponent input left [] []))
      (state (.packet .copyBudget 0) (memory.1,false,false)
        (bank background tail exponent input left (RatInput.Encoder.packet value []) [])),
      part.trace.length ≤ 3*RatInput.Encoder.fieldSize value+14 := by
  refine packet_layout caller .pullQ _ _ value tail rfl rfl rfl ?_
  unfold state
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem restoreQ_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cache exponent input left : List Bool) (value : Rat) :
    ∃ part : Segment caller
      (state (.packet .restoreQ 0) memory (bank background cache exponent input left (RatInput.Encoder.packet value []) []))
      (state (.packet .restoreR 0) (memory.1,false,false)
        (bank background (RatInput.Encoder.packet value cache) exponent input left [] [])),
      part.trace.length ≤ 3*RatInput.Encoder.fieldSize value+14 := by
  refine packet_layout caller .restoreQ _ _ value [] rfl rfl rfl ?_
  unfold state
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem restore12_actual (caller : Statement C) (site : PacketSite)
    (roles : packetRoles site=packetRoles .restoreR) (copy : packetCopy site=false)
    (background : Stack → List Bool) (memory : Store C) (cache exponent input right : List Bool) (value : Rat) :
    ∃ part : Segment caller
      (state (.packet site 0) memory (bank background cache exponent input (RatInput.Encoder.packet value []) right []))
      (state (packetNext site) (memory.1,false,false)
        (bank background (RatInput.Encoder.packet value cache) exponent input [] right [])),
      part.trace.length ≤ 3*RatInput.Encoder.fieldSize value+14 := by
  refine packet_layout caller site _ _ value [] rfl ?_ ?_ ?_
  · rw [roles];rfl
  · rw [roles];rfl
  · unfold state
    rw [roles,copy]
    congr 1
    funext slot
    fin_cases slot <;> rfl

theorem seed_step (caller : Statement C) (background : Stack → List Bool) (memory : Store C) (cache : List Bool) :
    TM2.step (program caller) (state .seedE memory (bank background cache [] [] [] [] []))=
      some (state (.packet .compareCopyY 0) memory
        (bank background cache (B23_4_RatWordPrep.NatField.packet 1 []) [] [] [] [])) := by
  have updated : Function.update (bank background cache [] [] [] [] []) 11 (B23_4_RatWordPrep.NatField.packet 1 [])=
      bank background cache (B23_4_RatWordPrep.NatField.packet 1 []) [] [] [] [] := by
    funext slot
    fin_cases slot <;> rfl
  change some (TM2.stepAux (prepend 11 _ _) memory _)=_
  rw [prepend_step]
  change some (state (.packet .compareCopyY 0) memory
    (Function.update (bank background cache [] [] [] [] []) 11 ((B23_4_RatWordPrep.NatField.packet 1 [])++[])))=_
  rw [List.append_nil,updated]

def qValue (number : Nat) : Rat := 12*2^number
def rValue (number : Nat) : Rat := (2*(number : Rat))*qValue number

def initialCost (background : Stack → List Bool) (tail : List Bool) (budget : Rat) (number : Nat) : Nat :=
  let q := qValue number
  let r := rValue number
  let cache := RatInput.Encoder.packet q (RatInput.Encoder.packet budget tail)
  let rcache := RatInput.Encoder.packet r cache
  QLoop.fullCoefficient*(QLoop.fullScale background tail budget number)^5+
    13*NatToRat.scale (bank background cache [] [] [] [] []) number (RatInput.Encoder.packet q [])+
    RatBinary.time RatMulDiv.mulCoefficient (QLoop.rawBackground background cache []) 2 number (RatInput.Encoder.packet q []) cache+
    RatBinary.time RatMulDiv.mulCoefficient (QLoop.rawBackground background cache []) (2*(number : Rat)) q [] cache+
    RatBinary.time RatMulDiv.mulCoefficient (QLoop.rawBackground background rcache []) 2 budget [] rcache+
    40*(RatInput.Encoder.fieldSize q+RatInput.Encoder.fieldSize r+
      RatInput.Encoder.fieldSize budget+RatInput.Encoder.fieldSize (2*budget))+1000

theorem initial_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (tail : List Bool) (budget : Rat) (number : Nat)
    (input : background 8=B23_4_RatWordPrep.NatField.packet number []) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state default memory (QLoop.bank background tail [] (RatInput.Encoder.packet budget []) []))
      (state (.packet .compareCopyY 0) afterMemory
        (bank background
          (RatInput.Encoder.packet (2*budget) (RatInput.Encoder.packet (rValue number)
            (RatInput.Encoder.packet (qValue number) (RatInput.Encoder.packet budget tail))))
          (B23_4_RatWordPrep.NatField.packet 1 []) [] [] [] []))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧ afterMemory.2=(false,false) ∧
      part.trace.length ≤ initialCost background tail budget number := by
  let q := qValue number
  let r := rValue number
  let bcache := RatInput.Encoder.packet budget tail
  let cache := RatInput.Encoder.packet q bcache
  let rcache := RatInput.Encoder.packet r cache
  obtain ⟨qMemory,qPart,qContext,_qFlags,qCount,_qMass⟩ := q_actual caller background memory tail budget number input
  let qPart' : Segment caller
      (state default memory (QLoop.bank background tail [] (RatInput.Encoder.packet budget []) []))
      (state (.packet .copyQ 0) qMemory (bank background cache [] [] [] [] [])) :=
    ⟨qPart.trace,qPart.first,qPart.chain,qPart.last.trans (congrArg some (by rw [bank_empty];rfl))⟩
  obtain ⟨copyPart,copyCount⟩ := copyQ_actual caller background qMemory bcache [] q
  obtain ⟨natPart,natCount⟩ := nat_actual caller background (qMemory.1,false,false) cache []
    (RatInput.Encoder.packet q []) number input
  let literalN := Segment.edge (literal_pair_step caller .twiceN background (qMemory.1,false,false) cache []
    (RatInput.Encoder.packet q []) (number : Rat))
  obtain ⟨firstMemory,firstMul,firstContext,firstCount⟩ := mul_actual caller .twiceN background
    (qMemory.1,false,false) cache [] 2 number (RatInput.Encoder.packet q [])
  let firstMul' : Segment caller
      (state (.mul .twiceN default) (qMemory.1,false,false)
        (bank background cache [] (RatPair.input 2 number (RatInput.Encoder.packet q [])) [] [] []))
      (state (.mul .timesQ default) firstMemory (bank background cache [] (RatPair.input (2*(number : Rat)) q []) [] [] [])) :=
    ⟨firstMul.trace,firstMul.first,firstMul.chain,firstMul.last.trans (congrArg some (by rw [pair_packets];rfl))⟩
  obtain ⟨rMemory,rMul,rContext,rCount⟩ := mul_actual caller .timesQ background firstMemory cache [] (2*(number : Rat)) q []
  obtain ⟨parkR,parkRCount⟩ := park15_actual caller .parkR rfl rfl background rMemory cache [] [] [] r
  obtain ⟨pullR,pullRCount⟩ := pull12_actual caller .pullR rfl rfl background (rMemory.1,false,false) cache [] [] [] r
  obtain ⟨pullQ,pullQCount⟩ := pullQ_actual caller background (rMemory.1,false,false) bcache [] [] (RatInput.Encoder.packet r []) q
  obtain ⟨copyBudget,copyBudgetCount⟩ := copy7_actual caller .copyBudget rfl rfl background (rMemory.1,false,false)
    tail [] [] (RatInput.Encoder.packet r []) (RatInput.Encoder.packet q []) budget
  obtain ⟨restoreQ,restoreQCount⟩ := restoreQ_actual caller background (rMemory.1,false,false) bcache []
    (RatInput.Encoder.packet budget []) (RatInput.Encoder.packet r []) q
  obtain ⟨restoreR,restoreRCount⟩ := restore12_actual caller .restoreR rfl rfl background (rMemory.1,false,false) cache []
    (RatInput.Encoder.packet budget []) [] r
  let literalY := Segment.edge (literal_pair_step caller .firstY background (rMemory.1,false,false) rcache [] [] budget)
  obtain ⟨yMemory,yMul,yContext,yCount⟩ := mul_actual caller .firstY background (rMemory.1,false,false) rcache [] 2 budget []
  obtain ⟨parkY,parkYCount⟩ := park15_actual caller .parkY rfl rfl background yMemory rcache [] [] [] (2*budget)
  let seed := Segment.edge (seed_step caller background (yMemory.1,false,false) (RatInput.Encoder.packet (2*budget) rcache))
  let j1 := qPart'.append copyPart
  let j2 := j1.append natPart
  let j3 := j2.append literalN
  let j4 := j3.append firstMul'
  let j5 := j4.append rMul
  let j6 := j5.append parkR
  let j7 := j6.append pullR
  let j8 := j7.append pullQ
  let j9 := j8.append copyBudget
  let j10 := j9.append restoreQ
  let j11 := j10.append restoreR
  let j12 := j11.append literalY
  let j13 := j12.append yMul
  let j14 := j13.append parkY
  let whole := j14.append seed
  refine ⟨(yMemory.1,false,false),whole,yContext.trans (rContext.trans (firstContext.trans qContext)),rfl,?_⟩
  have literalNCount : literalN.trace.length=2 := rfl
  have literalYCount : literalY.trace.length=2 := rfl
  have seedCount : seed.trace.length=2 := rfl
  have qCount' : qPart'.trace.length ≤ QLoop.fullCoefficient*(QLoop.fullScale background tail budget number)^5 := qCount
  have firstCount' : firstMul'.trace.length ≤ RatBinary.time RatMulDiv.mulCoefficient
      (QLoop.rawBackground background cache []) 2 number (RatInput.Encoder.packet q []) cache := firstCount
  have c1 : j1.trace.length ≤ qPart'.trace.length+copyPart.trace.length := qPart'.append_length copyPart
  have c2 : j2.trace.length ≤ j1.trace.length+natPart.trace.length := j1.append_length natPart
  have c3 : j3.trace.length ≤ j2.trace.length+literalN.trace.length := j2.append_length literalN
  have c4 : j4.trace.length ≤ j3.trace.length+firstMul'.trace.length := j3.append_length firstMul'
  have c5 : j5.trace.length ≤ j4.trace.length+rMul.trace.length := j4.append_length rMul
  have c6 : j6.trace.length ≤ j5.trace.length+parkR.trace.length := j5.append_length parkR
  have c7 : j7.trace.length ≤ j6.trace.length+pullR.trace.length := j6.append_length pullR
  have c8 : j8.trace.length ≤ j7.trace.length+pullQ.trace.length := j7.append_length pullQ
  have c9 : j9.trace.length ≤ j8.trace.length+copyBudget.trace.length := j8.append_length copyBudget
  have c10 : j10.trace.length ≤ j9.trace.length+restoreQ.trace.length := j9.append_length restoreQ
  have c11 : j11.trace.length ≤ j10.trace.length+restoreR.trace.length := j10.append_length restoreR
  have c12 : j12.trace.length ≤ j11.trace.length+literalY.trace.length := j11.append_length literalY
  have c13 : j13.trace.length ≤ j12.trace.length+yMul.trace.length := j12.append_length yMul
  have c14 : j14.trace.length ≤ j13.trace.length+parkY.trace.length := j13.append_length parkY
  have c15 : whole.trace.length ≤ j14.trace.length+seed.trace.length := j14.append_length seed
  change whole.trace.length ≤ _
  unfold initialCost
  change whole.trace.length ≤ QLoop.fullCoefficient*(QLoop.fullScale background tail budget number)^5+
    13*NatToRat.scale (bank background cache [] [] [] [] []) number (RatInput.Encoder.packet q [])+
    RatBinary.time RatMulDiv.mulCoefficient (QLoop.rawBackground background cache []) 2 number (RatInput.Encoder.packet q []) cache+
    RatBinary.time RatMulDiv.mulCoefficient (QLoop.rawBackground background cache []) (2*(number : Rat)) q [] cache+
    RatBinary.time RatMulDiv.mulCoefficient (QLoop.rawBackground background rcache []) 2 budget [] rcache+
    40*(RatInput.Encoder.fieldSize q+RatInput.Encoder.fieldSize r+RatInput.Encoder.fieldSize budget+
      RatInput.Encoder.fieldSize (2*budget))+1000
  omega

end RootB234.PrepExponent.Global

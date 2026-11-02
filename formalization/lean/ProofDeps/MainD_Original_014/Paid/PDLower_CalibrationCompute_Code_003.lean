module

public import Paid.PDLower_CalibrationCompute_Primitives_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

inductive Label where
  | enter | enterBases | enterCache | enterBias | levelGate | levelInit | initGate | initCell | initCenter | initStore | stepStart
  | stepGate | zeroStart | zeroGate | zeroCell | scatterStart | scatterGate
  | leftRead | leftInterior | leftStore | rightRead | rightInterior | rightStore | scatterNext
  | stepNext | sumStart | sumGate | sumCell | sumFinish | weight | divide | zeroWeight | emit | finish
  deriving DecidableEq,Repr

def labels : List Label := [.enter,.enterBases,.enterCache,.enterBias,.levelGate,.levelInit,.initGate,.initCell,.initCenter,.initStore,.stepStart,
  .stepGate,.zeroStart,.zeroGate,.zeroCell,.scatterStart,.scatterGate,.leftRead,.leftInterior,.leftStore,
  .rightRead,.rightInterior,.rightStore,.scatterNext,.stepNext,.sumStart,.sumGate,.sumCell,.sumFinish,
  .weight,.divide,.zeroWeight,.emit,.finish]

inductive Control where
  | go (target : Label)
  | branch (condition : Register) (zero nonzero : Label)
  | returnToCaller

structure BasicBlock where
  body : List Instruction
  control : Control

def incrementSlot (offset : ℕ) : List Instruction :=
  loadSlot offset .index ++ [.constant .flag (.natural 1),.natOp .add .index .index .flag] ++ storeSlot offset .index

def constantSlot (offset : ℕ) (value : Cell) : List Instruction :=
  [.constant .value value] ++ storeSlot offset .value

/-- Pure literal ISA blocks: M,Q,gamma and endpoints occur only in actual
register/heap loads, never as program constants or cached-output oracles. -/
def basicBlock : Label → BasicBlock
  | .enter => ⟨prologue,.go .enterBases⟩
  | .enterBases => ⟨
      [.constant .flag (.natural 2),.natOp .multiply .index .total .flag,
       .constant .flag (.natural 3),.natOp .add .index .index .flag,
       .constant .old (.natural 16),.natOp .add .old .fresh .old] ++ storeSlot 9 .old ++
      [.natOp .add .total .old .index] ++ storeSlot 10 .total ++
      [.natOp .add .total .total .index] ++ storeSlot 15 .total,.go .enterCache⟩
  | .enterCache => ⟨loadSlot 2 .value ++
      [.constant .flag (.natural 1),.natOp .add .value .value .flag] ++ loadSlot 15 .index ++
      [.store .index .value,.output .value,.natOp .add .index .index .flag] ++ storeSlot 15 .index ++
      constantSlot 5 (.natural 1),.go .enterBias⟩
  | .enterBias => ⟨loadSlot 4 .value ++
      [.constant .flag (.rational (1/2)),.ratOp .subtract .old .flag .value,.ratOp .add .total .flag .value] ++
      storeSlot 12 .old ++ storeSlot 13 .total ++ constantSlot 6 (.natural 0) ++ constantSlot 7 (.natural 0) ++
      constantSlot 8 (.natural 0) ++ constantSlot 11 (.rational 0) ++ constantSlot 14 (.natural 0),.go .levelGate⟩
  | .levelGate => ⟨loadSlot 5 .index ++ loadSlot 2 .total ++
      [.constant .flag (.natural 1),.natOp .add .total .total .flag,.natCompare .lessEqual .flag .index .total],
      .branch .flag .finish .levelInit⟩
  | .levelInit => ⟨loadSlot 5 .index ++ [.constant .flag (.natural 2),.natOp .multiply .index .index .flag,
      .constant .flag (.natural 1),.natOp .add .index .index .flag] ++ storeSlot 8 .index ++
      [.constant .old (.natural 16),.natOp .add .old .fresh .old] ++ storeSlot 9 .old ++
      loadSlot 2 .index ++ [.constant .flag (.natural 2),.natOp .multiply .index .index .flag,
        .constant .flag (.natural 3),.natOp .add .index .index .flag,.natOp .add .total .old .index] ++
      storeSlot 10 .total ++ constantSlot 7 (.natural 0),.go .initGate⟩
  | .initGate => ⟨loadSlot 7 .index ++ loadSlot 8 .total ++ [.natCompare .less .flag .index .total],
      .branch .flag .stepStart .initCell⟩
  | .initCell => ⟨loadSlot 5 .total ++ [.natCompare .equal .flag .index .total,.constant .value (.rational 0)],
      .branch .flag .initStore .initCenter⟩
  | .initCenter => ⟨[.constant .value (.rational 1)],.go .initStore⟩
  | .initStore => ⟨loadSlot 9 .old ++ [.natOp .add .address .old .index,.store .address .value] ++ incrementSlot 7,.go .initGate⟩
  | .stepStart => ⟨constantSlot 6 (.natural 0),.go .stepGate⟩
  | .stepGate => ⟨loadSlot 6 .index ++ loadSlot 3 .total ++ [.natCompare .less .flag .index .total],
      .branch .flag .sumStart .zeroStart⟩
  | .zeroStart => ⟨constantSlot 7 (.natural 0),.go .zeroGate⟩
  | .zeroGate => ⟨loadSlot 7 .index ++ loadSlot 8 .total ++ [.natCompare .less .flag .index .total],
      .branch .flag .scatterStart .zeroCell⟩
  | .zeroCell => ⟨loadSlot 10 .old ++ [.natOp .add .address .old .index,.constant .value (.rational 0),.store .address .value] ++
      incrementSlot 7,.go .zeroGate⟩
  | .scatterStart => ⟨constantSlot 7 (.natural 0),.go .scatterGate⟩
  | .scatterGate => ⟨loadSlot 7 .index ++ loadSlot 8 .total ++ [.natCompare .less .flag .index .total],
      .branch .flag .stepNext .leftRead⟩
  | .leftRead => ⟨loadSlot 9 .old ++ [.natOp .add .address .old .index,.load .value .address] ++
      loadSlot 12 .old ++ [.ratOp .multiply .value .value .old] ++ loadSlot 8 .total ++
      [.constant .flag (.natural 1),.natOp .subtract .total .total .flag,.constant .old (.natural 0),
       .natCompare .equal .flag .index .old,.natCompare .equal .old .index .total,.natOp .add .flag .flag .old],
      .branch .flag .leftInterior .leftStore⟩
  | .leftInterior => ⟨[.constant .flag (.natural 1),.natOp .subtract .index .index .flag],.go .leftStore⟩
  | .leftStore => ⟨loadSlot 10 .old ++ [.natOp .add .address .old .index,.load .old .address,
      .ratOp .add .value .old .value,.store .address .value],.go .rightRead⟩
  | .rightRead => ⟨loadSlot 7 .index ++ loadSlot 9 .old ++ [.natOp .add .address .old .index,.load .value .address] ++
      loadSlot 13 .old ++ [.ratOp .multiply .value .value .old] ++ loadSlot 8 .total ++
      [.constant .flag (.natural 1),.natOp .subtract .total .total .flag,.constant .old (.natural 0),
       .natCompare .equal .flag .index .old,.natCompare .equal .old .index .total,.natOp .add .flag .flag .old],
      .branch .flag .rightInterior .rightStore⟩
  | .rightInterior => ⟨[.constant .flag (.natural 1),.natOp .add .index .index .flag],.go .rightStore⟩
  | .rightStore => ⟨loadSlot 10 .old ++ [.natOp .add .address .old .index,.load .old .address,
      .ratOp .add .value .old .value,.store .address .value],.go .scatterNext⟩
  | .scatterNext => ⟨incrementSlot 7,.go .scatterGate⟩
  | .stepNext => ⟨incrementSlot 6 ++ loadSlot 9 .old ++ loadSlot 10 .total ++ storeSlot 9 .total ++ storeSlot 10 .old,
      .go .stepGate⟩
  | .sumStart => ⟨constantSlot 11 (.rational 0) ++ constantSlot 7 (.natural 0),.go .sumGate⟩
  | .sumGate => ⟨loadSlot 7 .index ++ loadSlot 5 .total ++ [.natCompare .less .flag .index .total],
      .branch .flag .sumFinish .sumCell⟩
  | .sumCell => ⟨loadSlot 9 .old ++ [.natOp .add .address .old .index,.load .value .address] ++
      loadSlot 11 .old ++ [.ratOp .add .value .old .value] ++ storeSlot 11 .value ++ incrementSlot 7,.go .sumGate⟩
  | .sumFinish => ⟨loadSlot 5 .index ++ loadSlot 9 .old ++ [.natOp .add .address .old .index,.load .value .address,
      .constant .old (.rational (1/2)),.ratOp .multiply .value .value .old] ++
      loadSlot 11 .old ++ [.ratOp .add .value .old .value] ++ storeSlot 11 .value,.go .weight⟩
  | .weight => ⟨loadSlot 1 .old ++ loadSlot 5 .index ++
      [.constant .flag (.natural 2),.natOp .multiply .index .index .flag,.constant .flag (.natural 1),
       .natOp .subtract .index .index .flag,.natOp .add .address .old .index,.load .total .address,
       .constant .old (.rational (1/2)),.ratOp .subtract .total .old .total] ++ loadSlot 11 .value ++
      [.ratOp .subtract .value .old .value,.constant .old (.rational 0),.ratCompare .equal .flag .value .old],
      .branch .flag .divide .zeroWeight⟩
  | .divide => ⟨[.ratOp .divide .value .total .value],.go .emit⟩
  | .zeroWeight => ⟨[.constant .value (.rational 0)],.go .emit⟩
  | .emit => ⟨loadSlot 15 .index ++ loadSlot 11 .old ++ [.store .index .old,.constant .flag (.natural 1),
      .natOp .add .index .index .flag,.store .index .value,.output .old,.output .value,.natOp .add .index .index .flag] ++
      storeSlot 15 .index ++ incrementSlot 5,.go .levelGate⟩
  | .finish => ⟨loadSlot 0 .old ++ loadSlot 2 .index ++
      [.constant .flag (.natural 2),.natOp .multiply .index .index .flag,.constant .flag (.natural 3),
       .natOp .add .index .index .flag,.constant .flag (.natural 2),.natOp .multiply .value .index .flag,
       .constant .flag (.natural 16),.natOp .add .value .value .flag,.natOp .add .address .fresh .value],.returnToCaller⟩

def blockLength (label : Label) : ℕ := (basicBlock label).body.length+1

def labelAddress (origin : ℕ) (label : Label) : ℕ :=
  origin+((labels.take (labels.idxOf label)).map blockLength).sum

def controlInstruction (origin : ℕ) : Control → Instruction
  | .go target => .jump (labelAddress origin target)
  | .branch register zero nonzero => .branchZero register (labelAddress origin zero) (labelAddress origin nonzero)
  | .returnToCaller => .jumpIndirect .old

def compiledBlock (origin : ℕ) (label : Label) : List Instruction :=
  (basicBlock label).body ++ [controlInstruction origin (basicBlock label).control]

def kernel (origin : ℕ) : Program := (labels.flatMap (compiledBlock origin)).toArray

theorem compiledBlock_length (origin : ℕ) (label : Label) :
    (compiledBlock origin label).length = blockLength label := by
  simp only [compiledBlock,List.length_append,List.length_cons,List.length_nil,blockLength]

theorem labels_complete (label : Label) : label ∈ labels := by
  cases label <;> simp [labels]

end PDLower.CalibrationCompute

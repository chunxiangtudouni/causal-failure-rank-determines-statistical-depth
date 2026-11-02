module

public import Paid.PDLower_CalibrationCompute_Constants_021

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def enterBiasPrefixCode : List Instruction := loadSlot 4 .value ++
  [.constant .flag (.rational (1/2)),.ratOp .subtract .old .flag .value,.ratOp .add .total .flag .value]

def enterBiasComputed (before : State) (base : ℕ) (gamma : ℚ) : State :=
  let loaded := loadSlotResult before base 4 .value
  {loaded with
    pc := loaded.pc+3
    register := Function.update
      (Function.update (Function.update loaded.register .flag (.rational (1/2)))
        .old (.rational (1/2-gamma)))
      .total (.rational (1/2+gamma))}

def enterBiasResult (before : State) (base : ℕ) (gamma : ℚ) : State :=
  let a := enterBiasComputed before base gamma
  let b := storeSlotResult a base 12 .old
  let c := storeSlotResult b base 13 .total
  let d := constantSlotResult c base 6 (.natural 0)
  let e := constantSlotResult d base 7 (.natural 0)
  let f := constantSlotResult e base 8 (.natural 0)
  let g := constantSlotResult f base 11 (.rational 0)
  constantSlotResult g base 14 (.natural 0)

theorem enterBiasPrefix_execute (input : List Cell) (before : State) (base : ℕ) (gamma : ℚ)
    (fresh : before.register .fresh = .natural base)
    (gammaLive : base+4 ∈ before.live) (gammaValue : before.heap (base+4) = .rational gamma) :
    linearExecute input enterBiasPrefixCode before = some (enterBiasComputed before base gamma) := by
  simp [enterBiasPrefixCode,linearExecute,loadSlot,Instruction.execute,State.set,NatOp.eval,RatOp.eval,
    Cell.nat?,Cell.rat?,fresh,gammaLive,gammaValue,enterBiasComputed,loadSlotResult,Nat.add_assoc]

theorem enterBiasComputed_fresh (before : State) (base : ℕ) (gamma : ℚ) :
    (enterBiasComputed before base gamma).register .fresh = before.register .fresh := by
  simp [enterBiasComputed,loadSlotResult]

theorem enterBias_execute (input : List Cell) (before : State) (base : ℕ) (gamma : ℚ)
    (fresh : before.register .fresh = .natural base)
    (gammaLive : base+4 ∈ before.live) (gammaValue : before.heap (base+4) = .rational gamma) :
    linearExecute input (basicBlock .enterBias).body before = some (enterBiasResult before base gamma) := by
  let a := enterBiasComputed before base gamma
  let b := storeSlotResult a base 12 .old
  let c := storeSlotResult b base 13 .total
  let d := constantSlotResult c base 6 (.natural 0)
  let e := constantSlotResult d base 7 (.natural 0)
  let f := constantSlotResult e base 8 (.natural 0)
  let g := constantSlotResult f base 11 (.rational 0)
  have fa : a.register .fresh = .natural base := by simpa only [a,enterBiasComputed_fresh] using fresh
  have fb : b.register .fresh = .natural base := by simpa [b,storeSlotResult] using fa
  have fc : c.register .fresh = .natural base := by simpa [c,storeSlotResult] using fb
  have fd : d.register .fresh = .natural base := (constantSlot_fresh c base 6 (.natural 0)).trans fc
  have fe : e.register .fresh = .natural base := (constantSlot_fresh d base 7 (.natural 0)).trans fd
  have ff : f.register .fresh = .natural base := (constantSlot_fresh e base 8 (.natural 0)).trans fe
  have fg : g.register .fresh = .natural base := (constantSlot_fresh f base 11 (.rational 0)).trans ff
  have code : (basicBlock .enterBias).body = enterBiasPrefixCode ++ storeSlot 12 .old ++ storeSlot 13 .total ++
      constantSlot 6 (.natural 0) ++ constantSlot 7 (.natural 0) ++ constantSlot 8 (.natural 0) ++
      constantSlot 11 (.rational 0) ++ constantSlot 14 (.natural 0) := by
    simp only [basicBlock,enterBiasPrefixCode,List.append_assoc]
  change linearExecute input (basicBlock .enterBias).body before = some (constantSlotResult g base 14 (.natural 0))
  rw [code]
  simp only [List.append_assoc]
  rw [linearExecute_append,enterBiasPrefix_execute input before base gamma fresh gammaLive gammaValue,Option.bind_some]
  rw [linearExecute_append,storeSlot_execute input a base 12 .old fa (by decide),Option.bind_some]
  rw [linearExecute_append,storeSlot_execute input b base 13 .total fb (by decide),Option.bind_some]
  rw [linearExecute_append,constantSlot_execute input c base 6 (.natural 0) fc,Option.bind_some]
  rw [linearExecute_append,constantSlot_execute input d base 7 (.natural 0) fd,Option.bind_some]
  rw [linearExecute_append,constantSlot_execute input e base 8 (.natural 0) fe,Option.bind_some]
  rw [linearExecute_append,constantSlot_execute input f base 11 (.rational 0) ff,Option.bind_some]
  exact constantSlot_execute input g base 14 (.natural 0) fg

theorem enterBias_output (before : State) (base : ℕ) (gamma : ℚ) :
    (enterBiasResult before base gamma).output = before.output := rfl

theorem enterBias_pc (before : State) (base : ℕ) (gamma : ℚ) :
    (enterBiasResult before base gamma).pc = before.pc+32 := by
  simp [enterBiasResult,enterBiasComputed,loadSlotResult,constantSlotResult,storeSlotResult,State.set,Nat.add_assoc]

end PDLower.CalibrationCompute

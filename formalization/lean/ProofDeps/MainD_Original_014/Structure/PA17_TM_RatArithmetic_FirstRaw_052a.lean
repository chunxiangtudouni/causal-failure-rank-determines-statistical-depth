module
public import Structure.PA17_TM_RatArithmetic_MulStart_049d

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFirstRaw052
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticMulStart049
attribute [local implicit_reducible] stageCap mulStartCap

/-- A fixed finite table on actual049 HALT labels. The original operands
and their observed memory are never arguments of this code. -/
def decodedMemory (k : Nat) (q : Fin (mulStartCap k+1)) : Fin 64 :=
  ⟨((localOf (p:=2) (s:=stageCap k) q).val/8)%64,Nat.mod_lt _ (by decide)⟩

theorem decodedMemory_home (k : Nat) (memory : Fin 64) (sx : Bool) (counter bank : List Bool) :
    decodedMemory k (homeFinal k memory sx counter bank).q=memory := by
  apply Fin.ext
  change ((localOf (p:=2) (s:=stageCap k)
    (label (2 : Fin 3) (padLabel (home_le_stage k) (label memory (7 : Fin 8))))).val/8)%64=memory.val
  rw [localOf_label]
  change ((memory.val*8+7)/8)%64=memory.val
  rw [Nat.mul_comm memory.val 8,Nat.mul_add_div (by decide),show 7/8=0 from rfl,Nat.add_zero,
    Nat.mod_eq_of_lt memory.isLt]

theorem decodedMemory_original (k : Nat) (x y : Rat) :
    decodedMemory k (originalFinal k x y).q=actualMemory x y := decodedMemory_home _ _ _ _ _

def commonCap (k states : Nat) : Nat := mulStartCap k+states
def bridgeCap (k states : Nat) : Nat := totalStates 1 (commonCap k states)
attribute [local implicit_reducible] commonCap bridgeCap

theorem prefix_le_common (k states : Nat) : mulStartCap k≤commonCap k states := by unfold commonCap;omega
theorem consumer_le_common (k states : Nat) : states≤commonCap k states := by unfold commonCap;omega

def checkedIndex (small large : Nat) (q : Fin (large+1)) : Fin (small+1) :=
  if h : q.val<small+1 then ⟨q.val,h⟩ else 0

theorem checkedIndex_pad {small large : Nat} (h : small≤large) (q : Fin (small+1)) :
    checkedIndex small large (padLabel h q)=q := by
  unfold checkedIndex
  split_ifs with bound
  · apply Fin.ext
    rfl
  · exact (bound q.isLt).elim

def prefixCode (k states : Nat) (q : Fin (commonCap k states+1)) : Fin (mulStartCap k+1) :=
  checkedIndex (mulStartCap k) (commonCap k states) q

theorem prefixCode_pad (k states : Nat) (q : Fin (mulStartCap k+1)) :
    prefixCode k states (padLabel (prefix_le_common k states) q)=q := by
  exact checkedIndex_pad (small:=mulStartCap k) (large:=commonCap k states) (prefix_le_common k states) q

def bridgeFamily {states : Nat} (k : Nat) (consumer : Machine states) (phase : Fin 2) :
    Machine (commonCap k states) :=
  if phase.val=0 then padMachine (prefix_le_common k states) (mulStartMachine k)
  else padMachine (consumer_le_common k states) consumer

def bridgePorts (k states : Nat) (entry : Fin 64→Fin (states+1)) (phase : Fin 2)
    (q : Fin (commonCap k states+1)) : Option (Fin 2 × Fin (commonCap k states+1)) :=
  if phase.val=0 then some (1,padLabel (consumer_le_common k states)
    (entry (decodedMemory k (prefixCode k states q)))) else none

/-- The consumer and all64 entry ports are compiled before any original
input. A local049 HALT really writes its current symbol to itself and
enters the consumer's actual memory row. -/
def bridgeMachine {states : Nat} (k : Nat) (consumer : Machine states) (entry : Fin 64→Fin (states+1)) :
    Machine (bridgeCap k states) := blockMachine (bridgeFamily k consumer) (bridgePorts k states entry)

def prefixFinal (k states : Nat) (x y : Rat) : MachineState (bridgeCap k states) :=
  blockCfg (0 : Fin 2) (padCfg (prefix_le_common k states) (originalFinal k x y))

def consumerState (k states : Nat) (q : Fin (states+1)) (tape : Tape Bool) :
    MachineState (bridgeCap k states) :=
  blockCfg (1 : Fin 2) (padCfg (consumer_le_common k states) (⟨q,tape⟩ : MachineState states))

theorem actual_transfer {states : Nat} (k : Nat) (consumer : Machine states)
    (entry : Fin 64→Fin (states+1)) (x y : Rat)
    (halt : TM0.step (mulStartMachine k) (originalFinal k x y)=none) :
    TM0.step (bridgeMachine k consumer entry) (prefixFinal k states x y)=
      some (consumerState k states (entry (actualMemory x y)) (originalFinal k x y).Tape) := by
  let last := padCfg (prefix_le_common k states) (originalFinal k x y)
  have hf : TM0.step (bridgeFamily k consumer (0 : Fin 2)) last=none := by
    change TM0.step (padMachine (prefix_le_common k states) (mulStartMachine k)) last=none
    simp only [last,pad_step,halt,Option.map_none]
  have port : bridgePorts k states entry (0 : Fin 2) last.q=
      some (1,padLabel (consumer_le_common k states) (entry (actualMemory x y))) := by
    simp only [bridgePorts,Fin.val_zero,ite_true,last,padCfg,prefixCode_pad,decodedMemory_original]
  have ht := block_transfer (bridgeFamily k consumer) (bridgePorts k states entry) (0 : Fin 2) last
    (1,padLabel (consumer_le_common k states) (entry (actualMemory x y))) hf port
  exact ht

theorem bridgeCap_eq (k states : Nat) : bridgeCap k states=47520*k+2*states+15937217 := by
  simp only [bridgeCap,commonCap,totalStates,mulStartCap_eq]
  omega

theorem consumerState_label (k states : Nat) (q : Fin (states+1)) (tape : Tape Bool) :
    (consumerState k states q tape).q.val=commonCap k states+1+q.val := by
  simp only [consumerState,blockCfg,label,padCfg,padLabel,Fin.val_one,Nat.one_mul]

theorem consumerState_tape (k states : Nat) (q : Fin (states+1)) (tape : Tape Bool) :
    (consumerState k states q tape).Tape=tape := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFirstRaw052

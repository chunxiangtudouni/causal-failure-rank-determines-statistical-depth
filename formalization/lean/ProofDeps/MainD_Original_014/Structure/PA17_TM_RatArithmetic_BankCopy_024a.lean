module
public import Structure.PA17_TM_RatArithmetic_Copy_006e

/-! The fixed nearest-field copy crosses a real zero gap to a stable TRUE
work anchor. The gap length occurs only in tape specifications and traces.
The original source footer is really restored before each outward crossing
and really clamped again after the return crossing. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankCopy024

def oldLabel (q : Fin 43) : Fin 59 := PSTRTMSeq005.leftLabel (b := 15) q

def oldCfg (s : MachineState 42) : MachineState 58 := PSTRTMSeq005.leftCfg (b := 15) s

/-- 59 fixed labels. No gap, source width, fuel or result is a code input. -/
def copyMachine : Machine 58 := fun q symbol =>
  match q.val with
  | 0 => some (43,.move .right)
  | 5 => some (45,.move .left)
  | 18 => if symbol then some (16,.move .right) else some (48,.write true)
  | 19 => if symbol then some (17,.move .right) else some (49,.write true)
  | 38 => if symbol then some (54,.move .left) else some (39,.move .left)
  | 42 => some (56,.move .right)
  | 43 => some (if symbol then 44 else 43,.move .right)
  | 44 => some (1,.move .right)
  | 45 => some (46,.move .left)
  | 46 => some (47,.move .left)
  | 47 => if symbol then some (7,.write false) else some (47,.move .left)
  | 48 => some (50,.move .right)
  | 49 => some (51,.move .right)
  | 50 => some (if symbol then 52 else 50,.move .right)
  | 51 => some (if symbol then 53 else 51,.move .right)
  | 52 => some (20,.move .right)
  | 53 => some (21,.move .right)
  | 54 => if symbol then some (55,.write false) else some (54,.move .left)
  | 55 => some (38,.move .left)
  | 56 => some (if symbol then 57 else 56,.move .right)
  | 57 => some (58,.move .right)
  | _ =>
    if h : q.val < 43 then
      (PA17TMRatArithmeticCopy006.copyMachine ⟨q.val,h⟩ symbol).map
        (fun p => (oldLabel p.1,p.2))
    else none

def state (q : Fin 59) (left right : List Bool) : MachineState 58 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def bankTail (gap : Nat) (copied : List Bool) : List Bool :=
  List.replicate gap false ++ true::false::PA17TMRatArithmeticCopy006.workspace copied

def destinationLeft (gap : Nat) (sourceLeft : List Bool) : List Bool :=
  false::true::(List.replicate gap false ++ true::sourceLeft)

theorem halt (left right : List Bool) :
    Turing.TM0.step copyMachine (state 58 left right) = none := by
  simp [Turing.TM0.step,copyMachine,state]

theorem chain_append (xs ys : List (MachineState 58)) (last first : MachineState 58)
    (hx : xs.IsChain (fun a b => Turing.TM0.step copyMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step copyMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step copyMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

/-- Read actual FALSE cells until the first real TRUE anchor. -/
def zeroRight (q : Fin 59) (left tail : List Bool) : Nat → List (MachineState 58)
  | 0 => [state q left (true::tail)]
  | gap+1 =>
    state q left (false::(List.replicate gap false ++ true::tail)) ::
      zeroRight q (false::left) tail gap

theorem zeroRight_head (q : Fin 59) (left tail : List Bool) (gap : Nat) :
    (zeroRight q left tail gap).head? =
      some (state q left (List.replicate gap false ++ true::tail)) := by
  cases gap <;> rfl

theorem zeroRight_length (q : Fin 59) (left tail : List Bool) (gap : Nat) :
    (zeroRight q left tail gap).length = gap+1 := by
  induction gap generalizing left with
  | zero => rfl
  | succ gap ih => simp [zeroRight,ih,Nat.add_assoc]

theorem zeroRight_last (q : Fin 59) (left tail : List Bool) (gap : Nat) :
    (zeroRight q left tail gap).getLast? =
      some (state q (List.replicate gap false ++ left) (true::tail)) := by
  induction gap generalizing left with
  | zero => rfl
  | succ gap ih =>
    have hn : zeroRight q (false::left) tail gap ≠ [] := by
      intro h
      have hh := zeroRight_head q (false::left) tail gap
      simp [h] at hh
    rw [zeroRight,List.getLast?_cons_of_ne_nil hn,ih,List.replicate_succ']
    simp only [List.append_assoc,List.singleton_append]

theorem zeroRight_chain (q : Fin 59) (left tail : List Bool) (gap : Nat)
    (hq : copyMachine q false = some (q,.move .right)) :
    (zeroRight q left tail gap).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  induction gap generalizing left with
  | zero => exact .singleton _
  | succ gap ih =>
    rw [zeroRight]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [zeroRight_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      simp [Turing.TM0.step,state,hq,Turing.Tape.mk₂]
    · exact ih _

def zeroBackStart (q : Fin 59) (left tail : List Bool) : Nat → MachineState 58
  | 0 => state q left (true::tail)
  | gap+1 => state q (List.replicate gap false ++ true::left) (false::tail)

/-- Read actual FALSE cells leftward until the restored source footer TRUE. -/
def zeroLeft (q : Fin 59) (left tail : List Bool) : Nat → List (MachineState 58)
  | 0 => [state q left (true::tail)]
  | gap+1 =>
    state q (List.replicate gap false ++ true::left) (false::tail) ::
      zeroLeft q left (false::tail) gap

theorem zeroLeft_head (q : Fin 59) (left tail : List Bool) (gap : Nat) :
    (zeroLeft q left tail gap).head? = some (zeroBackStart q left tail gap) := by
  cases gap <;> rfl

theorem zeroLeft_length (q : Fin 59) (left tail : List Bool) (gap : Nat) :
    (zeroLeft q left tail gap).length = gap+1 := by
  induction gap generalizing tail with
  | zero => rfl
  | succ gap ih => simp [zeroLeft,ih,Nat.add_assoc]

theorem zeroLeft_last (q : Fin 59) (left tail : List Bool) (gap : Nat) :
    (zeroLeft q left tail gap).getLast? =
      some (state q left (true::(List.replicate gap false ++ tail))) := by
  induction gap generalizing tail with
  | zero => rfl
  | succ gap ih =>
    have hn : zeroLeft q left (false::tail) gap ≠ [] := by
      intro h
      have hh := zeroLeft_head q left (false::tail) gap
      simp [h] at hh
    rw [zeroLeft,List.getLast?_cons_of_ne_nil hn,ih,List.replicate_succ']
    simp only [List.append_assoc,List.singleton_append]

theorem zeroLeft_chain (q : Fin 59) (left tail : List Bool) (gap : Nat)
    (hq : copyMachine q false = some (q,.move .left)) :
    (zeroLeft q left tail gap).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  induction gap generalizing tail with
  | zero => exact .singleton _
  | succ gap ih =>
    rw [zeroLeft]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [zeroLeft_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      cases gap <;>
        simp [zeroBackStart,List.replicate_succ,Turing.TM0.step,state,hq,Turing.Tape.mk₂]
    · exact ih _

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankCopy024

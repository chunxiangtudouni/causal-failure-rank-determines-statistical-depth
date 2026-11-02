module
public import Structure.PA17_TM_RatArithmetic_BankCopy_024b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankCopy024

theorem oldCfg_state (q : Fin 43) (left right : List Bool) :
    oldCfg (PA17TMRatArithmeticCopy006.state q left right) = state (oldLabel q) left right := rfl

def pairTrace (dataQ flagQ : Fin 43) (left suffix digits : List Bool) : List (MachineState 58) :=
  (PA17TMRatArithmeticCopy006.pairScan dataQ flagQ left suffix digits).map oldCfg

theorem pairTrace_head (dataQ flagQ : Fin 43) (left suffix digits : List Bool) :
    (pairTrace dataQ flagQ left suffix digits).head? = some
      (state (oldLabel dataQ) left (PSTRTMIncrement009.blocks digits ++ false::false::suffix)) := by
  simp only [pairTrace,List.head?_map,PA17TMRatArithmeticCopy006.pairScan_head,Option.map_some,oldCfg_state]

theorem pairTrace_last (dataQ flagQ : Fin 43) (left suffix digits : List Bool) :
    (pairTrace dataQ flagQ left suffix digits).getLast? = some
      (state (oldLabel flagQ) (false::(PSTRTMRawNat010.leftBlocks digits.reverse ++ left)) (false::suffix)) := by
  simp only [pairTrace,List.getLast?_map,PA17TMRatArithmeticCopy006.pairScan_last,Option.map_some,oldCfg_state]

theorem pairTrace_length (dataQ flagQ : Fin 43) (left suffix digits : List Bool) :
    (pairTrace dataQ flagQ left suffix digits).length = 2*digits.length+2 := by
  simp only [pairTrace,List.length_map,PA17TMRatArithmeticCopy006.pairScan_length]

theorem pairTrace_chain (dataQ flagQ : Fin 43) (left suffix digits : List Bool)
    (hd : ∀ bit, copyMachine (oldLabel dataQ) bit = some (oldLabel flagQ,.move .right))
    (hf : copyMachine (oldLabel flagQ) true = some (oldLabel dataQ,.move .right)) :
    (pairTrace dataQ flagQ left suffix digits).IsChain
      (fun a b => Turing.TM0.step copyMachine a = some b) := by
  induction digits generalizing left with
  | nil =>
    change [state (oldLabel dataQ) left (false::false::suffix),
      state (oldLabel flagQ) (false::left) (false::suffix)].IsChain _
    simp [List.isChain_cons_cons,Turing.TM0.step,state,hd,Turing.Tape.mk₂]
  | cons bit later ih =>
    change (state (oldLabel dataQ) left (PSTRTMIncrement009.blocks (bit::later) ++ false::false::suffix) ::
      state (oldLabel flagQ) (bit::left) (true::(PSTRTMIncrement009.blocks later ++ false::false::suffix)) ::
      pairTrace dataQ flagQ (true::bit::left) suffix later).IsChain _
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step,state,hd,Turing.Tape.mk₂,PSTRTMIncrement009.blocks]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [pairTrace_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      simp [Turing.TM0.step,state,hf,Turing.Tape.mk₂]
    · exact ih _

def outwardQ (bit : Bool) : Fin 59 := if bit then 49 else 48
def outwardScanQ (bit : Bool) : Fin 59 := if bit then 51 else 50
def outwardGuardQ (bit : Bool) : Fin 59 := if bit then 53 else 52

/-- The source footer was physically FALSE at the last outFlag. The first
state here is after the actual writeTRUE. The stable work anchor staysTRUE. -/
def outwardTrace (bit : Bool) (base copied : List Bool) (gap : Nat) : List (MachineState 58) :=
  [state (outwardQ bit) (false::base) (true::bankTail gap copied)] ++
  zeroRight (outwardScanQ bit) (true::false::base)
    (false::PA17TMRatArithmeticCopy006.workspace copied) gap ++
  [state (outwardGuardQ bit) (true::(List.replicate gap false ++ true::false::base))
    (false::PA17TMRatArithmeticCopy006.workspace copied)]

theorem outward_head (bit : Bool) (base copied : List Bool) (gap : Nat) :
    (outwardTrace bit base copied gap).head? =
      some (state (outwardQ bit) (false::base) (true::bankTail gap copied)) := rfl

theorem outward_last (bit : Bool) (base copied : List Bool) (gap : Nat) :
    (outwardTrace bit base copied gap).getLast? = some
      (state (outwardGuardQ bit) (true::(List.replicate gap false ++ true::false::base))
        (false::PA17TMRatArithmeticCopy006.workspace copied)) := by
  unfold outwardTrace
  rw [List.getLast?_append]
  rfl

theorem outward_length (bit : Bool) (base copied : List Bool) (gap : Nat) :
    (outwardTrace bit base copied gap).length = gap+3 := by
  simp only [outwardTrace,List.length_append,List.length_singleton,zeroRight_length]
  omega

theorem outward_chain (bit : Bool) (base copied : List Bool) (gap : Nat) :
    (outwardTrace bit base copied gap).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  have hz := zeroRight_chain (outwardScanQ bit) (true::false::base)
    (false::PA17TMRatArithmeticCopy006.workspace copied) gap (by cases bit <;> rfl)
  have hr := chain_append
    (zeroRight (outwardScanQ bit) (true::false::base)
      (false::PA17TMRatArithmeticCopy006.workspace copied) gap)
    [state (outwardGuardQ bit) (true::(List.replicate gap false ++ true::false::base))
      (false::PA17TMRatArithmeticCopy006.workspace copied)] _ _ hz (.singleton _)
    (zeroRight_last (outwardScanQ bit) (true::false::base)
      (false::PA17TMRatArithmeticCopy006.workspace copied) gap) (by rfl) (by
      cases bit <;> simp [Turing.TM0.step,copyMachine,state,outwardScanQ,outwardGuardQ,Turing.Tape.mk₂])
  have hh : (zeroRight (outwardScanQ bit) (true::false::base)
      (false::PA17TMRatArithmeticCopy006.workspace copied) gap ++
      [state (outwardGuardQ bit) (true::(List.replicate gap false ++ true::false::base))
        (false::PA17TMRatArithmeticCopy006.workspace copied)]).head? =
      some (state (outwardScanQ bit) (true::false::base)
        (List.replicate gap false ++ true::false::PA17TMRatArithmeticCopy006.workspace copied)) := by
    simp [List.head?_append,zeroRight_head]
  have h := chain_append
    [state (outwardQ bit) (false::base) (true::bankTail gap copied)]
    (zeroRight (outwardScanQ bit) (true::false::base)
      (false::PA17TMRatArithmeticCopy006.workspace copied) gap ++
      [state (outwardGuardQ bit) (true::(List.replicate gap false ++ true::false::base))
        (false::PA17TMRatArithmeticCopy006.workspace copied)]) _ _ (.singleton _) hr (by rfl) hh (by
    cases bit <;> simp [Turing.TM0.step,copyMachine,state,outwardQ,outwardScanQ,bankTail,Turing.Tape.mk₂])
  simpa only [outwardTrace,List.append_assoc] using h

/-- From the destination guard, the preceding step reaches anchorTRUE.
After the gap scan, sourceFooter is really writtenFALSE before sourceReturn. -/
def returnTrace (base copied : List Bool) (gap : Nat) : List (MachineState 58) :=
  [state 38 (List.replicate gap false ++ true::false::base)
    (true::false::PA17TMRatArithmeticCopy006.workspace copied)] ++
  zeroLeft 54 (false::base) (true::false::PA17TMRatArithmeticCopy006.workspace copied) gap ++
  [state 55 (false::base) (false::bankTail gap copied)]

theorem return_head (base copied : List Bool) (gap : Nat) :
    (returnTrace base copied gap).head? = some
      (state 38 (List.replicate gap false ++ true::false::base)
        (true::false::PA17TMRatArithmeticCopy006.workspace copied)) := rfl

theorem return_last (base copied : List Bool) (gap : Nat) :
    (returnTrace base copied gap).getLast? = some
      (state 55 (false::base) (false::bankTail gap copied)) := by
  unfold returnTrace
  rw [List.getLast?_append]
  rfl

theorem return_length (base copied : List Bool) (gap : Nat) :
    (returnTrace base copied gap).length = gap+3 := by
  simp only [returnTrace,List.length_append,List.length_singleton,zeroLeft_length]
  omega

theorem return_chain (base copied : List Bool) (gap : Nat) :
    (returnTrace base copied gap).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  have hz := zeroLeft_chain 54 (false::base)
    (true::false::PA17TMRatArithmeticCopy006.workspace copied) gap (by rfl)
  have hr := chain_append
    (zeroLeft 54 (false::base) (true::false::PA17TMRatArithmeticCopy006.workspace copied) gap)
    [state 55 (false::base) (false::bankTail gap copied)] _ _ hz (.singleton _)
    (zeroLeft_last 54 (false::base) (true::false::PA17TMRatArithmeticCopy006.workspace copied) gap)
    (by rfl) (by simp [Turing.TM0.step,copyMachine,state,bankTail,Turing.Tape.mk₂])
  have hh : (zeroLeft 54 (false::base) (true::false::PA17TMRatArithmeticCopy006.workspace copied) gap ++
      [state 55 (false::base) (false::bankTail gap copied)]).head? =
      some (zeroBackStart 54 (false::base) (true::false::PA17TMRatArithmeticCopy006.workspace copied) gap) := by
    simp [List.head?_append,zeroLeft_head]
  have h := chain_append
    [state 38 (List.replicate gap false ++ true::false::base)
      (true::false::PA17TMRatArithmeticCopy006.workspace copied)]
    (zeroLeft 54 (false::base) (true::false::PA17TMRatArithmeticCopy006.workspace copied) gap ++
      [state 55 (false::base) (false::bankTail gap copied)]) _ _ (.singleton _) hr (by rfl) hh (by
    cases gap <;> simp [zeroBackStart,List.replicate_succ,Turing.TM0.step,copyMachine,state,Turing.Tape.mk₂])
  simpa only [returnTrace,List.append_assoc] using h

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankCopy024

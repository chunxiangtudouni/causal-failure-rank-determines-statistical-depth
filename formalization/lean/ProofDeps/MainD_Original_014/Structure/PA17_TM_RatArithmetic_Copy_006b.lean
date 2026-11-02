module
public import Structure.PA17_TM_RatArithmetic_Copy_006a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopy006

/-- Scan real data/true-flag pairs. The final00 is present and arbitrary
suffix remains opaque. Both source-outbound and workspace scans reuse this. -/
def pairScan (dataQ flagQ : Fin 43) (left suffix : List Bool) : List Bool → List (MachineState 42)
  | [] => [state dataQ left (false::false::suffix),state flagQ (false::left) (false::suffix)]
  | bit::later =>
    state dataQ left (PSTRTMIncrement009.blocks (bit::later) ++ false::false::suffix) ::
    state flagQ (bit::left) (true::(PSTRTMIncrement009.blocks later ++ false::false::suffix)) ::
    pairScan dataQ flagQ (true::bit::left) suffix later

theorem pairScan_head (dataQ flagQ : Fin 43) (left suffix digits : List Bool) :
    (pairScan dataQ flagQ left suffix digits).head? = some
      (state dataQ left (PSTRTMIncrement009.blocks digits ++ false::false::suffix)) := by
  cases digits <;> rfl

theorem pairScan_length (dataQ flagQ : Fin 43) (left suffix digits : List Bool) :
    (pairScan dataQ flagQ left suffix digits).length = 2*digits.length+2 := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih => simp only [pairScan,List.length_cons,ih]; omega

theorem pairScan_last (dataQ flagQ : Fin 43) (left suffix digits : List Bool) :
    (pairScan dataQ flagQ left suffix digits).getLast? = some
      (state flagQ (false::(PSTRTMRawNat010.leftBlocks digits.reverse ++ left)) (false::suffix)) := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    have hne : pairScan dataQ flagQ (true::bit::left) suffix later ≠ [] := by
      have hh := pairScan_head dataQ flagQ (true::bit::left) suffix later
      intro h
      simp [h] at hh
    simp only [pairScan,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMRawNat010.leftBlocks,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem pairScan_chain (dataQ flagQ : Fin 43) (left suffix digits : List Bool)
    (hd : ∀ bit, copyMachine dataQ bit = some (flagQ,.move .right))
    (hf : copyMachine flagQ true = some (dataQ,.move .right)) :
    (pairScan dataQ flagQ left suffix digits).IsChain
      (fun a b => Turing.TM0.step copyMachine a = some b) := by
  induction digits generalizing left with
  | nil =>
    simp [pairScan,List.isChain_cons_cons,Turing.TM0.step,state,hd,Turing.Tape.mk₂]
  | cons bit later ih =>
    rw [pairScan]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step,state,hd,Turing.Tape.mk₂,PSTRTMIncrement009.blocks]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [pairScan_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      simp [Turing.TM0.step,state,hf,Turing.Tape.mk₂]
    · exact ih _

def backStart (flagQ : Fin 43) (previous left tail : List Bool) : MachineState 42 :=
  match previous with
  | [] => state flagQ left (false::tail)
  | bit::previous =>
    state flagQ (bit::(PSTRTMRawNat010.leftBlocks previous ++ false::left)) (true::tail)

/-- Read-only return across already copied true flags to a real false marker. -/
def backScan (flagQ dataQ : Fin 43) (left tail : List Bool) : List Bool → List (MachineState 42)
  | [] => [state flagQ left (false::tail)]
  | bit::previous =>
    state flagQ (bit::(PSTRTMRawNat010.leftBlocks previous ++ false::left)) (true::tail) ::
    state dataQ (PSTRTMRawNat010.leftBlocks previous ++ false::left) (bit::true::tail) ::
    backScan flagQ dataQ left (bit::true::tail) previous

theorem backScan_head (flagQ dataQ : Fin 43) (left tail previous : List Bool) :
    (backScan flagQ dataQ left tail previous).head? = some (backStart flagQ previous left tail) := by
  cases previous <;> rfl

theorem backScan_length (flagQ dataQ : Fin 43) (left tail previous : List Bool) :
    (backScan flagQ dataQ left tail previous).length = 2*previous.length+1 := by
  induction previous generalizing tail with
  | nil => rfl
  | cons bit previous ih => simp only [backScan,List.length_cons,ih]; omega

theorem backScan_last (flagQ dataQ : Fin 43) (left tail previous : List Bool) :
    (backScan flagQ dataQ left tail previous).getLast? = some
      (state flagQ left (false::(PSTRTMIncrement009.blocks previous.reverse ++ tail))) := by
  induction previous generalizing tail with
  | nil => rfl
  | cons bit previous ih =>
    have hne : backScan flagQ dataQ left (bit::true::tail) previous ≠ [] := by
      have hh := backScan_head flagQ dataQ left (bit::true::tail) previous
      intro h
      simp [h] at hh
    simp only [backScan,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMIncrement009.blocks,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem backScan_chain (flagQ dataQ : Fin 43) (left tail previous : List Bool)
    (hf : copyMachine flagQ true = some (dataQ,.move .left))
    (hd : ∀ bit, copyMachine dataQ bit = some (flagQ,.move .left)) :
    (backScan flagQ dataQ left tail previous).IsChain
      (fun a b => Turing.TM0.step copyMachine a = some b) := by
  induction previous generalizing tail with
  | nil => exact .singleton _
  | cons bit previous ih =>
    rw [backScan]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step,state,hf,Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [backScan_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      cases previous <;>
        simp [backStart,Turing.TM0.step,state,hd,Turing.Tape.mk₂,PSTRTMRawNat010.leftBlocks]
    · exact ih _

/-- The two new OWN cells are individually written false. The trace ends on
the appended data, ready for a leftward return through the old workspace. -/
def writeTrace (bit : Bool) (left : List Bool) : List (MachineState 42) :=
  [state (writeData bit) left [false,false],
   state 26 left [bit,false],
   state 27 (bit::left) [false],
   state 28 (bit::left) [true],
   state 29 (true::bit::left) [false,false],
   state 30 (true::bit::left) [false,false],
   state 31 (false::true::bit::left) [false],
   state 32 (false::true::bit::left) [false],
   state 33 (true::bit::left) [false,false],
   state 34 (bit::left) [true,false,false],
   state 35 left [bit,true,false,false]]

theorem writeTrace_head (bit : Bool) (left : List Bool) :
    (writeTrace bit left).head? = some (state (writeData bit) left [false,false]) := rfl

theorem writeTrace_last (bit : Bool) (left : List Bool) :
    (writeTrace bit left).getLast? = some (state 35 left [bit,true,false,false]) := rfl

theorem writeTrace_length (bit : Bool) (left : List Bool) : (writeTrace bit left).length = 11 := rfl

private theorem blank_two_false :
    Turing.ListBlank.mk ([false,false] : List Bool) = Turing.ListBlank.mk ([] : List Bool) :=
  (PSTRTMRawNat010.blank_append_false [false]).trans PSTRTMRawNat010.blank_single_false

private theorem blank_bit_false (bit : Bool) :
    Turing.ListBlank.mk [bit,false] = Turing.ListBlank.mk [bit] :=
  PSTRTMRawNat010.blank_append_false [bit]

private theorem blank_bit_two_false (bit : Bool) :
    Turing.ListBlank.mk [bit,false,false] = Turing.ListBlank.mk [bit] :=
  (PSTRTMRawNat010.blank_append_false [bit,false]).trans (blank_bit_false bit)

private theorem blank_pair_two_false (first second : Bool) :
    Turing.ListBlank.mk [first,second,false,false] = Turing.ListBlank.mk [first,second] :=
  (PSTRTMRawNat010.blank_append_false [first,second,false]).trans
    (PSTRTMRawNat010.blank_append_false [first,second])

attribute [local simp] blank_two_false blank_bit_false blank_bit_two_false blank_pair_two_false
  PSTRTMRawNat010.blank_single_false

theorem writeTrace_chain (bit : Bool) (left : List Bool) :
    (writeTrace bit left).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  cases bit <;>
    simp [writeTrace,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,writeData,Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopy006

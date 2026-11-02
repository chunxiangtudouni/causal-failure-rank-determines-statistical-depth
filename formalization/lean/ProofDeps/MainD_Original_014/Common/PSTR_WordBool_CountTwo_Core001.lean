module

public import Common.PSTR_SYM_CounterRound_031
public import Common.PSTR_SYM_Carry_042
public import Structure.PA17_TM_RatArithmetic_Parse_002g

/-! Exactly two real decrements at the original unread head. The original
head bit is captured by a real transition into finite control, replaced
by FALSE for the existing counter callee, and restored by a real WRITE. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.CountTwo

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMSeq005 PSTRTMIncrement009 PSTRTMRawNat010
open PSTRTMThresholdCountdownCode164 PSTRSymbolicCounter PA17TMRatArithmeticParse002

def cursorTape (base digits : List Bool) (head : Bool) (tail : List Bool) : Tape Bool :=
  Tape.mk₂ (false :: (leftBlocks digits.reverse ++ false :: base)) (head :: tail)

/-- The already frozen footer machine moves RIGHT on either current bit. -/
theorem right_runsFrom (tape : Tape Bool) :
    RunsFrom footerMachine ⟨0,tape⟩ [⟨0,tape⟩,⟨1,tape.move .right⟩] ⟨1,tape.move .right⟩ := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [List.isChain_cons_cons, TM0.step, footerMachine]
  · simp [TM0.step, footerMachine]

def backRoundMachine : Machine 22 := seqMachine fieldBackMachine counterRoundMachine
def oneRoundMachine : Machine 24 := seqMachine backRoundMachine footerMachine

def backRoundTrace (base digits tail : List Bool) : List (MachineState 22) :=
  (fieldBackTrace base digits (false :: tail)).map (leftCfg (b:=16)) ++
    (counterRoundTrace base digits tail).map (rightCfg (a:=5))

def backRoundFinal (base digits tail : List Bool) : MachineState 22 :=
  rightCfg (a:=5) (counterRoundFinal base digits tail)

theorem backRound_runsFrom (base digits tail : List Bool) (positive : true ∈ digits) :
    RunsFrom backRoundMachine ⟨0,cursorTape base digits false tail⟩
      (backRoundTrace base digits tail) (backRoundFinal base digits tail) := by
  apply seq_runsFrom fieldBackMachine counterRoundMachine
    ⟨0,cursorTape base digits false tail⟩
    (fieldBackFinal base digits (false :: tail)) (counterRoundFinal base digits tail)
    (fieldBackTrace base digits (false :: tail)) (counterRoundTrace base digits tail)
  · exact fieldBack_runsFrom base digits (false :: tail)
  · rw [fieldBack_final_tape]
    exact counterRound_runsFrom base digits tail positive

theorem end_right (base digits tail : List Bool) :
    (Tape.mk₂ (leftBlocks digits.reverse ++ false :: base) (false :: false :: tail)).move .right =
      cursorTape base digits false tail := by
  simp [cursorTape, Tape.mk₂]

def oneRoundTrace (base digits tail : List Bool) : List (MachineState 24) :=
  (backRoundTrace base digits tail).map (leftCfg (b:=1)) ++
    ([⟨0,(backRoundFinal base digits tail).Tape⟩,
      ⟨1,(backRoundFinal base digits tail).Tape.move .right⟩] : List (MachineState 1)).map (rightCfg (a:=22))

def oneRoundFinal (base digits tail : List Bool) : MachineState 24 :=
  rightCfg (a:=22) (⟨1,(backRoundFinal base digits tail).Tape.move .right⟩ : MachineState 1)

theorem oneRound_runsFrom (base digits tail : List Bool) (positive : true ∈ digits) :
    RunsFrom oneRoundMachine ⟨0,cursorTape base digits false tail⟩
      (oneRoundTrace base digits tail) (oneRoundFinal base digits tail) := by
  apply seq_runsFrom backRoundMachine footerMachine ⟨0,cursorTape base digits false tail⟩
    (backRoundFinal base digits tail)
    (⟨1,(backRoundFinal base digits tail).Tape.move .right⟩ : MachineState 1)
    (backRoundTrace base digits tail) _ (backRound_runsFrom base digits tail positive)
  exact right_runsFrom _

theorem oneRound_final_tape (base digits tail : List Bool) :
    (oneRoundFinal base digits tail).Tape = cursorTape base (predDigits digits) false tail := by
  change (counterRoundFinal base digits tail).Tape.move .right = _
  rw [counterRound_final_tape]
  exact end_right _ _ _

theorem oneRound_time (base digits tail : List Bool) (positive : true ∈ digits) :
    (oneRoundTrace base digits tail).length ≤ 10*digits.length+15 := by
  have counter := counterRound_time_le base digits tail positive
  simp only [oneRoundTrace, backRoundTrace, List.length_append, List.length_map,
    List.length_cons, List.length_nil, fieldBackTrace_length]
  omega

def twoRoundMachine : Machine 49 := seqMachine oneRoundMachine oneRoundMachine

def twoRoundTrace (base digits tail : List Bool) : List (MachineState 49) :=
  (oneRoundTrace base digits tail).map (leftCfg (b:=24)) ++
    (oneRoundTrace base (predDigits digits) tail).map (rightCfg (a:=24))

def twoRoundFinal (base digits tail : List Bool) : MachineState 49 :=
  rightCfg (a:=24) (oneRoundFinal base (predDigits digits) tail)

theorem two_positive (digits : List Bool) (enough : 2 ≤ valueDigits digits) :
    true ∈ digits ∧ true ∈ predDigits digits := by
  have first := has_true_of_value_pos digits (by omega)
  have value := pred_value digits first
  exact ⟨first, has_true_of_value_pos _ (by omega)⟩

theorem two_value (digits : List Bool) (enough : 2 ≤ valueDigits digits) :
    valueDigits (predDigits (predDigits digits)) + 2 = valueDigits digits := by
  have positive := two_positive digits enough
  have first := pred_value digits positive.1
  have second := pred_value (predDigits digits) positive.2
  omega

theorem width_preserved (digits : List Bool) :
    (predDigits (predDigits digits)).length = digits.length := by
  rw [pred_length,pred_length]

theorem twoRound_runsFrom (base digits tail : List Bool) (enough : 2 ≤ valueDigits digits) :
    RunsFrom twoRoundMachine ⟨0,cursorTape base digits false tail⟩
      (twoRoundTrace base digits tail) (twoRoundFinal base digits tail) := by
  have positive := two_positive digits enough
  apply seq_runsFrom oneRoundMachine oneRoundMachine ⟨0,cursorTape base digits false tail⟩
    (oneRoundFinal base digits tail) (oneRoundFinal base (predDigits digits) tail)
    (oneRoundTrace base digits tail) (oneRoundTrace base (predDigits digits) tail)
    (oneRound_runsFrom base digits tail positive.1)
  rw [oneRound_final_tape]
  exact oneRound_runsFrom base (predDigits digits) tail positive.2

theorem twoRound_final_tape (base digits tail : List Bool) :
    (twoRoundFinal base digits tail).Tape = cursorTape base (predDigits (predDigits digits)) false tail :=
  oneRound_final_tape base (predDigits digits) tail

theorem twoRound_time (base digits tail : List Bool) (enough : 2 ≤ valueDigits digits) :
    (twoRoundTrace base digits tail).length ≤ 20*digits.length+30 := by
  have positive := two_positive digits enough
  have first := oneRound_time base digits tail positive.1
  have second := oneRound_time base (predDigits digits) tail positive.2
  rw [pred_length] at second
  simp only [twoRoundTrace, List.length_append, List.length_map]
  omega

def savedBit (bit : Bool) : Fin 8 := if bit then 1 else 0
def bodyLabel (q : Fin 400) : Fin 402 := ⟨q.val+1,by omega⟩
def haltPort : Fin 402 := 401
def entryPort : Fin 402 := 0

/-- Capture, one fixed carried callee table, restore, and one common halt. -/
def machine : Machine 401 := fun label symbol =>
  if label.val=0 then
    some (bodyLabel (PSTRSymbolicCarry.carryLabel (0 : Fin 50) (savedBit symbol)), .write false)
  else if inside : label.val<401 then
    let q : Fin 400 := ⟨label.val-1,by omega⟩
    match PSTRSymbolicCarry.carryMachine twoRoundMachine q symbol with
    | none => some (haltPort, .write ((PSTRSymbolicCarry.savedLabel (states:=49) q).val == 1))
    | some (next,op) => some (bodyLabel next,op)
  else none

def bodyCfg (bit : Bool) (cfg : MachineState 49) : MachineState 401 :=
  ⟨bodyLabel (PSTRSymbolicCarry.carryLabel cfg.q (savedBit bit)),cfg.Tape⟩

theorem body_lookup (q : Fin 400) (symbol : Bool) :
    machine (bodyLabel q) symbol =
      match PSTRSymbolicCarry.carryMachine twoRoundMachine q symbol with
      | none => some (haltPort,.write ((PSTRSymbolicCarry.savedLabel (states:=49) q).val == 1))
      | some (next,op) => some (bodyLabel next,op) := by
  have positive : q.val+1 ≠ 0 := by omega
  have inside : q.val+1 < 401 := by omega
  simp only [machine,bodyLabel,positive,inside,↓reduceIte,↓reduceDIte,Nat.add_sub_cancel_right,Fin.eta]

theorem body_step (bit : Bool) (cfg : MachineState 49) :
    TM0.step machine (bodyCfg bit cfg) =
      match TM0.step twoRoundMachine cfg with
      | none => some ⟨haltPort,cfg.Tape.write bit⟩
      | some next => some (bodyCfg bit next) := by
  cases cfg with
  | mk q tape =>
    simp only [TM0.step,bodyCfg]
    rw [body_lookup]
    simp only [PSTRSymbolicCarry.carryMachine,PSTRSymbolicRelabel.relabelMachine,TM0.Machine.map,
      PSTRSymbolicCarry.original_carry,PSTRSymbolicCarry.saved_carry,PSTRSymbolicRelabel.boolIdentity,id_eq]
    have recovered : ((savedBit bit).val == 1) = bit := by cases bit <;> rfl
    rw [recovered]
    cases action : twoRoundMachine q tape.head with
    | none => rfl
    | some pair =>
      obtain ⟨next,op⟩ := pair
      cases op <;> rfl

theorem capture_step (left tail : List Bool) (bit : Bool) :
    TM0.step machine ⟨entryPort,Tape.mk₂ left (bit::tail)⟩ =
      some (bodyCfg bit ⟨0,Tape.mk₂ left (false::tail)⟩) := by
  cases bit <;> simp [TM0.step,machine,entryPort,bodyCfg,savedBit,Tape.mk₂]

theorem final_halt (tape : Tape Bool) : TM0.step machine ⟨haltPort,tape⟩ = none := by
  simp [TM0.step,machine,haltPort]

def initial (base digits : List Bool) (bit : Bool) (tail : List Bool) : MachineState 401 :=
  ⟨entryPort,cursorTape base digits bit tail⟩

def final (base digits : List Bool) (bit : Bool) (tail : List Bool) : MachineState 401 :=
  ⟨haltPort,cursorTape base (predDigits (predDigits digits)) bit tail⟩

def trace (base digits : List Bool) (bit : Bool) (tail : List Bool) : List (MachineState 401) :=
  [initial base digits bit tail] ++
    (twoRoundTrace base digits tail).map (bodyCfg bit) ++ [final base digits bit tail]

theorem trace_chain (base digits : List Bool) (bit : Bool) (tail : List Bool)
    (enough : 2 ≤ valueDigits digits) :
    (trace base digits bit tail).IsChain (fun before after => TM0.step machine before = some after) := by
  have run := twoRound_runsFrom base digits tail enough
  let body := (twoRoundTrace base digits tail).map (bodyCfg bit)
  have bodyHead : body.head? = some (bodyCfg bit ⟨0,cursorTape base digits false tail⟩) := by
    simp only [body,List.head?_map,run.1,Option.map_some]
  have bodyLast : body.getLast? = some (bodyCfg bit (twoRoundFinal base digits tail)) := by
    simp only [body,List.getLast?_map,run.2.2.1,Option.map_some]
  have bodyChain : body.IsChain (fun before after => TM0.step machine before = some after) := by
    apply (List.isChain_map _).mpr
    exact run.2.1.imp (fun before after edge => by simp [body_step,edge])
  have firstChain : ([initial base digits bit tail] ++ body).IsChain
      (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append (.singleton _) bodyChain
    intro before beforeLast after afterHead
    simp only [List.getLast?_singleton,Option.mem_some_iff] at beforeLast
    simp only [bodyHead,Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact capture_step _ tail bit
  have firstLast : ([initial base digits bit tail] ++ body).getLast? =
      some (bodyCfg bit (twoRoundFinal base digits tail)) := by
    simp only [List.getLast?_append,bodyLast,Option.some_or]
  change (([initial base digits bit tail] ++ body) ++ [final base digits bit tail]).IsChain _
  apply List.IsChain.append firstChain (.singleton _)
  intro before beforeLast after afterHead
  simp only [firstLast,Option.mem_some_iff] at beforeLast
  simp only [List.head?_singleton,Option.mem_some_iff] at afterHead
  subst before
  subst after
  have restore := body_step bit (twoRoundFinal base digits tail)
  rw [run.2.2.2,twoRound_final_tape] at restore
  simpa [final,cursorTape,Tape.mk₂] using restore

theorem runsFrom (base digits : List Bool) (bit : Bool) (tail : List Bool)
    (enough : 2 ≤ valueDigits digits) :
    RunsFrom machine (initial base digits bit tail) (trace base digits bit tail) (final base digits bit tail) := by
  refine ⟨rfl,trace_chain base digits bit tail enough,?_,final_halt _⟩
  simp only [trace,List.getLast?_append,List.getLast?_singleton,Option.some_or]

theorem trace_time (base digits : List Bool) (bit : Bool) (tail : List Bool)
    (enough : 2 ≤ valueDigits digits) :
    (trace base digits bit tail).length ≤ 64*(digits.length+1) := by
  have rounds := twoRound_time base digits tail enough
  simp only [trace,List.length_append,List.length_map,List.length_cons,List.length_nil]
  omega

/-- The internal ABI has exactly one qualification, the positive two-count. -/
theorem actual (base digits : List Bool) (bit : Bool) (tail : List Bool) (inputLen : Nat)
    (enough : 2 ≤ valueDigits digits) :
    ∃ path finish,
      RunsFrom machine ⟨entryPort,cursorTape base digits bit tail⟩ path finish ∧
      finish.q = haltPort ∧ TM0.step machine finish = none ∧
      finish.Tape = cursorTape base (predDigits (predDigits digits)) bit tail ∧
      path.length ≤ 64*(digits.length+1) ∧
      ∀ clock, visitedSpace machine inputLen (path.take clock) ≤ inputLen+128*(digits.length+1)+1 := by
  have time := trace_time base digits bit tail enough
  refine ⟨trace base digits bit tail,final base digits bit tail,runsFrom base digits bit tail enough,
    rfl,final_halt _,rfl,time,?_⟩
  intro clock
  have space := PSTRTMTrace002.visitedSpace_le machine inputLen ((trace base digits bit tail).take clock)
  have shorter := List.length_take_le' clock (trace base digits bit tail)
  omega

theorem fixed_counter :
    ∃ (cap : Nat) (code : Machine cap) (entry halt : Fin (cap+1)),
      ∀ (base digits : List Bool) (bit : Bool) (tail : List Bool) (inputLen : Nat),
        2 ≤ valueDigits digits →
        ∃ path finish,
          RunsFrom code ⟨entry,cursorTape base digits bit tail⟩ path finish ∧
          finish.q = halt ∧ TM0.step code finish = none ∧
          finish.Tape = cursorTape base (predDigits (predDigits digits)) bit tail ∧
          path.length ≤ 64*(digits.length+1) ∧
          ∀ clock, visitedSpace code inputLen (path.take clock) ≤ inputLen+128*(digits.length+1)+1 :=
  ⟨401,machine,entryPort,haltPort,actual⟩

end PaperProofs.Common.Native.PSTRWordBool.CountTwo

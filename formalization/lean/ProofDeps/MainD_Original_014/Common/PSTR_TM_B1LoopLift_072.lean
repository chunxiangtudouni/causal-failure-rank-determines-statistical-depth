module
public import Common.PSTR_TM_B1LoopCode_071

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1LoopLift072
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMB1LoopCode071

theorem compare_command (q next : Fin 21) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMCompareCode054.compareMachine q symbol = some (next, statement)) :
    loopMachine (compareLabel q) symbol = some (compareLabel next, statement) := by
  have hq : q.val < 18 := by
    by_contra hn
    simp [PSTRTMCompareCode054.compareMachine, show ¬q.val < 3 by omega,
      show ¬q.val < 9 by omega, show ¬q.val < 15 by omega, hn] at old
  simp [loopMachine, compareLabel, show q.val < 21 by omega, show q.val ≠ 19 by omega,
    show q.val ≠ 18 by omega, show q.val ≠ 20 by omega, old]

theorem counter_command (q next : Fin 15) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMIncrement009.incrementMachine q symbol = some (next, statement)) :
    loopMachine (counterLabel q) symbol = some (counterLabel next, statement) := by
  have hn : q.val ≠ 14 := by intro h; simp [PSTRTMIncrement009.incrementMachine, h] at old
  have hq := q.isLt
  simp [loopMachine, counterLabel, show ¬21 + q.val < 21 by omega, show 21 + q.val < 36 by omega,
    show 21 + q.val ≠ 35 by omega, old]

theorem rewindBefore_command (q next : Fin 6) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMColumnRewind067.rewindMachine q symbol = some (next, statement)) :
    loopMachine (rewindBeforeLabel q) symbol = some (rewindBeforeLabel next, statement) := by
  have hn : q.val ≠ 5 := by intro h; simp [PSTRTMColumnRewind067.rewindMachine, h] at old
  have hq := q.isLt
  simp [loopMachine, rewindBeforeLabel, show ¬36 + q.val < 21 by omega,
    show ¬36 + q.val < 36 by omega, show 36 + q.val < 42 by omega,
    show 36 + q.val ≠ 41 by omega, old]

theorem shift_command (q next : Fin 20) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMShiftColumnCode065.shiftMachine q symbol = some (next, statement)) :
    loopMachine (shiftLabel q) symbol = some (shiftLabel next, statement) := by
  have hq : q.val < 18 := by
    by_contra hn
    simp [PSTRTMShiftColumnCode065.shiftMachine, show ¬q.val < 2 by omega,
      show ¬q.val < 6 by omega, show ¬q.val < 10 by omega, hn] at old
  simp [loopMachine, shiftLabel, show ¬42 + q.val < 21 by omega,
    show ¬42 + q.val < 36 by omega, show ¬42 + q.val < 42 by omega,
    show 42 + q.val < 62 by omega, show 42 + q.val ≠ 60 by omega, old]

theorem rewindAfter_command (q next : Fin 6) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMColumnRewind067.rewindMachine q symbol = some (next, statement)) :
    loopMachine (rewindAfterLabel q) symbol = some (rewindAfterLabel next, statement) := by
  have hn : q.val ≠ 5 := by intro h; simp [PSTRTMColumnRewind067.rewindMachine, h] at old
  have hq := q.isLt
  simp [loopMachine, rewindAfterLabel, show ¬62 + q.val < 21 by omega,
    show ¬62 + q.val < 36 by omega, show ¬62 + q.val < 42 by omega,
    show ¬62 + q.val < 62 by omega, show 62 + q.val < 68 by omega,
    show 62 + q.val ≠ 67 by omega, old]

private theorem retained_step {a b : Nat} (oldMachine : Machine a) (newMachine : Machine b)
    (labelMap : Fin (a+1) → Fin (b+1))
    (commands : ∀ q next symbol statement, oldMachine q symbol = some (next, statement) →
      newMachine (labelMap q) symbol = some (labelMap next, statement))
    (before after : MachineState a) (old : Turing.TM0.step oldMachine before = some after) :
    Turing.TM0.step newMachine ⟨labelMap before.q, before.Tape⟩ = some ⟨labelMap after.q, after.Tape⟩ := by
  cases before with
  | mk q tape =>
    unfold Turing.TM0.step at old
    cases hc : oldMachine q tape.head with
    | none => simp [hc] at old
    | some command =>
      obtain ⟨next, statement⟩ := command
      simp only [hc, Option.map_some, Option.some.injEq] at old
      subst after
      have hm := commands q next tape.head statement hc
      simp only [Turing.TM0.step, hm, Option.map_some]

theorem compare_step (before after : MachineState 20)
    (old : Turing.TM0.step PSTRTMCompareCode054.compareMachine before = some after) :
    Turing.TM0.step loopMachine (liftCompare before) = some (liftCompare after) :=
  retained_step _ _ compareLabel compare_command before after old

theorem counter_step (before after : MachineState 14)
    (old : Turing.TM0.step PSTRTMIncrement009.incrementMachine before = some after) :
    Turing.TM0.step loopMachine (liftCounter before) = some (liftCounter after) :=
  retained_step _ _ counterLabel counter_command before after old

theorem rewindBefore_step (before after : MachineState 5)
    (old : Turing.TM0.step PSTRTMColumnRewind067.rewindMachine before = some after) :
    Turing.TM0.step loopMachine (liftRewindBefore before) = some (liftRewindBefore after) :=
  retained_step _ _ rewindBeforeLabel rewindBefore_command before after old

theorem shift_step (before after : MachineState 19)
    (old : Turing.TM0.step PSTRTMShiftColumnCode065.shiftMachine before = some after) :
    Turing.TM0.step loopMachine (liftShift before) = some (liftShift after) :=
  retained_step _ _ shiftLabel shift_command before after old

theorem rewindAfter_step (before after : MachineState 5)
    (old : Turing.TM0.step PSTRTMColumnRewind067.rewindMachine before = some after) :
    Turing.TM0.step loopMachine (liftRewindAfter before) = some (liftRewindAfter after) :=
  retained_step _ _ rewindAfterLabel rewindAfter_command before after old

theorem compare_chain (trace : List (MachineState 20))
    (old : trace.IsChain (fun a b => Turing.TM0.step PSTRTMCompareCode054.compareMachine a = some b)) :
    (trace.map liftCompare).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) :=
  (List.isChain_map _).mpr (old.imp compare_step)

theorem counter_chain (trace : List (MachineState 14))
    (old : trace.IsChain (fun a b => Turing.TM0.step PSTRTMIncrement009.incrementMachine a = some b)) :
    (trace.map liftCounter).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) :=
  (List.isChain_map _).mpr (old.imp counter_step)

theorem rewindBefore_chain (trace : List (MachineState 5))
    (old : trace.IsChain (fun a b => Turing.TM0.step PSTRTMColumnRewind067.rewindMachine a = some b)) :
    (trace.map liftRewindBefore).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) :=
  (List.isChain_map _).mpr (old.imp rewindBefore_step)

theorem shift_chain (trace : List (MachineState 19))
    (old : trace.IsChain (fun a b => Turing.TM0.step PSTRTMShiftColumnCode065.shiftMachine a = some b)) :
    (trace.map liftShift).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) :=
  (List.isChain_map _).mpr (old.imp shift_step)

theorem rewindAfter_chain (trace : List (MachineState 5))
    (old : trace.IsChain (fun a b => Turing.TM0.step PSTRTMColumnRewind067.rewindMachine a = some b)) :
    (trace.map liftRewindAfter).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) :=
  (List.isChain_map _).mpr (old.imp rewindAfter_step)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1LoopLift072

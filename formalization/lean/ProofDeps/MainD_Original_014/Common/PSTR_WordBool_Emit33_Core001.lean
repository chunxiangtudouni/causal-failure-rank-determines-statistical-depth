module

public import Common.PSTR_WordBool_RawInit_Shape001
public import Common.PSTR_TM_Seq_005

/-! One fixed finite writer. Four actual entry labels carry the two bits.
The machine overwrites exactly 33 cells and really moves RIGHT after each
write, preserving both arbitrary outside parts of the tape. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.Emit33

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005

def entry : Bool → Bool → Fin 85
  | false, false => 0
  | false, true => 6
  | true, false => 12
  | true, true => 18

def haltPort : Fin 85 := 84

/-- The first three writes retain both bits in finite control; all four
paths then share the same thirty literal FALSE write/RIGHT pairs. -/
def code : Machine 84 := fun q _ =>
  if q.val < 24 then
    match q.val with
    | 0 => some (1, .write false)
    | 1 => some (2, .move .right)
    | 2 => some (3, .write true)
    | 3 => some (4, .move .right)
    | 4 => some (5, .write false)
    | 5 => some (24, .move .right)
    | 6 => some (7, .write false)
    | 7 => some (8, .move .right)
    | 8 => some (9, .write true)
    | 9 => some (10, .move .right)
    | 10 => some (11, .write true)
    | 11 => some (24, .move .right)
    | 12 => some (13, .write true)
    | 13 => some (14, .move .right)
    | 14 => some (15, .write true)
    | 15 => some (16, .move .right)
    | 16 => some (17, .write false)
    | 17 => some (24, .move .right)
    | 18 => some (19, .write true)
    | 19 => some (20, .move .right)
    | 20 => some (21, .write true)
    | 21 => some (22, .move .right)
    | 22 => some (23, .write true)
    | 23 => some (24, .move .right)
    | _ => none
  else if h : q.val < 84 then
    some (⟨q.val + 1, by omega⟩,
      if q.val % 2 = 0 then .write false else .move .right)
  else none

private def state (q : Fin 85) (left right : List Bool) : MachineState 84 :=
  ⟨q, Tape.mk₂ left right⟩

private def tailPort (n : Nat) : Fin 85 := ⟨84 - 2*n, by omega⟩
private def tailMid (n : Nat) : Fin 85 := ⟨83 - 2*n, by omega⟩

private theorem tail_write (n : Nat) (hn : n < 30) (symbol : Bool) :
    code (tailPort (n+1)) symbol = some (tailMid n, .write false) := by
  have h24 : ¬84 - 2*(n+1) < 24 := by omega
  have h84 : 84 - 2*(n+1) < 84 := by omega
  have even : (84 - 2*(n+1)) % 2 = 0 := by omega
  have next : 84 - 2*(n+1) + 1 = 83 - 2*n := by omega
  simp [code, tailPort, tailMid, h24, h84, even, next]

private theorem tail_move (n : Nat) (hn : n < 30) (symbol : Bool) :
    code (tailMid n) symbol = some (tailPort n, .move .right) := by
  have h24 : ¬83 - 2*n < 24 := by omega
  have h84 : 83 - 2*n < 84 := by omega
  have odd : ¬(83 - 2*n) % 2 = 0 := by omega
  have next : 83 - 2*n + 1 = 84 - 2*n := by omega
  simp [code, tailPort, tailMid, h24, h84, odd, next]

private theorem halted (left right : List Bool) :
    TM0.step code (state haltPort left right) = none := by
  simp [state, haltPort, TM0.step, code]

private def tailTrace (left old suffix : List Bool) : List (MachineState 84) :=
  match old with
  | [] => [state haltPort left suffix]
  | bit :: later =>
    [state (tailPort (later.length+1)) left ((bit :: later) ++ suffix),
     state (tailMid later.length) left (false :: (later ++ suffix))] ++
      tailTrace (false :: left) later suffix

private theorem tail_head (left old suffix : List Bool) :
    (tailTrace left old suffix).head? =
      some (state (tailPort old.length) left (old ++ suffix)) := by
  cases old <;> rfl

private theorem tail_length (left old suffix : List Bool) :
    (tailTrace left old suffix).length = 2*old.length+1 := by
  induction old generalizing left with
  | nil => rfl
  | cons bit later ih =>
    simp only [tailTrace, List.length_append, List.length_cons, List.length_nil, ih]
    omega

private theorem tail_runs (left old suffix : List Bool) (room : old.length ≤ 30) :
    RunsFrom code (state (tailPort old.length) left (old ++ suffix))
      (tailTrace left old suffix)
      (state haltPort ((List.replicate old.length false).reverse ++ left) suffix) := by
  induction old generalizing left with
  | nil =>
    refine ⟨rfl, .singleton _, rfl, halted _ _⟩
  | cons bit later ih =>
    have short : later.length < 30 := by simp only [List.length_cons] at room; omega
    have run := ih (false :: left) (by omega)
    have first : TM0.step code
        (state (tailPort (later.length+1)) left ((bit :: later) ++ suffix)) =
        some (state (tailMid later.length) left (false :: (later ++ suffix))) := by
      simp [state, TM0.step, tail_write _ short, Tape.mk₂]
    have second : TM0.step code
        (state (tailMid later.length) left (false :: (later ++ suffix))) =
        some (state (tailPort later.length) (false :: left) (later ++ suffix)) := by
      simp [state, TM0.step, tail_move _ short, Tape.mk₂]
    refine ⟨rfl, ?_, ?_, halted _ _⟩
    · change ([state (tailPort (later.length+1)) left ((bit :: later) ++ suffix),
        state (tailMid later.length) left (false :: (later ++ suffix))] ++
          tailTrace (false :: left) later suffix).IsChain _
      apply List.IsChain.append
      · simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using first
      · exact run.2.1
      · intro before hb after ha
        have hb' : state (tailMid later.length) left (false :: (later ++ suffix)) = before := by
          simpa using hb
        have ha' : state (tailPort later.length) (false :: left) (later ++ suffix) = after := by
          simpa only [tail_head, Option.mem_some_iff] using ha
        subst before; subst after
        exact second
    · change ([state (tailPort (later.length+1)) left ((bit :: later) ++ suffix),
        state (tailMid later.length) left (false :: (later ++ suffix))] ++
          tailTrace (false :: left) later suffix).getLast? = _
      rw [List.getLast?_append, run.2.2.1]
      simp [List.replicate_succ, List.reverse_cons, List.append_assoc]

private def prefixPort (bottom bit : Bool) (phase : Fin 6) : Fin 85 :=
  ⟨(entry bottom bit).val + phase.val, by
    have hp := phase.isLt
    cases bottom <;> cases bit <;> simp only [entry] <;> omega⟩

private def prefixTrace (bottom bit a b c : Bool) (left later suffix : List Bool) :
    List (MachineState 84) :=
  [state (prefixPort bottom bit 0) left (a :: b :: c :: (later ++ suffix)),
   state (prefixPort bottom bit 1) left (bottom :: b :: c :: (later ++ suffix)),
   state (prefixPort bottom bit 2) (bottom :: left) (b :: c :: (later ++ suffix)),
   state (prefixPort bottom bit 3) (bottom :: left) (true :: c :: (later ++ suffix)),
   state (prefixPort bottom bit 4) (true :: bottom :: left) (c :: (later ++ suffix)),
   state (prefixPort bottom bit 5) (true :: bottom :: left) (bit :: (later ++ suffix))]

private theorem runs_three (bottom bit a b c : Bool) (left later suffix : List Bool)
    (size : later.length = 30) :
    ∃ trace, RunsFrom code
      ⟨entry bottom bit, Tape.mk₂ left ((a :: b :: c :: later) ++ suffix)⟩ trace
      ⟨haltPort, Tape.mk₂ ((RawInit.rowBits bottom bit).reverse ++ left) suffix⟩ ∧
      trace.length = 67 := by
  let front := prefixTrace bottom bit a b c left later suffix
  let back := tailTrace (bit :: true :: bottom :: left) later suffix
  have run := tail_runs (bit :: true :: bottom :: left) later suffix (by omega)
  refine ⟨front ++ back, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · cases bottom <;> cases bit <;> rfl
    · apply List.IsChain.append
      · cases bottom <;> cases bit <;>
          simp [front, prefixTrace, prefixPort, entry, state, TM0.step, code,
            Tape.mk₂, List.isChain_cons_cons]
      · exact run.2.1
      · intro before hb after ha
        have hb' : state (prefixPort bottom bit 5)
            (true :: bottom :: left) (bit :: (later ++ suffix)) = before := by
          simpa [front, prefixTrace] using hb
        have ha' : state (tailPort later.length)
            (bit :: true :: bottom :: left) (later ++ suffix) = after := by
          simpa only [back, tail_head, Option.mem_some_iff] using ha
        subst before; subst after
        cases bottom <;> cases bit <;>
          simp [prefixPort, entry, state, TM0.step, code, tailPort, size, Tape.mk₂]
    · simp [front, back, List.getLast?_append, run.2.2.1, state,
        RawInit.rowBits, size, List.reverse_cons]
    · exact halted _ _
  · simp only [List.length_append, front, prefixTrace, List.length_cons,
      List.length_nil, back, tail_length, size]

/-- The overwrite length is a proof index only; no length, old data, or
answer is passed to the transition table. -/
theorem runs_list (bottom bit : Bool) (left old suffix : List Bool) (size : old.length = 33) :
    ∃ trace, RunsFrom code
      ⟨entry bottom bit, Tape.mk₂ left (old ++ suffix)⟩ trace
      ⟨haltPort, Tape.mk₂ ((RawInit.rowBits bottom bit).reverse ++ left) suffix⟩ ∧
      trace.length = 67 := by
  cases old with
  | nil => simp at size
  | cons a old =>
    cases old with
    | nil => simp at size
    | cons b old =>
      cases old with
      | nil => simp at size
      | cons c later =>
        exact runs_three bottom bit a b c left later suffix (by
          simp only [List.length_cons] at size
          omega)

/-- Same actual run, fixed common HALT, exact whole tape, and every-clock
visited space. Both outside lists and all 33 overwritten bits are arbitrary. -/
theorem actual (bottom bit : Bool) (left : List Bool) (old : Vector Bool 33)
    (suffix : List Bool) (inputLen : Nat) :
    ∃ trace final, RunsFrom code
      ⟨entry bottom bit, Tape.mk₂ left (old.toList ++ suffix)⟩ trace final ∧
      final.q = haltPort ∧
      final.Tape = Tape.mk₂ ((RawInit.rowBits bottom bit).reverse ++ left) suffix ∧
      trace.length ≤ 67 ∧
      (∀ clock, visitedSpace code inputLen (trace.take clock) ≤ inputLen + 135) ∧
      TM0.step code final = none := by
  obtain ⟨trace, run, size⟩ := runs_list bottom bit left old.toList suffix (by simp)
  refine ⟨trace, _, run, rfl, rfl, size.le, ?_, run.2.2.2⟩
  intro clock
  have bound := PSTRTMTrace002.visitedSpace_le code inputLen (trace.take clock)
  have short : (trace.take clock).length ≤ 67 := by
    rw [List.length_take, size]
    exact Nat.min_le_right _ _
  omega

/-- All code and all ports are chosen before every bit, archive, overwrite
vector, suffix, and resource proof index. -/
theorem fixed_writer : ∃ (m : Nat) (B : Machine m)
    (e : Bool → Bool → Fin (m+1)) (z : Fin (m+1)),
    ∀ (bottom bit : Bool) (left : List Bool) (old : Vector Bool 33)
      (suffix : List Bool) (inputLen : Nat),
    ∃ trace final, RunsFrom B
      ⟨e bottom bit, Tape.mk₂ left (old.toList ++ suffix)⟩ trace final ∧
      final.q = z ∧
      final.Tape = Tape.mk₂ ((RawInit.rowBits bottom bit).reverse ++ left) suffix ∧
      trace.length ≤ 67 ∧
      (∀ clock, visitedSpace B inputLen (trace.take clock) ≤ inputLen + 135) ∧
      TM0.step B final = none := by
  exact ⟨84, code, entry, haltPort, actual⟩

end PaperProofs.Common.Native.PSTRWordBool.Emit33

module
public import Structure.PA17_TM_RatArithmetic_Parse_002c

/-! Two real field scans after physical sign transport. In particular,
the denominator may be followed by TRUE: it is a suffix cell, not OWN00. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002

def signHalt (negative : Bool) : Fin 4 := if negative then 3 else 2

/-- The symbol read at the ORIGINAL sign cell chooses an actual finite
HALT port. Tag/sign data are retained, and the head really reaches num. -/
def signCursorMachine : Machine 3 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (signHalt symbol,.move .right)
  | _ => none

def signState (q : Fin 4) (left right : List Bool) : MachineState 3 := ⟨q,Turing.Tape.mk₂ left right⟩

def signTrace (base : List Bool) (tag negative : Bool) (tail : List Bool) : List (MachineState 3) :=
  [signState 0 base (tag::negative::tail),signState 1 (tag::base) (negative::tail),
    signState (signHalt negative) (negative::tag::base) tail]

theorem sign_runsFrom (base : List Bool) (tag negative : Bool) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom signCursorMachine (signState 0 base (tag::negative::tail))
      (signTrace base tag negative tail) (signState (signHalt negative) (negative::tag::base) tail) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · cases negative <;> simp [signTrace,signHalt,List.isChain_cons_cons,Turing.TM0.step,signCursorMachine,signState,Turing.Tape.mk₂]
  · cases negative <;> simp [Turing.TM0.step,signCursorMachine,signState,signHalt]

def tagMachine : Machine 2 := fun q _ =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (2,.move .right)
  | _ => none

def tagState (q : Fin 3) (left right : List Bool) : MachineState 2 := ⟨q,Turing.Tape.mk₂ left right⟩

def tagTrace (base : List Bool) (tag sign : Bool) (tail : List Bool) : List (MachineState 2) :=
  [tagState 0 base (tag::sign::tail),tagState 1 (tag::base) (sign::tail),tagState 2 (sign::tag::base) tail]

theorem tag_runsFrom (base : List Bool) (tag sign : Bool) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom tagMachine (tagState 0 base (tag::sign::tail))
      (tagTrace base tag sign tail) (tagState 2 (sign::tag::base) tail) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [tagTrace,List.isChain_cons_cons,Turing.TM0.step,tagMachine,tagState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,tagMachine,tagState]

def firstLeft (base first : List Bool) : List Bool := false::(PSTRTMRawNat010.leftBlocks first.reverse++base)

def bothLeft (base first second : List Bool) : List Bool := firstLeft (firstLeft base first) second

def fieldsMachine : Machine 35 := PSTRTMSeq005.seqMachine streamMachine streamMachine

def fieldsTrace (base first second suffix : List Bool) : List (MachineState 35) :=
  (streamTrace base [] first (rawField second++suffix)).map (PSTRTMSeq005.leftCfg (b:=17)) ++
    (streamTrace (firstLeft base first) [] second suffix).map (PSTRTMSeq005.rightCfg (a:=17))

def fieldsFinal (base first second suffix : List Bool) : MachineState 35 :=
  PSTRTMSeq005.rightCfg (a:=17) (streamFinal (firstLeft base first) second suffix)

theorem fields_runsFrom (base first second suffix : List Bool) :
    PSTRTMSeq005.RunsFrom fieldsMachine
      ⟨0,Turing.Tape.mk₂ base (rawField first++rawField second++suffix)⟩
      (fieldsTrace base first second suffix) (fieldsFinal base first second suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom streamMachine streamMachine
    (streamInitial base first (rawField second++suffix))
    (streamFinal base first (rawField second++suffix)) (streamFinal (firstLeft base first) second suffix)
    (streamTrace base [] first (rawField second++suffix)) (streamTrace (firstLeft base first) [] second suffix)
    (stream_runsFrom base first (rawField second++suffix)) (stream_runsFrom (firstLeft base first) second suffix)
  simpa only [fieldsTrace,fieldsMachine,fieldsFinal,streamInitial,streamFinal,streamState,
    firstLeft,List.append_assoc,PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

theorem fields_final_tape (base first second suffix : List Bool) :
    (fieldsFinal base first second suffix).Tape = Turing.Tape.mk₂ (bothLeft base first second) suffix := rfl

theorem fieldsTrace_length (base first second suffix : List Bool) :
    (fieldsTrace base first second suffix).length = first.length^2+second.length^2+9*(first.length+second.length)+4 := by
  change (((streamTrace base [] first (rawField second++suffix)).map (PSTRTMSeq005.leftCfg (a:=17) (b:=17))) ++
    (streamTrace (firstLeft base first) [] second suffix).map (PSTRTMSeq005.rightCfg (a:=17) (b:=17))).length = _
  rw [List.length_append,List.length_map,List.length_map,streamTrace_length,streamTrace_length]
  ring

def moveSignMachine : Machine 9 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (if symbol then 5 else 2,.move .left)
  | 2 => some (3,.write false)
  | 3 => some (4,.move .right)
  | 4 => some (8,.write false)
  | 5 => some (6,.write true)
  | 6 => some (7,.move .right)
  | 7 => some (8,.write false)
  | 8 => some (9,.move .right)
  | _ => none

def moveSignState (q : Fin 10) (left right : List Bool) : MachineState 9 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def moveSignTrace (base : List Bool) (negative : Bool) (tail : List Bool) : List (MachineState 9) :=
  [moveSignState 0 base (true::negative::tail),
   moveSignState 1 (true::base) (negative::tail),
   moveSignState (if negative then 5 else 2) base (true::negative::tail),
   moveSignState (if negative then 6 else 3) base (negative::negative::tail),
   moveSignState (if negative then 7 else 4) (negative::base) (negative::tail),
   moveSignState 8 (negative::base) (false::tail),
   moveSignState 9 (false::negative::base) tail]

/-- The original sign is actually read and moved into the original tag cell.
Its old cell becomes the numerator's real left false guard. -/
theorem moveSign_runsFrom (base : List Bool) (negative : Bool) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom moveSignMachine
      (moveSignState 0 base (true::negative::tail)) (moveSignTrace base negative tail)
      (moveSignState 9 (false::negative::base) tail) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · cases negative <;> simp [moveSignTrace,List.isChain_cons_cons,Turing.TM0.step,
      moveSignMachine,moveSignState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,moveSignMachine,moveSignState]

def ratMachine : Machine 45 := PSTRTMSeq005.seqMachine moveSignMachine fieldsMachine

def ratTrace (base : List Bool) (negative : Bool) (first second suffix : List Bool) : List (MachineState 45) :=
  (moveSignTrace base negative (rawField first++rawField second++suffix)).map (PSTRTMSeq005.leftCfg (b:=35)) ++
    (fieldsTrace (false::negative::base) first second suffix).map (PSTRTMSeq005.rightCfg (a:=9))

def ratFinal (base : List Bool) (negative : Bool) (first second suffix : List Bool) : MachineState 45 :=
  PSTRTMSeq005.rightCfg (a:=9) (fieldsFinal (false::negative::base) first second suffix)

theorem rat_runsFrom (base : List Bool) (negative : Bool) (first second suffix : List Bool) :
    PSTRTMSeq005.RunsFrom ratMachine
      ⟨0,Turing.Tape.mk₂ base (true::negative::(rawField first++rawField second++suffix))⟩
      (ratTrace base negative first second suffix) (ratFinal base negative first second suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom moveSignMachine fieldsMachine
    (moveSignState 0 base (true::negative::(rawField first++rawField second++suffix)))
    (moveSignState 9 (false::negative::base) (rawField first++rawField second++suffix))
    (fieldsFinal (false::negative::base) first second suffix)
    (moveSignTrace base negative (rawField first++rawField second++suffix))
    (fieldsTrace (false::negative::base) first second suffix)
    (moveSign_runsFrom base negative (rawField first++rawField second++suffix))
    (fields_runsFrom (false::negative::base) first second suffix)
  simpa only [ratMachine,ratTrace,ratFinal,moveSignState,PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

theorem rat_final_tape (base : List Bool) (negative : Bool) (first second suffix : List Bool) :
    (ratFinal base negative first second suffix).Tape =
      Turing.Tape.mk₂ (bothLeft (false::negative::base) first second) suffix := rfl

theorem ratTrace_length (base : List Bool) (negative : Bool) (first second suffix : List Bool) :
    (ratTrace base negative first second suffix).length =
      first.length^2+second.length^2+9*(first.length+second.length)+11 := by
  change (((moveSignTrace base negative (rawField first++rawField second++suffix)).map
      (PSTRTMSeq005.leftCfg (a:=9) (b:=35))) ++
    (fieldsTrace (false::negative::base) first second suffix).map
      (PSTRTMSeq005.rightCfg (a:=9) (b:=35))).length = _
  rw [List.length_append,List.length_map,List.length_map,fieldsTrace_length]
  change 7+(first.length^2+second.length^2+9*(first.length+second.length)+4) = _
  omega

/-- Original rational Datum, all signs and zero, with arbitrary genuine
left archive and right suffix. Sign transport supplies a genuine left guard. -/
theorem encodeDatum_rat_runsFrom (base suffix : List Bool) (x : Rat) :
    PSTRTMSeq005.RunsFrom ratMachine ⟨0,Turing.Tape.mk₂ base (encodeDatum (.rational x)++suffix)⟩
      (ratTrace base (sign x) (numeratorDigits x) (denominatorDigits x) suffix)
      (ratFinal base (sign x) (numeratorDigits x) (denominatorDigits x) suffix) := by
  have h := rat_runsFrom base (sign x) (numeratorDigits x) (denominatorDigits x) suffix
  simpa only [rational_datum,List.append_assoc,List.cons_append,List.nil_append] using h

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002

module
public import Structure.RootB23_Threshold_FinalSerialize_Shift_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.FinalSerialize.Rats
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002
open RootB23.Threshold.Window.MarshalSerialize

def fields (qs : List Rat) : List (List Bool) := qs.flatMap (fun q => [numeratorDigits q,denominatorDigits q])
def raw (q : Rat) (qs : List Rat) (tail : List Bool) : List Bool :=
  word (numeratorDigits q) (denominatorDigits q :: fields qs) tail
def datums (q : Rat) (qs : List Rat) : List Bool := encodeDatum (.rational q) ++ qs.flatMap (fun r => encodeDatum (.rational r))
def datumTail (q : Rat) : List Bool := false :: (encodeNat q.num.natAbs ++ encodeNat q.den)
def padding (n : Nat) : Nat := 4*n+3
def rawWidth (q : Rat) (qs : List Rat) : Nat := width (numeratorDigits q) (denominatorDigits q :: fields qs)

theorem fields_length (qs : List Rat) : (fields qs).length = 2*qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    change (numeratorDigits q :: denominatorDigits q :: fields qs).length = 2*(qs.length+1)
    simp only [List.length_cons,ih]
    omega

theorem raw_nil (q : Rat) (tail : List Bool) : raw q [] tail = Uncapped.Serialize.inputRight q.num.natAbs q.den tail := rfl

theorem raw_cons (q next : Rat) (qs : List Rat) (tail : List Bool) :
    raw q (next :: qs) tail = Uncapped.Serialize.inputRight q.num.natAbs q.den
      (true :: false :: raw next qs tail) := rfl

theorem datum_true (q : Rat) (nonnegative : 0≤q) : encodeDatum (.rational q) = true :: datumTail q := by
  have sign : decide (q<0) = false := by
    simp only [decide_eq_false_iff_not]
    exact not_lt.mpr nonnegative
  rw [encodeDatum,sign]
  rfl

def cap : Nat → Nat
  | 0 => 95
  | n+1 => (((141+Shift.cap (2*n+1)+1)+cap n+1)+60+1)

def parsedCode : Machine 141 := PSTRTMSeq005.seqMachine Uncapped.Serialize.code ratMachine

def code : (n : Nat) → Machine (cap n)
  | 0 => RatCodec.finalCode
  | n+1 => PSTRTMSeq005.seqMachine (a := (141+Shift.cap (2*n+1)+1)+cap n+1) (b := 60)
      (PSTRTMSeq005.seqMachine (a := 141+Shift.cap (2*n+1)+1) (b := cap n)
        (PSTRTMSeq005.seqMachine (a := 141) (b := Shift.cap (2*n+1)) parsedCode (Shift.code (2*n+1)))
        (code n)) RatCodec.restoreCode

def cost (q : Rat) (qs : List Rat) : Nat := match qs with
  | [] => 128*(RatCodec.width q)^2
  | next :: later =>
      (((128*(RatCodec.width q)^2+64*(RatCodec.width q)^2)+
        (18*rawWidth next later+42*(2*later.length+2)+8))+cost next later)+128*(RatCodec.width q)^2

theorem final_port (n : Nat) :
    PSTRTMSeq005.rightLabel (a := (141+Shift.cap (2*n+1)+1)+cap n+1) (60 : Fin 61) = maxLabel (cap (n+1)) := by
  apply Fin.ext
  change ((141+Shift.cap (2*n+1)+1)+cap n+1)+1+(60 : Fin 61).val =
    ((141+Shift.cap (2*n+1)+1)+cap n+1)+60+1
  simp only [show (60 : Fin 61).val=60 by decide]

theorem padding_step (n : Nat) : padding (n+1) = padding n+4 := by unfold padding;omega

/-- The fixed-length Rat chain consumes real fields and compacts every
remaining field after each Rat. It restores the earlier parsed Rat tags
only after its actual successor exists. All residue FALSEs remain before
the same arbitrary suffix and every TRUE delimiter is genuinely written. -/
theorem bounded (archive : List Bool) (q : Rat) (qs : List Rat) (tail : List Bool)
    (nonnegative : 0≤q) (restNonnegative : ∀ r ∈ qs,0≤r) :
    BoundedRun (code qs.length) (Tape.mk₂ (false :: false :: archive) (raw q qs tail))
      (maxLabel (cap qs.length))
      (Tape.mk₂ archive (datums q qs ++ true :: (List.replicate (padding qs.length) false ++ tail))) (cost q qs) := by
  induction qs generalizing archive q tail with
  | nil =>
    have last := RatCodec.final_bounded archive tail q nonnegative
    have base_port : (95 : Fin 96) = maxLabel 95 := by decide
    rw [base_port] at last
    simpa only [code,cap,maxLabel,raw_nil,datums,List.flatMap_nil,List.append_nil,
      padding,List.length_nil,Nat.mul_zero,Nat.zero_add,List.replicate_succ,List.replicate_zero,
      List.cons_append,List.nil_append,RatCodec.footerTail,cost] using last
  | cons next later ih =>
    have nextNonnegative := restNonnegative next (by simp)
    have laterNonnegative : ∀ r ∈ later,0≤r := by intro r member;exact restNonnegative r (by simp [member])
    have first := RatCodec.first_bounded archive (true :: false :: raw next later tail) q nonnegative
    have parsed := RatCodec.scan_bounded archive
      (Uncapped.Serialize.remainder (true :: false :: raw next later tail)) q
    have moved := Shift.bounded (ratLeft archive q) (numeratorDigits next) (denominatorDigits next :: fields later) tail
    have fieldCount : (denominatorDigits next :: fields later).length = 2*later.length+1 := by
      rw [List.length_cons,fields_length]
    rw [fieldCount] at moved
    have after := ih (ratLeft archive q) next (List.replicate 4 false ++ tail) nextNonnegative laterNonnegative
    let nextTail := datumTail next ++
      (later.flatMap (fun r => encodeDatum (.rational r)) ++ true ::
        (List.replicate (padding later.length) false ++ (List.replicate 4 false ++ tail)))
    have nextWord : datums next later ++ true ::
        (List.replicate (padding later.length) false ++ (List.replicate 4 false ++ tail)) = true :: nextTail := by
      rw [datums,datum_true next nextNonnegative]
      simp only [nextTail,List.cons_append,List.append_assoc]
    have restored := RatCodec.restore_bounded archive nextTail q nonnegative
    rw [← nextWord] at restored
    have actual := (((first.seq parsed).seq moved).seq after).seq restored
    rw [final_port] at actual
    have tailJoin : List.replicate (padding later.length) false ++ (List.replicate 4 false ++ tail) =
        List.replicate (padding (later.length+1)) false ++ tail := by
      rw [padding_step,List.replicate_add,List.append_assoc]
    rw [tailJoin] at actual
    rw [← raw_cons] at actual
    simpa only [code,cap,parsedCode,datums,List.flatMap_cons,
      List.append_assoc,List.length_cons,cost,rawWidth,Nat.add_assoc]
      using actual

def quadCode : Machine 1376 := code 3

end RootB23.Threshold.FinalSerialize.Rats

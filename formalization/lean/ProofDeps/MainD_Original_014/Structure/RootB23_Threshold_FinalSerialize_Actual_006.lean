module
public import Structure.RootB23_Threshold_FinalSerialize_Control_004
public import Structure.RootB23_Threshold_FinalSerialize_Rats_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.FinalSerialize.Actual
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002
open RootB23.Threshold.Window.MarshalSerialize

attribute [local implicit_reducible] Pass.walkCap Pass.backCap Control.clearMidCap Control.clearCap
  Shift.passCap Shift.moveCap Shift.cap Rats.cap

def frontCode : Machine 169 := PSTRTMSeq005.seqMachine Control.nineCode Control.entryCode
def ratsCode : Machine 1546 := PSTRTMSeq005.seqMachine frontCode Rats.quadCode
def returnCode : Machine 1553 := PSTRTMSeq005.seqMachine ratsCode PSTRTMThresholdBackupReturn227.returnMachine
def naturalCode : Machine 1592 := PSTRTMSeq005.seqMachine returnCode NatSplice.spliceMachine
def code : Machine 1614 := PSTRTMSeq005.seqMachine naturalCode Control.headerCode

def ratWord (t r o i : Rat) (suffix : List Bool) : List Bool :=
  Rats.datums t [r,o,i] ++ true :: (List.replicate 16 false ++ suffix)

private theorem raw_width_form (q : Rat) (qs : List Rat) :
    Rats.rawWidth q qs = (numeratorDigits q).length+(denominatorDigits q).length+
      ((Rats.fields qs).map List.length).sum := by
  change (numeratorDigits q).length+((denominatorDigits q).length+((Rats.fields qs).map List.length).sum) = _
  omega

private theorem fields_width_cons (q : Rat) (qs : List Rat) :
    ((Rats.fields (q :: qs)).map List.length).sum =
      (numeratorDigits q).length+(denominatorDigits q).length+((Rats.fields qs).map List.length).sum := by
  change (numeratorDigits q).length+((denominatorDigits q).length+((Rats.fields qs).map List.length).sum) = _
  omega

private theorem arithmetic (w a b c d x y z : Nat)
    (positive : 1≤w) (ha : a≤w) (hb : b≤w) (hc : c≤w) (hd : d≤w)
    (hx : x≤w) (hy : y≤w) (hz : z≤w) :
    (((128*a^2+64*a^2)+(18*x+260))+
      ((((128*b^2+64*b^2)+(18*y+176))+
        ((((128*c^2+64*c^2)+(18*z+92))+128*d^2)+128*c^2))+128*b^2))+128*a^2 ≤8192*w^2 := by
  have aa := Nat.pow_le_pow_left ha 2
  have bb := Nat.pow_le_pow_left hb 2
  have cc := Nat.pow_le_pow_left hc 2
  have dd := Nat.pow_le_pow_left hd 2
  have linear : w≤w^2 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤2)
  have xx := hx.trans linear
  have yy := hy.trans linear
  have zz := hz.trans linear
  have unit := positive.trans linear
  nlinarith only [aa,bb,cc,dd,xx,yy,zz,unit]

private theorem width_bits (b : Nat) (t r o i : Rat) : totalWidth b t r o i =
    natBits b+natBits t.num.natAbs+natBits t.den+natBits r.num.natAbs+natBits r.den+
      natBits o.num.natAbs+natBits o.den+natBits i.num.natAbs+natBits i.den := by
  simp only [totalWidth,nineFields,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    numeratorDigits_length,denominatorDigits_length,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  omega

theorem quad_cost_le (b : Nat) (t r o i : Rat) : Rats.cost t [r,o,i] ≤8192*(totalWidth b t r o i+1)^2 := by
  let w := totalWidth b t r o i+1
  have positive : 1≤w := by dsimp only [w];omega
  have ht : RatCodec.width t≤w := by unfold w;rw [width_bits];unfold RatCodec.width;omega
  have hr : RatCodec.width r≤w := by unfold w;rw [width_bits];unfold RatCodec.width;omega
  have ho : RatCodec.width o≤w := by unfold w;rw [width_bits];unfold RatCodec.width;omega
  have hi : RatCodec.width i≤w := by unfold w;rw [width_bits];unfold RatCodec.width;omega
  have h6 : Rats.rawWidth r [o,i]≤w := by
    unfold w
    rw [width_bits,raw_width_form,fields_width_cons,fields_width_cons]
    simp only [Rats.fields,List.flatMap_nil,List.map_nil,List.sum_nil,numeratorDigits_length,denominatorDigits_length]
    omega
  have h4 : Rats.rawWidth o [i]≤w := by
    unfold w
    rw [width_bits,raw_width_form,fields_width_cons]
    simp only [Rats.fields,List.flatMap_nil,List.map_nil,List.sum_nil,numeratorDigits_length,denominatorDigits_length]
    omega
  have h2 : Rats.rawWidth i []≤w := by
    unfold w
    rw [width_bits,raw_width_form]
    simp only [Rats.fields,List.flatMap_nil,List.map_nil,List.sum_nil,numeratorDigits_length,denominatorDigits_length]
    omega
  have bound := arithmetic w (RatCodec.width t) (RatCodec.width r) (RatCodec.width o) (RatCodec.width i)
    (Rats.rawWidth r [o,i]) (Rats.rawWidth o [i]) (Rats.rawWidth i []) positive ht hr ho hi h6 h4 h2
  simpa only [Rats.cost,List.length_cons,List.length_nil,Nat.reduceMul,Nat.reduceAdd] using bound

private theorem whole_fee (w b ratios : Nat) (small : b≤w) (ratiosSmall : ratios≤8192*(w+1)^2) :
    (((((4*w+170)+(2*b+11))+ratios)+(2*b+6))+64*(b+1)^2)+22 ≤32768*(w+1)^2 := by
  have square := Nat.pow_le_pow_left (Nat.add_le_add_right small 1) 2
  nlinarith only [square,small,ratiosSmall,Nat.zero_le (w^2)]

/-- One fixed nine-block consumer before ALL original field values.
The seven owned FALSEs are consumed only by the actual count5 header;
the original arbitrary suffix retains its absolute boundary behind the
sixteen real compression FALSEs. No internal blank equivalence is used. -/
theorem bounded (archive suffix : List Bool) (b : Nat) (t r o i : Rat)
    (ht : 0 ≤ t) (hr : 0 ≤ r) (ho : 0 ≤ o) (hi : 0 ≤ i) :
    BoundedRun code (Tape.mk₂ (List.replicate 7 false ++ archive) (inputRight b t r o i suffix)) 1614
      (Tape.mk₂ archive (encode [.natural b,.rational t,.rational r,.rational o,.rational i] ++
        List.replicate 16 false ++ suffix)) (32768*(totalWidth b t r o i+1)^2) := by
  let outer := List.replicate 6 false ++ archive
  let digits := PSTRTMNatValue017.rawPayload b
  let rest := [numeratorDigits t,denominatorDigits t,numeratorDigits r,denominatorDigits r,
    numeratorDigits o,denominatorDigits o,numeratorDigits i,denominatorDigits i]
  have cleared : BoundedRun Control.nineCode
      (Tape.mk₂ (false :: outer) (word digits rest (true :: suffix))) 158
      (Tape.mk₂ (false :: outer) (word digits rest (false :: suffix)))
      (4*width digits rest+170) := by
    have actual := Control.clear_bounded outer digits rest suffix
    simp only [rest,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul] at actual
    have port : maxLabel (Control.clearCap 8) = (158 : Fin 159) := by decide
    rw [port] at actual
    simpa only [Control.nineCode,rest,Nat.add_assoc,Nat.reduceAdd] using actual
  have entered := Control.entry_bounded outer digits (Rats.raw t [r,o,i] (false :: suffix))
  have restNonnegative : ∀ q ∈ [r,o,i],0 ≤ q := by
    intro q member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | rfl | empty
    · exact hr
    · exact ho
    · exact hi
    · cases empty
  have ratios : BoundedRun Rats.quadCode
      (Tape.mk₂ (false :: false :: Control.bArchive outer digits) (Rats.raw t [r,o,i] (false :: suffix))) 1376
      (Tape.mk₂ (Control.bArchive outer digits) (Rats.datums t [r,o,i] ++ true ::
        (List.replicate (Rats.padding [r,o,i].length) false ++ false :: suffix)))
      (Rats.cost t [r,o,i]) := by
    have actual := Rats.bounded (Control.bArchive outer digits) t [r,o,i] (false :: suffix) ht restNonnegative
    simp only [List.length_cons,List.length_nil,Nat.reduceAdd] at actual
    have port : maxLabel (Rats.cap 3) = (1376 : Fin 1377) := by decide
    rw [port] at actual
    simpa only [Rats.quadCode,List.length_cons,List.length_nil,Nat.reduceAdd] using actual
  have ratioWord : Rats.datums t [r,o,i] ++ true ::
      (List.replicate (Rats.padding [r,o,i].length) false ++ false :: suffix) = ratWord t r o i suffix := rfl
  rw [ratioWord] at ratios
  let tail := Rats.datumTail t ++
    ([r,o,i].flatMap (fun q => encodeDatum (.rational q)) ++ true :: (List.replicate 16 false ++ suffix))
  have ratTrue : ratWord t r o i suffix = true :: tail := by
    rw [ratWord,Rats.datums,Rats.datum_true t ht]
    simp only [tail,List.cons_append,List.append_assoc]
  rw [ratTrue] at ratios
  have returned : BoundedRun PSTRTMThresholdBackupReturn227.returnMachine
      (Tape.mk₂ (Control.bArchive outer digits) (true :: tail)) 6
      (Tape.mk₂ (false :: outer) (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: tail))
      (2*digits.length+6) := by
    have actual := PSTRTMThresholdBackupReturn227.return_runsFrom outer digits (true :: tail)
    have last : PSTRTMThresholdBackupReturn227.returnFinal outer digits (true :: tail) =
        ⟨6,Tape.mk₂ (false :: outer) (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: tail)⟩ := rfl
    rw [last] at actual
    exact ⟨PSTRTMThresholdBackupReturn227.returnTrace outer digits (true :: tail),actual,
      by rw [PSTRTMThresholdBackupReturn227.return_length]⟩
  have spliced := NatSplice.splice_bounded b (false :: outer) tail
  have header := Control.header_bounded archive (encodeDatum (.natural b) ++ true :: tail)
  have actual := ((((cleared.seq entered).seq ratios).seq returned).seq spliced).seq header
  change BoundedRun code _ (PSTRTMSeq005.rightLabel (a := 1592) (21 : Fin 22)) _ _ at actual
  have port : PSTRTMSeq005.rightLabel (a := 1592) (21 : Fin 22) = (1614 : Fin 1615) := by decide
  rw [port] at actual
  have output : encodeNat 5 ++ (encodeDatum (.natural b) ++ true :: tail) =
      encode [.natural b,.rational t,.rational r,.rational o,.rational i] ++ List.replicate 16 false ++ suffix := by
    rw [← ratTrue]
    simp only [encode,ratWord,Rats.datums,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.append_assoc,List.cons_append,List.nil_append]
  rw [output] at actual
  have width : width digits rest = totalWidth b t r o i := rfl
  have bits : digits.length = natBits b := by simp only [digits,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have small : natBits b≤totalWidth b t r o i := by rw [width_bits];omega
  have cost := whole_fee (totalWidth b t r o i) (natBits b) (Rats.cost t [r,o,i]) small (quad_cost_le b t r o i)
  change BoundedRun code
    (Tape.mk₂ (List.replicate 7 false ++ archive) (inputRight b t r o i suffix)) 1614
    (Tape.mk₂ archive (encode [.natural b,.rational t,.rational r,.rational o,.rational i] ++
      List.replicate 16 false ++ suffix)) _ at actual
  exact actual.mono (by simpa only [width,bits] using cost)

theorem actual_contract (archive suffix : List Bool) (b : Nat) (t r o i : Rat)
    (ht : 0 ≤ t) (hr : 0 ≤ r) (ho : 0 ≤ o) (hi : 0 ≤ i) :
    ∃ trace, PSTRTMSeq005.RunsFrom code
      ⟨0,Tape.mk₂ (List.replicate 7 false ++ archive) (inputRight b t r o i suffix)⟩ trace
      ⟨1614,Tape.mk₂ archive (encode [.natural b,.rational t,.rational r,.rational o,.rational i] ++
        List.replicate 16 false ++ suffix)⟩ ∧ trace.length≤32768*(totalWidth b t r o i+1)^2 ∧
      ∀ chargedLength clock, visitedSpace code chargedLength (trace.take clock) ≤
        chargedLength+65536*(totalWidth b t r o i+1)^2+1 := by
  obtain ⟨trace,run,time⟩ := bounded archive suffix b t r o i ht hr ho hi
  refine ⟨trace,run,time,?_⟩
  intro chargedLength clock
  have space := PSTRTMTrace002.visitedSpace_le code chargedLength (trace.take clock)
  have taken : (trace.take clock).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
  omega

end RootB23.Threshold.FinalSerialize.Actual

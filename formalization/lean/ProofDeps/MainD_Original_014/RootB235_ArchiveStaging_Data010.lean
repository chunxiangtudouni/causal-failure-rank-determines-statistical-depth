module
public import RootB235_ArchiveStaging_Rational009

/-! Every original Datum constructor is serialized on the same fixed
machine. Reverse list induction follows the physical archive cursor;
the original count bank and arbitrary normalized higher frame are retained.
No semantic data or length is passed into the machine. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
open Turing RationalControllerComputation
open RationalControllerComputation.PSTRSymbolicLaneArchive
open RationalControllerComputation.PSTRSymbolicLaneScan
open RationalControllerComputation.PSTRSymbolicPairedArchive
open RationalControllerComputation.PSTRSymbolicCursorArchive
open RationalControllerComputation.PSTRSymbolicRawLoop
open RationalControllerComputation.PA17TMRatArithmeticParse002

namespace DataLoop

def cleanDatum : Datum → List Bool
  | .natural n => List.replicate ((PSTRTMNatValue017.rawPayload n).length+1) false
  | .rational value => sign value::List.replicate
      ((numeratorDigits value).length+(denominatorDigits value).length+1) false

def clean (data : List Datum) : List Bool := data.flatMap cleanDatum

def cursor (root : List Bool) (data : List Datum) (higher output : List Bool) (gap : Nat) : Tape Bool :=
  (Tape.mk₂ ((navigationCells (allDatumPairs data)).reverse++false::true::root)
    (Macro.suffix higher output gap)).move .left

theorem word_raw (n : Nat) : Rational.numberWord (PSTRTMNatValue017.rawPayload n)=encodeNat n := by
  simp only [Rational.numberWord,PSTRTMNatValue017.rawPayload,List.length_ofFn,encodeNat]
  simp only [List.append_assoc,List.singleton_append]

theorem clean_bytes (value : Datum) : 2*(cleanDatum value).length=(encodeDatum value).length := by
  cases value with
  | natural n =>
    simp only [cleanDatum,List.length_replicate,encodeDatum,List.length_cons,
      PSTRTMLength004.encodeNat_length,PSTRTMNatValue017.rawPayload,List.length_ofFn]
    omega
  | rational value =>
    simp only [cleanDatum,List.length_replicate,encodeDatum,List.length_cons,List.length_append,
      List.length_nil,PSTRTMLength004.encodeNat_length,numeratorDigits,denominatorDigits,
      PSTRTMNatValue017.rawPayload,List.length_ofFn]
    omega

theorem clean_pairs (value : Datum) : (cleanDatum value).length=(datumPairs value).length := by
  have paired := pairs_bytes [value]
  have bytes := clean_bytes value
  simp only [allDatumPairs,List.flatMap_cons,List.flatMap_nil,List.append_nil] at paired
  omega

theorem clean_length (data : List Datum) : (clean data).length=(allDatumPairs data).length := by
  induction data with
  | nil => rfl
  | cons value later ih =>
    simp only [clean,List.flatMap_cons,List.length_append,allDatumPairs,←clean_pairs]
    exact congrArg (fun n => (cleanDatum value).length+n) ih

theorem boundary (root : List Bool) (data : List Datum) :
    ∃ bit left, (navigationCells (allDatumPairs data)).reverse++false::true::root=bit::true::left := by
  by_cases empty : data=[]
  · subst data
    exact ⟨false,root,rfl⟩
  · obtain ⟨earlier,last,shape⟩ := allDatumPairs_end data empty
    refine ⟨last,(navigationCells earlier).reverse++false::true::root,?_⟩
    simp [shape,navigationCells,List.reverse_append]

theorem cursor_source (root : List Bool) (data : List Datum) (higher output left : List Bool)
    (bit : Bool) (gap : Nat)
    (shape : (navigationCells (allDatumPairs data)).reverse++false::true::root=bit::true::left) :
    cursor root data higher output gap=Macro.source left higher output true bit gap := by
  simp only [cursor,shape,Macro.source,Tape.mk₂]
  simp

theorem cursor_snoc (root : List Bool) (data : List Datum) (value : Datum) (higher output : List Bool)
    (gap : Nat) : cursor root (data++[value]) higher output gap=
      (Tape.mk₂ ((navigationCells (datumPairs value)).reverse++
        ((navigationCells (allDatumPairs data)).reverse++false::true::root))
        (Macro.suffix higher output gap)).move .left := by
  simp only [cursor,allDatumPairs,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,navigationCells_append,List.reverse_append,List.append_assoc]

noncomputable def round (root : List Bool) (earlier : List Datum) (value : Datum)
    (higher output : List Bool) (gap : Nat) :
    Segment Control.code (Control.state 0 (cursor root (earlier++[value]) higher output gap))
      (Control.state 0 (cursor root earlier (cleanDatum value++higher) (encodeDatum value++output) gap))
      (100000*((datumPairs value).length+higher.length+output.length+gap+1)^2) := by
  classical
  let bit := Classical.choose (boundary root earlier)
  let left := Classical.choose (Classical.choose_spec (boundary root earlier))
  have shape := Classical.choose_spec (Classical.choose_spec (boundary root earlier))
  change (navigationCells (allDatumPairs earlier)).reverse++false::true::root=bit::true::left at shape
  rw [cursor_snoc,shape,cursor_source root earlier (cleanDatum value++higher)
    (encodeDatum value++output) left bit gap shape]
  cases value with
  | natural n =>
    let digits := PSTRTMNatValue017.rawPayload n
    have cells : navigationCells (datumPairs (.natural n))=MarkSeek.pairs digits++[true,false] := by
      rw [datumPairs_cells]
      rfl
    rw [cells]
    have path := Control.natural left digits higher output bit gap (rawPayload_nonempty n)
    have entry : (Tape.mk₂ ((MarkSeek.pairs digits++[true,false]).reverse++bit::true::left)
        (Macro.suffix higher output gap)).move .left=Control.naturalTape left digits higher output bit gap := by
      simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
        Control.naturalTape,Macro.source,Restore.pairs_reverse,Tape.mk₂]
      simp
    rw [entry]
    have outputEq : false::(List.replicate digits.length true++false::(digits++output))=
        encodeDatum (.natural n)++output := by
      rw [show encodeDatum (.natural n)=false::Rational.numberWord digits from by
        simp only [encodeDatum,digits,word_raw]]
      simp only [Rational.numberWord,List.cons_append,List.append_assoc]
    rw [outputEq] at path
    have widthEq : (datumPairs (.natural n)).length=digits.length+1 := by
      rw [←clean_pairs]
      simp only [cleanDatum,List.length_replicate,digits]
    simpa only [Control.cfg,cleanDatum,digits,List.replicate_succ] using
      path.weaken (t:=100000*((datumPairs (.natural n)).length+higher.length+output.length+gap+1)^2)
        (by
          have square := Nat.pow_le_pow_left (show digits.length+higher.length+output.length+gap+1≤
            (datumPairs (.natural n)).length+higher.length+output.length+gap+1 by rw [widthEq];omega) 2
          exact (Nat.mul_le_mul_left 2000 square).trans (Nat.mul_le_mul_right _ (by decide : 2000≤100000)))
  | rational value =>
    have denNonempty : denominatorDigits value≠[] := rawPayload_nonempty value.den
    cases denShape : denominatorDigits value with
    | nil => exact False.elim (denNonempty denShape)
    | cons first later =>
      cases numShape : (numeratorDigits value).reverse with
      | nil =>
        have original := congrArg List.reverse numShape
        simp only [List.reverse_reverse,List.reverse_nil] at original
        exact False.elim (rawPayload_nonempty value.num.natAbs original)
      | cons near older =>
        have numEq : numeratorDigits value=(near::older).reverse := by
          simpa only [List.reverse_reverse] using congrArg List.reverse numShape
        have cells : navigationCells (datumPairs (.rational value))=
            false::sign value::(MarkSeek.pairs (numeratorDigits value)++true::first::
              (MarkSeek.pairs later++[true,true])) := by
          rw [datumPairs_cells]
          simp only [pairedDatum,pairedRationalWord,denShape,rationalWord,zeroPairs,MarkSeek.pairs]
        rw [cells]
        have entry : (Tape.mk₂
            ((false::sign value::(MarkSeek.pairs (numeratorDigits value)++true::first::
              (MarkSeek.pairs later++[true,true]))).reverse++bit::true::left)
            (Macro.suffix higher output gap)).move .left=
              Rational.tape left (near::older).reverse later higher output bit (sign value) first gap := by
          rw [numEq]
          simp only [List.reverse_cons,List.reverse_append,List.reverse_nil,List.nil_append,
            List.cons_append,List.append_assoc,Rational.tape,Macro.source,Restore.pairs_reverse,
            List.reverse_reverse,Tape.mk₂]
          simp
        rw [entry]
        have path := Rational.actual left older later higher output bit (sign value) near first gap
        have outputEq : true::sign value::(Rational.numberWord (near::older).reverse++
            Rational.numberWord (first::later)++output)=encodeDatum (.rational value)++output := by
          rw [←numEq,←denShape]
          simp only [encodeDatum,numeratorDigits,denominatorDigits,word_raw,sign,List.cons_append,
            List.nil_append,List.append_assoc]
        have cleanEq : cleanDatum (.rational value)=sign value::
            List.replicate ((near::older).reverse.length+(first::later).length+1) false := by
          simp only [cleanDatum,numEq,denShape]
        have widthEq : (datumPairs (.rational value)).length=
            (near::older).reverse.length+(first::later).length+2 := by
          rw [←clean_pairs,cleanEq]
          simp only [List.length_cons,List.length_replicate]
        have highEq : sign value::(List.replicate
            ((near::older).reverse.length+(first::later).length+1) false++higher)=cleanDatum (.rational value)++higher := by
          simp only [cleanEq,List.cons_append]
        dsimp only at path
        rw [outputEq,highEq] at path
        simpa only [Control.cfg] using
          path.weaken (t:=100000*((datumPairs (.rational value)).length+higher.length+output.length+gap+1)^2)
            (by
              apply Nat.mul_le_mul_left 100000
              apply Nat.pow_le_pow_left
              rw [widthEq]
              omega)

def budget (limit : Nat) : Nat := 1000000*(limit+1)^2

noncomputable def actual (root : List Bool) (data : List Datum) (higher output : List Bool)
    (gap limit : Nat) (pairRoom : (allDatumPairs data).length+higher.length≤limit)
    (outputRoom : (data.flatMap encodeDatum).length+output.length≤limit) (gapRoom : gap≤limit) :
    Segment Control.code (Control.state 0 (cursor root data higher output gap))
      (Control.state 0 (cursor root [] (clean data++higher) (data.flatMap encodeDatum++output) gap))
      (data.length*budget limit+1) := by
  induction data using List.reverseRecOn generalizing higher output with
  | nil =>
    simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add,clean,List.flatMap_nil,List.nil_append] using
      Segment.point Control.code (Control.state 0 (cursor root [] higher output gap))
  | append_singleton earlier value ih =>
    have pairEq : (allDatumPairs (earlier++[value])).length=
        (allDatumPairs earlier).length+(datumPairs value).length := by
      simp only [allDatumPairs,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.length_append]
    have byteEq : ((earlier++[value]).flatMap encodeDatum).length=
        (earlier.flatMap encodeDatum).length+(encodeDatum value).length := by
      simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append]
    have front := round root earlier value higher output gap
    have frontRoom : 100000*((datumPairs value).length+higher.length+output.length+gap+1)^2≤budget limit := by
      rw [pairEq] at pairRoom
      unfold budget
      have sum : (datumPairs value).length+higher.length+output.length+gap+1≤3*limit+1 := by omega
      have square := Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left sum 2)
      exact square.trans (by nlinarith [Nat.zero_le (limit^2)])
    have pairRoom' : (allDatumPairs earlier).length+(cleanDatum value++higher).length≤limit := by
      simp only [List.length_append,clean_pairs]
      rw [pairEq] at pairRoom
      omega
    have outputRoom' : (earlier.flatMap encodeDatum).length+(encodeDatum value++output).length≤limit := by
      simp only [List.length_append]
      rw [byteEq] at outputRoom
      omega
    have rest := ih (cleanDatum value++higher) (encodeDatum value++output) pairRoom' outputRoom'
    have result := (front.weaken frontRoom).trans rest
    simpa only [clean,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.append_assoc,List.length_append,List.length_singleton,Nat.add_mul,Nat.one_mul] using
      result.weaken (t:=(earlier++[value]).length*budget limit+1) (by
        simp only [List.length_append,List.length_singleton,Nat.add_mul,Nat.one_mul]
        omega)

end DataLoop
end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging

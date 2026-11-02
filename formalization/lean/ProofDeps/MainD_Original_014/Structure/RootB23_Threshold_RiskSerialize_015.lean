module
public import Structure.RootB23_Threshold_DenominatorCopy_014
public import Structure.RootB23_Threshold_Uncapped_Serialize_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.RiskSerialize
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

def fourLeftCode : Machine 4 := fun q _=>match q.val with
  | 0=>some (1,.move .left)
  | 1=>some (2,.move .left)
  | 2=>some (3,.move .left)
  | 3=>some (4,.move .left)
  | _=>none
def fourLeftTrace (left : List Bool) (x y z t : Bool) (right : List Bool) : List (MachineState 4) :=
  [⟨0,Tape.mk₂ (x::y::z::t::left) right⟩,
   ⟨1,Tape.mk₂ (y::z::t::left) (x::right)⟩,
   ⟨2,Tape.mk₂ (z::t::left) (y::x::right)⟩,
   ⟨3,Tape.mk₂ (t::left) (z::y::x::right)⟩,
   ⟨4,Tape.mk₂ left (t::z::y::x::right)⟩]
theorem fourLeft_bounded (left : List Bool) (x y z t : Bool) (right : List Bool) :
    BoundedRun fourLeftCode (Tape.mk₂ (x::y::z::t::left) right) 4
      (Tape.mk₂ left (t::z::y::x::right)) 5 := by
  refine ⟨fourLeftTrace left x y z t right,⟨rfl,?_,rfl,?_⟩,by rfl⟩
  · simp [fourLeftTrace,List.isChain_cons_cons,TM0.step,fourLeftCode,Tape.mk₂]
  · simp [TM0.step,fourLeftCode]

/-- Erase the actual NUM-destination marker, rather than reinterpreting
its TRUE cell as an owned FALSE guard for the positive Rat serializer. -/
def clearMarkerCode : Machine 5 := fun q _=>match q.val with
  | 0=>some (1,.move .left)
  | 1=>some (2,.move .left)
  | 2=>some (3,.write false)
  | 3=>some (4,.move .right)
  | 4=>some (5,.move .right)
  | _=>none
def clearMarkerTrace (base word : List Bool) : List (MachineState 5) :=
  [⟨0,Tape.mk₂ (false::true::false::base) word⟩,
   ⟨1,Tape.mk₂ (true::false::base) (false::word)⟩,
   ⟨2,Tape.mk₂ (false::base) (true::false::word)⟩,
   ⟨3,Tape.mk₂ (false::base) (false::false::word)⟩,
   ⟨4,Tape.mk₂ (false::false::base) (false::word)⟩,
   ⟨5,Tape.mk₂ (false::false::false::base) word⟩]
theorem clearMarker_bounded (base word : List Bool) :
    BoundedRun clearMarkerCode (Tape.mk₂ (false::true::false::base) word) 5
      (Tape.mk₂ (false::false::false::base) word) 6 := by
  refine ⟨clearMarkerTrace base word,⟨rfl,?_,rfl,?_⟩,by rfl⟩
  · simp [clearMarkerTrace,List.isChain_cons_cons,TM0.step,clearMarkerCode,Tape.mk₂]
  · simp [TM0.step,clearMarkerCode]

def denLeft (base num : List Bool) : List Bool :=
  false::true::false::false::(PSTRTMRawNat010.leftBlocks num.reverse++false::true::false::base)
def word (num den : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks num++Uncapped.Serialize.marker (PA17TMRatArithmeticCopy006.workspace den)

def rewindCode : Machine 8 := PSTRTMSeq005.seqMachine fourLeftCode PSTRTMMulRewind085.rewindMachine
def connectCode : Machine 14 := PSTRTMSeq005.seqMachine rewindCode clearMarkerCode

theorem connect_bounded (base num den : List Bool) :
    BoundedRun connectCode (Tape.mk₂ (denLeft base num) (PA17TMRatArithmeticCopy006.workspace den)) 14
      (Tape.mk₂ (false::false::false::base) (word num den)) (2*num.length+14) := by
  have moved:=fourLeft_bounded (PSTRTMRawNat010.leftBlocks num.reverse++false::true::false::base)
    false true false false (PA17TMRatArithmeticCopy006.workspace den)
  have rewound : BoundedRun PSTRTMMulRewind085.rewindMachine
      (Tape.mk₂ (PSTRTMRawNat010.leftBlocks num.reverse++false::true::false::base)
        (false::false::true::false::PA17TMRatArithmeticCopy006.workspace den)) 3
      (Tape.mk₂ (false::true::false::base) (word num den)) (2*num.length+3) :=
    ⟨PSTRTMPairRewind105.fullTrace (true::false::base) num.reverse
        (false::false::true::false::PA17TMRatArithmeticCopy006.workspace den),
      PSTRTMPairRewind105.rewind_runsFrom _ _ _,
      by rw [PSTRTMPairRewind105.full_length,List.length_reverse]⟩
  exact ((moved.seq rewound).seq (clearMarker_bounded base (word num den))).mono (by omega)

def code : Machine 110 := PSTRTMSeq005.seqMachine connectCode Uncapped.Serialize.code

/-- Both copied fields are serialized by the already frozen actual
positive Rat producer. Its four real FALSE residue cells are retained. -/
theorem rational_bounded (base : List Bool) (risk : Rat) (positive : 0<risk) :
    BoundedRun code
      (Tape.mk₂ (denLeft base (PSTRTMNatValue017.rawPayload risk.num.natAbs))
        (PA17TMRatArithmeticCopy006.workspace (PSTRTMNatValue017.rawPayload risk.den))) 110
      (Tape.mk₂ (false::base) (encodeDatum (.rational risk)++Uncapped.Serialize.remainder []))
      (2*natBits risk.num.natAbs+14+128*(natBits risk.num.natAbs+natBits risk.den+1)^2) := by
  have connected:=connect_bounded base (PSTRTMNatValue017.rawPayload risk.num.natAbs)
    (PSTRTMNatValue017.rawPayload risk.den)
  have actual:=Uncapped.Serialize.actual_runsFrom (false::base) risk.num.natAbs risk.den []
  have lastEq : Uncapped.Serialize.final (false::base) risk.num.natAbs risk.den []=
      (⟨95,Tape.mk₂ (false::base)
        (encodeDatum (.rational risk)++Uncapped.Serialize.remainder [])⟩ : MachineState 95) := by
    change (⟨PSTRTMSeq005.rightLabel (a:=90) (4 : Fin 5),_⟩ : MachineState 95)=_
    have labelEq : PSTRTMSeq005.rightLabel (a:=90) (4 : Fin 5)=(95 : Fin 96) := by decide
    rw [labelEq]
    have nonnegative : ¬risk<0 := not_lt.mpr (le_of_lt positive)
    simp only [encodeDatum,nonnegative,decide_false,List.cons_append,List.nil_append,List.append_assoc]
  rw [lastEq] at actual
  have serialized : BoundedRun Uncapped.Serialize.code
      (Tape.mk₂ (false::false::false::base)
        (word (PSTRTMNatValue017.rawPayload risk.num.natAbs) (PSTRTMNatValue017.rawPayload risk.den))) 95
      (Tape.mk₂ (false::base) (encodeDatum (.rational risk)++Uncapped.Serialize.remainder []))
      (128*(natBits risk.num.natAbs+natBits risk.den+1)^2) :=
    ⟨_,actual,by simpa only [PA17TMRatArithmeticPairEncode017.payload_length] using
      Uncapped.Serialize.actual_time_le (false::base) risk.num.natAbs risk.den []⟩
  have joined:=connected.seq serialized
  exact joined.mono (by simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn];omega)

end RootB23.Threshold.RiskSerialize

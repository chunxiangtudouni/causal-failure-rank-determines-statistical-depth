module
public import Structure.RootB23_Threshold_SourceRoutes_010
public import Structure.RootB23_Threshold_PacketSteps_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.DenominatorRoute
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)

private def rightTrace (left right : List Bool) : List (MachineState 3) :=
  [⟨0,Tape.mk₂ left (false::true::false::right)⟩,
   ⟨1,Tape.mk₂ (false::left) (true::false::right)⟩,
   ⟨2,Tape.mk₂ (true::false::left) (false::right)⟩,
   ⟨3,Tape.mk₂ (false::true::false::left) right⟩]
private theorem right_bounded (left right : List Bool) :
    BoundedRun PacketSteps.skipCode (Tape.mk₂ left (false::true::false::right)) 3
      (Tape.mk₂ (false::true::false::left) right) 4 := by
  refine ⟨rightTrace left right,⟨rfl,?_,rfl,?_⟩,by rfl⟩
  · simp [rightTrace,List.isChain_cons_cons,TM0.step,PacketSteps.skipCode,Tape.mk₂]
  · simp [TM0.step,PacketSteps.skipCode]

def leftCode : Machine 3 := fun q _=>match q.val with
  | 0=>some (1,.move .left)
  | 1=>some (2,.move .left)
  | 2=>some (3,.move .left)
  | _=>none
private def leftTrace (left right : List Bool) : List (MachineState 3) :=
  [⟨0,Tape.mk₂ (false::true::false::left) right⟩,
   ⟨1,Tape.mk₂ (true::false::left) (false::right)⟩,
   ⟨2,Tape.mk₂ (false::left) (true::false::right)⟩,
   ⟨3,Tape.mk₂ left (false::true::false::right)⟩]
private theorem left_bounded (left right : List Bool) :
    BoundedRun leftCode (Tape.mk₂ (false::true::false::left) right) 3
      (Tape.mk₂ left (false::true::false::right)) 4 := by
  refine ⟨leftTrace left right,⟨rfl,?_,rfl,?_⟩,by rfl⟩
  · simp [leftTrace,List.isChain_cons_cons,TM0.step,leftCode,Tape.mk₂]
  · simp [TM0.step,leftCode]

def outToNumCode : Machine 65 := PSTRTMSeq005.seqMachine FactorWalk.denCode PacketSteps.skipCode
def outCode : Machine 67 := PSTRTMSeq005.seqMachine outToNumCode PA17TMRatArithmeticWidth018.scanMachine
def backNumCode : Machine 5 := PSTRTMSeq005.seqMachine
  PA17TMRatArithmeticParse002.backOneMachine PSTRTMMulRewind085.rewindMachine
def backFactorCode : Machine 9 := PSTRTMSeq005.seqMachine backNumCode leftCode
def backCode : Machine 92 := PSTRTMSeq005.seqMachine backFactorCode FactorBack.denCode
def route : RoutedCopy.Route :=
  ⟨padMachine (by decide : 67≤100) outCode,padMachine (by decide : 92≤100) backCode,
    padLabel (by decide : 67≤100) 67,padLabel (by decide : 92≤100) 92⟩

def tail (copied suffix : List Bool) : List Bool :=
  true::false::(PSTRTMIncrement009.blocks copied++false::false::suffix)
def right (digits depth b copied : List Bool) (gap : ℕ) (q : Rat) (suffix : List Bool) : List Bool :=
  FactorWalk.denRight digits depth b gap q (tail copied suffix)
def finish (depth b copied : List Bool) (gap : ℕ) (q : Rat) (left later : List Bool) : List Bool :=
  false::(PSTRTMRawNat010.leftBlocks copied.reverse++false::true::false::
    SourceRoutes.denFinish depth b gap q left later)
def cost (depth b copied : List Bool) (gap : ℕ) (q : Rat) : ℕ :=
  2*copied.length+SourceRoutes.denCost depth b gap q
def context (depth b copied : List Bool) (gap : ℕ) (q : Rat) : List Bool :=
  SourceRoutes.denContext depth b gap q++false::true::false::(PSTRTMIncrement009.blocks copied++[false])

theorem out_bounded (left digits depth b copied suffix : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0 ≤ q) (bNonempty : b≠[]) :
    BoundedRun outCode (Tape.mk₂ left (right digits depth b copied gap q suffix)) 67
      (Tape.mk₂ (finish depth b copied gap q left digits) (false::suffix))
      (2*digits.length+2*depth.length+2*gap+2*b.length+2*copied.length+
        64*(natBits q.num.natAbs+natBits q.den+1)^2+22) := by
  let base:=SourceRoutes.denFinish depth b gap q left digits
  have first:=FactorWalk.denominator_bounded left digits depth b (tail copied suffix) gap q nonnegative bNonempty
  have next:=right_bounded base (PSTRTMIncrement009.blocks copied++false::false::suffix)
  have scanned : BoundedRun PA17TMRatArithmeticWidth018.scanMachine
      (Tape.mk₂ (false::true::false::base) (PSTRTMIncrement009.blocks copied++false::false::suffix)) 1
      (Tape.mk₂ (finish depth b copied gap q left digits) (false::suffix)) (2*copied.length+2) := by
    refine ⟨PA17TMRatArithmeticWidth018.scanTrace (false::true::false::base) copied false suffix,?_,
      by rw [PA17TMRatArithmeticWidth018.scanTrace_length]⟩
    exact PA17TMRatArithmeticWidth018.scan_runsFrom _ _ _ _
  exact ((first.seq next).seq scanned).mono (by omega)

theorem back_bounded (archive digits depth b copied suffix : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0 ≤ q) (depthNonempty : depth≠[]) :
    BoundedRun backCode (Tape.mk₂ (finish depth b copied gap q (false::archive) digits) (false::suffix)) 92
      (Tape.mk₂ (false::archive) (right digits depth b copied gap q suffix))
      (2*digits.length+2*depth.length+2*gap+2*b.length+2*copied.length+
        128*(natBits q.num.natAbs+natBits q.den+1)^2+30) := by
  let base:=SourceRoutes.denFinish depth b gap q (false::archive) digits
  have one : BoundedRun PA17TMRatArithmeticParse002.backOneMachine
      (Tape.mk₂ (finish depth b copied gap q (false::archive) digits) (false::suffix)) 1
      (Tape.mk₂ (PSTRTMRawNat010.leftBlocks copied.reverse++false::true::false::base) (false::false::suffix)) 2 :=
    ⟨PA17TMRatArithmeticParse002.backOneTrace
      (PSTRTMRawNat010.leftBlocks copied.reverse++false::true::false::base) false (false::suffix),
      PA17TMRatArithmeticParse002.backOne_runsFrom _ _ _,by rfl⟩
  have rewind : BoundedRun PSTRTMMulRewind085.rewindMachine
      (Tape.mk₂ (PSTRTMRawNat010.leftBlocks copied.reverse++false::true::false::base) (false::false::suffix)) 3
      (Tape.mk₂ (false::true::false::base) (PSTRTMIncrement009.blocks copied++false::false::suffix))
      (2*copied.length+3) :=
    ⟨PSTRTMPairRewind105.fullTrace (true::false::base) copied.reverse (false::false::suffix),
      PSTRTMPairRewind105.rewind_runsFrom _ _ _,by rw [PSTRTMPairRewind105.full_length,List.length_reverse]⟩
  have moved:=left_bounded base (PSTRTMIncrement009.blocks copied++false::false::suffix)
  have source:=FactorBack.denominator_bounded archive digits depth b (tail copied suffix) gap q nonnegative depthNonempty
  exact (((one.seq rewind).seq moved).seq source).mono (by omega)

theorem word (digits depth b copied : List Bool) (gap : ℕ) (q : Rat) (suffix : List Bool) :
    right digits depth b copied gap q suffix=RoutedCopy.fieldWord (context depth b copied gap q) digits suffix := by
  rw [right,SourceRoutes.den_word]
  simp only [RoutedCopy.fieldWord,context,tail,List.append_assoc,List.cons_append,List.nil_append]

theorem correct (depth b copied : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0 ≤ q) (depthNonempty : depth≠[]) (bNonempty : b≠[]) :
    RoutedCopy.RouteCorrect route (context depth b copied gap q) (finish depth b copied gap q)
      (cost depth b copied gap q) := by
  have old:=SourceRoutes.denominator_correct depth b gap q nonnegative depthNonempty bNonempty
  refine ⟨rfl,?_,?_,?_⟩
  · intro left bit later
    simp only [finish]
    rw [old.finish_cons]
  · intro left later suffix
    have actual:=out_bounded left later depth b copied suffix gap q nonnegative bNonempty
    rw [word] at actual
    have padded:=PA17TMRatArithmeticFarLoad031.bounded_pad (by decide : 67≤100) actual
    exact padded.mono (by dsimp only [cost,SourceRoutes.denCost];omega)
  · intro archive later suffix
    have actual:=back_bounded archive later depth b copied suffix gap q nonnegative depthNonempty
    rw [word] at actual
    have padded:=PA17TMRatArithmeticFarLoad031.bounded_pad (by decide : 92≤100) actual
    exact padded.mono (by dsimp only [cost,SourceRoutes.denCost];omega)

end RootB23.Threshold.DenominatorRoute

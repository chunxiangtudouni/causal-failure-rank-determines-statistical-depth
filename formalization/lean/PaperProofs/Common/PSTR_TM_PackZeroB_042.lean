module
public import PaperProofs.Common.PSTR_TM_PackColumns_038
public import PaperProofs.Common.PSTR_TM_PackEOF_040

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackZeroB042
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036

private theorem append_link (xs ys : List (MachineState 193)) (last first : MachineState 193)
    (hx : xs.IsChain (fun a b => Turing.TM0.step packMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step packMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step packMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step packMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def eofLeft (a : Bool) (left first : List Bool) : List Bool :=
  false :: false :: true :: false :: false :: PSTRTMPackEOF040.context a left first.reverse

def tailTrace (a : Bool) (left first : List Bool) : List (MachineState 193) :=
  [state 193 (eofLeft a left first) [true]] ++
    ((PSTRTMAlignUnit032.separateTrace false a left first.reverse []).map liftAlign ++
      [state 0 (true :: false :: true :: a :: left)
        (PSTRTMIncrement009.blocks first ++ [false,false,true,false])])

theorem tail_head (a : Bool) (left first : List Bool) :
    (tailTrace a left first).head? = some (state 193 (eofLeft a left first) [true]) := rfl

theorem tail_last (a : Bool) (left first : List Bool) :
    (tailTrace a left first).getLast? = some
      (state 0 (true :: false :: true :: a :: left) (PSTRTMIncrement009.blocks first ++ [false,false,true,false])) := by
  rw [tailTrace, ← List.append_assoc, List.getLast?_append]
  rfl

theorem tail_length (a : Bool) (left first : List Bool) :
    (tailTrace a left first).length = 10 * first.length + 30 := by
  simp only [tailTrace, List.length_append, List.length_cons, List.length_nil, List.length_map,
    PSTRTMAlignUnit032.separate_length, List.length_reverse]
  omega

theorem tail_chain (a : Bool) (left first : List Bool) :
    (tailTrace a left first).IsChain (fun before after => Turing.TM0.step packMachine before = some after) := by
  have htail := append_link
    ((PSTRTMAlignUnit032.separateTrace false a left first.reverse []).map liftAlign)
    [state 0 (true :: false :: true :: a :: left) (PSTRTMIncrement009.blocks first ++ [false,false,true,false])] _ _
    (PSTRTMPackLift037.align_chain _ (PSTRTMAlignUnit032.separate_chain false a left first.reverse [])) (.singleton _)
    (by simp [List.getLast?_map, PSTRTMAlignUnit032.separate_last]) rfl
    (PSTRTMPackLift037.align_transfer _ _)
  have hh : (((PSTRTMAlignUnit032.separateTrace false a left first.reverse []).map liftAlign) ++
      [state 0 (true :: false :: true :: a :: left) (PSTRTMIncrement009.blocks first ++ [false,false,true,false])]).head? = some
        (liftAlign (PSTRTMAlignCode030.state (PSTRTMAlignCode030.hole 2 false)
          (false :: true :: false :: false :: PSTRTMPackEOF040.context a left first.reverse) [false,true])) := by
    simp [List.head?_append, List.head?_map, PSTRTMAlignUnit032.separate_head,
      PSTRTMAlignUnit032.frontierLeft, PSTRTMPackEOF040.context]
  apply append_link _ _ _ _ (.singleton _) htail rfl hh
  exact PSTRTMPackEOF040.eof_enter _

/-- An actual A digit is paired with an actual newly-written flagged0
when B reaches its real isolated blank EOF. All A remainder is preserved. -/
def zeroBTrace (a : Bool) (left first : List Bool) : List (MachineState 193) :=
  PSTRTMPackColumns038.dispatchTrace a left
    (PSTRTMIncrement009.blocks first ++ [false,false,true,false,false,false]) ++
    ((PSTRTMPackEOF040.scanTrace a false false left first []).map liftAlign ++ tailTrace a left first)

theorem zeroB_head (a : Bool) (left first : List Bool) :
    (zeroBTrace a left first).head? = some
      (state 0 left (a :: true :: (PSTRTMIncrement009.blocks first ++ [false,false,true,false,false,false]))) := rfl

theorem zeroB_last (a : Bool) (left first : List Bool) :
    (zeroBTrace a left first).getLast? = some
      (state 0 (true :: false :: true :: a :: left) (PSTRTMIncrement009.blocks first ++ [false,false,true,false])) := by
  simp [zeroBTrace, List.getLast?_append, tail_last]

theorem zeroB_length (a : Bool) (left first : List Bool) :
    (zeroBTrace a left first).length = 12 * first.length + 41 := by
  simp only [zeroBTrace, PSTRTMPackColumns038.dispatchTrace, List.length_append,
    List.length_cons, List.length_nil, List.length_map, PSTRTMPackEOF040.scan_length, tail_length]
  omega

theorem zeroB_chain (a : Bool) (left first : List Bool) :
    (zeroBTrace a left first).IsChain (fun before after => Turing.TM0.step packMachine before = some after) := by
  have htail := append_link
    ((PSTRTMPackEOF040.scanTrace a false false left first []).map liftAlign) (tailTrace a left first) _ _
    (PSTRTMPackLift037.align_chain _ (PSTRTMPackEOF040.scan_chain a false false left first []))
    (tail_chain a left first)
    (by simp [List.getLast?_map, PSTRTMPackEOF040.scan_last, eofLeft]) (tail_head a left first)
    (PSTRTMPackEOF040.eof_write _)
  have hh : (((PSTRTMPackEOF040.scanTrace a false false left first []).map liftAlign) ++
      tailTrace a left first).head? = some
        (liftAlign (PSTRTMAlignCode030.state 0 left
          (a :: true :: (PSTRTMIncrement009.blocks first ++ [false,false,true,false,false,false])))) := by
    simp [List.head?_append, List.head?_map, PSTRTMPackEOF040.scan_head]
  exact append_link _ _ _ _ (PSTRTMPackColumns038.dispatch_chain a left _) htail rfl hh
    (PSTRTMPackColumns038.dispatch_enter a left _)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackZeroB042

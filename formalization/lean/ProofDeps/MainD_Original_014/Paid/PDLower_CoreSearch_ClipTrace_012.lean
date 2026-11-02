module

public import Paid.PDLower_CoreSearch_SelectorLayout_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

def KeepsLow (original current : ℕ→Cell) : Prop := ∀ slot<29,current slot=original slot

theorem KeepsLow.refl (values : ℕ→Cell) : KeepsLow values values := fun _ _ => rfl

theorem KeepsLow.trans {first middle last : ℕ→Cell} (one : KeepsLow first middle) (two : KeepsLow middle last) :
    KeepsLow first last := fun slot bounded => (two slot bounded).trans (one slot bounded)

theorem KeepsLow.update {first current : ℕ→Cell} (kept : KeepsLow first current) (target : ℕ) (value : Cell)
    (above : 29≤target) : KeepsLow first (Function.update current target value) := by
  intro slot bounded
  rw [Function.update_of_ne (by omega : slot≠target)]
  exact kept slot bounded

theorem KeepsLow.heap {before after : State} {first last : ℕ→Cell} (kept : KeepsLow first last)
    (initialHeader : Header before 0 first) (finalHeader : Header after 0 last) :
    ∀ slot<29,after.heap slot=before.heap slot := by
  intro slot bounded
  have initial := initialHeader.value slot (by unfold headerWords;omega)
  have final := finalHeader.value slot (by unfold headerWords;omega)
  simp only [Nat.zero_add] at initial final
  exact final.trans ((kept slot bounded).trans initial.symm)

/-- Real46-op conditional clipping, including ACTUAL producers of zero
and one. This internal tail takes the newly recomputed31 value; the final
bracket entry below supplies it by execution, never by a caller oracle. -/
theorem clip_trace (program : Program) (input : List Cell) (origin : ℕ) (before : State) (values : ℕ→Cell) (weight : ℚ)
    (position : before.pc=origin) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (ratio : values 31=.rational weight) (fetched : FetchesCode program origin (clipCode origin)) :
    ∃ (after : State) (finalValues : ℕ→Cell),ScalarSegment program input before after 660 ∧
      Header after 0 finalValues ∧ KeepsLow values finalValues ∧ after.register .fresh=.natural 0 ∧
      after.pc=origin+46 ∧ after.heap 29=.rational (clipRat weight) := by
  have fetch := clipCode_fetches program origin fetched
  let v1 := Function.update (Function.update values 41 (.rational 0)) 42 (.rational 1)
  obtain ⟨t1,s1,h1,l1,c1,time1,header1,fresh1,pc1,_out1,mem1⟩ :=
    selectorConstants_trace program input before values header fresh (by rw [position];exact fetch.constants)
  have run1 : ScalarSegment program input before s1 135 := ⟨t1,h1,l1,c1,time1,mem1⟩
  have keep1 : KeepsLow values v1 := ((KeepsLow.refl values).update 41 _ (by decide)).update 42 _ (by decide)
  have ratio1 : v1 31=.rational weight := by simp [v1,ratio]
  obtain ⟨t2,h2,l2,c2,time2,header2,mem2⟩ :=
    clipLowerGuard_trace weight program input s1 v1 header1 fresh1 ratio1 (by simp [v1])
      (by rw [pc1,position];exact fetch.lower)
  let s2 := comparisonStoredResult s1 31 41 (decide (weight<0))
  let v2 := Function.update v1 40 (.natural (if weight<0 then 1 else 0))
  have run2 : ScalarSegment program input s1 s2 165 := ⟨t2,h2,l2,c2,time2,mem2⟩
  have keep2 : KeepsLow values v2 := keep1.update 40 _ (by decide)
  have fields2 := comparisonStored_fields s1 31 41 (decide (weight<0))
  have fresh2 : s2.register .fresh=.natural 0 := fields2.2.2.1.trans fresh1
  have pc2 : s2.pc=origin+18 := by
    dsimp only [s2]
    rw [fields2.2.2.2.2.1,pc1,position]
  by_cases below : weight<0
  · let s3 : State := {s2 with pc:=origin+42}
    have flag : s2.register .flag=.natural 1 := by simpa [s2,below] using fields2.2.2.2.1
    have run3 : ScalarSegment program input s2 s3 30 :=
      ScalarSegment.control program input s2 (.branchZero .flag (origin+19) (origin+42)) (origin+42)
        (by rw [pc2];exact fetch.lowerBranch) (by simp [Instruction.execute,Cell.nat?,flag])
    obtain ⟨t4,s4,h4,l4,c4,time4,header4,fresh4,pc4,_out4,mem4⟩ :=
      clipZero_trace weight program input s3 v2 header2 fresh2 below (by exact fetch.zero)
    let v4 := Function.update v2 29 (.rational (clipRat weight))
    have run4 : ScalarSegment program input s3 s4 75 := ⟨t4,h4,l4,c4,time4,mem4⟩
    have value := header4.value 29 (by decide)
    refine ⟨s4,v4,(((run1.trans run2).trans run3).trans run4).mono (by decide),header4,
      keep2.update 29 _ (by decide),fresh4,?_,?_⟩
    · dsimp only [s3] at pc4
      omega
    · simpa only [Nat.zero_add,Function.update_self] using value
  · let s3 : State := {s2 with pc:=origin+19}
    have flag : s2.register .flag=.natural 0 := by simpa [s2,below] using fields2.2.2.2.1
    have run3 : ScalarSegment program input s2 s3 30 :=
      ScalarSegment.control program input s2 (.branchZero .flag (origin+19) (origin+42)) (origin+19)
        (by rw [pc2];exact fetch.lowerBranch) (by simp [Instruction.execute,Cell.nat?,flag])
    have ratio2 : v2 31=.rational weight := by simp [v2,ratio1]
    have one2 : v2 42=.rational 1 := by simp [v2,v1]
    obtain ⟨t4,h4,l4,c4,time4,header4,mem4⟩ :=
      clipUpperGuard_trace weight program input s3 v2 header2 fresh2 one2 ratio2 (by exact fetch.upper)
    let s4 := comparisonStoredResult s3 42 31 (decide (1<weight))
    let v4 := Function.update v2 40 (.natural (if 1<weight then 1 else 0))
    have run4 : ScalarSegment program input s3 s4 165 := ⟨t4,h4,l4,c4,time4,mem4⟩
    have keep4 : KeepsLow values v4 := keep2.update 40 _ (by decide)
    have fields4 := comparisonStored_fields s3 42 31 (decide (1<weight))
    have fresh4 : s4.register .fresh=.natural 0 := fields4.2.2.1.trans fresh2
    have pc4 : s4.pc=origin+29 := by
      dsimp only [s4]
      rw [fields4.2.2.2.2.1]
    by_cases above : 1<weight
    · let s5 : State := {s4 with pc:=origin+37}
      have flag : s4.register .flag=.natural 1 := by simpa [s4,above] using fields4.2.2.2.1
      have run5 : ScalarSegment program input s4 s5 30 :=
        ScalarSegment.control program input s4 (.branchZero .flag (origin+30) (origin+37)) (origin+37)
          (by rw [pc4];exact fetch.upperBranch) (by simp [Instruction.execute,Cell.nat?,flag])
      obtain ⟨t6,s6,h6,l6,c6,time6,header6,fresh6,pc6,_out6,mem6⟩ :=
        clipOne_trace weight program input s5 v4 header4 fresh4 above (by exact fetch.one)
      let v6 := Function.update v4 29 (.rational (clipRat weight))
      have run6 : ScalarSegment program input s5 s6 75 := ⟨t6,h6,l6,c6,time6,mem6⟩
      let after : State := {s6 with pc:=origin+46}
      have jumpPC : s6.pc=origin+41 := by dsimp only [s5] at pc6;omega
      have jump : ScalarSegment program input s6 after 30 :=
        ScalarSegment.control program input s6 (.jump (origin+46)) (origin+46) (by rw [jumpPC];exact fetch.oneJump) rfl
      have value := header6.value 29 (by decide)
      refine ⟨after,v6,((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans jump).mono (by decide),
        header6,keep4.update 29 _ (by decide),fresh6,rfl,?_⟩
      simpa only [Nat.zero_add,Function.update_self] using value
    · let s5 : State := {s4 with pc:=origin+30}
      have flag : s4.register .flag=.natural 0 := by simpa [s4,above] using fields4.2.2.2.1
      have run5 : ScalarSegment program input s4 s5 30 :=
        ScalarSegment.control program input s4 (.branchZero .flag (origin+30) (origin+37)) (origin+30)
          (by rw [pc4];exact fetch.upperBranch) (by simp [Instruction.execute,Cell.nat?,flag])
      have ratio4 : v4 31=.rational weight := by simp [v4,ratio2]
      obtain ⟨t6,s6,h6,l6,c6,time6,header6,fresh6,pc6,_out6,mem6⟩ :=
        clipCopy_trace weight program input s5 v4 header4 fresh4 ratio4 below above (by exact fetch.copy)
      let v6 := Function.update v4 29 (.rational (clipRat weight))
      have run6 : ScalarSegment program input s5 s6 105 := ⟨t6,h6,l6,c6,time6,mem6⟩
      let after : State := {s6 with pc:=origin+46}
      have jumpPC : s6.pc=origin+36 := by dsimp only [s5] at pc6;omega
      have jump : ScalarSegment program input s6 after 30 :=
        ScalarSegment.control program input s6 (.jump (origin+46)) (origin+46) (by rw [jumpPC];exact fetch.copyJump) rfl
      have value := header6.value 29 (by decide)
      refine ⟨after,v6,((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans jump).mono (by decide),
        header6,keep4.update 29 _ (by decide),fresh6,rfl,?_⟩
      simpa only [Nat.zero_add,Function.update_self] using value

end PDLower.CoreSearch

module

public import Paid.PDROC_D27Prepare_Tail_001
public import Paid.PDROC_D27Prepare_Resources_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Tail

def binomialRegion : Finset ℕ := {12,32,33,40,41,42,48,49,50}

structure BinomialData (P : Parameters) (memory : SlotMemory) (i : ℕ) : Prop where
  stages : Has memory 0 (.natural P.certificate.stages)
  tools : Has memory 1 (.natural P.tools)
  natZero : Has memory 13 (.natural 0)
  natOne : Has memory 14 (.natural 1)
  ratZero : Has memory 16 (.rational 0)
  ratOne : Has memory 17 (.rational 1)
  dyadic : Has memory 39 (.rational ((1/2 : ℚ)^P.certificate.stages))
  index : Has memory 40 (.natural i)
  choose : Has memory 41 (.rational (P.certificate.stages.choose i))
  tail : Has memory 42 (.rational (Binomial.partialTail P.certificate.stages P.tools i))

theorem binomial_setup_memory_bounds (memory : SlotMemory) (B : ℕ)
    (bounded : MemoryBounds 64 B memory)
    (hzero : Has memory 13 (.natural 0)) (hone : Has memory 17 (.rational 1))
    (hrzero : Has memory 16 (.rational 0)) :
    SequenceMemoryBounds binomialSetupCommands memory 64 B := by
  let m1 := memory.write 40 (.natural 0)
  let m2 := m1.write 41 (.rational 1)
  let m3 := m2.write 42 (.rational 0)
  have b1 : MemoryBounds 64 B m1 := bounded.write 40 _ (by decide)
    (by simpa only [hzero.2] using bounded.values 13 hzero.1)
  have b2 : MemoryBounds 64 B m2 := b1.write 41 _ (by decide)
    (by simpa only [hone.2] using bounded.values 17 hone.1)
  have b3 : MemoryBounds 64 B m3 := b2.write 42 _ (by decide)
    (by simpa only [hrzero.2] using bounded.values 16 hrzero.1)
  have e1 : (SlotCommand.copy 13 40).eval memory=some m1 := copy_eval memory 13 40 _ hzero
  have e2 : (SlotCommand.copy 17 41).eval m1=some m2 :=
    copy_eval m1 17 41 _ (by simpa [m1,Has,SlotMemory.write] using hone)
  have e3 : (SlotCommand.copy 16 42).eval m2=some m3 :=
    copy_eval m2 16 42 _ (by simpa [m2,m1,Has,SlotMemory.write] using hrzero)
  exact SequenceMemoryBounds.cons _ _ memory m1 64 B bounded e1
    (SequenceMemoryBounds.cons _ _ m1 m2 64 B b1 e2
      (SequenceMemoryBounds.cons _ [] m2 m3 64 B b2 e3
        (SequenceMemoryBounds.nil m3 64 B b3)))

theorem binomial_initial_data (P : Parameters) (memory : SlotMemory)
    (hN : Has memory 0 (.natural P.certificate.stages)) (hK : Has memory 1 (.natural P.tools))
    (hzero : Has memory 13 (.natural 0)) (hone : Has memory 14 (.natural 1))
    (hrzero : Has memory 16 (.rational 0)) (hrone : Has memory 17 (.rational 1))
    (hpower : Has memory 39 (.rational ((1/2 : ℚ)^P.certificate.stages))) :
    BinomialData P (binomialInitial memory) 0 := by
  constructor
  · simpa [Has,binomialInitial,SlotMemory.write] using hN
  · simpa [Has,binomialInitial,SlotMemory.write] using hK
  · simpa [Has,binomialInitial,SlotMemory.write] using hzero
  · simpa [Has,binomialInitial,SlotMemory.write] using hone
  · simpa [Has,binomialInitial,SlotMemory.write] using hrzero
  · simpa [Has,binomialInitial,SlotMemory.write] using hrone
  · simpa [Has,binomialInitial,SlotMemory.write] using hpower
  · simp [Has,binomialInitial,SlotMemory.write]
  · simp [Has,binomialInitial,SlotMemory.write]
  · simp [Has,binomialInitial,SlotMemory.write,Binomial.partialTail_zero]

def binomialAddMemory (P : Parameters) (memory : SlotMemory) (i : ℕ) : SlotMemory :=
  if P.tools < i then memory.write 42
    (.rational ((Binomial.partialTail P.certificate.stages P.tools i : ℚ)+P.certificate.stages.choose i))
  else memory

theorem binomial_add_tail (P : Parameters) (memory : SlotMemory) (i : ℕ)
    (old : Has memory 42 (.rational (Binomial.partialTail P.certificate.stages P.tools i))) :
    Has (binomialAddMemory P memory i) 42
      (.rational (Binomial.partialTail P.certificate.stages P.tools (i+1))) := by
  by_cases included : P.tools < i
  · have equal := Binomial.partialTail_rat_succ P.certificate.stages P.tools i
    rw [ite_eq_left included] at equal
    simpa only [binomialAddMemory,ite_eq_left included,equal] using
      Has.write_same memory 42 (.rational
        ((Binomial.partialTail P.certificate.stages P.tools i : ℚ)+P.certificate.stages.choose i))
  · have equal := Binomial.partialTail_rat_succ P.certificate.stages P.tools i
    rw [ite_eq_right included,add_zero] at equal
    simpa only [binomialAddMemory,ite_eq_right included,equal] using old

theorem binomial_add_preserves (P : Parameters) (memory : SlotMemory) (i address : ℕ)
    (value : Cell) (outside : address≠42) (old : Has memory address value) :
    Has (binomialAddMemory P memory i) address value := by
  unfold binomialAddMemory
  split
  · exact Has.write_other memory address 42 value _ old outside
  · exact old

theorem binomial_next_preserves (memory : SlotMemory) (N i address : ℕ) (value : Cell)
    (outside : address≠48 ∧ address≠49 ∧ address≠32 ∧ address≠33 ∧
      address≠50 ∧ address≠41 ∧ address≠40) (old : Has memory address value) :
    Has (binomialNext memory N i) address value := by
  rcases outside with ⟨h48,h49,h32,h33,h50,h41,h40⟩
  simpa [Has,binomialNext,SlotMemory.write,h48,h49,h32,h33,h50,h41,h40] using old

def binomialCycleMemory (P : Parameters) (memory : SlotMemory) (i : ℕ) : SlotMemory :=
  binomialNext (binomialAddMemory P memory i) P.certificate.stages i

theorem binomial_cycle_data (P : Parameters) (memory : SlotMemory) (i : ℕ)
    (data : BinomialData P memory i) : BinomialData P (binomialCycleMemory P memory i) (i+1) := by
  have preserve (address : ℕ) (value : Cell)
      (outside : address≠42 ∧ address≠48 ∧ address≠49 ∧ address≠32 ∧ address≠33 ∧
        address≠50 ∧ address≠41 ∧ address≠40) (old : Has memory address value) :
      Has (binomialCycleMemory P memory i) address value :=
    binomial_next_preserves _ _ _ address value outside.2
      (binomial_add_preserves P memory i address value outside.1 old)
  constructor
  · exact preserve 0 _ (by decide) data.stages
  · exact preserve 1 _ (by decide) data.tools
  · exact preserve 13 _ (by decide) data.natZero
  · exact preserve 14 _ (by decide) data.natOne
  · exact preserve 16 _ (by decide) data.ratZero
  · exact preserve 17 _ (by decide) data.ratOne
  · exact preserve 39 _ (by decide) data.dyadic
  · exact binomial_next_index _ _ _
  · exact binomial_next_choose _ _ _
  · exact binomial_next_preserves _ _ _ 42 _ (by decide) (binomial_add_tail P memory i data.tail)

end PDROC.D27Prepare.Tail

module
public import Structure.PA17_TM_RatArithmetic_CachedPass_036g

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
open PA17TMRatArithmeticBankWalk033

theorem cachedFieldCost_le (j k : Nat) (records : List RecordSpec)
    (n previous width following total : Nat) (hp : previous+width≤total) (hf : width+following≤total) :
    cachedFieldFee j k records (n+k*previous) width following ≤
      width*(2*n+(2*k+4)*total+4*k+2*totalGap records+4*totalWidth records+21*j+61)+2 := by
  unfold cachedFieldFee cycleSurcharge
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  have hk := Nat.mul_le_mul_left (2*k) hp
  nlinarith

def cachedTraceFee (j k : Nat) (records : List RecordSpec) (n a b c d : Nat) : Nat :=
  cachedFieldFee j k records n a (b+c+d)+
  cachedFieldFee j k records (n+k*a) b (c+d)+3+
  cachedFieldFee j k records (n+k*a+k*b) c d+
  cachedFieldFee j k records (n+k*a+k*b+k*c) d 0+(2*(a+b+c+d)+31)

theorem cachedTraceFee_le (j k : Nat) (records : List RecordSpec) (n a b c d : Nat) :
    cachedTraceFee j k records n a b c d≤cachedPassFee j k records (a+b+c+d) n := by
  let width := a+b+c+d
  have hc1 := cachedFieldCost_le j k records n 0 a (b+c+d) width
    (by dsimp [width];omega) (by dsimp [width];omega)
  have hc2 := cachedFieldCost_le j k records n a b (c+d) width
    (by dsimp [width];omega) (by dsimp [width];omega)
  have hc3 := cachedFieldCost_le j k records n (a+b) c d width
    (by dsimp [width];omega) (by dsimp [width];omega)
  have hc4 := cachedFieldCost_le j k records n (a+b+c) d 0 width
    (by dsimp [width];omega) (by dsimp [width];omega)
  dsimp [cachedTraceFee,cachedFieldFee,cycleSurcharge,cachedPassFee,width] at hc1 hc2 hc3 hc4 ⊢
  nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036

module

public import SquaresInCircles.Eight.Frames.Diagonal.Selection
public import SquaresInCircles.Eight.Frames.Diagonal.Trigonometry
public import SquaresInCircles.Eight.Frames.Mid.HighVaryingCalculus

/-!
# Eight squares: the two varying target-middle endpoint selections

The moving multiplier stays correlated with the angle throughout each
whole interval.  In the negative-source family its product with the
support harmonic is decreasing, so the actual final endpoint supplies
the uniform derivative reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighMidSupports
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalSupport
open FrameDiagonalSelection FrameDiagonalTrigonometry
open FrameMidHighVaryingCalculus (lam domain domain_quadrant multiplier_bounds)

theorem positive_trigonometry {x : ℝ} (hx : x∈domain true) :
    (99/1000:ℝ)<Real.sin x ∧ (91/100:ℝ)<Real.cos x := by
  have hsl := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤1/10 by norm_num)
  have hcr := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤21/50 by norm_num)
  norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hsl hcr
  have hs := sine_monotone
    (rational_quadrant (show (1/10:ℝ)∈Icc 0 (71/50) by norm_num))
    (domain_quadrant hx) hx.1
  have hc := cosine_antitone (domain_quadrant hx)
    (rational_quadrant (show (21/50:ℝ)∈Icc 0 (71/50) by norm_num)) hx.2
  constructor <;> linarith [hsl.1,hcr.2.2.1]

theorem negative_trigonometry {x : ℝ} (hx : x∈domain false) :
    (389/1000:ℝ)<Real.sin x ∧ (33/40:ℝ)<Real.cos x := by
  have hsl := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤2/5 by norm_num)
  have hcr := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤3/5 by norm_num)
  norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hsl hcr
  have hs := sine_monotone
    (rational_quadrant (show (2/5:ℝ)∈Icc 0 (71/50) by norm_num))
    (domain_quadrant hx) hx.1
  have hc := cosine_antitone (domain_quadrant hx)
    (rational_quadrant (show (3/5:ℝ)∈Icc 0 (71/50) by norm_num)) hx.2
  constructor <;> linarith [hsl.1,hcr.2.2.1]

def product (x : ℝ) : ℝ := lam false x*FrameDiagonalTrigonometry.harmonic (157/250) (343/250) x
def productD (x : ℝ) : ℝ :=
  -(73/200)*FrameDiagonalTrigonometry.harmonic (157/250) (343/250) x+
    lam false x*((157/250)*Real.cos x-(343/250)*Real.sin x)

theorem product_deriv (x : ℝ) : HasDerivAt product (productD x) x := by
  convert (FrameMidHighVaryingCalculus.lam_deriv false x).mul
    (harmonic_deriv (157/250) (343/250) x) using 1
  · rfl
  · dsimp [productD,FrameMidHighVaryingCalculus.m]

theorem productD_negative {x : ℝ} (hx : x∈domain false) : productD x<0 := by
  have ht := negative_trigonometry hx
  have hl : (421/1000:ℝ)≤lam false x ∧ lam false x≤247/500 := by
    dsimp [lam,FrameMidHighVaryingCalculus.origin,FrameMidHighVaryingCalculus.m,
      domain,FrameMidHighVaryingCalculus.left,FrameMidHighVaryingCalculus.right] at *
    constructor <;> linarith [hx.1,hx.2]
  have hH : 1<FrameDiagonalTrigonometry.harmonic (157/250) (343/250) x := by
    dsimp [FrameDiagonalTrigonometry.harmonic]
    linarith [ht.1,ht.2]
  have hD : (157/250)*Real.cos x-(343/250)*Real.sin x<(19/200:ℝ) := by
    linarith [Real.cos_le_one x,ht.1]
  have hp := mul_le_mul_of_nonneg_left hD.le (show 0≤lam false x by linarith [hl.1])
  dsimp [productD]
  nlinarith [hl.2]

theorem product_antitone : AntitoneOn product (domain false) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (product_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => product_deriv x
  · exact fun x hx => (productD_negative (Ioo_subset_Icc_self hx)).le

theorem negative_product_lower {x : ℝ} (hx : x∈domain false) :
    (93/250)*k+q<lam false x*((157/250)*Real.sin x+(343/250)*Real.cos x) := by
  have hm := product_antitone hx (FrameMidHighVaryingCalculus.right_mem false) hx.2
  change product (3/5)≤product x at hm
  have ht := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤3/5 by norm_num)
  have hend : (93/250)*k+q<product (3/5) := by
    dsimp [product,lam,FrameMidHighVaryingCalculus.origin,
      FrameMidHighVaryingCalculus.m,FrameDiagonalTrigonometry.harmonic,k,q]
    norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at ht ⊢
    linarith [ht.1,ht.2.2.1]
  exact hend.trans_le hm

theorem positive_product_lower {x : ℝ} (hx : x∈domain true) :
    (93/250)*k+q<lam true x*((157/250)*Real.sin x+(343/250)*Real.cos x) := by
  have ht := positive_trigonometry hx
  have hl : (123/250:ℝ)≤lam true x := by
    dsimp [lam,FrameMidHighVaryingCalculus.origin,FrameMidHighVaryingCalculus.m,
      domain,FrameMidHighVaryingCalculus.left,FrameMidHighVaryingCalculus.right] at *
    linarith [hx.2]
  have hH : (131/100:ℝ)<(157/250)*Real.sin x+(343/250)*Real.cos x := by
    linarith [ht.1,ht.2]
  have hp := mul_le_mul (show (123/250:ℝ)≤lam true x from hl) hH.le
    (by norm_num : (0:ℝ)≤131/100) (by linarith : 0≤lam true x)
  norm_num [k,q]
  nlinarith

theorem target_last_of_product {B lam' x : ℝ} (hB : B∈arc true)
    (hx : x∈Icc 0 (Real.pi/2)) (hl : lam'∈Icc 0 (31/50:ℝ))
    (hp : (93/250)*k+q<lam'*((157/250)*Real.sin x+(343/250)*Real.cos x)) :
    target true false lam' x b2≤target true false lam' x B := by
  have ht := FrameLowPair.quadrant hx
  have hD : -(1:ℝ)≤Real.sin x-Real.cos x := by linarith
  have hmul := mul_le_mul_of_nonneg_left hD hl.1
  have hU : 0≤-targetU true false lam' x := by
    norm_num [targetU,primary,sign,k]
    linarith [hl.2]
  apply target_last_of_derivative hB
  intro z hz
  have hr := slope_mid_bounds hz
  have hbound := mul_le_mul_of_nonneg_left hr.2.le hU
  norm_num [targetU,targetV,primary,transverse,sign] at hbound ⊢
  nlinarith

theorem varying_target {i : Bool} {B x : ℝ} (hB : B∈arc true)
    (hx : x∈domain i) :
    target true false (lam i x) x b2≤target true false (lam i x) x B := by
  have hl := multiplier_bounds hx
  apply target_last_of_product hB (domain_quadrant hx)
    ⟨by linarith [hl.1],hl.2.1⟩
  cases i
  · exact negative_product_lower hx
  · exact positive_product_lower hx

end SquaresInCircles.Eight.FrameHighMidSupports

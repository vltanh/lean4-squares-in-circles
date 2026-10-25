module

public import SquaresInCircles.Eight.TableFree.FrameHighLowDiagonalScalar

/-!
# Exact geometry of the low-axial contact boundary

The same explicit contact height supports both the ordinary high
marker and its quarter-rotated continuation.  Every derivative and
domain estimate below follows from the circle chart and the actual
closed angular interval.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowAxialGeometry
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus

def domain : Set ℝ := Icc (0:ℝ) (23/50)
def normalDomain : Set ℝ := Icc (11/100:ℝ) (23/50)
def upperDomain : Set ℝ := Icc (0:ℝ) (11/100)
def Z (x : ℝ) : ℝ := 1/2+(1/2)*Real.cos x+(1/2-a0)*Real.sin x
def P (x : ℝ) : ℝ := (a0-1/2)*Real.cos x+(1/2)*Real.sin x
def Pd (x : ℝ) : ℝ := -(a0-1/2)*Real.sin x+(1/2)*Real.cos x

theorem quadrant {x : ℝ} (hx : x∈domain) : x∈Icc 0 (Real.pi/2) :=
  ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩

theorem Z_deriv (x : ℝ) : HasDerivAt Z (-P x) x := by
  have h := (((Real.hasDerivAt_cos x).const_mul (1/2)).const_add (1/2)).fun_add
    ((Real.hasDerivAt_sin x).const_mul (1/2-a0))
  have he : -P x=1/2*-Real.sin x+(1/2-a0)*Real.cos x := by simp only [P]; ring
  rw [he]
  exact h

theorem P_deriv (x : ℝ) : HasDerivAt P (Pd x) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul (a0-1/2)).fun_add
    ((Real.hasDerivAt_sin x).const_mul (1/2))
  have he : Pd x=(a0-1/2)*-Real.sin x+1/2*Real.cos x := by simp only [Pd]; ring
  rw [he]
  exact h

theorem Pd_eq (x : ℝ) : Pd x=Z x-1/2 := by dsimp [Pd,Z]; ring
@[simp] theorem Z_zero : Z 0=1 := by norm_num [Z]
@[simp] theorem P_zero : P 0=a0-1/2 := by simp [P]

theorem P_positive {x : ℝ} (hx : x∈domain) : 0<P x := by
  have ht := FrameLowPair.quadrant (quadrant hx)
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  have hcos : 0<Real.cos x := by nlinarith
  have hp := mul_pos (show 0<a0-1/2 by linarith [a0_precise.1]) hcos
  dsimp [P]
  linarith

theorem Z_antitone : AntitoneOn Z domain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (Z_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => Z_deriv x
  · exact fun x hx => neg_nonpos.mpr (P_positive (Ioo_subset_Icc_self hx)).le

theorem final_trig : (44394/100000:ℝ)<Real.sin (23/50) ∧
    Real.sin (23/50)<8879/20000 ∧ (17921/20000:ℝ)<Real.cos (23/50) ∧
      Real.cos (23/50)<44803/50000 := by
  have hs := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤23/50 by norm_num)
  have hsu := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤23/50 by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤23/50 by norm_num)
  have hcu := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤23/50 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C12,HighOrderTaylor.C14,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs hsu hc hcu
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem endpoint_heights : (1793/2000:ℝ)<Z (11/100) ∧ Z (11/100)<897/1000 ∧
    (541/1000:ℝ)<Z (23/50) ∧ Z (23/50)<543/1000 := by
  have ht0 := FrameHighLowDiagonalCurve.final_trig
  have ht1 := final_trig
  have hs0L := mul_le_mul
    (show (914575670/1000000000:ℝ)≤a0-1/2 by linarith [a0_precise.1]) ht0.1.le
    (by norm_num : (0:ℝ)≤10977830/100000000) (by linarith [a0_precise.1] : 0≤a0-1/2)
  have hs0U := mul_le_mul
    (show a0-1/2≤914575672/1000000000 by linarith [a0_precise.2]) ht0.2.1.le
    (by linarith [ht0.1] : 0≤Real.sin (11/100)) (by norm_num : (0:ℝ)≤914575672/1000000000)
  have hs1L := mul_le_mul
    (show (914575670/1000000000:ℝ)≤a0-1/2 by linarith [a0_precise.1]) ht1.1.le
    (by norm_num : (0:ℝ)≤44394/100000) (by linarith [a0_precise.1] : 0≤a0-1/2)
  have hs1U := mul_le_mul
    (show a0-1/2≤914575672/1000000000 by linarith [a0_precise.2]) ht1.2.1.le
    (by linarith [ht1.1] : 0≤Real.sin (23/50)) (by norm_num : (0:ℝ)≤914575672/1000000000)
  dsimp only [Z]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith [ht0.2.2.1,ht0.2.2.2,ht1.2.2.1,ht1.2.2.2]

theorem Z_bounds {x : ℝ} (hx : x∈domain) : (541/1000:ℝ)<Z x ∧ Z x≤1 := by
  have hl := Z_antitone hx (show (23/50:ℝ)∈domain by constructor <;> norm_num) hx.2
  have hu := Z_antitone (show (0:ℝ)∈domain by constructor <;> norm_num) hx hx.1
  rw [Z_zero] at hu
  exact ⟨endpoint_heights.2.2.1.trans_le hl,hu⟩

theorem Z_extended {x : ℝ} (hx : x∈domain) : Z x∈extendedDomain := by
  have hh := Z_bounds hx
  constructor <;> linarith [hh.1,hh.2]

theorem normal_chart {x : ℝ} (hx : x∈normalDomain) : Z x∈Icc b2 c0 := by
  have hdom : x∈domain := ⟨by linarith [hx.1],hx.2⟩
  have hlo := (Z_bounds hdom).1
  have hu := Z_antitone (show (11/100:ℝ)∈domain by constructor <;> norm_num) hdom hx.1
  constructor <;> linarith [b2_bounds.2,endpoint_heights.2.1,c0_bounds.1]

theorem normal_Pd {x : ℝ} (hx : x∈normalDomain) : 0<Pd x ∧ Pd x<199/500 := by
  have hdom : x∈domain := ⟨by linarith [hx.1],hx.2⟩
  have hz := Z_bounds hdom
  have hu := Z_antitone (show (11/100:ℝ)∈domain by constructor <;> norm_num) hdom hx.1
  rw [Pd_eq]
  constructor <;> linarith [endpoint_heights.2.1]

theorem P_monotone : MonotoneOn P domain := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (P_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => P_deriv x
  · intro x hx
    rw [Pd_eq]
    linarith [(Z_bounds (Ioo_subset_Icc_self hx)).1]

theorem P_lower {x : ℝ} (hx : x∈domain) : (1829/2000:ℝ)<P x := by
  have hh := P_monotone (show (0:ℝ)∈domain by constructor <;> norm_num) hx hx.1
  rw [P_zero] at hh
  linarith [a0_precise.1]

theorem normal_P_lower {x : ℝ} (hx : x∈normalDomain) : (24/25:ℝ)<P x := by
  have hh := P_monotone (show (11/100:ℝ)∈domain by constructor <;> norm_num)
    ⟨by linarith [hx.1],hx.2⟩ hx.1
  have ht := FrameHighLowDiagonalCurve.final_trig
  have hm := mul_le_mul
    (show (914575670/1000000000:ℝ)≤a0-1/2 by linarith [a0_precise.1]) ht.2.2.1.le
    (by norm_num : (0:ℝ)≤99395609/100000000) (by linarith [a0_precise.1] : 0≤a0-1/2)
  dsimp only [P] at hh ⊢
  linarith [ht.1]

theorem upper_chart {x : ℝ} (hx : x∈upperDomain) :
    (896/1000:ℝ)<Z x ∧ Z x≤1 ∧ (79/100:ℝ)<A (Z x) ∧ A (Z x)<903/1000 := by
  have hdom : x∈domain := ⟨hx.1,by linarith [hx.2]⟩
  have hlo := Z_antitone hdom (show (11/100:ℝ)∈domain by constructor <;> norm_num) hx.2
  have hu := (Z_bounds hdom).2
  have hz : (896/1000:ℝ)<Z x := by linarith [endpoint_heights.1]
  have hc := extended_circle (Z_extended hdom)
  have hp := extended_shift_pos (Z_extended hdom)
  have hlowSq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤349/250)
    (show (349/250:ℝ)≤Z x+1/2 by linarith) 2
  have huppSq := pow_le_pow_left₀ (show 0≤Z x+1/2 by linarith)
    (show Z x+1/2≤3/2 by linarith) 2
  norm_num [Q0] at hc
  refine ⟨hz,hu,?_,?_⟩
  · by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le (show A (Z x)+1/2≤129/100 by linarith) 2
    nlinarith
  · by_contra! hbad
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1403/1000)
      (show (1403/1000:ℝ)≤A (Z x)+1/2 by linarith) 2
    nlinarith

theorem upper_marker_bounds {x : ℝ} (hx : x∈upperDomain) :
    0<Gd (Z x) ∧ Gd (Z x)<41/40 ∧ (11/20:ℝ)<Gdd (Z x) := by
  have hz := upper_chart hx
  have hp : 0<A (Z x)+1/2 := by linarith [hz.2.2.1]
  have hr0 : 0 ≤ slope (Z x) := div_nonneg (by linarith [hz.1]) hp.le
  have hr : slope (Z x)<50/43 := by
    apply (div_lt_iff₀ hp).2
    linarith [hz.2.1,hz.2.2.1]
  have hcube := pow_le_pow_left₀ hp.le
    (show A (Z x)+1/2≤1403/1000 by linarith [hz.2.2.2]) 3
  have hcurv : (11/20:ℝ)<FrameHighArc.v*Q0/(A (Z x)+1/2)^3 := by
    apply (lt_div_iff₀ (pow_pos hp 3)).2
    norm_num [FrameHighArc.v,Q0] at *
    nlinarith
  rw [mul_div_assoc] at hcurv
  dsimp only [Gd,Gdd,slopeD]
  refine ⟨?_,?_,hcurv⟩ <;> norm_num [FrameHighArc.u,FrameHighArc.v] <;> linarith

end SquaresInCircles.Eight.TableFree.FrameHighLowAxialGeometry

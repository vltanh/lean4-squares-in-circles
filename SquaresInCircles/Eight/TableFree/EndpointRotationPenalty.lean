module

public import SquaresInCircles.Eight.TableFree.OrdinaryNegativeEnvelope

/-!
# An original rotated endpoint costs at least its zero-angle stress

Uncompiled source draft.  The stress coefficient ranges continuously
over `[4/5,2]` and the signed angle over `[-7/10,7/10]`.  Positive
angles use one square-root tangent and a half-angle bound.  Negative
angles use the proved norm concavity and monotonicity, with one exact
comparison at coefficient `4/5`.  The estimate retains a uniform strict
reserve for every nonzero original angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EndpointRotationPenalty
open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope

def R : ℝ := Real.sqrt qCap
def charge : ℝ := 50/49

def defect (l d : ℝ) : ℝ :=
  R*(pairNorm l 1 d-pairNorm l 1 0)-l*psi d-charge*d

theorem R_sq : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
theorem R_nonneg : 0≤R := Real.sqrt_nonneg _

/-- The coefficient of the square-root tangent is bounded on the whole
positive coefficient line by one polynomial sum of squares. -/
theorem tangent_coefficient {l : ℝ} (hl : 0≤l) :
    R*l≤(7/10)*(1+l)*pairNorm l 1 0 := by
  have hN0 : 0≤pairNorm l 1 0 := Real.sqrt_nonneg _
  have hN2 : (pairNorm l 1 0)^2=1+l^2 := by
    rw [pairNorm_zero,Real.sq_sqrt (by positivity : 0≤l^2+(1:ℝ)^2)]
    ring
  have hpoly : 0≤(l-1)^2*(l^2+4*l+1) :=
    mul_nonneg (sq_nonneg _) (by nlinarith [sq_nonneg l])
  have hid : (1+l)^2*(1+l^2)-8*l^2=(l-1)^2*(l^2+4*l+1) := by ring
  have hRmul := congrArg (fun z : ℝ => z*l^2) R_sq
  have hNmul := congrArg (fun z : ℝ => (1+l)^2*z) hN2
  have hsq : (R*l)^2≤((7/10)*(1+l)*pairNorm l 1 0)^2 := by
    dsimp [qCap] at hRmul
    nlinarith [sq_nonneg l]
  have hright : 0≤(7/10)*(1+l)*pairNorm l 1 0 := by positivity
  nlinarith [mul_nonneg R_nonneg hl]

theorem positive_norm_gain {l x : ℝ} (hl : 0<l) (hx : x∈Icc 0 frameCap) :
    R*(pairNorm l 1 x-pairNorm l 1 0)≤
      (7/10)*(1+l)*Real.sin x := by
  have hx' : |x|≤frameCap := by rw [abs_of_nonneg hx.1]; exact hx.2
  have hz : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hN0 := pairNorm_pos hl (show (0:ℝ)<1 by norm_num) hz
  have hN2 := pairNorm_sq hl (show (0:ℝ)<1 by norm_num) hx'
  have hZ2 := pairNorm_sq hl (show (0:ℝ)<1 by norm_num) hz
  simp only [pairEnergy,pairProduct,Real.sin_zero,mul_zero,add_zero,one_pow,mul_one] at hN2 hZ2
  have htan : pairNorm l 1 0*(pairNorm l 1 x-pairNorm l 1 0)≤l*Real.sin x := by
    nlinarith [sq_nonneg (pairNorm l 1 x-pairNorm l 1 0)]
  have hmul := mul_le_mul_of_nonneg_left htan R_nonneg
  have hc := mul_le_mul_of_nonneg_right (tangent_coefficient hl.le)
    (transport_trig hx).2.2.1
  refine le_of_mul_le_mul_left ?_ hN0
  linarith

theorem positive_defect {l x : ℝ} (hl : l∈Icc (4/5 : ℝ) 2)
    (hx : x∈Icc 0 frameCap) :
    defect l x≤ -(737/4900)*x := by
  have hl0 : 0<l := by linarith [hl.1]
  have hnorm := positive_norm_gain hl0 hx
  have hx' : 0≤x ∧ x≤4/5 := ⟨hx.1,by dsimp [frameCap] at hx; linarith [hx.2]⟩
  have hhalf := halfRatio_upper hx'
  have hhalf' : halfRatio x≤77/200 := by dsimp [frameCap] at hx; linarith [hx.2]
  have hid := (halfRatio_identities hx').2
  have hs0 := (transport_trig hx).2.2.1
  have hcharge := mul_le_mul_of_nonneg_right hhalf' hs0
  rw [hid] at hcharge
  have hcharge' := mul_le_mul_of_nonneg_left hcharge hl0.le
  have hcoeff := mul_nonneg (show 0≤2-l by linarith [hl.2]) hs0
  have hsin := Real.sin_le hx.1
  rw [defect,psi_positive hx]
  dsimp [PositiveAngularEnvelope.phi,charge]
  linarith

/-- A stronger negative-angle endpoint at coefficient `4/5`, obtained
from positive square comparisons on the actual two circle norms. -/
theorem V_four_fifths_endpoint :
    (3/4 : ℝ)<V R (4/5) 1 frameCap := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hs := cap_sin_lower
  have hc := (transport_trig hh).1
  have hZl : (32/25 : ℝ)<pairNorm (4/5) 1 0 := by
    rw [pairNorm_zero,Real.lt_sqrt (by norm_num)]
    norm_num
  have hMu : pairNorm (4/5) 1 (-frameCap)<781/1000 := by
    unfold pairNorm
    rw [Real.sqrt_lt' (by norm_num),Real.sin_neg]
    linarith
  have hR := sqrt_cap_lower
  change (19787/10000 : ℝ)<R at hR
  have hp := mul_pos (show 0<R by linarith)
    (show 0<pairNorm (4/5) 1 0-pairNorm (4/5) 1 (-frameCap)-499/1000 by linarith)
  dsimp [V]
  nlinarith

theorem V_four_fifths_chord {x : ℝ} (hx : x∈Icc 0 frameCap) :
    (15/14)*x≤V R (4/5) 1 x := by
  have hconc := V_concave R_nonneg R_sq.le (show (0:ℝ)<4/5 by norm_num)
    (show (4/5 : ℝ)≤1 by norm_num) (show (1:ℝ)≤2*(4/5) by norm_num)
  have hh : 0<frameCap := by norm_num [frameCap]
  have hα : 0≤x/frameCap ∧ x/frameCap≤1 :=
    ⟨div_nonneg hx.1 hh.le,(div_le_one hh).2 hx.2⟩
  have h := hconc.2 ⟨le_rfl,hh.le⟩ ⟨hh.le,le_rfl⟩
    (sub_nonneg.mpr hα.2) hα.1 (by ring)
  have he : (x/frameCap)*frameCap=x := div_mul_cancel₀ x hh.ne'
  simp only [smul_eq_mul,V_zero,mul_zero,zero_add,he] at h
  have hmul := mul_le_mul_of_nonneg_left V_four_fifths_endpoint.le hα.1
  have hc : (x/frameCap)*(3/4)=(15/14)*x := by dsimp [frameCap]; ring
  rw [hc] at hmul
  exact hmul.trans h

theorem negative_gain {l x : ℝ} (hl : l∈Icc (4/5 : ℝ) 2)
    (hx : x∈Icc 0 frameCap) :
    (15/14)*x≤R*(pairNorm l 1 0-pairNorm l 1 (-x))+
      l*(Real.cos x-1) := by
  by_cases hl1 : l≤1
  · have hmono := V_monotone_smaller R_nonneg (show (0:ℝ)<1 by norm_num) hx
      (show (4/5 : ℝ)∈Icc (1/2) 1 by norm_num)
      (show l∈Icc (1/2) 1 by constructor <;> linarith [hl.1]) hl.1
    have hchord := V_four_fifths_chord hx
    have hshift := mul_nonneg (sub_nonneg.mpr hl1)
      (show 0≤1-Real.cos x by linarith [Real.cos_le_one x])
    dsimp [V] at hmono hchord
    nlinarith
  · have h1l : 1≤l := (lt_of_not_ge hl1).le
    have hchord := V_chord_lower (show (0:ℝ)<1 by norm_num) h1l
      (by linarith [hl.2] : l≤2*(1:ℝ)) hx
    rw [V,pairNorm_symm 1 l (-x),pairNorm_symm 1 l 0] at hchord
    change (87/70)*(1:ℝ)*x≤
      l*(Real.cos x-1)-R*(pairNorm l 1 (-x)-pairNorm l 1 0) at hchord
    linarith [hx.1]

theorem negative_defect {l x : ℝ} (hl : l∈Icc (4/5 : ℝ) 2)
    (hx : x∈Icc 0 frameCap) :
    defect l (-x)≤ -(5/98)*x := by
  have h := negative_gain hl hx
  rw [defect,psi_negative hx]
  dsimp [charge]
  linarith

/-- The full signed rotation comparison, with a strictly positive
coefficient multiplying the magnitude of the original error. -/
theorem defect_upper {l d : ℝ} (hl : l∈Icc (4/5 : ℝ) 2)
    (hd : |d|≤frameCap) : defect l d≤ -(5/98)*|d| := by
  by_cases hd0 : 0≤d
  · have h := positive_defect hl ⟨hd0,(le_abs_self d).trans hd⟩
    rw [abs_of_nonneg hd0]
    linarith
  · have hn : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have h := negative_defect hl hn
    simpa only [neg_neg,abs_of_neg (lt_of_not_ge hd0)] using h

theorem rotation_comparison {l d : ℝ} (hl : l∈Icc (4/5 : ℝ) 2)
    (hd : |d|≤frameCap) :
    R*pairNorm l 1 d-l*(1+psi d)-charge*d≤R*pairNorm l 1 0-l := by
  have h := defect_upper hl hd
  dsimp [defect] at h
  linarith [abs_nonneg d]

end SquaresInCircles.Eight.TableFree.EndpointRotationPenalty

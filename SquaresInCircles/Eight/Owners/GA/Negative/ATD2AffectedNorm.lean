module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2SecantBaseline

/-!
# Eight squares: the affected-pair norm in secant coordinates

Its x derivative is a
normalized coordinate; its z derivative has the factor r+x cos z-sin z.
This gives the exact monotonicity used when z is moved to s in the
positive-surplus argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedNorm
open Candidate Secondary PositiveAngularEnvelope SecantBaseline

def norm (r z x : ℝ) : ℝ := Real.sqrt ((x+r*Real.cos z)^2+(1-r*Real.sin z)^2)
def first (r z x : ℝ) : ℝ := (x+r*Real.cos z)/norm r z x
def second (r z x : ℝ) : ℝ := (1-r*Real.sin z)^2/(norm r z x)^3
def zFirst (r z x : ℝ) : ℝ := -r*(x*Real.sin z+Real.cos z)/norm r z x
def firstZ (r z x : ℝ) : ℝ :=
  r*(1-r*Real.sin z)*(r+x*Real.cos z-Real.sin z)/(norm r z x)^3

theorem norm_sq (r z x : ℝ) :
    (norm r z x)^2=(x+r*Real.cos z)^2+(1-r*Real.sin z)^2 :=
  Real.sq_sqrt (by positivity)

theorem norm_sq_expanded (r z x : ℝ) :
    (norm r z x)^2=1+x^2+r^2+2*r*(x*Real.cos z-Real.sin z) := by
  rw [norm_sq]
  linear_combination r^2*(Real.sin_sq_add_cos_sq z)

theorem second_coordinate_pos {r z : ℝ}
    (hr : r∈Icc (0:ℝ) (71/50:ℝ)) (hz : z∈Icc 0 frameCap) :
    0<1-r*Real.sin z := by
  have ht := transport_trig hz
  have hmul := mul_le_mul hr.2 ht.2.2.2.1.le ht.2.2.1 (by norm_num : (0:ℝ)≤71/50)
  linarith

theorem norm_pos {r z x : ℝ} (hv : 0<1-r*Real.sin z) : 0<norm r z x := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg (x+r*Real.cos z)]

theorem norm_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (norm r z) (first r z x) x := by
  have hn := norm_pos (x:=x) hv
  have hr : (x+r*Real.cos z)^2+(1-r*Real.sin z)^2≠0 := by
    nlinarith [norm_sq r z x]
  have hh := ((((hasDerivAt_id x).add_const (r*Real.cos z)).pow 2).add_const
    ((1-r*Real.sin z)^2)).sqrt hr
  convert hh using 1
  · rfl
  · dsimp [first,norm]
    ring

theorem first_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (first r z) (second r z x) x := by
  have hn := norm_pos (x:=x) hv
  have hh := ((hasDerivAt_id x).add_const (r*Real.cos z)).div
    (norm_hasDerivAt hv) hn.ne'
  convert hh using 1
  · rfl
  · dsimp [first,second]
    field_simp [hn.ne']
    nlinarith only [norm_sq r z x]

theorem normZ_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (fun z => norm r z x) (zFirst r z x) z := by
  have hn := norm_pos (x:=x) hv
  have hr : (x+r*Real.cos z)^2+(1-r*Real.sin z)^2≠0 := by
    nlinarith [norm_sq r z x]
  have hu := ((Real.hasDerivAt_cos z).const_mul r).const_add x
  have hv' := ((Real.hasDerivAt_sin z).const_mul r).const_sub 1
  have hh := ((hu.pow 2).add (hv'.pow 2)).sqrt hr
  convert hh using 1
  · rfl
  · dsimp [zFirst,norm]
    ring

theorem firstZ_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (fun z => first r z x) (firstZ r z x) z := by
  have hn := norm_pos (x:=x) hv
  have hh := (((Real.hasDerivAt_cos z).const_mul r).const_add x).div
    (normZ_hasDerivAt hv) hn.ne'
  have he : -r*Real.sin z*(norm r z x)^2+
      r*(x+r*Real.cos z)*(x*Real.sin z+Real.cos z)=
      r*(1-r*Real.sin z)*(r+x*Real.cos z-Real.sin z) := by
    rw [norm_sq]
    linear_combination r^2*(1-r*Real.sin z)*(Real.sin_sq_add_cos_sq z)
  convert hh using 1
  · rfl
  · dsimp [firstZ,first,zFirst]
    field_simp [hn.ne']
    nlinarith only [he]

theorem first_le_one {r z x : ℝ} (hv : 0<1-r*Real.sin z) : first r z x≤1 := by
  have hn := norm_pos (x:=x) hv
  unfold first
  apply (div_le_one hn).2
  nlinarith [norm_sq r z x,sq_nonneg (1-r*Real.sin z)]

theorem tan_identity {s : ℝ} (hc : 0<Real.cos s) :
    Real.tan s*Real.cos s-Real.sin s=0 ∧
    1+Real.tan s^2=(1/Real.cos s)^2 := by
  constructor
  · rw [Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    ring
  · rw [Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    nlinarith only [Real.sin_sq_add_cos_sq s]

theorem first_z_monotone {r s : ℝ}
    (hr : r∈Icc (0:ℝ) (71/50:ℝ)) (hs : s∈Icc 0 frameCap) :
    MonotoneOn (fun z => first r z (Real.tan s)) (Icc 0 s) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hdomain (z : ℝ) (hz : z∈Icc 0 s) : z∈Icc 0 frameCap := ⟨hz.1,hz.2.trans hs.2⟩
  apply monoOn_of_hasDeriv_nonneg
    (fun z hz => (firstZ_hasDerivAt (x:=Real.tan s)
      (second_coordinate_pos hr (hdomain z hz))).continuousAt.continuousWithinAt)
    (fun z hz => firstZ_hasDerivAt (x:=Real.tan s)
      (second_coordinate_pos hr (hdomain z (Ioo_subset_Icc_self hz))))
  intro z hz
  have hz' := Ioo_subset_Icc_self hz
  have hdiff : s-z∈Icc 0 frameCap :=
    ⟨by linarith [hz'.2],by linarith [hs.2,hz'.1]⟩
  have hsin := (transport_trig hdiff).2.2.1
  have he : Real.tan s*Real.cos z-Real.sin z=Real.sin (s-z)/Real.cos s := by
    rw [Real.tan_eq_sin_div_cos,Real.sin_sub]
    field_simp [hc.ne']
  have hbr : 0≤r+Real.tan s*Real.cos z-Real.sin z := by
    have hn := div_nonneg hsin hc.le
    rw [←he] at hn
    linarith [hr.1]
  unfold firstZ
  exact div_nonneg
    (mul_nonneg (mul_nonneg hr.1 (second_coordinate_pos hr (hdomain z hz')).le) hbr)
    (pow_nonneg (Real.sqrt_nonneg _) 3)

theorem norm_at_equal {r s : ℝ}
    (hr : r∈Icc (0:ℝ) (71/50:ℝ)) (hs : s∈Icc 0 frameCap) :
    norm r s (Real.tan s)=denominator r s/Real.cos s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hn := norm_pos (x:=Real.tan s) (second_coordinate_pos hr hs)
  have hsupp := SecantNormCurvature.norm_pos (a:=r) hc
  have he := norm_sq_expanded r s (Real.tan s)
  rw [(tan_identity hc).1,mul_zero,add_zero] at he
  have he' : (norm r s (Real.tan s))^2=(SecantNormCurvature.supportNorm r s)^2 := by
    rw [SecantNormCurvature.norm_sq]
    dsimp [SecantNormCurvature.secant]
    nlinarith only [he,(tan_identity hc).2]
  have hnorm : norm r s (Real.tan s)=SecantNormCurvature.supportNorm r s := by
    nlinarith
  rw [hnorm,support_norm_identity hc]

theorem first_at_equal {r s : ℝ}
    (hr : r∈Icc (0:ℝ) (71/50:ℝ)) (hs : s∈Icc 0 frameCap) :
    first r s (Real.tan s)=
      (Real.sin s+r*Real.cos s^2)/denominator r s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  unfold first
  rw [norm_at_equal hr hs,Real.tan_eq_sin_div_cos]
  field_simp [hc.ne',(denominator_pos r s).ne']

theorem first_le_equal {r s z : ℝ}
    (hr : r∈Icc (0:ℝ) (71/50:ℝ)) (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 s) :
    first r z (Real.tan s)≤(Real.sin s+r*Real.cos s^2)/denominator r s := by
  have hh := first_z_monotone hr hs hz (show s∈Icc 0 s from ⟨hs.1,le_rfl⟩) hz.2
  simpa only [first_at_equal hr hs] using hh

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedNorm

import SquaresInCircles.Six.Stress.PairStress

/-!
# The diagonal estimate

Let W, D and S be at the phases `π + w`, `π + d` and `3π/2 + s`, with
`-11/25 ≤ w ≤ 2/5`, `-2/5 ≤ s ≤ 11/25` and `1/2 ≤ d ≤ π/4`, and let
`β = (w - s)/2`, `δ = d - π/4 - (w + s)/2`. The force on D has length
`L = diagonalK (cos β - sin β)` and makes the angle `-δ` with the axis of D, and
the angular parts of the thresholds of W–D and D–S add up to
`diagonalK cos β cos δ`. Against this force a square in the disk of radius
`radius` has work at most `rhoStar L cos δ` when `2 R₆ |sin δ| ≤ 1`, attained at
a corner of the cap, and at most the far-vertex value
`L (R₆ - (cos δ + |sin δ|)/2)` otherwise, by Cauchy–Schwarz. The remainder, the
lines of the two pairs plus the thresholds less this support plus `2 pairBase`,
is nonnegative and vanishes only at `w = s = 0`, `d = π/4`. In the cap case it
is at least `(3/200)(|w| + |s|)`, by Taylor bounds in `β` and `δ`. In the vertex
case `|δ| ≥ 29/100`, so `|w + s|` is large, and a minorant concave in `|δ|` is
positive at both ends of its range, at one end through two quartics above their
chords.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization

/-- The force on D, in its frame, for W, D and S at the phases `π + w`, `π + d`
and `3π/2 + s`. -/
def diagonalLocalForce (w s d : ℝ) : Point :=
  (mStar*(Real.sin (d-w)+Real.cos (d-s)),mStar*(Real.cos (d-w)-Real.sin (d-s)))

/-- The angles `β = (w - s)/2` and `δ = d - π/4 - (w + s)/2`. -/
def diagonalBeta (w s : ℝ) : ℝ := (w-s)/2
def diagonalDelta (w s d : ℝ) : ℝ := d-Real.pi/4-(w+s)/2

/-- A bound for the work of the force `L (cos δ, -sin δ)` on D: the cap value when
`2 R₆ |sin δ| ≤ 1`, the far-vertex value otherwise. -/
def diagonalSupport (L δ : ℝ) : ℝ :=
  if 2*radius*|Real.sin δ|≤1 then rhoStar*L*Real.cos δ
  else L*(radius-(Real.cos δ+|Real.sin δ|)/2)

/-- The diagonal term: the angular parts of the thresholds of W–D and D–S with
the weight `mStar`, less the support of D; the constant parts `mStar/2` are counted
with the pairs. -/
def diagonalValue (w s d : ℝ) : ℝ :=
  mStar*(angularWidth (d-w)+angularWidth (d-s))-
    diagonalSupport (diagonalK*(Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s)))
      (diagonalDelta w s d)

/-- The domain of the diagonal estimate. -/
def DiagonalDomain (w s d : ℝ) : Prop :=
  (-11/25≤w ∧ w≤2/5) ∧ (-2/5≤s ∧ s≤11/25) ∧ (1/2≤d ∧ d≤Real.pi/4)

/-- The lines of the two pairs, the diagonal term and twice the pair base. -/
def remainder (w s d : ℝ) : ℝ := line w+line (-s)+diagonalValue w s d+2*pairBase

lemma diagonal_parameters {w s d : ℝ} (h : DiagonalDomain w s d) :
    (-11/25≤diagonalBeta w s ∧ diagonalBeta w s≤2/5) ∧ |diagonalDelta w s d|≤71/100 ∧
    (0≤d-w ∧ d-w≤Real.pi/2) ∧ (0≤d-s ∧ d-s≤Real.pi/2) := by
  obtain ⟨hw,hs,hd⟩ := h
  have := Real.pi_gt_d2
  have := Real.pi_lt_d4
  unfold diagonalBeta diagonalDelta
  refine ⟨⟨?_,?_⟩,abs_le.mpr ⟨?_,?_⟩,⟨?_,?_⟩,?_,?_⟩ <;>
    linarith [hw.1,hw.2,hs.1,hs.2,hd.1,hd.2]

lemma diagonal_trig_signs {w s d : ℝ} (h : DiagonalDomain w s d) :
    0<Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s) ∧
    0<Real.cos (diagonalDelta w s d) ∧
    |Real.sin (diagonalDelta w s d)|≤Real.cos (diagonalDelta w s d) := by
  have hp := diagonal_parameters h
  have hb : |diagonalBeta w s|≤11/25 := abs_le.mpr ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩
  have hcb := (small_angle hb).1
  have hsb := (abs_le.mp (Real.abs_sin_le_abs.trans hb)).2
  have hcd := (small_angle hp.2.1).1
  have hsd := Real.abs_sin_le_abs.trans hp.2.1
  exact ⟨by linarith,by linarith,by linarith⟩

/-! ### The support of D -/

/-- The work of `L (cos δ, -sin δ)`, for `|sin δ| ≤ cos δ`, on a centre of a square
in the disk of radius `radius` is at most `diagonalSupport L δ`. -/
lemma diagonal_support_bound {a b L δ : ℝ} (hL : 0≤L) (hδ : |Real.sin δ|≤Real.cos δ)
    (hbox : (|a|+1/2)^2+(|b|+1/2)^2≤radius^2) :
    L*(a*Real.cos δ-b*Real.sin δ)≤diagonalSupport L δ := by
  have hc0 : 0≤Real.cos δ := (abs_nonneg _).trans hδ
  have hct : Real.cos δ^2+|Real.sin δ|^2=1 := by rw [sq_abs]; linarith [Real.sin_sq_add_cos_sq δ]
  have hw : a*Real.cos δ-b*Real.sin δ≤|a| * Real.cos δ+|b| * |Real.sin δ| := by
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self a) hc0
    have h2 : -(b*Real.sin δ)≤|b| * |Real.sin δ| := by
      rw [← abs_mul]; exact neg_le_abs _
    linarith
  have hR := radius_bounds
  unfold diagonalSupport
  split_ifs with hcap
  · have hq : 0<radius^2-1/4 := by nlinarith
    have hs := Real.sq_sqrt hq.le
    have ha0 := Real.sqrt_pos.mpr hq
    have hslope : Real.sqrt (radius^2-1/4)*|Real.sin δ|≤Real.cos δ/2 := by
      have hsq : (Real.sqrt (radius^2-1/4)*|Real.sin δ|)^2≤(Real.cos δ/2)^2 := by
        rw [mul_pow,hs]
        nlinarith [mul_le_mul hcap hcap (mul_nonneg (mul_nonneg zero_le_two radius_pos.le)
          (abs_nonneg _)) zero_le_one]
      exact (pow_le_pow_iff_left₀ (by positivity) (by linarith) two_ne_zero).mp hsq
    have hkey : Real.sqrt (radius^2-1/4)*(|a|+1/2-Real.sqrt (radius^2-1/4))+
        1/2*(|b|+1/2-1/2)≤0 := by
      nlinarith [sq_nonneg (|a|+1/2-Real.sqrt (radius^2-1/4)),sq_nonneg |b|]
    have hcorner : (|a|+1/2)*Real.cos δ+(|b|+1/2)*|Real.sin δ|≤
        Real.sqrt (radius^2-1/4)*Real.cos δ+|Real.sin δ|/2 := by
      have hm := mul_nonneg (sub_nonneg.mpr hslope) (abs_nonneg b)
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hc0 hkey]
    have hρ : rhoStar=Real.sqrt (radius^2-1/4)-1/2 := rfl
    rw [hρ]
    nlinarith [mul_le_mul_of_nonneg_left hw hL]
  · have h := dot_le_radius (v := (Real.cos δ,|Real.sin δ|)) (p := (|a|+1/2,|b|+1/2))
      radius_pos.le (by simpa only [normSq] using hbox)
    simp only [dot,vectorLength,normSq,hct,Real.sqrt_one,mul_one] at h
    nlinarith [mul_le_mul_of_nonneg_left hw hL]

/-! ### The force and the thresholds -/

lemma diagonal_force_formula (w s d : ℝ) :
    diagonalLocalForce w s d=
      (diagonalK*(Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s))*
        Real.cos (diagonalDelta w s d),
       -diagonalK*(Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s))*
        Real.sin (diagonalDelta w s d)) := by
  have hw : d-w=Real.pi/4+diagonalDelta w s d-diagonalBeta w s := by
    simp only [diagonalDelta,diagonalBeta]; ring
  have hs : d-s=Real.pi/4+diagonalDelta w s d+diagonalBeta w s := by
    simp only [diagonalDelta,diagonalBeta]; ring
  apply Prod.ext <;>
    simp only [diagonalLocalForce,hw,hs,Real.sin_sub,Real.cos_sub,Real.sin_add,Real.cos_add,
      sin_quarter,cos_quarter,diagonalK] <;> ring

lemma diagonal_threshold_formula {w s d : ℝ} (h : DiagonalDomain w s d) :
    mStar*(angularWidth (d-w)+angularWidth (d-s))=
      diagonalK*Real.cos (diagonalBeta w s)*Real.cos (diagonalDelta w s d) := by
  have hp := diagonal_parameters h
  have hpi := Real.pi_pos
  have width (x : ℝ) (hx : 0≤x ∧ x≤Real.pi/2) :
      angularWidth x=(Real.cos x+Real.sin x)/2 := by
    rw [angularWidth,abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith,hx.2⟩),
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith))]
  rw [width _ hp.2.2.1,width _ hp.2.2.2,
    show d-w=Real.pi/4+diagonalDelta w s d-diagonalBeta w s by
      simp only [diagonalDelta,diagonalBeta]; ring,
    show d-s=Real.pi/4+diagonalDelta w s d+diagonalBeta w s by
      simp only [diagonalDelta,diagonalBeta]; ring]
  simp only [Real.sin_sub,Real.cos_sub,Real.sin_add,Real.cos_add,sin_quarter,cos_quarter,
    diagonalK]
  ring

/-- The work of the force on D on a centre of a square in the disk of radius
`radius` is at most the support of D. -/
lemma diagonal_work_le {w s d a b : ℝ} (h : DiagonalDomain w s d)
    (hbox : (|a|+1/2)^2+(|b|+1/2)^2≤radius^2) :
    (diagonalLocalForce w s d).1*a+(diagonalLocalForce w s d).2*b≤
      diagonalSupport (diagonalK*(Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s)))
        (diagonalDelta w s d) := by
  have hsign := diagonal_trig_signs h
  have hb := diagonal_support_bound (mul_pos diagonalK_pos hsign.1).le hsign.2.2 hbox
  rw [diagonal_force_formula]
  simp only at hb ⊢
  linarith

/-- The cap expression of the remainder. -/
def diagonalCap (w s d : ℝ) : ℝ :=
  diagonalK*((1-rhoStar)*Real.cos (diagonalBeta w s)+rhoStar*Real.sin (diagonalBeta w s))*
    Real.cos (diagonalDelta w s d)

/-- The vertex expression of the remainder. -/
def diagonalVertex (w s d : ℝ) : ℝ :=
  diagonalK*((3*Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s))*
      Real.cos (diagonalDelta w s d)/2+
    (Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s))*|Real.sin (diagonalDelta w s d)|/2-
    radius*(Real.cos (diagonalBeta w s)-Real.sin (diagonalBeta w s)))

lemma diagonal_value_formula {w s d : ℝ} (h : DiagonalDomain w s d) :
    diagonalValue w s d=if 2*radius*|Real.sin (diagonalDelta w s d)|≤1
      then diagonalCap w s d else diagonalVertex w s d := by
  rw [diagonalValue,diagonal_threshold_formula h,diagonalSupport]
  split_ifs <;> simp only [diagonalCap,diagonalVertex] <;> ring

/-! ### The cap case -/

lemma twice_beta_abs_le (w s : ℝ) : 2*|diagonalBeta w s|≤|w|+|s| := by
  have h : |w-s|≤|w|+|s| := abs_le.mpr
    ⟨by linarith [neg_abs_le w,le_abs_self s],by linarith [le_abs_self w,neg_abs_le s]⟩
  have he : w-s=2*diagonalBeta w s := by dsimp [diagonalBeta]; ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at h
  exact h

lemma line_sum (w s : ℝ) :
    line w+line (-s)=(23/100)*(|w|+|s|)-(98/100)*diagonalBeta w s := by
  have hw : line w=(23/100)*|w|-(49/100)*w := by
    rcases le_total 0 w with h | h
    · rw [line,max_eq_right (by linarith),max_eq_left h,abs_of_nonneg h]; ring
    · rw [line,max_eq_left (by linarith),max_eq_right h,abs_of_nonpos h]; ring
  have hs : line (-s)=(23/100)*|s|+(49/100)*s := by
    rcases le_total 0 s with h | h
    · rw [line,neg_neg,max_eq_left h,max_eq_right (by linarith),abs_of_nonneg h]; ring
    · rw [line,neg_neg,max_eq_right h,max_eq_left (by linarith),abs_of_nonpos h]; ring
  rw [hw,hs]
  dsimp [diagonalBeta]
  ring

lemma pairBase_eq_diagonal_scale : 2*pairBase=diagonalK*(rhoStar-1) := by
  linear_combination pairBase_diagonal_identity

/-- The cap expression with the lines and twice the pair base is at least
`(3/200)(|w| + |s|)` on the whole domain. -/
theorem diagonal_cap_lower {w s d : ℝ} (hdom : DiagonalDomain w s d) :
    (3/200)*(|w|+|s|)≤line w+line (-s)+diagonalCap w s d+2*pairBase := by
  let b := diagonalBeta w s
  let z := diagonalDelta w s d
  let Z := |w|+|s|
  let T := diagonalK*rhoStar
  let P := diagonalK*(rhoStar-1)*(1-Real.cos b*Real.cos z)
  have hparams := diagonal_parameters hdom
  have hsign := diagonal_trig_signs hdom
  have hT : (139:ℝ)/100<T ∧ T<(141:ℝ)/100 := by
    have hK := diagonalK_bounds
    have hρ := rhoStar_bounds
    constructor <;> nlinarith
  have hT0 : 0≤T := by linarith [hT.1]
  have hcd0 : 0≤Real.cos z := hsign.2.1.le
  have hcd1 := Real.cos_le_one z
  have hcc : Real.cos b*Real.cos z≤1 := by
    have hh := mul_le_mul (Real.cos_le_one b) hcd1 hcd0 (by norm_num : (0:ℝ)≤1)
    simpa using hh
  have hP : 0≤P := mul_nonneg
    (mul_nonneg diagonalK_pos.le (by linarith [rhoStar_bounds.1])) (sub_nonneg.mpr hcc)
  have hZ0 : 0≤Z := add_nonneg (abs_nonneg w) (abs_nonneg s)
  have hZb : 2*|b|≤Z := twice_beta_abs_le w s
  have hid : line w+line (-s)+diagonalCap w s d+2*pairBase=
      (23/100)*Z-(98/100)*b+T*Real.sin b*Real.cos z+P := by
    rw [line_sum,pairBase_eq_diagonal_scale]
    dsimp [diagonalCap,P,T,Z,b,z,diagonalBeta]
    ring
  rw [hid]
  change (3/200)*Z≤(23/100)*Z-(98/100)*b+T*Real.sin b*Real.cos z+P
  by_cases hb : b≤0
  · have hsin0 : Real.sin b≤0 := by
      have hh := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-b by linarith)
        (show -b≤Real.pi by linarith [hparams.1.1,Real.pi_gt_d2])
      rw [Real.sin_neg] at hh
      linarith
    have hsinlo : b≤Real.sin b := by
      have hh := Real.sin_le (show 0≤-b by linarith)
      rw [Real.sin_neg] at hh
      linarith
    have hp := mul_nonneg (show 0≤-Real.sin b by linarith) (sub_nonneg.mpr hcd1)
    have hprod : b≤Real.sin b*Real.cos z := by nlinarith only [hp,hsinlo]
    have hm := mul_le_mul_of_nonneg_left hprod hT0
    have hcoef := mul_le_mul_of_nonpos_right hT.2.le hb
    rw [abs_of_nonpos hb] at hZb
    nlinarith only [hm,hcoef,hZb,hP]
  · have hb0 : 0≤b := (lt_of_not_ge hb).le
    have hb1 : b≤2/5 := hparams.1.2
    have hbsq : b^2≤4/25 := by nlinarith only [hb0,hb1]
    have hzsq : z^2≤5041/10000 := by
      have hh := pow_le_pow_left₀ (abs_nonneg z) hparams.2.1 2
      rw [sq_abs] at hh
      norm_num at hh
      exact hh
    let q := b^2/6+z^2/2
    have hq0 : 0≤q := by positivity
    have hq1 : q≤16723/60000 := by dsimp [q]; linarith
    have hTq := mul_le_mul hT.2.le hq1 hq0 (by norm_num : (0:ℝ)≤141/100)
    have hcoef : 0≤T-98/100-T*q := by linarith [hT.1]
    have hsinlo := Real.sin_ge_sub_cube hb0
    have hsinhi := Real.sin_le hb0
    have hcoslo := Real.one_sub_sq_div_two_le_cos (x := z)
    have hfirst := mul_nonneg (sub_nonneg.mpr hsinhi) (sub_nonneg.mpr hcd1)
    have hsecond := mul_nonneg hb0 (show 0≤Real.cos z-(1-z^2/2) by linarith)
    have hsinprod : b*(1-q)≤Real.sin b*Real.cos z := by
      dsimp [q]
      nlinarith only [hfirst,hsecond,hsinlo]
    have hmul := mul_le_mul_of_nonneg_left hsinprod hT0
    have hreserve := mul_nonneg hb0 hcoef
    nlinarith only [hmul,hreserve,hP,hZ0]

/-- The cap remainder vanishes only at the angles of the model,
`w = s = 0` and `d = π/4`. -/
theorem diagonal_cap_zero {w s d : ℝ} (hdom : DiagonalDomain w s d)
    (heq : line w+line (-s)+diagonalCap w s d+2*pairBase=0) :
    w=0 ∧ s=0 ∧ d=Real.pi/4 := by
  have hlow := diagonal_cap_lower hdom
  rw [heq] at hlow
  have hw : w=0 := abs_eq_zero.mp (by nlinarith [abs_nonneg w,abs_nonneg s])
  have hs : s=0 := abs_eq_zero.mp (by nlinarith [abs_nonneg w,abs_nonneg s])
  subst w
  subst s
  have hid : line 0+line (-0)+diagonalCap 0 0 d+2*pairBase=
      diagonalK*(rhoStar-1)*(1-Real.cos (d-Real.pi/4)) := by
    rw [pairBase_eq_diagonal_scale]
    simp only [line,neg_zero,max_self,mul_zero,sub_zero,diagonalCap,diagonalBeta,diagonalDelta,
      zero_add,zero_div,Real.cos_zero,Real.sin_zero,add_zero]
    ring
  rw [hid] at heq
  have hcoef : 0<diagonalK*(rhoStar-1) := mul_pos diagonalK_pos (by linarith [rhoStar_bounds.1])
  have hcos : Real.cos (d-Real.pi/4)=1 := by
    have hh := (mul_eq_zero.mp heq).resolve_left hcoef.ne'
    linarith
  have hdelta := (diagonal_parameters hdom).2.1
  have hbound : |d-Real.pi/4|≤Real.pi := by
    simpa only [diagonalDelta,zero_add,zero_div,sub_zero] using
      hdelta.trans (by linarith [Real.pi_gt_d2] : (71:ℝ)/100≤Real.pi)
  have hpoly := cos_le_one_sub_fifth_sq hbound
  rw [hcos] at hpoly
  have hz : d-Real.pi/4=0 := by nlinarith [sq_nonneg (d-Real.pi/4)]
  exact ⟨rfl,rfl,sub_eq_zero.mp hz⟩

/-! ### The vertex case -/

/-- A minorant of the remainder in the vertex case, in `x = |w + s|/2`, `y = |β|`
and `t = |δ|`, with the radius and `rhoStar` replaced by `8443/5000` and
`1391/1250`; in `t` a constant plus `A cos t + B sin t` with `A, B ≥ 0`. -/
def vertexMinorant (x y t : ℝ) : ℝ :=
  (9/25)*max x y+(77/100)*y+
    (3/2+y/2)*Real.cos t+(1/2+y/2)*Real.sin t-
    (8443/5000)*(1+y)+1391/1250-1

private def minorantPenalty (t : ℝ) : ℝ := 4593/5000-(Real.cos t+Real.sin t)/2
private def minorantBase (t : ℝ) : ℝ := (3/2)*Real.cos t+(1/2)*Real.sin t-7879/5000

private lemma minorant_decomposition (x y t : ℝ) :
    vertexMinorant x y t=minorantBase t+(9/25)*max x y-minorantPenalty t*y := by
  dsimp [vertexMinorant,minorantBase,minorantPenalty]
  ring

private lemma minorant_penalty_bounds {t : ℝ} (ht : 2/7≤t ∧ t≤3/4) :
    0≤minorantPenalty t ∧ minorantPenalty t≤9/25 := by
  have ht0 : 0≤t := by linarith [ht.1]
  have hsq := mul_nonneg (sub_nonneg.mpr ht.2)
    (show 0≤3/4+t by linarith [ht.1])
  have hcoef : 0≤1/2-t/2-t^2/6 := by nlinarith [ht.2]
  have hp := mul_nonneg ht0 hcoef
  have hs := Real.sin_ge_sub_cube ht0
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have hlow : 1+t/2≤Real.cos t+Real.sin t := by nlinarith only [hp,hs,hc]
  have hhigh : Real.cos t+Real.sin t≤3/2 := by
    nlinarith [Real.sin_sq_add_cos_sq t,sq_nonneg (Real.cos t-Real.sin t)]
  dsimp [minorantPenalty]
  constructor <;> linarith [hlow,hhigh,ht.1]

private lemma minorant_base_left : 0<minorantBase (29/100) := by
  have hs := Real.sin_ge_sub_cube (x := (29:ℝ)/100) (by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (29:ℝ)/100)
  dsimp [minorantBase]
  nlinarith only [hs,hc]

private def smallBoundary (x : ℝ) : ℝ :=
  (3/2+x/2)*(1-(2/7+x)^2/2)+
    (1/2+x/2)*((2/7+x)-(2/7+x)^3/6)-7879/5000-(2793/5000)*x

private def largeBoundary (x : ℝ) : ℝ :=
  (43/25-x/2)*(1-(2/7+x)^2/2)+
    (18/25-x/2)*((2/7+x)-(2/7+x)^3/6)-
    7879/5000+(9/25)*x-(4593/5000)*(11/25-x)

private lemma small_boundary_pos {x : ℝ} (hx : 0≤x ∧ x≤11/50) :
    0<smallBoundary x := by
  have hid : smallBoundary x=
      quartic (-2067/35000) (10449/35000) (-5/28) (-13/42) (-1/12) (2/7+x) := by
    dsimp [smallBoundary,quartic]
    ring
  rw [hid]
  apply quartic_positive_of_chord (l := (2:ℝ)/7) (u := (177:ℝ)/350)
  · norm_num
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [quartic]
  · norm_num [quartic]
  · have hT : 0≤2/7+x := by linarith [hx.1]
    nlinarith [sq_nonneg (2/7+x)]

private lemma large_boundary_pos {x : ℝ} (hx : 11/50≤x ∧ x≤11/25) :
    0<largeBoundary x := by
  have hid : largeBoundary x=
      quartic (-52767/109375) (57451/35000) (-501/350)
        (223/2100) (1/12) (2/7+x) := by
    dsimp [largeBoundary,quartic]
    ring
  rw [hid]
  apply quartic_positive_of_chord (l := (177:ℝ)/350) (u := (127:ℝ)/175)
  · norm_num
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [quartic]
  · norm_num [quartic]
  · have hT0 : 0≤2/7+x := by linarith [hx.1]
    have hT1 : 2/7+x≤3/4 := by linarith [hx.2]
    have hsq := mul_nonneg (sub_nonneg.mpr hT1)
      (show 0≤3/4+(2/7+x) by linarith)
    nlinarith

private lemma minorant_left {x y : ℝ} (hy : 0≤y) :
    0<vertexMinorant x y (29/100) := by
  have hp := minorant_penalty_bounds (t := (29:ℝ)/100) (by constructor <;> norm_num)
  have hM := mul_nonneg (show (0:ℝ)≤9/25 by norm_num)
    (sub_nonneg.mpr (le_max_right x y))
  have hY := mul_nonneg (sub_nonneg.mpr hp.2) hy
  rw [minorant_decomposition]
  nlinarith only [minorant_base_left,hM,hY]

private lemma minorant_right {x y : ℝ}
    (hx : 0≤x) (hy : 0≤y) (hdiamond : x+y≤11/25) :
    0<vertexMinorant x y (2/7+x) := by
  let t := 2/7+x
  have hxb : x≤11/25 := by linarith
  have ht : 2/7≤t ∧ t≤3/4 := by dsimp [t]; constructor <;> linarith
  have hp := minorant_penalty_bounds ht
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have hs := Real.sin_ge_sub_cube (show 0≤t by linarith [ht.1])
  rw [minorant_decomposition]
  change 0<minorantBase t+(9/25)*max x y-minorantPenalty t*y
  by_cases hsmall : x≤11/50
  · have hM1 := mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr (le_max_left x y))
    have hM2 := mul_nonneg hp.1 (sub_nonneg.mpr (le_max_right x y))
    have hC := mul_le_mul_of_nonneg_left hc (show 0≤3/2+x/2 by linarith)
    have hS := mul_le_mul_of_nonneg_left hs (show 0≤1/2+x/2 by linarith)
    have hpositive := small_boundary_pos ⟨hx,hsmall⟩
    have hid : smallBoundary x=(3/2+x/2)*(1-t^2/2)+
        (1/2+x/2)*(t-t^3/6)-7879/5000-(2793/5000)*x := rfl
    rw [hid] at hpositive
    dsimp [minorantBase,minorantPenalty] at *
    nlinarith only [hM1,hM2,hC,hS,hpositive]
  · have hM := mul_nonneg (show (0:ℝ)≤9/25 by norm_num)
      (sub_nonneg.mpr (le_max_left x y))
    have hY := mul_nonneg hp.1 (show 0≤11/25-x-y by linarith)
    have hC := mul_le_mul_of_nonneg_left hc (show 0≤43/25-x/2 by linarith)
    have hS := mul_le_mul_of_nonneg_left hs (show 0≤18/25-x/2 by linarith)
    have hpositive := large_boundary_pos ⟨(lt_of_not_ge hsmall).le,hxb⟩
    have hid : largeBoundary x=(43/25-x/2)*(1-t^2/2)+
        (18/25-x/2)*(t-t^3/6)-7879/5000+(9/25)*x-(4593/5000)*(11/25-x) := rfl
    rw [hid] at hpositive
    dsimp [minorantBase,minorantPenalty] at *
    nlinarith only [hM,hY,hC,hS,hpositive]

/-- The minorant is positive on the diamond `x, y ≥ 0`, `x + y ≤ 11/25`, for
`29/100 ≤ t ≤ 2/7 + x`. -/
theorem vertexMinorant_pos {x y t : ℝ}
    (hx : 0≤x) (hy : 0≤y) (hdiamond : x+y≤11/25)
    (ht : 29/100≤t ∧ t≤2/7+x) : 0<vertexMinorant x y t := by
  have hleft := minorant_left (x := x) hy
  have hright := minorant_right hx hy hdiamond
  have hh := harmonic_pos_of_endpoints
    (K := -((8443/5000)*(1+y)-1391/1250+1-(9/25)*max x y-(77/100)*y))
    (A := 3/2+y/2) (B := 1/2+y/2) (l := (29:ℝ)/100) (u := 2/7+x)
    (by linarith) (by linarith) (by norm_num)
    (by linarith [Real.pi_gt_d2]) ht
    (by dsimp [vertexMinorant] at hleft; linarith)
    (by dsimp [vertexMinorant] at hright; linarith)
  dsimp [vertexMinorant]
  linarith

private lemma vertex_expression_pos {K R rho x b t : ℝ}
    (hKlo : 5/4≤K) (hKhi : K≤253/200)
    (hRlo : 8/5≤R) (hRhi : R≤8443/5000) (hrho : 1391/1250≤rho)
    (hx : 0≤x) (hdiamond : x+|b|≤11/25)
    (ht : 29/100≤t ∧ t≤2/7+x) :
    0<(46/100)*max x |b|-(98/100)*b+
      K*((3*Real.cos b-Real.sin b)*Real.cos t/2+
        (Real.cos b-Real.sin b)*Real.sin t/2-
        R*(Real.cos b-Real.sin b)+rho-1) := by
  let A := (3/2)*Real.cos t+(1/2)*Real.sin t-R
  let B := R-(Real.cos t+Real.sin t)/2
  let y := |b|
  let M := max x y
  have hK0 : 0<K := by linarith
  have hy0 : 0≤y := abs_nonneg b
  have hy1 : y≤1/2 := by dsimp [y]; linarith
  have hM0 : 0≤M := hx.trans (le_max_left x y)
  have hwidth : Real.cos t+Real.sin t≤3/2 := by
    nlinarith [Real.sin_sq_add_cos_sq t,sq_nonneg (Real.cos t-Real.sin t)]
  have hweighted : (3/2)*Real.cos t+(1/2)*Real.sin t≤8/5 := by
    have hc := sq_nonneg (Real.cos t-3*Real.sin t)
    by_contra! hh
    have hp := mul_pos
      (show 0<3*Real.cos t+Real.sin t-16/5 by linarith)
      (show 0<3*Real.cos t+Real.sin t+16/5 by linarith)
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hA : A≤0 := by dsimp [A]; linarith
  have hB : 17/20≤B := by dsimp [B]; linarith
  have hKB : 17/16≤K*B := by
    have hp := mul_le_mul hKlo hB (by norm_num : (0:ℝ)≤17/20) hK0.le
    nlinarith only [hp]
  have hKB0 : 0≤K*B := by linarith
  have hcos : A≤A*Real.cos b := by
    simpa only [mul_one] using mul_le_mul_of_nonpos_left (Real.cos_le_one b) hA
  have hKcos := mul_le_mul_of_nonneg_left hcos hK0.le
  have hsin : (98/100)*y-K*B*y≤-(98/100)*b+K*B*Real.sin b := by
    by_cases hb : b≤0
    · have hs := Real.sin_le (show 0≤-b by linarith)
      rw [Real.sin_neg] at hs
      have hp := mul_le_mul_of_nonneg_left (show b≤Real.sin b by linarith) hKB0
      dsimp [y]
      rw [abs_of_nonpos hb]
      nlinarith only [hp]
    · have hb0 : 0≤b := (lt_of_not_ge hb).le
      have hb1 : b≤1/2 := by simpa [y,abs_of_nonneg hb0] using hy1
      have hsq := mul_nonneg (sub_nonneg.mpr hb1) (show 0≤1/2+b by linarith)
      have hcube := mul_nonneg hb0 (show 0≤1/4-b^2 by nlinarith)
      have hs := Real.sin_ge_sub_cube hb0
      have hsum : (47/24)*b≤Real.sin b+b := by nlinarith only [hcube,hs]
      have hp := mul_le_mul hKB hsum (show 0≤(47/24)*b by positivity) hKB0
      dsimp [y]
      rw [abs_of_nonneg hb0]
      nlinarith only [hp,hb0]
  have htrig : (46/100)*M+(98/100)*y+K*(A-B*y+rho-1)≤
      (46/100)*M-(98/100)*b+K*(A*Real.cos b+B*Real.sin b+rho-1) := by
    nlinarith only [hKcos,hsin]
  have hM := mul_nonneg (show 0≤46/100-(9/25)*K by linarith) hM0
  have hY := mul_nonneg (show 0≤98/100-(77/100)*K by linarith) hy0
  have hRad := mul_nonneg hK0.le
    (mul_nonneg (sub_nonneg.mpr hRhi) (show 0≤1+y by linarith))
  have hRho := mul_nonneg hK0.le (sub_nonneg.mpr hrho)
  have hid : (46/100)*M+(98/100)*y+K*(A-B*y+rho-1)-
      K*vertexMinorant x y t =
      (46/100-(9/25)*K)*M+(98/100-(77/100)*K)*y+
      K*(8443/5000-R)*(1+y)+K*(rho-1391/1250) := by
    dsimp [A,B,M,vertexMinorant]
    ring
  have hminorant : K*vertexMinorant x y t≤
      (46/100)*M+(98/100)*y+K*(A-B*y+rho-1) := by
    nlinarith only [hid,hM,hY,hRad,hRho]
  have hpos := mul_pos hK0 (vertexMinorant_pos hx hy0 hdiamond ht)
  have hresult := hpos.trans_le (hminorant.trans htrig)
  have he : (3*Real.cos b-Real.sin b)*Real.cos t/2+
      (Real.cos b-Real.sin b)*Real.sin t/2-R*(Real.cos b-Real.sin b)+rho-1=
      A*Real.cos b+B*Real.sin b+rho-1 := by dsimp [A,B]; ring
  rw [he]
  exact hresult

private lemma diamond_bound {w s d : ℝ} (hd : DiagonalDomain w s d) :
    |(w+s)/2|+|diagonalBeta w s|≤11/25 := by
  let a := (w+s)/2
  let b := diagonalBeta w s
  have hw : a+b=w := by dsimp [a,b,diagonalBeta]; ring
  have hs : a-b=s := by dsimp [a,b,diagonalBeta]; ring
  change |a|+|b|≤11/25
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg ha,abs_of_nonneg hb]
    linarith [hd.1.2]
  · rw [abs_of_nonneg ha,abs_of_neg hb]
    linarith [hd.2.1.2]
  · rw [abs_of_neg ha,abs_of_nonneg hb]
    linarith [hd.2.1.1]
  · rw [abs_of_neg ha,abs_of_neg hb]
    linarith [hd.1.1]

private lemma max_bound (w s : ℝ) :
    2*max |(w+s)/2| |diagonalBeta w s|≤|w|+|s| := by
  have ha := abs_add_le w s
  have hb := abs_sub w s
  have he : w+s=2*((w+s)/2) := by ring
  have hf : w-s=2*diagonalBeta w s := by dsimp [diagonalBeta]; ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ha
  rw [hf,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hb
  by_cases h : |(w+s)/2|≤|diagonalBeta w s|
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left (le_of_not_ge h)]; exact ha

/-- In the vertex case, with the vertex term of D for the diagonal term, the
remainder is positive. -/
theorem diagonal_vertex_pos {w s d : ℝ} (hd : DiagonalDomain w s d)
    (hv : 1≤2*Six.radius*|Real.sin (diagonalDelta w s d)|) :
    0<line w+line (-s)+diagonalVertex w s d+2*pairBase := by
  let a := (w+s)/2
  let b := diagonalBeta w s
  let z := diagonalDelta w s d
  let x := |a|
  let t := |z|
  have hdiamond : x+|b|≤11/25 := diamond_bound hd
  have hR := radius_bounds
  have hK := diagonalK_bounds
  have hsin := Real.abs_sin_le_abs (x := z)
  have hprod := mul_le_mul hR.2.le hsin (abs_nonneg (Real.sin z))
    (by norm_num : (0:ℝ)≤16885431/10000000)
  have htlo : 29/100≤t := by
    change 1≤2*Six.radius*|Real.sin z| at hv
    dsimp [t]
    nlinarith only [hv,hprod]
  have htriangle := abs_sub (d-Real.pi/4) a
  have hsign : d-Real.pi/4≤0 := by linarith [hd.2.2.2]
  rw [abs_of_nonpos hsign] at htriangle
  have hpi : Real.pi<(22:ℝ)/7 := by linarith [Real.pi_lt_d4]
  have hthi : t≤2/7+x := by
    change |d-Real.pi/4-a|≤2/7+|a|
    linarith [hd.2.2.1]
  have hp := vertex_expression_pos
    (K := diagonalK) (R := Six.radius) (rho := rhoStar) (x := x) (b := b) (t := t)
    (by linarith [hK.1]) (by linarith [hK.2])
    (by linarith [hR.1]) (by linarith [hR.2])
    (by linarith [rhoStar_bounds.1]) (abs_nonneg a) hdiamond ⟨htlo,hthi⟩
  have hzpi : |z|≤Real.pi := by
    have hh := (diagonal_parameters hd).2.1
    change |z|≤71/100 at hh
    linarith [Real.pi_gt_d2]
  dsimp [t] at hp
  rw [Real.cos_abs,← Real.abs_sin_eq_sin_abs_of_abs_le_pi hzpi] at hp
  have hsum : 2*max x |b|≤|w|+|s| := max_bound w s
  have hid : line w+line (-s)+diagonalVertex w s d+2*pairBase=
      (23/100)*(|w|+|s|)-(98/100)*b+
      diagonalK*((3*Real.cos b-Real.sin b)*Real.cos z/2+
        (Real.cos b-Real.sin b)*|Real.sin z|/2-
        Six.radius*(Real.cos b-Real.sin b)+rhoStar-1) := by
    rw [line_sum,pairBase_eq_diagonal_scale]
    dsimp [diagonalVertex,b,z,diagonalBeta]
    ring
  rw [hid]
  nlinarith only [hp,hsum]

/-! ### The remainder -/

/-- The remainder is nonnegative on the domain. -/
theorem remainder_nonnegative {w s d : ℝ} (hd : DiagonalDomain w s d) : 0≤remainder w s d := by
  rw [remainder,diagonal_value_formula hd]
  split_ifs with hc
  · nlinarith [diagonal_cap_lower hd,abs_nonneg w,abs_nonneg s]
  · exact (diagonal_vertex_pos hd (le_of_not_ge hc)).le

/-- The remainder vanishes only at the angles of the model. -/
theorem remainder_zero {w s d : ℝ} (hd : DiagonalDomain w s d) (heq : remainder w s d=0) :
    w=0 ∧ s=0 ∧ d=Real.pi/4 := by
  rw [remainder,diagonal_value_formula hd] at heq
  split_ifs at heq with hc
  · exact diagonal_cap_zero hd heq
  · linarith [diagonal_vertex_pos hd (le_of_not_ge hc)]

end SquaresInCircles.Six.Stress

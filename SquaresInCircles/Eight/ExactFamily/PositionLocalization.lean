module

public import SquaresInCircles.Eight.ExactFamily.CircleConvexity
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Analytic stationary-position localization on the broad radius strip

Uncompiled draft.  One comparison position, `87/100`, handles the entire
radius and tilt strip.  Circle equations imply all comparison bounds.
Strict convexity then places every stationary position to its right.
There is no interval subdivision or recursive root search in this module.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

def slopeRatio (q u : ℝ) : ℝ :=
  (2-u)*topLeft q u/(topRight q u*topHeight q u)
def positionHalf (q c s u : ℝ) : ℝ :=
  firstComponent q c s u*(s+c*u/lowerRight q u)-
    secondComponent q c s u*slopeRatio q u*(c+s*lowerHeight q u/lowerLeft q u)

theorem upper_curve_deriv {q u : ℝ} {f : ℝ → ℝ} {f' : ℝ}
    (hf : HasDerivAt f f' u) (hr : 0<upper q (f u)) :
    HasDerivAt (fun x => upper q (f x)) (-f u*f'/upper q (f u)) u := by
  have hrad : q-f u^2≠0 := ne_of_gt (Real.sqrt_pos.mp hr)
  have h := ((hasDerivAt_const u q).sub (hf.pow 2)).sqrt hrad
  convert h using 1
  · rfl
  · change -f u*f'/upper q (f u)=(0-2*f u^(2-1)*f')/(2*upper q (f u))
    field_simp [ne_of_gt hr]
    ring

theorem position_deriv {q c s u : ℝ}
    (hr : 0<lowerRight q u) (hU : 0<topRight q u)
    (hY : 0<topHeight q u) (hw : 0<lowerLeft q u) :
    HasDerivAt (defect q c s) (2*positionHalf q c s u) u := by
  have dr : HasDerivAt (lowerRight q) (-u/lowerRight q u) u := by
    simpa [lowerRight] using upper_curve_deriv (hasDerivAt_id u) hr
  have dU : HasDerivAt (topRight q) ((2-u)/topRight q u) u := by
    have h := upper_curve_deriv ((hasDerivAt_const u (2:ℝ)).sub (hasDerivAt_id u)) hU
    convert h using 1 <;> dsimp [topRight] <;> ring
  have dV : HasDerivAt (topLeft q) (-((2-u)/topRight q u)) u := by
    simpa [topLeft] using (hasDerivAt_const u (3:ℝ)).sub dU
  have dY : HasDerivAt (topHeight q) (slopeRatio q u) u := by
    have h := upper_curve_deriv dV hY
    convert h using 1
    · rfl
    · dsimp [slopeRatio,topHeight]
      field_simp [ne_of_gt hU,ne_of_gt hY]
      ring
  have dv : HasDerivAt (lowerHeight q) (-slopeRatio q u) u := by
    simpa [lowerHeight] using (hasDerivAt_const u (2:ℝ)).sub dY
  have dw : HasDerivAt (lowerLeft q)
      (lowerHeight q u*slopeRatio q u/lowerLeft q u) u := by
    have h := upper_curve_deriv dv hw
    convert h using 1 <;> dsimp [lowerLeft] <;> ring
  have dk₁ : HasDerivAt (firstComponent q c s) (s+c*u/lowerRight q u) u := by
    have h := ((hasDerivAt_const u (2:ℝ)).sub ((dr.sub_const 1).const_mul c)).add
      ((hasDerivAt_id u).const_mul s)
    convert h using 1
    · rfl
    · ring
  have dk₂ : HasDerivAt (secondComponent q c s)
      (-slopeRatio q u*(c+s*lowerHeight q u/lowerLeft q u)) u := by
    have h := ((hasDerivAt_const u (1:ℝ)).add (dv.const_mul c)).sub
      ((dw.sub_const 1).const_mul s)
    convert h using 1
    · rfl
    · ring
  have h := ((dk₁.pow 2).add (dk₂.pow 2)).sub (hasDerivAt_const u q)
  convert h using 1 <;> dsimp [defect,positionHalf] <;> ring

def comparisonPosition : ℝ := 87/100
def comparisonX (q : ℝ) : ℝ := comparisonPosition/lowerRight q comparisonPosition
def comparisonY (q : ℝ) : ℝ :=
  lowerHeight q comparisonPosition/lowerLeft q comparisonPosition

structure ComparisonBounds (q : ℝ) : Prop where
  r_lower : 1773/1000<lowerRight q comparisonPosition
  r_upper : lowerRight q comparisonPosition<1778/1000
  U_lower : 1619/1000<topRight q comparisonPosition
  U_upper : topRight q comparisonPosition<1625/1000
  V_lower : 1375/1000<topLeft q comparisonPosition
  V_upper : topLeft q comparisonPosition<1381/1000
  Y_lower : 1411/1000<topHeight q comparisonPosition
  Y_upper : topHeight q comparisonPosition<1424/1000
  v_lower : 576/1000<lowerHeight q comparisonPosition
  v_upper : lowerHeight q comparisonPosition<589/1000
  w_lower : 1885/1000<lowerLeft q comparisonPosition
  w_upper : lowerLeft q comparisonPosition<1894/1000
  p_lower : 671/1000<slopeRatio q comparisonPosition
  p_upper : slopeRatio q comparisonPosition<684/1000
  x_lower : 489/1000<comparisonX q
  x_upper : comparisonX q<491/1000
  y_lower : 3/10<comparisonY q
  y_upper : comparisonY q<5/16

theorem sqrt_between {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hl : a^2<x) (hu : x<b^2) : a<Real.sqrt x ∧ Real.sqrt x<b := by
  have hx : 0 ≤ x := by nlinarith [sq_nonneg a]
  have hs := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  constructor
  · by_contra! hh
    have hsq := square_mono_nonneg hn hh
    nlinarith
  · by_contra! hh
    have hsq := square_mono_nonneg hb hh
    nlinarith

/-- These bounds follow by successive square comparisons, with no split
of the radius interval. -/
theorem comparison_bounds {q : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500) : ComparisonBounds q := by
  have hr : 1773/1000<lowerRight q comparisonPosition ∧
      lowerRight q comparisonPosition<1778/1000 := by
    apply sqrt_between (by norm_num) (by norm_num) <;>
      dsimp [lowerRight,upper,comparisonPosition] <;> nlinarith
  have hU : 1619/1000<topRight q comparisonPosition ∧
      topRight q comparisonPosition<1625/1000 := by
    apply sqrt_between (by norm_num) (by norm_num) <;>
      dsimp [topRight,upper,comparisonPosition] <;> nlinarith
  have hV : 1375/1000<topLeft q comparisonPosition ∧
      topLeft q comparisonPosition<1381/1000 := by
    dsimp [topLeft]
    constructor <;> linarith [hU.1,hU.2]
  have hY : 1411/1000<topHeight q comparisonPosition ∧
      topHeight q comparisonPosition<1424/1000 := by
    apply sqrt_between (by norm_num) (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ topLeft q comparisonPosition) hV.2.le
      dsimp [topHeight,upper]
      nlinarith
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 1375/1000) hV.1.le
      dsimp [topHeight,upper]
      nlinarith
  have hv : 576/1000<lowerHeight q comparisonPosition ∧
      lowerHeight q comparisonPosition<589/1000 := by
    dsimp [lowerHeight]
    constructor <;> linarith [hY.1,hY.2]
  have hw : 1885/1000<lowerLeft q comparisonPosition ∧
      lowerLeft q comparisonPosition<1894/1000 := by
    apply sqrt_between (by norm_num) (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ lowerHeight q comparisonPosition) hv.2.le
      dsimp [lowerLeft,upper]
      nlinarith
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 576/1000) hv.1.le
      dsimp [lowerLeft,upper]
      nlinarith
  have hUp : 0<topRight q comparisonPosition := by linarith [hU.1]
  have hYp : 0<topHeight q comparisonPosition := by linarith [hY.1]
  have hprodL : (1619/1000:ℝ)*(1411/1000) ≤
      topRight q comparisonPosition*topHeight q comparisonPosition :=
    mul_le_mul hU.1.le hY.1.le (by norm_num) hUp.le
  have hprodU : topRight q comparisonPosition*topHeight q comparisonPosition ≤
      (1625/1000:ℝ)*(1424/1000) :=
    mul_le_mul hU.2.le hY.2.le hYp.le (by norm_num)
  have hp : 671/1000<slopeRatio q comparisonPosition ∧
      slopeRatio q comparisonPosition<684/1000 := by
    dsimp [slopeRatio,comparisonPosition]
    constructor
    · rw [lt_div_iff₀ (mul_pos hUp hYp)]
      have hs := mul_le_mul_of_nonneg_left hprodU (by norm_num : (0:ℝ) ≤ 671/1000)
      nlinarith [hV.1]
    · rw [div_lt_iff₀ (mul_pos hUp hYp)]
      have hs := mul_le_mul_of_nonneg_left hprodL (by norm_num : (0:ℝ) ≤ 684/1000)
      nlinarith [hV.2]
  have hx : 489/1000<comparisonX q ∧ comparisonX q<491/1000 := by
    dsimp [comparisonX,comparisonPosition]
    constructor
    · rw [lt_div_iff₀ (by linarith : 0<lowerRight q (87/100))]
      nlinarith [hr.2]
    · rw [div_lt_iff₀ (by linarith : 0<lowerRight q (87/100))]
      nlinarith [hr.1]
  have hy : 3/10<comparisonY q ∧ comparisonY q<5/16 := by
    dsimp [comparisonY]
    constructor
    · rw [lt_div_iff₀ (by linarith : 0<lowerLeft q comparisonPosition)]
      nlinarith [hw.2,hv.1]
    · rw [div_lt_iff₀ (by linarith : 0<lowerLeft q comparisonPosition)]
      nlinarith [hw.1,hv.2]
  exact ⟨hr.1,hr.2,hU.1,hU.2,hV.1,hV.2,hY.1,hY.2,hv.1,hv.2,
    hw.1,hw.2,hp.1,hp.2,hx.1,hx.2,hy.1,hy.2⟩

theorem comparison_domain {q : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500) : Domain q comparisonPosition := by
  have hb := comparison_bounds hql hqu
  have hr : 0<lowerRight q comparisonPosition := by linarith [hb.r_lower]
  have hU : 0<topRight q comparisonPosition := by linarith [hb.U_lower]
  have hY : 0<topHeight q comparisonPosition := by linarith [hb.Y_lower]
  have hw : 0<lowerLeft q comparisonPosition := by linarith [hb.w_lower]
  refine ⟨by norm_num [comparisonPosition],?_,?_,?_,?_⟩
  · have h : 0<q-comparisonPosition^2 := Real.sqrt_pos.mp hr
    linarith
  · have h : 0<q-(2-comparisonPosition)^2 := Real.sqrt_pos.mp hU
    linarith
  · have h : 0<q-topLeft q comparisonPosition^2 := Real.sqrt_pos.mp hY
    linarith
  · have h : 0<q-lowerHeight q comparisonPosition^2 := Real.sqrt_pos.mp hw
    linarith

def coefficientLc (q : ℝ) : ℝ := 2*comparisonX q-slopeRatio q comparisonPosition
def coefficientLs (q : ℝ) : ℝ := 2-slopeRatio q comparisonPosition*comparisonY q
def coefficientQc (q : ℝ) : ℝ :=
  (lowerRight q comparisonPosition-1)*comparisonX q+
    slopeRatio q comparisonPosition*lowerHeight q comparisonPosition
def coefficientJ (q : ℝ) : ℝ :=
  comparisonPosition*comparisonX q-(lowerRight q comparisonPosition-1)-
    slopeRatio q comparisonPosition*lowerHeight q comparisonPosition*comparisonY q+
      slopeRatio q comparisonPosition*(lowerLeft q comparisonPosition-1)
def coefficientQs (q : ℝ) : ℝ :=
  comparisonPosition+slopeRatio q comparisonPosition*
    (lowerLeft q comparisonPosition-1)*comparisonY q

/-- Five small inequalities are sufficient for the complete angle interval.
Their inputs were derived from the actual circle radicals above. -/
theorem comparison_coefficients {q : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500) :
    coefficientLc q ≤ 5/16 ∧ coefficientLs q ≤ 9/5 ∧ 61/80 ≤ coefficientQc q ∧
      coefficientJ q ≤ 3/20 ∧ coefficientQs q ≤ 17/16 := by
  have h := comparison_bounds hql hqu
  have hp : 0 ≤ slopeRatio q comparisonPosition := by linarith [h.p_lower]
  have hv : 0 ≤ lowerHeight q comparisonPosition := by linarith [h.v_lower]
  have hy : 0 ≤ comparisonY q := by linarith [h.y_lower]
  have hpy : (671/1000:ℝ)*(3/10) ≤ slopeRatio q comparisonPosition*comparisonY q :=
    mul_le_mul h.p_lower.le h.y_lower.le (by norm_num) hp
  have hrx : (773/1000:ℝ)*(489/1000) ≤
      (lowerRight q comparisonPosition-1)*comparisonX q :=
    mul_le_mul (by linarith [h.r_lower]) h.x_lower.le (by norm_num)
      (by linarith [h.r_lower])
  have hpv : (671/1000:ℝ)*(576/1000) ≤
      slopeRatio q comparisonPosition*lowerHeight q comparisonPosition :=
    mul_le_mul h.p_lower.le h.v_lower.le (by norm_num) hp
  have hpvy : (671/1000:ℝ)*(576/1000)*(3/10) ≤
      slopeRatio q comparisonPosition*lowerHeight q comparisonPosition*comparisonY q :=
    mul_le_mul hpv h.y_lower.le (by norm_num) (mul_nonneg hp hv)
  have hpw : slopeRatio q comparisonPosition*(lowerLeft q comparisonPosition-1) ≤
      (684/1000:ℝ)*(894/1000) :=
    mul_le_mul h.p_upper.le (by linarith [h.w_upper])
      (by linarith [h.w_lower]) (by norm_num)
  have hpwy : slopeRatio q comparisonPosition*(lowerLeft q comparisonPosition-1)*comparisonY q ≤
      (684/1000:ℝ)*(894/1000)*(5/16) :=
    mul_le_mul hpw h.y_upper.le hy (by norm_num)
  refine ⟨?_,?_,?_,?_,?_⟩
  · dsimp [coefficientLc]
    linarith [h.x_upper,h.p_lower]
  · dsimp [coefficientLs]
    linarith
  · dsimp [coefficientQc]
    linarith
  · dsimp [coefficientJ,comparisonPosition]
    nlinarith [h.x_upper,h.r_lower]
  · dsimp [coefficientQs,comparisonPosition]
    linarith

def comparisonPolynomial (q h L : ℝ) : ℝ :=
  L*coefficientLc q-coefficientQc q+h*(L*coefficientLs q+coefficientJ q)+
    h^2*coefficientQs q

theorem comparisonPolynomial_bound {q h L : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hh : 0 ≤ h) (hhu : h ≤ 1/5) (hL : 0 ≤ L) (hLu : L ≤ 51/50) :
    comparisonPolynomial q h L ≤ -(81/20000) := by
  obtain ⟨hLc,hLs,hQc,hJ,hQs⟩ := comparison_coefficients hql hqu
  have h₀ : L*coefficientLc q ≤ (51/50:ℝ)*(5/16) :=
    (mul_le_mul_of_nonneg_left hLc hL).trans
      (mul_le_mul_of_nonneg_right hLu (by norm_num))
  have h₁ : L*coefficientLs q+coefficientJ q ≤ (51/50:ℝ)*(9/5)+3/20 := by
    have h := (mul_le_mul_of_nonneg_left hLs hL).trans
      (mul_le_mul_of_nonneg_right hLu (by norm_num))
    linarith
  have h₂ : h*(L*coefficientLs q+coefficientJ q) ≤
      (1/5:ℝ)*((51/50)*(9/5)+3/20) :=
    (mul_le_mul_of_nonneg_left h₁ hh).trans
      (mul_le_mul_of_nonneg_right hhu (by norm_num))
  have h₃ : h^2*coefficientQs q ≤ (1/25:ℝ)*(17/16) := by
    have hs : h^2 ≤ (1/25:ℝ) := by nlinarith [square_mono_nonneg hh hhu]
    exact (mul_le_mul_of_nonneg_left hQs (sq_nonneg h)).trans
      (mul_le_mul_of_nonneg_right hs (by norm_num))
  dsimp [comparisonPolynomial]
  linarith

theorem scaled_position_identity (r v w p x y u c s : ℝ) (hc : c≠0) :
    (2-c*(r-1)+s*u)*(s+c*x)-(1+c*v-s*(w-1))*p*(c+s*y) =
    c^2*((1/c)*(2*x-p)-((r-1)*x+p*v)+
      (s/c)*((1/c)*(2-p*y)+(u*x-(r-1)-p*v*y+p*(w-1)))+
        (s/c)^2*(u+p*(w-1)*y)) := by
  field_simp [hc]
  ring

theorem comparison_position_identity {q c s : ℝ} (hc : c≠0) :
    positionHalf q c s comparisonPosition=
      c^2*comparisonPolynomial q (s/c) (1/c) := by
  have h := scaled_position_identity
    (lowerRight q comparisonPosition) (lowerHeight q comparisonPosition)
    (lowerLeft q comparisonPosition) (slopeRatio q comparisonPosition)
    (comparisonX q) (comparisonY q) comparisonPosition c s hc
  simpa [positionHalf,comparisonPolynomial,coefficientLc,coefficientLs,coefficientQc,
    coefficientJ,coefficientQs,comparisonX,comparisonY,firstComponent,secondComponent,
    div_eq_mul_inv,mul_assoc] using h

theorem comparison_position_negative {q c s : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (ht : s/c ≤ 1/5) (hunit : c^2+s^2=1) :
    positionHalf q c s comparisonPosition<0 := by
  have hh : 0 ≤ s/c := div_nonneg hs hc.le
  have hL : 0 ≤ (1:ℝ)/c := (div_pos (by norm_num) hc).le
  have hsq : ((1:ℝ)/c)^2=1+(s/c)^2 := by
    field_simp [ne_of_gt hc]
    nlinarith
  have hh2 : (s/c)^2 ≤ (1/25:ℝ) := by
    nlinarith [square_mono_nonneg hh ht]
  have hLu : (1:ℝ)/c ≤ 51/50 := by
    by_contra! hbad
    have hbig := square_strict_mono_nonneg (by norm_num : (0:ℝ) ≤ 51/50) hbad
    nlinarith
  have hb := comparisonPolynomial_bound hql hqu hh ht hL hLu
  rw [comparison_position_identity (ne_of_gt hc)]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos hc) (by linarith)

/-- A derivative-zero position is to the right of the one comparison point.
The two-point secant inequalities require differentiability only at those
two points, so radical endpoints elsewhere cause no regularity gap. -/
theorem stationary_position_lower {q c s u : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (ht : s/c ≤ 1/5) (hunit : c^2+s^2=1)
    (hu : Domain q u) (hstat : HasDerivAt (defect q c s) 0 u) : comparisonPosition<u := by
  have hq : q<4 := by linarith
  have hcu : c ≤ 1 := by nlinarith [sq_nonneg s,sq_nonneg (c-1)]
  have hsu : s ≤ 1 := by nlinarith [sq_nonneg c,sq_nonneg (s-1)]
  have hconv := strictConvexOn_defect hq hc hcu hs hsu
  have hcomp := comparison_domain hql hqu
  have hb := comparison_bounds hql hqu
  have hd := position_deriv (q:=q) (c:=c) (s:=s) (u:=comparisonPosition)
    (by linarith [hb.r_lower]) (by linarith [hb.U_lower])
    (by linarith [hb.Y_lower]) (by linarith [hb.w_lower])
  have hn := comparison_position_negative hql hqu hc hs ht hunit
  by_contra! hle
  rcases lt_or_eq_of_le hle with hlt | rfl
  · have h₁ := hconv.lt_slope_of_hasDerivAt hu hcomp hlt hstat
    have h₂ := hconv.slope_lt_of_hasDerivAt hu hcomp hlt hd
    linarith
  · have he := hstat.unique hd
    linarith

/-- A zero position derivative gives the global fixed-tilt minimum on the
full domain.  Only differentiability at the selected position is used. -/
theorem stationary_global_minimum {q c s u : ℝ} (hq : q<4)
    (hc : 0<c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hsu : s ≤ 1)
    (hu : Domain q u) (hstat : HasDerivAt (defect q c s) 0 u) :
    ∀ v, Domain q v → defect q c s u ≤ defect q c s v := by
  have hconv := (strictConvexOn_defect hq hc hcu hs hsu).convexOn
  intro v hv
  rcases lt_trichotomy u v with hlt | rfl | hlt
  · have h := hconv.le_slope_of_hasDerivAt hu hv hlt hstat
    rw [slope_def_field,le_div_iff₀ (sub_pos.mpr hlt)] at h
    linarith
  · rfl
  · have h := hconv.slope_le_of_hasDerivAt hv hu hlt hstat
    rw [slope_def_field,div_le_iff₀ (sub_pos.mpr hlt)] at h
    linarith

theorem coordinate_positionHalf {d : Coordinates} (hd : d.IsChain) :
    2*positionHalf d.q d.c d.s (-d.y)= -d.positionDerivative := by
  obtain ⟨hr,hU,hV,hY,hv,hw⟩ := coordinate_values hd
  have hp : slopeRatio d.q (-d.y)= -d.y₄deriv := by
    rw [slopeRatio,hV,hU,hY]
    dsimp [Coordinates.y₄deriv]
    field_simp [ne_of_gt hd.x₂_pos,ne_of_gt hd.y₃_pos]
    ring
  have hfirst : firstComponent d.q d.c d.s (-d.y)= -d.h₁ := by
    rw [firstComponent,hr]
    dsimp [Coordinates.h₁]
    ring
  have hsecond : secondComponent d.q d.c d.s (-d.y)= -d.h₂ := by
    rw [secondComponent,hv,hw]
    dsimp [Coordinates.h₂]
    ring
  rw [positionHalf,hfirst,hsecond,hr,hv,hw,hp]
  dsimp [Coordinates.positionDerivative,Coordinates.h₁deriv,Coordinates.h₂deriv]
  field_simp [ne_of_gt hd.x₁_pos,ne_of_lt hd.x₄_neg]
  ring

/-- The broad stationary predicate itself now yields `87/100<-y<1`
without calling `stationary_localization` or the recursive root checker. -/
theorem stationary_coordinate_lower {d : Coordinates} (hd : d.IsStationary) :
    comparisonPosition< -d.y := by
  have hc : 0<d.c := halfAngleCos_pos (by rw [abs_lt]; constructor <;> linarith [hd.z_pos,hd.z_lt_one])
  have hs : 0 ≤ d.s := (halfAngleSin_pos hd.z_pos).le
  have ht : d.s/d.c ≤ 1/5 := by
    have hden : 0<1-d.z^2 := by nlinarith [hd.z_pos,hd.z_lt_one,sq_nonneg (1-d.z)]
    have he : d.s/d.c=2*d.z/(1-d.z^2) := by
      dsimp [Coordinates.c,Coordinates.s,halfAngleCos,halfAngleSin]
      field_simp [ne_of_gt (halfAngle_den_pos d.z),ne_of_gt hden]
      ring
    rw [he]
    exact hd.tilt_range.le
  have hdom := coordinate_domain hd.toIsChain (by linarith [hd.y_upper])
  obtain ⟨hr,hU,_,hY,_,hw⟩ := coordinate_values hd.toIsChain
  have hp := position_deriv (q:=d.q) (c:=d.c) (s:=d.s) (u:=-d.y)
    (by rw [hr]; exact hd.x₁_pos) (by rw [hU]; exact hd.x₂_pos)
    (by rw [hY]; exact hd.y₃_pos) (by rw [hw]; linarith [hd.x₄_neg])
  rw [coordinate_positionHalf hd.toIsChain,hd.position_stationary,neg_zero] at hp
  exact stationary_position_lower hd.q_lower hd.q_upper hc hs ht d.unit hdom hp

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

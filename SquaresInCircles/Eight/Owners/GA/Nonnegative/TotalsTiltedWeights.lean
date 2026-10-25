module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsCoefficients
public import SquaresInCircles.Eight.Owners.GA.Positive.TDScalarBounds

/-!
# Eight squares: the tilted weight on every original A/TD split

The triangle's two
edge certificates control the whole affine E coordinate. The rectangle
uses monotonicity only on its actual interval theta <= 1/6. The B
coefficient envelope retains q-star on the triangle and the original
upper tilted coefficient on the rectangle.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Explicit
open Secondary TensorWholeIntervalPolynomial TwoVariablePolynomial

def tilt (z : ℝ) : ℝ := Real.cos z+(293/1000)*Real.sin z
def tilted (r : Region) (x y z : ℝ) : ℝ := c r x y*tilt z

theorem tilted_eq (r : Region) (x y z : ℝ) :
    tilted r x y z=PositiveTD.tilted (c r x y) z := by
  rfl

theorem tilt_hasDerivAt (z : ℝ) :
    HasDerivAt tilt (-Real.sin z+(293/1000)*Real.cos z) z := by
  have h : HasDerivAt (fun z => Real.cos z+(293/1000)*Real.sin z)
      (-Real.sin z+(293/1000)*Real.cos z) z :=
    (Real.hasDerivAt_cos z).add ((Real.hasDerivAt_sin z).const_mul (293/1000:ℝ))
  exact h

theorem tilt_second (z : ℝ) :
    HasDerivAt (fun z => -Real.sin z+(293/1000)*Real.cos z) (-tilt z) z := by
  convert (Real.hasDerivAt_sin z).neg.add ((Real.hasDerivAt_cos z).const_mul (293/1000:ℝ))
    using 1 <;> dsimp [tilt] <;> ring

theorem tilt_lower {z : ℝ} (hz : z∈Icc 0 frameCap) : (478/625:ℝ)<tilt z := by
  have ht := transport_trig hz
  dsimp [tilt]
  linarith [ht.1,ht.2.2.1]

theorem tilt_square (z : ℝ) :
    (tilt z)^2+((293/1000)*Real.cos z-Real.sin z)^2=1+(293/1000:ℝ)^2 := by
  dsimp [tilt]
  linear_combination (1+(293/1000:ℝ)^2)*(Real.sin_sq_add_cos_sq z)

theorem tilt_upper (z : ℝ) : tilt z<(24/23:ℝ) := by
  have hh := tilt_square z
  nlinarith [sq_nonneg ((293/1000)*Real.cos z-Real.sin z)]

theorem tilt_concave : ConcaveOn ℝ (Icc 0 frameCap) tilt :=
  concave_of_deriv2 (fun z _ => tilt_hasDerivAt z) (fun z _ => tilt_second z)
    (fun z hz => by linarith [tilt_lower hz])

theorem tilt_minimum {z t : ℝ} (ht : t∈Icc 0 frameCap) (hz : z∈Icc 0 t) :
    min 1 (tilt t)≤tilt z := by
  have hh := tilt_concave.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht hz
  simpa [tilt] using hh

theorem tilt_small_monotone : MonotoneOn tilt (Icc (0:ℝ) (1/6)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun z _ => (tilt_hasDerivAt z).continuousAt.continuousWithinAt)
    (fun z _ => tilt_hasDerivAt z)
  intro z hz
  have hzf : z∈Icc 0 frameCap := ⟨hz.1.le,by simp only [frameCap]; linarith [hz.2]⟩
  have ht := transport_trig hzf
  have hs := Real.sin_lt hz.1
  linarith [ht.1,hz.2]

theorem tilt_taylor {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z PositiveTD.Certificate.C10+(293/1000)*aeval z PositiveTD.Certificate.S11≤tilt z ∧
    tilt z≤aeval z PositiveTD.Certificate.C12+(293/1000)*aeval z PositiveTD.Certificate.S9 := by
  have ht := PositiveTD.Certificate.taylor_bounds hz
  dsimp [tilt]
  exact ⟨by linarith [ht.2.2.2.2.1,ht.2.1],by linarith [ht.2.2.2.2.2,ht.2.2.1]⟩

theorem affine_minimum {b y v w : ℝ} (hy : y∈Icc 0 b) :
    min v (v+b*w)≤v+y*w := by
  by_cases hw : 0≤w
  · exact (min_le_left _ _).trans (by nlinarith [mul_nonneg hy.1 hw])
  · have hh := mul_le_mul_of_nonpos_right hy.2 (le_of_not_ge hw)
    exact (min_le_right _ _).trans (by linarith)

theorem edge_evaluate (far : Bool) (p : Bivar) (x : ℝ) :
    aeval x (Coefficients.edge far p)=evaluate x (if far then 8/15-x else 0) p := by
  cases far <;> simp [Coefficients.edge,evaluate_restrict,Coefficients.d]

theorem triangle_lowerM_gap {x y : ℝ} (hd : Domain .triangle x y) :
    (21/2500:ℝ)<evaluate x y (Coefficients.lowerM-Certificate.k .triangle) := by
  have hx := triangle_x hd
  have h0 := Coefficients.lowerGap_lower false hx
  have h1 := Coefficients.lowerGap_lower true hx
  simp only [Coefficients.lowerGap,edge_evaluate,Bool.false_eq_true,ite_false,ite_true] at h0 h1
  let T : ℝ := aeval (1/6+x) PositiveTD.Certificate.C10+
    (293/1000)*aeval (1/6+x) PositiveTD.Certificate.S11
  have he (Y : ℝ) : evaluate x Y (Coefficients.lowerM-Certificate.k .triangle)=
      c .triangle x 0*T-k .triangle x 0+Y*(T/4-7/25) := by
    simp only [Coefficients.lowerM,map_sub,map_mul,map_add,evaluate_lift,evaluate_scalar,
      Certificate.evaluate_c,Certificate.evaluate_theta,Certificate.evaluate_k]
    dsimp [theta,T,c,k]
    ring
  rw [he 0] at h0
  rw [he (8/15-x)] at h1
  have hm := affine_minimum (v:=c .triangle x 0*T-k .triangle x 0)
    (w:=T/4-7/25) (show y∈Icc 0 (8/15-x) from ⟨hd.2.1,by linarith [hd.2.2]⟩)
  rw [he y]
  have hmin : (21/2500:ℝ) < min (c .triangle x 0*T-k .triangle x 0)
      (c .triangle x 0*T-k .triangle x 0+(8/15-x)*(T/4-7/25)) :=
    lt_min (by simpa using h0) h1
  exact hmin.trans_le hm

theorem triangle_tilted_endpoint_lower {x y : ℝ} (hd : Domain .triangle x y) :
    k .triangle x y<tilted .triangle x y (theta .triangle x y) := by
  have hθ := (domains hd).1
  have hc := (base_bounds .triangle hd).c_positive
  have ht := mul_le_mul_of_nonneg_left (tilt_taylor hθ).1 hc.le
  have hgap := triangle_lowerM_gap hd
  simp only [Coefficients.lowerM,map_sub,map_mul,map_add,evaluate_lift,evaluate_scalar,
    Certificate.evaluate_c,Certificate.evaluate_theta,Certificate.evaluate_k] at hgap
  dsimp [tilted]
  linarith

theorem triangle_tilted_lower {x y z : ℝ} (hd : Domain .triangle x y)
    (hz : z∈Icc 0 (theta .triangle x y)) : k .triangle x y<tilted .triangle x y z := by
  have hb := base_bounds .triangle hd
  have hmin := mul_le_mul_of_nonneg_left (tilt_minimum (domains hd).1 hz) hb.c_positive.le
  have hendpoint := triangle_tilted_endpoint_lower hd
  have hinitial := (triangle_differences hd).2.1
  dsimp [tilted] at hendpoint ⊢
  rcases le_total 1 (tilt (theta .triangle x y)) with ht | ht
  · rw [min_eq_left ht] at hmin
    linarith
  · rw [min_eq_right ht] at hmin
    linarith

theorem triangle_upperM_gap {x y : ℝ} (hd : Domain .triangle x y) :
    0<evaluate x y (Certificate.qStar .triangle-Certificate.M .triangle .atT) := by
  have hx := triangle_x hd
  have h0 := Coefficients.upperGap_lower false hx
  have h1 := Coefficients.upperGap_lower true hx
  simp only [Coefficients.upperGap,edge_evaluate,Bool.false_eq_true,ite_false,ite_true] at h0 h1
  have hr0 : ((Coefficients.gapReserve false:ℚ):ℝ)=239/50000 := by
    norm_num [Coefficients.gapReserve]
  have hr1 : ((Coefficients.gapReserve true:ℚ):ℝ)=1/625 := by
    norm_num [Coefficients.gapReserve]
  rw [hr0] at h0
  rw [hr1] at h1
  let T : ℝ := aeval (1/6+x) PositiveTD.Certificate.C12+
    (293/1000)*aeval (1/6+x) PositiveTD.Certificate.S9
  have he (Y : ℝ) : evaluate x Y (Certificate.qStar .triangle-Certificate.M .triangle .atT)=
      qStar .triangle x 0-c .triangle x 0*T+Y*((1-T)/4) := by
    simp only [Certificate.M,map_sub,map_mul,map_add,evaluate_lift,evaluate_scalar,
      Certificate.evaluate_c,Certificate.evaluate_theta,Certificate.evaluate_qStar]
    dsimp [theta,T,qStar,l,c]
    ring
  rw [he 0] at h0
  rw [he (8/15-x)] at h1
  have hm := affine_minimum (v:=qStar .triangle x 0-c .triangle x 0*T)
    (w:=(1-T)/4) (show y∈Icc 0 (8/15-x) from ⟨hd.2.1,by linarith [hd.2.2]⟩)
  rw [he y]
  exact (lt_min (by linarith : 0<qStar .triangle x 0-c .triangle x 0*T)
    (by linarith : 0<qStar .triangle x 0-c .triangle x 0*T+(8/15-x)*((1-T)/4))).trans_le hm

def qMinusC (x : ℝ) : ℝ := 637/10000-(279/2500)*x+(277/5000)*x^2-(1289/10000)*x^3

theorem qMinusC_hasDerivAt (x : ℝ) :
    HasDerivAt qMinusC (-279/2500+(277/2500)*x-(3867/10000)*x^2) x := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
  have h2 : HasDerivAt (fun x : ℝ => x^2) (2*x) x := by
    simpa using hasDerivAt_pow 2 x
  have h3 : HasDerivAt (fun x : ℝ => x^3) (3*x^2) x := by
    simpa using hasDerivAt_pow 3 x
  have h : HasDerivAt (fun x : ℝ => 637/10000-(279/2500)*x+(277/5000)*x^2-(1289/10000)*x^3)
      (0-(279/2500)*1+(277/5000)*(2*x)-(1289/10000)*(3*x^2)) x :=
    (((hasDerivAt_const x (637/10000:ℝ)).sub (h1.const_mul _)).add (h2.const_mul _)).sub
      (h3.const_mul _)
  exact h.congr_deriv (by ring)

theorem qMinusC_positive {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) : 0<qMinusC x := by
  have hm : AntitoneOn qMinusC (Icc (0:ℝ) (8/15)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x _ => (qMinusC_hasDerivAt x).continuousAt.continuousWithinAt)
      (fun x _ => qMinusC_hasDerivAt x)
    intro x hx
    nlinarith [hx.2,sq_nonneg x]
  have hh := hm hx (show (8/15:ℝ)∈Icc 0 (8/15) by norm_num) hx.2
  have he : qMinusC (8/15)=(12947/33750000:ℝ) := by norm_num [qMinusC]
  rw [he] at hh
  linarith

theorem triangle_q_envelope {x y : ℝ} (hd : Domain .triangle x y) :
    l .triangle x y≤qStar .triangle x y ∧
    c .triangle x y<qStar .triangle x y ∧
    tilted .triangle x y (theta .triangle x y)<qStar .triangle x y := by
  have hx := triangle_x hd
  have he : qStar .triangle x y-c .triangle x y=qMinusC x := by
    dsimp [qStar,l,c,qMinusC]
    ring
  have hgap := triangle_upperM_gap hd
  have hθ := (domains hd).1
  have hc := (base_bounds .triangle hd).c_positive
  have hupper := mul_le_mul_of_nonneg_left (tilt_taylor hθ).2 hc.le
  simp only [Certificate.M,map_sub,map_mul,map_add,evaluate_lift,evaluate_scalar,
    Certificate.evaluate_c,Certificate.evaluate_theta,Certificate.evaluate_qStar] at hgap
  refine ⟨?_,?_,?_⟩
  · dsimp [qStar]
    linarith [hx.2]
  · linarith [qMinusC_positive hx]
  · dsimp [tilted]
    linarith

theorem rectangle_theta {x y : ℝ} (hd : Domain .rectangle x y) :
    theta .rectangle x y∈Icc 0 (1/6:ℝ) := by
  dsimp [theta]
  exact ⟨by linarith [hd.1.2],by linarith [hd.1.1]⟩

theorem rectangle_tilted_bounds {x y z : ℝ} (hd : Domain .rectangle x y)
    (hz : z∈Icc 0 (theta .rectangle x y)) :
    c .rectangle x y≤tilted .rectangle x y z ∧
      tilted .rectangle x y z≤tilted .rectangle x y (theta .rectangle x y) ∧
      tilted .rectangle x y (theta .rectangle x y)<299/250 := by
  have hθ := rectangle_theta hd
  have hzf : z∈Icc 0 (1/6:ℝ) := ⟨hz.1,hz.2.trans hθ.2⟩
  have hb := base_bounds .rectangle hd
  have h0 := tilt_small_monotone (show (0:ℝ)∈Icc 0 (1/6) by norm_num) hzf hz.1
  have h1 := tilt_small_monotone hzf hθ hz.2
  have h2 := mul_le_mul_of_nonneg_left h0 hb.c_positive.le
  have h3 := mul_le_mul_of_nonneg_left h1 hb.c_positive.le
  have ht := tilt_taylor (domains hd).1
  have hcoef : c .rectangle x y≤11913/10000-(1/4)*theta .rectangle x y := by
    dsimp [c,theta]
    linarith [hd.2.2]
  have hp := mul_le_mul hcoef ht.2 (by linarith [tilt_lower (domains hd).1] : 0≤tilt (theta .rectangle x y))
    (by linarith [hb.c_positive] : 0≤11913/10000-(1/4)*theta .rectangle x y)
  have hmax := Coefficients.rectangle_maximum_upper hθ
  have he : aeval (theta .rectangle x y) Coefficients.rectangleMaximum=
      (11913/10000-(1/4)*theta .rectangle x y)*
        (aeval (theta .rectangle x y) PositiveTD.Certificate.C12+
          (293/1000)*aeval (theta .rectangle x y) PositiveTD.Certificate.S9) := by
    simp [Coefficients.rectangleMaximum]
  rw [he] at hmax
  simp only [tilt,Real.cos_zero,Real.sin_zero,mul_zero,add_zero,mul_one] at h2
  exact ⟨h2,h3,by dsimp [tilted]; linarith⟩

theorem tilted_lower (r : Region) {x y z : ℝ} (hd : Domain r x y)
    (hz : z∈Icc 0 (theta r x y)) : k r x y<tilted r x y z := by
  cases r
  · exact triangle_tilted_lower hd hz
  · have hh := rectangle_tilted_bounds hd hz
    have hb := rectangle_ranges hd
    exact hb.2.2.2.2.2.2.1.trans (hb.2.2.2.2.1.trans_le hh.1)

theorem tilted_ratio (r : Region) {x y z : ℝ} (hd : Domain r x y)
    (hz : z∈Icc 0 (theta r x y)) :
    (2/3)*l r x y<tilted r x y z ∧ tilted r x y z<(23/20)*l r x y := by
  have hb := base_bounds r hd
  have hzf : z∈Icc 0 frameCap := ⟨hz.1,hz.2.trans (domains hd).1.2⟩
  have hlo := mul_lt_mul_of_pos_left (tilt_lower hzf) hb.c_positive
  have hhi := mul_lt_mul_of_pos_left (tilt_upper z) hb.c_positive
  have hcl := mul_le_mul_of_nonneg_right hb.c_lower_ratio
    (by norm_num : (0:ℝ)≤478/625)
  have hcu := mul_le_mul_of_nonneg_right hb.c_upper_ratio
    (by norm_num : (0:ℝ)≤24/23)
  dsimp [tilted]
  exact ⟨by nlinarith [hb.l_positive],by nlinarith [hb.l_positive]⟩

theorem tilted_upper (r : Region) {x y z : ℝ} (hd : Domain r x y)
    (hz : z∈Icc 0 (theta r x y)) : tilted r x y z<6/5 := by
  cases r
  · have hc := triangle_c_bounds hd
    have ht := mul_lt_mul hc.2 (tilt_upper z).le
      (by linarith [tilt_lower ⟨hz.1,hz.2.trans (domains hd).1.2⟩] : 0<tilt z)
      (by norm_num : (0:ℝ)≤23/20)
    dsimp [tilted]
    linarith
  · have hh := rectangle_tilted_bounds hd hz
    linarith [hh.2.1,hh.2.2]

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Explicit

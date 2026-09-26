import SquaresInCircles.Seven.Labels
import SquaresInCircles.Seven.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The marker arc

For an admissible state, the closed square holds the arc of the unit circle of
half-width `801/1600` about its label: each of the four edge lines stays out
of the way, the far one trivially. The transverse edges are controlled by
arcsine bounds, and the near edge by an envelope that is concave, hence below
its tangent at `1/8`.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

lemma asin_half : Real.arcsin (1/2 : ℝ) = Real.pi/6 := by
  have h := Real.arcsin_sin (x := Real.pi/6)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  simpa only [Real.sin_pi_div_six] using h

/-- `(5/4) y - arcsin y` increases on `[-3/5, 3/5]` and decreases on `[3/5, 1]`:
its derivative is `5/4 - 1/√(1 - y²)`. -/
lemma asin_line_mono :
    MonotoneOn (fun y => (5/4)*y-Real.arcsin y) (Icc (-3/5) (3/5)) ∧
      AntitoneOn (fun y => (5/4)*y-Real.arcsin y) (Icc (3/5) 1) := by
  have hd (y : ℝ) (hy : y ∈ Ioo (-1) 1) :
      HasDerivAt (fun y => (5/4)*y-Real.arcsin y) (5/4-1/Real.sqrt (1-y^2)) y :=
    ((hasDerivAt_id y).const_mul (5/4)).sub
      (Real.hasDerivAt_arcsin (by linarith [hy.1]) (by linarith [hy.2])) |>.congr_deriv (by simp)
  have hr {y : ℝ} (hy : y ∈ Ioo (-1) 1) : 0 < Real.sqrt (1-y^2) :=
    Real.sqrt_pos.mpr (by nlinarith [hy.1,hy.2])
  have hs {y : ℝ} (hy : y ∈ Ioo (-1) 1) : Real.sqrt (1-y^2)^2 = 1-y^2 :=
    Real.sq_sqrt (by nlinarith [hy.1,hy.2])
  refine ⟨monoOn_of_hasDeriv_nonneg (by fun_prop)
    (fun y hy => hd y ⟨by linarith [hy.1],by linarith [hy.2]⟩) fun y hy => ?_,
    antiOn_of_hasDeriv_nonpos (by fun_prop)
    (fun y hy => hd y ⟨by linarith [hy.1],hy.2⟩) fun y hy => ?_⟩
  · have hy' : y ∈ Ioo (-1) 1 := ⟨by linarith [hy.1],by linarith [hy.2]⟩
    have hlo : 4/5 ≤ Real.sqrt (1-y^2) := by nlinarith [hy.1,hy.2,hr hy',hs hy']
    linarith [(div_le_iff₀ (hr hy')).mpr (show 1 ≤ 5/4*Real.sqrt (1-y^2) by linarith)]
  · have hy' : y ∈ Ioo (-1) 1 := ⟨by linarith [hy.1],hy.2⟩
    have hup : Real.sqrt (1-y^2) ≤ 4/5 := by nlinarith [hy.1,hy.2,hr hy',hs hy']
    linarith [(le_div_iff₀ (hr hy')).mpr (show 5/4*Real.sqrt (1-y^2) ≤ 1 by linarith)]

lemma marker_lower_endpoint {a u : ℝ} (h : Admissible a u) :
    Real.arcsin (u-1/2)+801/1600 < label a u := by
  have hasin : Real.arcsin (u-1/2) ≤ u-1/2+1331/256000 := by
    by_cases h0 : 0 ≤ u-1/2
    · have hb := arcsin_le_cubic h0 (by linarith [h.u_lt])
      have hc : (u-1/2)^3 ≤ (11/40 : ℝ)^3 := pow_le_pow_left₀ h0 (by linarith [h.u_lt]) 3
      linarith
    · linarith [arcsin_le_self_of_nonpos (by linarith [h.u_nonneg]) (le_of_not_ge h0)]
  have hp := Real.pi_gt_d2
  -- the axial term: `(5/4) y - arcsin y` increases from `y = -1/2`
  have hA : Real.pi/6 ≤ axial u-Real.arcsin (u-1/2) := by
    have hm := asin_line_mono.1 (show (-1/2 : ℝ) ∈ Icc (-3/5) (3/5) by norm_num)
      (show u-1/2 ∈ Icc (-3/5) (3/5) by constructor <;> linarith [h.u_nonneg,h.u_lt]) (by linarith [h.u_nonneg])
    beta_reduce at hm
    rw [neg_div,Real.arcsin_neg,asin_half] at hm
    dsimp [axial]
    linarith
  have hcs : (3/4)*(a+1/2)+(2/3)*(u+1/2) < 2171/1200 := by
    have hid : ((3/4)*(a+1/2)+(2/3)*(u+1/2))^2+
        ((2/3)*(a+1/2)-(3/4)*(u+1/2))^2 = (145/144)*phi a u := by
      dsimp [phi]; ring
    have hh := h.phi_le
    dsimp [targetSq] at hh
    have hs := sq_nonneg ((2/3)*(a+1/2)-(3/4)*(u+1/2))
    nlinarith
  have hT : Real.arcsin (u-1/2)+801/1600 < side a u := by
    dsimp [side]
    linarith
  have hcap : Real.arcsin (u-1/2)+801/1600 < Real.pi/4 := by
    linarith [h.u_lt]
  unfold label
  exact lt_min (lt_min (by linarith) hT) hcap

/-- `64((13/4)²(1 - x²)³ - 9x²(13/4 - (x+1)²)³)`: on `[0, 3/4]` it is positive
exactly where the second derivative of `arcEnvelope` is negative. -/
def arcCurvaturePolynomial (x : ℝ) : ℝ :=
  676*(1-x^2)^3-9*x^2*(9-8*x-4*x^2)^3

lemma arcCurvaturePolynomial_pos {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    0 < arcCurvaturePolynomial x :=
  bernstein_pos ![676,676,32221/64,64997/224,327833/2240,14627/128,
    3921235/28672,402967/4096,13945/256] (fun i => by fin_cases i <;> norm_num) (by norm_num)
    (fun x => by
      simp only [arcCurvaturePolynomial,bernstein,Fin.sum_univ_succ,Fin.sum_univ_zero]
      norm_num [Nat.choose]; ring) hx

/-- Upper envelope for side label plus arcsine of the near vertical edge. -/
def arcEnvelope (x : ℝ) : ℝ :=
  Real.pi/6+1/24+(1/3)*Real.sqrt (targetSq-(x+1)^2)+Real.arcsin x-3*x/4

def arcEnvelopeDeriv (x : ℝ) : ℝ :=
  1/Real.sqrt (1-x^2)-3/4-(x+1)/(3*Real.sqrt (targetSq-(x+1)^2))

def arcEnvelopeSecond (x : ℝ) : ℝ :=
  x/(Real.sqrt (1-x^2))^3-targetSq/(3*(Real.sqrt (targetSq-(x+1)^2))^3)

lemma arc_radicands {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    0 < 1-x^2 ∧ 0 < targetSq-(x+1)^2 := by
  dsimp [targetSq]
  constructor <;> nlinarith [hx.1,hx.2]

lemma arcEnvelope_hasDeriv {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    HasDerivAt arcEnvelope (arcEnvelopeDeriv x) x := by
  have hp := arc_radicands hx
  have hB : Real.sqrt (targetSq-(x+1)^2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hp.2)
  have hd : HasDerivAt (fun y : ℝ => targetSq-(y+1)^2) (-(2*(x+1))) x := by
    simpa using (((hasDerivAt_id x).add_const 1).pow 2).const_sub targetSq
  have hs := (hd.sqrt (ne_of_gt hp.2)).const_mul (1/3 : ℝ)
  have ha := Real.hasDerivAt_arcsin (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  have h := ((hs.const_add (Real.pi/6+1/24)).add ha).sub
    ((hasDerivAt_id x).const_mul (3/4 : ℝ))
  convert h using 1
  · ext y; dsimp [arcEnvelope]; ring
  · dsimp [arcEnvelopeDeriv]
    field_simp
    ring

lemma arcEnvelopeDeriv_hasDeriv {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    HasDerivAt arcEnvelopeDeriv (arcEnvelopeSecond x) x := by
  have hp := arc_radicands hx
  set A := Real.sqrt (1-x^2) with hAdef
  set B := Real.sqrt (targetSq-(x+1)^2) with hBdef
  have hA : 0 < A := Real.sqrt_pos.mpr hp.1
  have hB : 0 < B := Real.sqrt_pos.mpr hp.2
  have hB2 : B^2=targetSq-(x+1)^2 := Real.sq_sqrt hp.2.le
  have dA : HasDerivAt (fun y : ℝ => Real.sqrt (1-y^2)) (-x/A) x := by
    have h1 : HasDerivAt (fun y : ℝ => 1-y^2) (-(2*x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub 1
    have h := h1.sqrt (ne_of_gt hp.1)
    rw [← hAdef] at h
    refine h.congr_deriv ?_
    field_simp
  have dB : HasDerivAt (fun y : ℝ => Real.sqrt (targetSq-(y+1)^2)) (-(x+1)/B) x := by
    have h1 : HasDerivAt (fun y : ℝ => targetSq-(y+1)^2) (-(2*(x+1))) x := by
      simpa using (((hasDerivAt_id x).add_const 1).pow 2).const_sub targetSq
    have h := h1.sqrt (ne_of_gt hp.2)
    rw [← hBdef] at h
    refine h.congr_deriv ?_
    field_simp
  have hi : HasDerivAt (fun y : ℝ => 1/Real.sqrt (1-y^2)) (x/A^3) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).div dA (ne_of_gt hA)
    rw [← hAdef] at h
    refine h.congr_deriv ?_
    field_simp
    ring
  have hj : HasDerivAt (fun y : ℝ => (y+1)/(3*Real.sqrt (targetSq-(y+1)^2)))
      (targetSq/(3*B^3)) x := by
    have h := ((hasDerivAt_id x).add_const 1).div (dB.const_mul 3)
      (by positivity : 3*B ≠ 0)
    rw [← hBdef] at h
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    linarith
  exact (hi.sub_const (3/4 : ℝ)).sub hj

lemma arcEnvelopeSecond_neg {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    arcEnvelopeSecond x < 0 := by
  have hp := arc_radicands hx
  let A := Real.sqrt (1-x^2)
  let B := Real.sqrt (targetSq-(x+1)^2)
  have hA : 0 < A := Real.sqrt_pos.mpr hp.1
  have hB : 0 < B := Real.sqrt_pos.mpr hp.2
  have hA2 : A^2=1-x^2 := Real.sq_sqrt hp.1.le
  have hB2 : B^2=targetSq-(x+1)^2 := Real.sq_sqrt hp.2.le
  have hpoly := arcCurvaturePolynomial_pos hx
  have hid :
      64*((targetSq*A^3)^2-(3*x*B^3)^2)=arcCurvaturePolynomial x := by
    calc
      _ = 64*(targetSq^2*(A^2)^3-9*x^2*(B^2)^3) := by ring
      _ = _ := by rw [hA2,hB2]; dsimp [arcCurvaturePolynomial,targetSq]; ring
  have hleft : 0 ≤ 3*x*B^3 := by
    have hx0 := hx.1
    positivity
  have hright : 0 < targetSq*A^3 := by dsimp [targetSq]; positivity
  have hlt : 3*x*B^3 < targetSq*A^3 := by nlinarith
  have hrepr : arcEnvelopeSecond x =
      (3*x*B^3-targetSq*A^3)/(3*A^3*B^3) := by
    change x/A^3-targetSq/(3*B^3) = _
    field_simp [ne_of_gt hA,ne_of_gt hB]
  rw [hrepr]
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- The envelope is concave, so below its tangent at `1/8`, where it decreases. -/
lemma arcEnvelope_bound {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    arcEnvelope x ≤ Real.pi/6+5443/10000 := by
  have hdom (y : ℝ) (hy : y ∈ Icc (0 : ℝ) (3/4)) : 0 ≤ y ∧ y ≤ 3/4 := hy
  have ht := curvature_tangent (f := fun y => -arcEnvelope y) (d := fun y => -arcEnvelopeDeriv y)
    (dd := fun y => -arcEnvelopeSecond y) (κ := 0) (l := 0) (u := 3/4) (t := 1/8) hx
    (by norm_num) (fun y hy => (arcEnvelope_hasDeriv (hdom y hy)).neg)
    (fun y hy => (arcEnvelopeDeriv_hasDeriv (hdom y hy)).neg)
    (fun y hy => by linarith [arcEnvelopeSecond_neg (hdom y hy)])
  -- the value and the slope at `1/8`, through `√(63/64)` and `√(127/64)`
  have h63 := Real.sq_sqrt (show (0 : ℝ) ≤ 63/64 by norm_num)
  have h127 := Real.sq_sqrt (show (0 : ℝ) ≤ 127/64 by norm_num)
  have h63' := Real.sqrt_nonneg (63/64 : ℝ)
  have h127' := Real.sqrt_nonneg (127/64 : ℝ)
  have hA : 992156/1000000 < Real.sqrt (63/64) ∧ Real.sqrt (63/64) < 99216/100000 := by
    constructor <;> nlinarith
  have hB : 140867/100000 < Real.sqrt (127/64) ∧ Real.sqrt (127/64) < 140868/100000 := by
    constructor <;> nlinarith
  have hv : arcEnvelope (1/8) ≤ Real.pi/6+5430/10000 := by
    have ha := arcsin_le_cubic (x := 1/8) (by norm_num) (by norm_num)
    have he : arcEnvelope (1/8) = Real.pi/6+1/24+(1/3)*Real.sqrt (127/64)+Real.arcsin (1/8)-3/32 := by
      norm_num [arcEnvelope,targetSq]
    rw [he]
    norm_num at ha
    linarith
  have hd : -1/100 ≤ arcEnvelopeDeriv (1/8) ∧ arcEnvelopeDeriv (1/8) ≤ 0 := by
    have he : arcEnvelopeDeriv (1/8) = 1/Real.sqrt (63/64)-3/4-(9/8)/(3*Real.sqrt (127/64)) := by
      norm_num [arcEnvelopeDeriv,targetSq]
    rw [he]
    have h1 : 10079/10000 ≤ 1/Real.sqrt (63/64) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have h1' : 1/Real.sqrt (63/64) ≤ 100791/100000 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h2 : 2662/10000 ≤ (9/8)/(3*Real.sqrt (127/64)) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h2' : (9/8)/(3*Real.sqrt (127/64)) ≤ 26621/100000 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    constructor <;> linarith
  rcases le_total x (1/8) with hx8 | hx8
  · linarith [mul_nonneg (show 0 ≤ 1/8-x by linarith) (show 0 ≤ arcEnvelopeDeriv (1/8)+1/100 by
      linarith)]
  · linarith [mul_nonneg (show 0 ≤ x-1/8 by linarith) (neg_nonneg.mpr hd.2)]

lemma marker_vertical_endpoint {a u : ℝ} (h : Admissible a u) :
    label a u+801/1600 < Real.arccos (a-1/2) := by
  let x := a-1/2
  have hx : 0 ≤ x ∧ x ≤ 3/4 := by
    dsimp [x]; constructor <;> linarith [h.half_le,h.a_lt_five_fourths]
  have hp := (arc_radicands hx).2
  have hs := Real.sq_sqrt hp.le
  have hu : u+1/2 ≤ Real.sqrt (targetSq-(x+1)^2) := by
    have hh := h.phi_le
    have hn := Real.sqrt_nonneg (targetSq-(x+1)^2)
    dsimp [phi,x] at hh hs hn ⊢
    nlinarith [h.u_nonneg]
  have henv : side a u+Real.arcsin x ≤ arcEnvelope x := by
    dsimp [side,arcEnvelope,x] at *
    linarith
  have hb := arcEnvelope_bound hx
  have hl := h.label_le_side
  have hpi := Real.pi_gt_d4
  change label a u+801/1600 < Real.arccos x
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith

lemma marker_horizontal_endpoint {a u : ℝ} (h : Admissible a u) (hu : u ≤ 1/2) :
    label a u+801/1600 < Real.arcsin (u+1/2) := by
  have hs : Real.sin (63/100 : ℝ) < 3/5 := by
    have hb := sin_upper_five (x := 63/100) (by norm_num)
    norm_num at hb ⊢
    linarith
  have ha : (63/100 : ℝ) < Real.arcsin (3/5 : ℝ) :=
    (Real.lt_arcsin_iff_sin_lt'
      (show (63/100 : ℝ) ∈ Ico (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [Real.two_le_pi])).mpr hs
  -- `(5/4) y - arcsin y` is largest at `y = 3/5`
  have ht : Real.arcsin (3/5 : ℝ)+(5/4)*(u+1/2-3/5) ≤ Real.arcsin (u+1/2) := by
    rcases le_total (u+1/2) (3/5) with hy | hy
    · have hm := asin_line_mono.1 (show u+1/2 ∈ Icc (-3/5) (3/5) by
        constructor <;> linarith [h.u_nonneg]) (show (3/5 : ℝ) ∈ Icc (-3/5) (3/5) by norm_num) hy
      simp only at hm
      linarith
    · have hm := asin_line_mono.2 (show (3/5 : ℝ) ∈ Icc (3/5) 1 by norm_num)
        (show u+1/2 ∈ Icc (3/5) 1 by constructor <;> linarith) hy
      simp only at hm
      linarith
  have hl := h.label_le_axial
  dsimp [axial] at hl
  linarith

/-- The marker arc: chart angles within `801/1600` of the label stay in the
closed square. -/
theorem marker_arc {a u t : ℝ} (h : Admissible a u)
    (ht : |t-label a u| ≤ 801/1600) :
    |Real.cos t-a| ≤ 1/2 ∧ |Real.sin t-u| ≤ 1/2 := by
  have hl := marker_lower_endpoint h
  have hv := marker_vertical_endpoint h
  have hP := h.label_nonneg
  rcases abs_le.mp ht with ⟨ht0,ht1⟩
  have hcos0 : -Real.arccos (a-1/2) < t := by linarith
  have hcos1 : t < Real.arccos (a-1/2) := by linarith
  have ha0 : 0 ≤ a-1/2 := by linarith [h.half_le]
  have ha1 : a-1/2 ≤ 1 := by linarith [h.a_lt_five_fourths]
  have hcos : a-1/2 < Real.cos t := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t)
      (Real.arccos_le_pi (a-1/2)) (abs_lt.mpr ⟨hcos0,hcos1⟩)
    rw [Real.cos_arccos (by linarith) ha1,Real.cos_abs] at hh
    exact hh
  have htdom : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by
    have hA : Real.arccos (a-1/2) ≤ Real.pi/2 := Real.arccos_le_pi_div_two.mpr ha0
    constructor <;> linarith
  have hsin0 : u-1/2 < Real.sin t :=
    (Real.arcsin_lt_iff_lt_sin' ⟨htdom.1,htdom.2.le⟩).mp (by linarith)
  have hsin1 : Real.sin t ≤ u+1/2 := by
    by_cases hu : u ≤ 1/2
    · have hh := marker_horizontal_endpoint h hu
      have hs : Real.sin t < u+1/2 :=
        (Real.lt_arcsin_iff_sin_lt' ⟨htdom.1.le,htdom.2⟩).mp (by linarith)
      exact hs.le
    · linarith [Real.sin_le_one t]
  exact ⟨abs_le.mpr ⟨by linarith,by linarith [Real.cos_le_one t,h.half_le]⟩,
    abs_le.mpr ⟨by linarith,by linarith⟩⟩

end SquaresInCircles.Seven

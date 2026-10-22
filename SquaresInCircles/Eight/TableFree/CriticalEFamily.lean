module

public import SquaresInCircles.Eight.TableFree.ExceptionalContactSupport
public import SquaresInCircles.Eight.ExactFamily.GeometricStationary

/-!
# The exact supporting family on the critical E strip

Uncompiled source. The weights below are functions of the actual four
successive circle roots. Position stationarity aligns the B force with
its own circle point. After the pure B charge is included, the endpoint
is exactly the radial defect of the required D point. This identity
retains the sharp zero; no rational positive margin replaces it.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalEFamily
open ExactFamily.FiveCornerGeometry PositiveAngularEnvelope OrdinaryAngleConcavity
open ExceptionalContactSupport ExceptionalContactStress

def eta (q u : ℝ) : ℝ := lowerHeight q u/lowerLeft q u
def lam (q t u : ℝ) : ℝ := Real.cos t+eta q u*Real.sin t
def k (q t u : ℝ) : ℝ := lam q t u*topLeft q u/topHeight q u
def ell (q t u : ℝ) : ℝ := k q t u*(2-u)/topRight q u
def c (q t u : ℝ) : ℝ :=
  firstComponent q (Real.cos t) (Real.sin t) u/
    secondComponent q (Real.cos t) (Real.sin t) u
def requiredNorm (q t u : ℝ) : ℝ :=
  Real.sqrt (firstComponent q (Real.cos t) (Real.sin t) u^2+
    secondComponent q (Real.cos t) (Real.sin t) u^2)

theorem circle_identities {q u : ℝ} (h : SmoothDomain q u) :
    lowerRight q u^2+u^2=q ∧
    topRight q u^2+(2-u)^2=q ∧
    topHeight q u^2+topLeft q u^2=q ∧
    lowerLeft q u^2+lowerHeight q u^2=q :=
  ⟨upper_circle h.first_radicand,upper_circle h.second_radicand,
    upper_circle h.third_radicand,upper_circle h.fourth_radicand⟩

theorem positive_weights {q t u : ℝ} (h : SmoothDomain q u)
    (hc : 0<Real.cos t) (hs : 0≤Real.sin t) :
    0<eta q u ∧ 0<lam q t u ∧ 0<k q t u ∧ 0<ell q t u ∧ 0<c q t u := by
  have hv := h.toDomain.lowerHeight_pos h.radius_lt_four
  have hV := h.toDomain.topLeft_pos h.radius_lt_four
  have ha : 0<2-u := by linarith [h.toDomain.height_lt_two h.radius_lt_four]
  obtain ⟨h1,h2⟩ := components_pos h.radius_lt_four h.toDomain hc
    (Real.cos_le_one t) hs (Real.sin_le_one t)
  have he : 0<eta q u := div_pos hv h.w_pos
  have hl : 0<lam q t u := by dsimp [lam]; nlinarith [mul_nonneg he.le hs]
  have hk : 0<k q t u := div_pos (mul_pos hl hV) h.Y_pos
  exact ⟨he,hl,hk,div_pos (mul_pos hk ha) h.U_pos,div_pos h1 h2⟩

theorem stationary_ratio {q t u : ℝ} (h : SmoothDomain q u)
    (hc : 0<Real.cos t) (hs : 0≤Real.sin t)
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0) :
    ell q t u=c q t u*(Real.sin t+Real.cos t*u/lowerRight q u) := by
  have h2 := (components_pos h.radius_lt_four h.toDomain hc
    (Real.cos_le_one t) hs (Real.sin_le_one t)).2
  dsimp [positionHalf,slopeRatio] at hposition
  dsimp [ell,k,lam,eta,c]
  field_simp [h.r_pos.ne',h.U_pos.ne',h.Y_pos.ne',h.w_pos.ne',h2.ne'] at hposition ⊢
  nlinarith [hposition]

/-- An aligned force attains the support of the same circle. -/
theorem aligned_support {R x y a b : ℝ} (hR : 0≤R) (hx : 0<x)
    (hy : 0≤y) (ha : 0≤a) (hcirc : x^2+y^2=R^2)
    (halign : b*x=a*y) :
    R*Real.sqrt (a^2+b^2)=a*x+b*y := by
  have hb : 0≤b := by nlinarith [mul_nonneg ha hy]
  have hn := Real.sqrt_nonneg (a^2+b^2)
  have hn2 := Real.sq_sqrt (show 0≤a^2+b^2 by positivity)
  have hid : (a*x+b*y)^2+(a*y-b*x)^2=(a^2+b^2)*(x^2+y^2) := by ring
  have hprod : (R*Real.sqrt (a^2+b^2))^2=(a^2+b^2)*(x^2+y^2) := by
    rw [mul_pow,hn2,hcirc]
    ring
  have hd := add_nonneg (mul_nonneg ha hx.le) (mul_nonneg hb hy)
  nlinarith [mul_nonneg hR hn]

theorem supports {q R t u : ℝ} (h : SmoothDomain q u)
    (hR : 0≤R) (hR2 : R^2=q) (hc : 0<Real.cos t) (hs : 0≤Real.sin t)
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0) :
    R*pairNorm (lam q t u) (k q t u) 0=
      lam q t u*topHeight q u+k q t u*topLeft q u ∧
    R*pairNorm (k q t u) (ell q t u) 0=
      k q t u*topRight q u+ell q t u*(2-u) ∧
    R*pairNorm (ell q t u) (c q t u) (-t)=
      c q t u*Real.cos t*lowerRight q u+
        (ell q t u-c q t u*Real.sin t)*u ∧
    R*Real.sqrt (1+eta q u^2)=lowerLeft q u+eta q u*lowerHeight q u := by
  obtain ⟨hr,hU,hY,hw⟩ := circle_identities h
  obtain ⟨he,hl,hk,hell,hc'⟩ := positive_weights h hc hs
  have hV := h.toDomain.topLeft_pos h.radius_lt_four
  have hv := h.toDomain.lowerHeight_pos h.radius_lt_four
  have ha : 0<2-u := by linarith [h.toDomain.height_lt_two h.radius_lt_four]
  have hratio := stationary_ratio h hc hs hposition
  have hunit := trig_unit t
  refine ⟨?_,?_,?_,?_⟩
  · rw [pairNorm_zero]
    apply aligned_support hR h.Y_pos hV.le hl.le (hY.trans hR2.symm)
    dsimp [k]
    field_simp [h.Y_pos.ne']
  · rw [pairNorm_zero]
    apply aligned_support hR h.U_pos ha.le hk.le (hU.trans hR2.symm)
    dsimp [ell]
    field_simp [h.U_pos.ne']
  · have hnorm : pairNorm (ell q t u) (c q t u) (-t)=
        Real.sqrt ((c q t u*Real.cos t)^2+(ell q t u-c q t u*Real.sin t)^2) := by
      apply congrArg Real.sqrt
      simp only [pairNorm,Real.sin_neg]
      nlinarith [congrArg (fun x : ℝ => c q t u^2*x) hunit]
    rw [hnorm]
    apply aligned_support hR h.r_pos h.height_nonneg (mul_nonneg hc'.le hc.le)
      (hr.trans hR2.symm)
    rw [hratio]
    field_simp [h.r_pos.ne']
    ring
  · simpa only [one_pow,one_mul] using
      aligned_support hR h.w_pos hv.le (show (0:ℝ)≤1 by norm_num)
        (hw.trans hR2.symm) (show eta q u*lowerLeft q u=1*lowerHeight q u by
          dsimp [eta]; field_simp [h.w_pos.ne'])

theorem D_norm {q t u : ℝ} (h : SmoothDomain q u)
    (hc : 0<Real.cos t) (hs : 0≤Real.sin t) :
    pairNorm 1 (c q t u) 0=
      requiredNorm q t u/secondComponent q (Real.cos t) (Real.sin t) u := by
  have h2 := (components_pos h.radius_lt_four h.toDomain hc
    (Real.cos_le_one t) hs (Real.sin_le_one t)).2
  rw [pairNorm_zero]
  dsimp [c,requiredNorm]
  rw [← Real.sqrt_sq_eq_abs (secondComponent q (Real.cos t) (Real.sin t) u),abs_of_pos h2]
  rw [← Real.sqrt_div (by positivity)]
  congr 1
  field_simp [h2.ne']
  ring

/-- The unrounded endpoint identity, including its exact denominator. -/
theorem endpoint_identity {q R t u : ℝ} (h : SmoothDomain q u)
    (hR : 0≤R) (hR2 : R^2=q) (hc : 0<Real.cos t) (hs : 0≤Real.sin t)
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0) :
    atE R (k q t u) (ell q t u) (c q t u) (eta q u) t+
        V R (ell q t u) (c q t u) t=
      requiredNorm q t u*(requiredNorm q t u-R)/
        secondComponent q (Real.cos t) (Real.sin t) u := by
  obtain ⟨hH,hA,hB,hE⟩ := supports h hR hR2 hc hs hposition
  have hD := D_norm h hc hs
  have h2 := (components_pos h.radius_lt_four h.toDomain hc
    (Real.cos_le_one t) hs (Real.sin_le_one t)).2
  have hN2 : requiredNorm q t u^2=
      firstComponent q (Real.cos t) (Real.sin t) u^2+
        secondComponent q (Real.cos t) (Real.sin t) u^2 := Real.sq_sqrt (by positivity)
  have hV : topLeft q u+topRight q u=3 := by dsimp [topLeft]; ring
  have hv : topHeight q u+lowerHeight q u=2 := by dsimp [lowerHeight]; ring
  have htilt : tilt (eta q u) t=lam q t u := rfl
  dsimp [atE,contactScalar,V]
  rw [htilt]
  simp only [mul_add,mul_sub]
  rw [hH,hA,hB,hD,hE]
  dsimp [lam,c]
  field_simp [h2.ne']
  rw [hN2]
  dsimp [firstComponent,secondComponent]
  nlinarith [hV,hv]

theorem endpoint_nonnegative {q R t u : ℝ} (h : SmoothDomain q u)
    (hR : 0≤R) (hR2 : R^2=q) (hc : 0<Real.cos t) (hs : 0≤Real.sin t)
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0)
    (hdefect : 0≤defect q (Real.cos t) (Real.sin t) u) :
    0≤atE R (k q t u) (ell q t u) (c q t u) (eta q u) t+
      V R (ell q t u) (c q t u) t := by
  have hN : 0≤requiredNorm q t u := Real.sqrt_nonneg _
  have hN2 : requiredNorm q t u^2=
      firstComponent q (Real.cos t) (Real.sin t) u^2+
        secondComponent q (Real.cos t) (Real.sin t) u^2 := Real.sq_sqrt (by positivity)
  have hNR : R≤requiredNorm q t u := by dsimp [defect] at hdefect; nlinarith
  have h2 := (components_pos h.radius_lt_four h.toDomain hc
    (Real.cos_le_one t) hs (Real.sin_le_one t)).2
  rw [endpoint_identity h hR hR2 hc hs hposition]
  exact div_nonneg (mul_nonneg hN (sub_nonneg.mpr hNR)) h2.le

/-- A stationary radius supplies nonnegativity on every actual
minimizing-position fibre, not only at its stationary tilt. -/
theorem minimizing_endpoint {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {t : ℝ} (ht : t∈tiltInterval) :
    0≤atE (Real.sqrt d.q) (k d.q t (minimizingPosition d.q t))
      (ell d.q t (minimizingPosition d.q t)) (c d.q t (minimizingPosition d.q t))
      (eta d.q (minimizingPosition d.q t)) t+
      V (Real.sqrt d.q) (ell d.q t (minimizingPosition d.q t))
        (c d.q t (minimizingPosition d.q t)) t := by
  have h := minimizingPosition_smoothDomain hd.q_lower hd.q_upper
  obtain ⟨hc,hs,_⟩ := tiltInterval_bounds ht
  have hroot := minimizingPosition_root hd.q_lower hd.q_upper ht
  have hzero : positionHalf d.q (Real.cos t) (Real.sin t) (minimizingPosition d.q t)=0 := by
    dsimp [jointPosition] at hroot
    linarith
  have hn := stationary_envelope_nonneg hd ⟨ht.1.le,ht.2.le⟩
  rw [positionEnvelope_eq] at hn
  apply endpoint_nonnegative h (Real.sqrt_nonneg _) (Real.sq_sqrt (by linarith [hd.q_lower])) hc hs.le hzero
  exact hn

end SquaresInCircles.Eight.TableFree.CriticalEFamily

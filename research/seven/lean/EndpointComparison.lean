import research.seven.lean.EndpointGeometry

/-! J: the comparison rectangle is analytic; no states or angles are sampled. -/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Human

lemma endU_curve_hasDeriv {fa fu fr : ℝ → ℝ} {x da du dr : ℝ}
    (ha : HasDerivAt fa da x) (hu : HasDerivAt fu du x) (hr : HasDerivAt fr dr x) :
    HasDerivAt (fun y => endU (fa y) (fu y) (fr y))
      (-dr-da*Real.sin (endTheta (fa x) (fu x) (fr x))+
        du*Real.cos (endTheta (fa x) (fu x) (fr x))-
        ((9*da+26*du+5*dr)/12)*endK (fa x) (fu x) (fr x)) x := by
  have hθ := ((((ha.const_mul 9).add (hu.const_mul 26)).add
    (hr.const_mul 5)).sub_const 14).div_const 12
  have hd := ((hr.const_sub (1/2)).sub
    ((ha.sub_const (1/2)).mul hθ.sin)).add
    ((hu.add_const (1/2)).mul hθ.cos)
  convert hd using 1 <;>
    first | rfl | (funext y; dsimp [endU,endH,endTheta]; ring) |
      (dsimp [endK,endTheta]; ring)

lemma endV_curve_hasDeriv {fa fu fr : ℝ → ℝ} {x da du dr : ℝ}
    (ha : HasDerivAt fa da x) (hu : HasDerivAt fu du x) (hr : HasDerivAt fr dr x) :
    HasDerivAt (fun y => endV (fa y) (fu y) (fr y))
      (da*Real.cos (endTheta (fa x) (fu x) (fr x))+
        du*Real.sin (endTheta (fa x) (fu x) (fr x))+
        ((9*da+26*du+5*dr)/12)*endH (fa x) (fu x) (fr x)) x := by
  have hθ := ((((ha.const_mul 9).add (hu.const_mul 26)).add
    (hr.const_mul 5)).sub_const 14).div_const 12
  have hd := (((ha.sub_const (1/2)).mul hθ.cos).add
    ((hu.add_const (1/2)).mul hθ.sin)).sub_const (12/13)
  convert hd using 1 <;>
    first | rfl | (funext y; dsimp [endV,endK,endTheta]; ring) |
      (dsimp [endH,endTheta]; ring)

lemma endU_u_sign {a u r p : ℝ} (he : EndpointData a u r)
    (hp : 0 < p ∧ p < 1/2) :
    p*Real.sin (endTheta a u r)+Real.cos (endTheta a u r)-
      ((26-9*p)/12)*endK a u r < 0 := by
  have hs0 : 0 ≤ Real.sin (endTheta a u r) := by linarith [he.sin_lower]
  have hcoef : (43 : ℝ)/24 ≤ (26-9*p)/12 := by linarith [hp.2]
  have hcoef0 : 0 ≤ (26-9*p)/12 := by linarith
  have hm1 := mul_le_mul_of_nonneg_right hp.2.le hs0
  have hm2 := mul_le_mul_of_nonneg_left
    (show (9 : ℝ)/10 ≤ endK a u r by linarith [he.k_lower]) hcoef0
  nlinarith [he.sin_upper,he.cos_upper]

lemma endV_u_sign {a u r p : ℝ} (he : EndpointData a u r)
    (hp : 0 < p ∧ p < 1/2) :
    0 < -p*Real.cos (endTheta a u r)+Real.sin (endTheta a u r)+
      ((26-9*p)/12)*endH a u r := by
  have hm1 := mul_le_mul_of_nonneg_left he.cos_upper hp.1.le
  have hc : 0 ≤ (26-9*p)/12 := by linarith [hp.2]
  have hm2 := mul_nonneg hc (show 0 ≤ endH a u r by linarith [he.h_lower])
  nlinarith [he.sin_lower,hp.2]

lemma endU_circle_antitone {r : ℝ} (hr : (17 : ℝ)/22 ≤ r ∧ r ≤ 31/40) :
    AntitoneOn (fun u => endU (correlatedA u) u r) (Icc (29/100) (7/24)) := by
  apply Seven.antiOn_of_hasDeriv_nonpos (d := fun u =>
    correlatedP u*Real.sin (endTheta (correlatedA u) u r)+
    Real.cos (endTheta (correlatedA u) u r)-
    ((26-9*correlatedP u)/12)*endK (correlatedA u) u r)
  · dsimp [endU,endH,endTheta,correlatedA,correlatedX]; fun_prop
  · intro u hu
    convert endU_curve_hasDeriv (correlatedA_hasDeriv ⟨hu.1.le,hu.2.le⟩)
      (hasDerivAt_id u) (hasDerivAt_const u r) using 1 <;>
      first | rfl | (dsimp; ring)
  · intro u hu
    have hb := correlated_bounds ⟨hu.1.le,hu.2.le⟩
    exact (endU_u_sign (endpoint_correlated_data ⟨hu.1.le,hu.2.le⟩ hr)
      ⟨hb.2.2.2.1,hb.2.2.2.2⟩).le

lemma endV_circle_monotone {r : ℝ} (hr : (17 : ℝ)/22 ≤ r ∧ r ≤ 31/40) :
    MonotoneOn (fun u => endV (correlatedA u) u r) (Icc (29/100) (7/24)) := by
  apply Seven.monoOn_of_hasDeriv_nonneg (d := fun u =>
    -correlatedP u*Real.cos (endTheta (correlatedA u) u r)+
    Real.sin (endTheta (correlatedA u) u r)+
    ((26-9*correlatedP u)/12)*endH (correlatedA u) u r)
  · dsimp [endV,endK,endTheta,correlatedA,correlatedX]; fun_prop
  · intro u hu
    convert endV_curve_hasDeriv (correlatedA_hasDeriv ⟨hu.1.le,hu.2.le⟩)
      (hasDerivAt_id u) (hasDerivAt_const u r) using 1 <;>
      first | rfl | (dsimp; ring)
  · intro u hu
    have hb := correlated_bounds ⟨hu.1.le,hu.2.le⟩
    exact (endV_u_sign (endpoint_correlated_data ⟨hu.1.le,hu.2.le⟩ hr)
      ⟨hb.2.2.2.1,hb.2.2.2.2⟩).le

lemma endU_r_antitone {a u : ℝ}
    (ha : (67 : ℝ)/60 ≤ a ∧ a ≤ 9/8)
    (hu : (29 : ℝ)/100 ≤ u ∧ u ≤ 7/24) :
    AntitoneOn (endU a u) (Icc (17/22) (31/40)) := by
  apply Seven.antiOn_of_hasDeriv_nonpos (d := fun r => -1-(5/12)*endK a u r)
  · dsimp [endU,endH,endTheta]; fun_prop
  · intro r _
    convert endU_curve_hasDeriv (hasDerivAt_const r a)
      (hasDerivAt_const r u) (hasDerivAt_id r) using 1 <;>
      first | rfl | (dsimp; ring)
  · intro r hr
    have he := endpoint_box_data ha hu ⟨hr.1.le,hr.2.le⟩
    linarith [he.k_lower]

lemma endV_r_monotone {a u : ℝ}
    (ha : (67 : ℝ)/60 ≤ a ∧ a ≤ 9/8)
    (hu : (29 : ℝ)/100 ≤ u ∧ u ≤ 7/24) :
    MonotoneOn (endV a u) (Icc (17/22) (31/40)) := by
  apply Seven.monoOn_of_hasDeriv_nonneg (d := fun r => (5/12)*endH a u r)
  · dsimp [endV,endK,endTheta]; fun_prop
  · intro r _
    convert endV_curve_hasDeriv (hasDerivAt_const r a)
      (hasDerivAt_const r u) (hasDerivAt_id r) using 1 <;>
      first | rfl | (dsimp; ring)
  · intro r hr
    have he := endpoint_box_data ha hu ⟨hr.1.le,hr.2.le⟩
    linarith [he.h_lower]

lemma endU_a_antitone {u r : ℝ}
    (hu : (29 : ℝ)/100 ≤ u ∧ u ≤ 7/24)
    (hr : (17 : ℝ)/22 ≤ r ∧ r ≤ 31/40) :
    AntitoneOn (fun a => endU a u r) (Icc (67/60) (9/8)) := by
  apply Seven.antiOn_of_hasDeriv_nonpos (d := fun a =>
    -Real.sin (endTheta a u r)-(3/4)*endK a u r)
  · dsimp [endU,endH,endTheta]; fun_prop
  · intro a _
    convert endU_curve_hasDeriv (hasDerivAt_id a)
      (hasDerivAt_const a u) (hasDerivAt_const a r) using 1 <;>
      first | rfl | (dsimp; ring)
  · intro a ha
    have he := endpoint_box_data ⟨ha.1.le,ha.2.le⟩ hu hr
    linarith [he.sin_lower,he.k_lower]

lemma endV_a_monotone {u r : ℝ}
    (hu : (29 : ℝ)/100 ≤ u ∧ u ≤ 7/24)
    (hr : (17 : ℝ)/22 ≤ r ∧ r ≤ 31/40) :
    MonotoneOn (fun a => endV a u r) (Icc (67/60) (9/8)) := by
  apply Seven.monoOn_of_hasDeriv_nonneg (d := fun a =>
    Real.cos (endTheta a u r)+(3/4)*endH a u r)
  · dsimp [endV,endK,endTheta]; fun_prop
  · intro a _
    convert endV_curve_hasDeriv (hasDerivAt_id a)
      (hasDerivAt_const a u) (hasDerivAt_const a r) using 1 <;>
      first | rfl | (dsimp; ring)
  · intro a ha
    have he := endpoint_box_data ⟨ha.1.le,ha.2.le⟩ hu hr
    linarith [he.cos_lower,he.h_lower]

/-- sqrt(1511)<39-5/39: tangent to the radical at the integer square 39^2. -/
lemma rational_corner_dominates : correlatedA (7/24) ≤ (131 : ℝ)/117 := by
  have hb := correlated_bounds (u := (7/24 : ℝ)) (by constructor <;> norm_num)
  dsimp [correlatedA]
  nlinarith [hb.1,hb.2.2.1]

lemma endpoint_corner_compare {u r : ℝ}
    (hu : (29 : ℝ)/100 ≤ u ∧ u ≤ 7/24)
    (hr : (17 : ℝ)/22 ≤ r ∧ r ≤ 31/40) :
    endU (131/117) (7/24) (31/40) ≤ endU (correlatedA u) u r ∧
    0 < endV (correlatedA u) u r ∧
    endV (correlatedA u) u r ≤ endV (131/117) (7/24) (31/40) := by
  have huTop : (29/100 : ℝ) ≤ 7/24 ∧ (7/24 : ℝ) ≤ 7/24 := by
    constructor <;> norm_num
  have hrTop : (17/22 : ℝ) ≤ 31/40 ∧ (31/40 : ℝ) ≤ 31/40 := by
    constructor <;> norm_num
  have haTop := correlatedA_mem huTop
  have haBar : (67/60 : ℝ) ≤ 131/117 ∧ (131/117 : ℝ) ≤ 9/8 := by
    constructor <;> norm_num
  have hU1 := (endU_circle_antitone hr) hu huTop hu.2
  have hU2 := (endU_r_antitone haTop huTop) hr hrTop hr.2
  have hU3 := (endU_a_antitone huTop hrTop) haTop haBar rational_corner_dominates
  have hV1 := (endV_circle_monotone hr) hu huTop hu.2
  have hV2 := (endV_r_monotone haTop huTop) hr hrTop hr.2
  have hV3 := (endV_a_monotone huTop hrTop) haTop haBar rational_corner_dominates
  have he := endpoint_correlated_data hu hr
  have hpos : 0 < endV (correlatedA u) u r := by dsimp [endV]; linarith [he.k_lower]
  exact ⟨hU3.trans (hU2.trans hU1),hpos,hV1.trans (hV2.trans hV3)⟩

end SquaresInCircles.Seven.Human

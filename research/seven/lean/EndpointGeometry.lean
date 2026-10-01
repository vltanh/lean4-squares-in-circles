import research.seven.lean.CoarseBoundary

/-! J, endpoint comparison geometry. The radial coordinate stays on its circle. -/
noncomputable section
namespace SquaresInCircles.Seven.Human

def endTheta (a u r : ℝ) : ℝ := (9*a+26*u+5*r-14)/12

def endK (a u r : ℝ) : ℝ :=
  (a-1/2)*Real.cos (endTheta a u r)+(u+1/2)*Real.sin (endTheta a u r)

def endH (a u r : ℝ) : ℝ :=
  -(a-1/2)*Real.sin (endTheta a u r)+(u+1/2)*Real.cos (endTheta a u r)

def endU (a u r : ℝ) : ℝ := 1/2-r+endH a u r
def endV (a u r : ℝ) : ℝ := endK a u r-12/13

def correlatedX (u : ℝ) : ℝ := Real.sqrt (13/4-(u+1/2)^2)
def correlatedA (u : ℝ) : ℝ := correlatedX u-1/2
def correlatedP (u : ℝ) : ℝ := (u+1/2)/correlatedX u

structure EndpointData (a u r : ℝ) : Prop where
  angle_lower : (3 : ℝ)/5 < endTheta a u r
  angle_upper : endTheta a u r < (2 : ℝ)/3
  sin_lower : (141 : ℝ)/250 ≤ Real.sin (endTheta a u r)
  sin_upper : Real.sin (endTheta a u r) ≤ (2 : ℝ)/3
  cos_lower : (7 : ℝ)/9 ≤ Real.cos (endTheta a u r)
  cos_upper : Real.cos (endTheta a u r) ≤ 1
  k_lower : (12 : ℝ)/13 < endK a u r
  h_lower : (89 : ℝ)/450 ≤ endH a u r

lemma endpoint_box_data {a u r : ℝ}
    (ha : (67 : ℝ)/60 ≤ a ∧ a ≤ 9/8)
    (hu : (29 : ℝ)/100 ≤ u ∧ u ≤ 7/24)
    (hr : (17 : ℝ)/22 ≤ r ∧ r ≤ 31/40) : EndpointData a u r := by
  have ht : (3 : ℝ)/5 < endTheta a u r ∧ endTheta a u r < 2/3 := by
    dsimp [endTheta]
    constructor <;> linarith [ha.1,ha.2,hu.1,hu.2,hr.1,hr.2]
  have ht0 : 0 ≤ endTheta a u r := by linarith [ht.1]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi ht0
    (by linarith [ht.2,pi_lower])
  have hslo : (141 : ℝ)/250 ≤ Real.sin (endTheta a u r) := by
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
      (x := (3/5 : ℝ)) (y := endTheta a u r)
      (by linarith [pi_lower]) (by linarith [ht.2,pi_lower]) ht.1.le
    have hs := Real.sin_ge_sub_cube (show (0 : ℝ) ≤ 3/5 by norm_num)
    linarith
  have hshi : Real.sin (endTheta a u r) ≤ (2 : ℝ)/3 :=
    (Real.sin_le ht0).trans ht.2.le
  have hclo : (7 : ℝ)/9 ≤ Real.cos (endTheta a u r) := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := endTheta a u r)
    have ht2 : (endTheta a u r)^2 ≤ (2/3 : ℝ)^2 := by nlinarith [ht.1,ht.2]
    nlinarith
  have hchi := Real.cos_le_one (endTheta a u r)
  have hc0 : 0 ≤ Real.cos (endTheta a u r) := by linarith
  have hkA := mul_le_mul_of_nonneg_right
    (show (37 : ℝ)/60 ≤ a-1/2 by linarith [ha.1]) hc0
  have hkU := mul_le_mul_of_nonneg_right
    (show (79 : ℝ)/100 ≤ u+1/2 by linarith [hu.1]) hs0
  have hk : (12 : ℝ)/13 < endK a u r := by
    dsimp [endK]
    nlinarith
  have hhA := mul_le_mul_of_nonneg_right
    (show a-1/2 ≤ (5 : ℝ)/8 by linarith [ha.2]) hs0
  have hhU := mul_le_mul_of_nonneg_right
    (show (79 : ℝ)/100 ≤ u+1/2 by linarith [hu.1]) hc0
  have hh : (89 : ℝ)/450 ≤ endH a u r := by
    dsimp [endH]
    nlinarith
  exact ⟨ht.1,ht.2,hslo,hshi,hclo,hchi,hk,hh⟩

lemma correlated_bounds {u : ℝ} (hu : (29 : ℝ)/100 ≤ u ∧ u ≤ 7/24) :
    (97 : ℝ)/60 < correlatedX u ∧ correlatedX u < 13/8 ∧
    (correlatedX u)^2+(u+1/2)^2=(13 : ℝ)/4 ∧
    0 < correlatedP u ∧ correlatedP u < 1/2 := by
  have hr : 0 ≤ (13 : ℝ)/4-(u+1/2)^2 := by nlinarith [hu.1,hu.2]
  have hs := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg ((13 : ℝ)/4-(u+1/2)^2)
  change (correlatedX u)^2=13/4-(u+1/2)^2 at hs
  change 0 ≤ correlatedX u at hn
  have hlo : (97 : ℝ)/60 < correlatedX u := by nlinarith [hu.1,hu.2]
  have hhi : correlatedX u < (13 : ℝ)/8 := by nlinarith [hu.1,hu.2]
  have hx0 : 0 < correlatedX u := by linarith
  have hp0 : 0 < correlatedP u := by
    dsimp [correlatedP]
    exact div_pos (by linarith [hu.1]) hx0
  have hp1 : correlatedP u < (1 : ℝ)/2 := by
    dsimp [correlatedP]
    apply (div_lt_iff₀ hx0).mpr
    linarith [hu.2]
  exact ⟨hlo,hhi,by linarith,hp0,hp1⟩

lemma correlatedA_mem {u : ℝ} (hu : (29 : ℝ)/100 ≤ u ∧ u ≤ 7/24) :
    (67 : ℝ)/60 ≤ correlatedA u ∧ correlatedA u ≤ 9/8 := by
  have hb := correlated_bounds hu
  dsimp [correlatedA]
  constructor <;> linarith [hb.1,hb.2.1]

lemma correlatedA_hasDeriv {u : ℝ} (hu : (29 : ℝ)/100 ≤ u ∧ u ≤ 7/24) :
    HasDerivAt correlatedA (-correlatedP u) u := by
  have hb := correlated_bounds hu
  have hp : 0 < (13 : ℝ)/4-(u+1/2)^2 := by nlinarith [hb.1,hb.2.2.1]
  have hy : HasDerivAt (fun x : ℝ => x+1/2) 1 u := (hasDerivAt_id u).add_const (1/2)
  have hd := (((hasDerivAt_const u (13/4 : ℝ)).sub (hy.pow 2)).sqrt (ne_of_gt hp)).sub_const (1/2)
  convert hd using 1
  · rfl
  · dsimp [correlatedP,correlatedX]
    field_simp
    ring

lemma endpoint_correlated_data {u r : ℝ}
    (hu : (29 : ℝ)/100 ≤ u ∧ u ≤ 7/24)
    (hr : (17 : ℝ)/22 ≤ r ∧ r ≤ 31/40) : EndpointData (correlatedA u) u r :=
  endpoint_box_data (correlatedA_mem hu) hu hr

lemma correlated_at_transition : correlatedA Boundary.u0=Boundary.a0 := by
  have hu := transition_coarse_geometric
  have hb := correlated_bounds (u := Boundary.u0) ⟨hu.2.2.1.le,hu.2.2.2.1.le⟩
  have hc := transition_circle_exact
  have hx := transition_coordinates_positive
  have hY : Boundary.u0+1/2=Boundary.Y0 := by dsimp [Boundary.u0]; ring
  rw [hY] at hb
  have he : correlatedX Boundary.u0=Boundary.X0 := by nlinarith [hb.1,hb.2.2.1,hx.1]
  dsimp [correlatedA,Boundary.a0]
  rw [he]

end SquaresInCircles.Seven.Human

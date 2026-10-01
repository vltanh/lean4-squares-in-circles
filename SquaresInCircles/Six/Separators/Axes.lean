import SquaresInCircles.Six.Normalization.PinAxes
import SquaresInCircles.Six.Normalization.Basic
import SquaresInCircles.Common.Trigonometry

/-!
# The separating axes of consecutive exterior squares

Two exterior squares are separated along one of eight directed axes, `±e₁` and
`±e₂` of either square. The outward axis `e₁` of the first square and the
inward axis `-e₁` of the second never separate: an exterior square has radial
coordinate at least `aMin = 2 - ρ0`, every centre lies within `ρ0` of the disk
centre, and `ρ0 - aMin < 1/2`, the least threshold. If the phases of the two
squares differ by `q ∈ [0, π/2]`, a separation along the remaining primary
axes, `-e₁` of the first or `e₁` of the second, implies one along the secondary
axis of the other square: for `q ≤ 11/10` the primary projection stays below
the threshold since `cos q ≥ 9/20`, and beyond, `1 - sin q ≤ (13/50) cos q`
makes the secondary projection the larger one. The chord between the pins rules
out the axes `-e₂`, so W and D are separated along `e₂` of W or of D, and so
are D and S when `s ≤ d`.
-/

noncomputable section
namespace SquaresInCircles.Six
open Normalization

lemma frame_primary_le_rho0 (S : UnitSquare) {p : Point}
    (hp : normSq p≤rho0^2) : frameX S p≤rho0 := by
  have hf := frame_norm S p
  have hsq : (frameX S p)^2≤rho0^2 := by
    nlinarith [sq_nonneg (frameY S p)]
  nlinarith [rho0_bounds.1]

lemma pair_threshold_ge_half (S T : UnitSquare) : 1/2≤SAT.threshold S T := by
  dsimp [SAT.threshold]
  linarith [abs_nonneg (relativeC S T),abs_nonneg (relativeS S T)]

lemma normalized_center_radius {R : ℝ} (P : NormalizedPacking R) (i : Fin 5) :
    normSq (P.square i).center≤rho0^2 := by
  have hphi : phi (alpha (P.square i) (0,0)) (beta (P.square i) (0,0))≤Q0 := by
    rw [P.square_def,orientedSquare_alpha,orientedSquare_beta]
    simpa only [phi,abs_of_nonneg (show 0≤P.radial i by linarith [(P.contained i).half_le])]
      using (P.contained i).containment
  simpa [sub] using center_radius_sq hphi

lemma normalized_primary_lower {R : ℝ} (P : NormalizedPacking R) (i : Fin 5) :
    aMin≤frameX (P.square i) (P.square i).center := by
  have hf := oriented_frame_centerX (P.phase i) (P.radial i) (P.transverse i)
  have he : frameX (P.square i) (P.square i).center=P.radial i := by
    simpa [P.square_def,sub] using hf
  rw [he]
  exact (P.contained i).aMin_le (P.avoidsCore i)

/-- Two exterior squares are not separated along the outward axis `e₁` of the
first square (`k = 0`) nor along the inward axis `-e₁` of the second (`k = 5`). -/
theorem normalized_outward_axes_excluded {R : ℝ} (P : NormalizedPacking R)
    (i j : Fin 5) (k : Fin 8)
    (hsep : SAT.threshold (P.square i) (P.square j)≤
      dot (pairNormal k (P.square i) (P.square j))
        (sub (P.square j).center (P.square i).center)) : k≠0 ∧ k≠5 := by
  have hthreshold := pair_threshold_ge_half (P.square i) (P.square j)
  have hrho := rho0_bounds.2
  constructor
  · rintro rfl
    have hj := frame_primary_le_rho0 (P.square i) (normalized_center_radius P j)
    have hi := normalized_primary_lower P i
    change _≤dot (normalX (P.square i)) (sub (P.square j).center (P.square i).center) at hsep
    have hid : dot (normalX (P.square i)) (sub (P.square j).center (P.square i).center)=
        frameX (P.square i) (P.square j).center-frameX (P.square i) (P.square i).center := by
      dsimp [dot,normalX,frameX,sub]
      ring
    dsimp [aMin] at hi
    linarith
  · rintro rfl
    have hi := frame_primary_le_rho0 (P.square j) (normalized_center_radius P i)
    have hj := normalized_primary_lower P j
    change _≤dot (scale (-1) (normalX (P.square j)))
      (sub (P.square j).center (P.square i).center) at hsep
    have hid : dot (scale (-1) (normalX (P.square j))) (sub (P.square j).center (P.square i).center)=
        frameX (P.square j) (P.square i).center-frameX (P.square j) (P.square j).center := by
      dsimp [dot,scale,normalX,frameX,sub]
      ring
    dsimp [aMin] at hj
    linarith

/-- `cos q ≥ 9/20` for `|q| ≤ 11/10`, by the Taylor bound at `11/10`. -/
lemma nine_twentieths_le_cos {q : ℝ} (hq : |q|≤11/10) : 9/20≤Real.cos q := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg q)
    (show (11:ℝ)/10≤Real.pi by linarith [Real.pi_gt_three]) hq
  have hp := cos_lower_six (x := (11:ℝ)/10) (by norm_num)
  rw [Real.cos_abs] at hc
  norm_num at hp
  linarith

/-- `1 - sin q ≤ (13/50) cos q` for `11/10 ≤ q ≤ π/2`: there
`sin q ≥ sin (11/10) > (1 - k²)/(1 + k²)` for `k = 13/50`. -/
lemma one_sub_sin_le_cos {q : ℝ} (hq : 11/10≤q ∧ q≤Real.pi/2) :
    1-Real.sin q≤(13/50)*Real.cos q := by
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hq.1,Real.pi_pos],hq.2⟩
  have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤(11:ℝ)/10 by linarith [Real.pi_pos]) hq.2 hq.1
  have hl := Real.sin_ge_sub_cube (x := (11:ℝ)/10) (by norm_num)
  norm_num at hl
  have hs1 : 0≤1-Real.sin q := sub_nonneg.mpr (Real.sin_le_one q)
  have hfactor := mul_nonneg hs1 (show 0≤2669*Real.sin q-2331 by linarith)
  by_contra! h
  have hp := mul_pos (show 0<1-Real.sin q-(13/50)*Real.cos q by linarith)
    (show 0<1-Real.sin q+(13/50)*Real.cos q by linarith)
  nlinarith [Real.sin_sq_add_cos_sq q]

/-- The dominance of the secondary axes. For a phase gap `q ∈ [0, π/2]`, if
the projection of the centre difference on the inward axis `-e₁` of the first
square, `a - A cos q + B sin q`, reaches the threshold, so does its projection
`B + a sin q - b cos q` on the secondary axis of the second square. -/
lemma secondary_of_inward_primary {a b A B q : ℝ}
    (ha : a≤rho0) (hb : |b|≤U0) (hA : aMin≤A) (hB : |B|≤U0)
    (hq : 0≤q ∧ q≤Real.pi/2)
    (hsep : 1/2+angularWidth q≤a-A*Real.cos q+B*Real.sin q) :
    1/2+angularWidth q≤B+a*Real.sin q-b*Real.cos q := by
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hq.1,Real.pi_pos],hq.2⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hq.1 (by linarith [hq.2,Real.pi_pos])
  have hbb := abs_le.mp hb
  have hBB := abs_le.mp hB
  have hU := U0_upper
  have hr := rho0_bounds.2
  dsimp [aMin] at hA
  rcases le_or_gt q (11/10) with hsmall | hlarge
  · have hcos := nine_twentieths_le_cos (abs_le.mpr ⟨by linarith [hq.1],hsmall⟩)
    have h1 := mul_le_mul_of_nonneg_right hA hc
    have h2 := mul_le_mul_of_nonneg_right hBB.2 hs
    have h3 := mul_le_mul_of_nonneg_left hcos (show 0≤5/2-rho0 by linarith)
    rw [angularWidth,abs_of_nonneg hc,abs_of_nonneg hs] at hsep
    nlinarith
  · have hratio := one_sub_sin_le_cos ⟨hlarge.le,hq.2⟩
    have h1 := mul_le_mul_of_nonneg_left (show a-B≤rho0+U0 by linarith)
      (sub_nonneg.mpr (Real.sin_le_one q))
    have h2 := mul_le_mul_of_nonneg_right hratio
      (show 0≤rho0+U0 by linarith [rho0_bounds.1,abs_nonneg b])
    have h3 := mul_le_mul_of_nonneg_right (show 2-rho0-U0≤A-b by linarith) hc
    have h4 := mul_le_mul_of_nonneg_right
      (show (13/50)*(rho0+U0)≤2-rho0-U0 by linarith) hc
    nlinarith

/-- Two exterior squares whose phases differ by `q ∈ [0, π/2]`: every
separating directed axis other than `-e₂` of either square gives a separation
along the secondary axis `e₂` of one of them. -/
theorem secondary_of_separating_axis {R : ℝ} (P : NormalizedPacking R) {i j : Fin 5}
    (hq : 0≤P.phase j-P.phase i ∧ P.phase j-P.phase i≤Real.pi/2) {k : Fin 8}
    (hk3 : k≠3) (hk7 : k≠7)
    (hsep : SAT.threshold (P.square i) (P.square j)≤
      dot (pairNormal k (P.square i) (P.square j))
        (sub (P.square j).center (P.square i).center)) :
    SAT.threshold (P.square i) (P.square j)≤
        dot (normalY (P.square i)) (sub (P.square j).center (P.square i).center) ∨
      SAT.threshold (P.square i) (P.square j)≤
        dot (normalY (P.square j)) (sub (P.square j).center (P.square i).center) := by
  have hout := normalized_outward_axes_excluded P i j k hsep
  have hi := P.contained i
  have hj := P.contained j
  have hbi := hi.u_le_U0 (P.avoidsCore i)
  have hbj := hj.u_le_U0 (P.avoidsCore j)
  fin_cases k
  · exact absurd rfl hout.1
  · right
    change _≤dot (scale (-1) (normalX (P.square i))) _ at hsep
    rw [dot_scale_neg] at hsep
    change _≤-frameX (P.square i) _ at hsep
    change _≤frameY (P.square j) _
    rw [P.square_def i,P.square_def j,oriented_pair_threshold,pair_frameX_left] at hsep
    rw [P.square_def i,P.square_def j,oriented_pair_threshold,pair_frameY_right]
    exact secondary_of_inward_primary hi.a_le_rho0 hbi (hj.aMin_le (P.avoidsCore j)) hbj hq
      (by linarith)
  · exact Or.inl hsep
  · exact absurd rfl hk3
  · left
    change _≤frameX (P.square j) _ at hsep
    change _≤frameY (P.square i) _
    rw [P.square_def i,P.square_def j,oriented_pair_threshold,pair_frameX_right] at hsep
    rw [P.square_def i,P.square_def j,oriented_pair_threshold,pair_frameY_left]
    have h := secondary_of_inward_primary (b := -P.transverse j) (B := -P.transverse i)
      hj.a_le_rho0 (by rwa [abs_neg]) (hi.aMin_le (P.avoidsCore i)) (by rwa [abs_neg]) hq
      (by linarith)
    linarith
  · exact absurd rfl hout.2
  · exact Or.inr hsep
  · exact absurd rfl hk7

/-- W and D are separated along `e₂` of W (`k = 2`) or `e₂` of D (`k = 6`). -/
theorem westDiagonal_secondary {R : ℝ} (P : NormalizedPacking R) : ∃ k : Fin 8,
    SAT.threshold (P.square 2) (P.square 3)≤
      dot (pairNormal k (P.square 2) (P.square 3))
        (sub (P.square 3).center (P.square 2).center) ∧ (k=2 ∨ k=6) := by
  obtain ⟨k,hk,hk3,hk7⟩ := P.westDiagonal_separator
  have hw : P.phase 2=Real.pi+P.deviation 2 := P.phase_from_deviation 2
  have hd : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  have hq : 0≤P.phase 3-P.phase 2 ∧ P.phase 3-P.phase 2≤Real.pi/2 := by
    refine ⟨sub_nonneg.mpr P.primary_order.2.2.1.le,?_⟩
    rw [hw,hd]
    linarith [P.deviation_windows.2.2.1.1,P.diagonal_angle_range.2,Real.pi_gt_d2]
  rcases secondary_of_separating_axis P hq hk3 hk7 hk with h | h
  · exact ⟨2,h,Or.inl rfl⟩
  · exact ⟨6,h,Or.inr rfl⟩

/-- D and S are separated along the secondary axis of D or along that of S. -/
def SouthSecondaryChoice {R : ℝ} (P : NormalizedPacking R) : Prop :=
  (SAT.threshold (P.square 3) (P.square 4)≤
    dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) ∨
  (SAT.threshold (P.square 3) (P.square 4)≤
    dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center))

/-- If `s ≤ d`, D and S are separated along a secondary axis. -/
theorem south_secondary_choice_of_angle {R : ℝ} (P : NormalizedPacking R)
    (hs : P.deviation 4≤P.diagonalAngle) : SouthSecondaryChoice P := by
  obtain ⟨k,hk,_,hk3,hk7⟩ := P.diagonalSouth_separator
  have hS : P.phase 4=3*Real.pi/2+P.deviation 4 := P.phase_from_deviation 4
  have hD : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  exact secondary_of_separating_axis P
    ⟨sub_nonneg.mpr P.primary_order.2.2.2.1.le,by rw [hS,hD]; linarith⟩ hk3 hk7 hk

end SquaresInCircles.Six

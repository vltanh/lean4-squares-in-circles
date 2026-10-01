import SquaresInCircles.Common.Contacts
import SquaresInCircles.Common.Support
import SquaresInCircles.Common.Charts
import SquaresInCircles.Common.Trigonometry
import SquaresInCircles.Common.Congruence
import SquaresInCircles.Six.Constants
import SquaresInCircles.Common.SeparatingAxes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Charts, oriented squares and the separating axes of the central square

The normalization works in disks of squared radius at most `Q0`, just above the
square of the optimal radius, with the constants `R0`, `ρ0`, `c0`, `coreRadius`,
`aMin` and `U0` of `Constants`. An exterior square is read as
`orientedSquare t a b`, the square at the phase `t` with centre `(a, b)` in its
frame; a sorted chart has `1/2 ≤ a`, `|b| ≤ a` and
`(a + 1/2)² + (|b| + 1/2)² ≤ Q0` (`ContainedChart`), and if the square avoids
the core disk also `2 - ρ0 ≤ a` and `|b| ≤ U0` (`AvoidsCore`). Its centre lies
within `ρ0` of the origin. By the separating axis theorem it is separated from C
along its own axis, its secondary axis in either direction, or a side of C
(`central_separators_complete`); `centralMargin k t a b cx cy ≥ 0` is the
separating inequality along the axis `k`, with threshold `1/2 + angularWidth t`.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- A point beyond `(A, B)`, with `A, B ≥ 0`, lies outside the disk of squared
radius `Q0` if `(A, B)` does. -/
lemma corner_sq_le {A B x y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAx : A ≤ x) (hBy : B ≤ y)
    (h : x ^ 2 + y ^ 2 ≤ Q0) : A ^ 2 + B ^ 2 ≤ Q0 := by
  nlinarith [mul_le_mul hAx hAx hA (hA.trans hAx), mul_le_mul hBy hBy hB (hB.trans hBy)]

/-! ### Charts of exterior squares -/

/-- A sorted chart `(a, u)` whose far corner lies in the disk of squared radius
`Q0`. -/
structure ContainedChart (a u : ℝ) : Prop where
  half_le : 1 / 2 ≤ a
  u_nonneg : 0 ≤ u
  u_le : u ≤ a
  containment : (a + 1 / 2) ^ 2 + (u + 1 / 2) ^ 2 ≤ Q0

/-- The closed square avoids the open disk of radius `coreRadius` about the
origin: for `a ≥ 1/2` and `u ≥ 0`, the right side is the squared distance of its
nearest point. -/
def AvoidsCore (a u : ℝ) : Prop :=
  coreRadius ^ 2 ≤ (a - 1 / 2) ^ 2 + (max (u - 1 / 2) 0) ^ 2

namespace ContainedChart
variable {a u : ℝ} (h : ContainedChart a u)
include h

lemma a_le_rho0 : a ≤ rho0 := by
  have hs : (a + 1 / 2) ^ 2 ≤ Q0 - 1 / 4 := by
    nlinarith [h.containment, h.u_nonneg, sq_nonneg u]
  have hr := Real.le_sqrt_of_sq_le hs
  dsimp [rho0]
  linarith

/-- A square that avoids the core has `u < 1/2`: its nearest point is not a
corner. -/
lemma u_lt_half (hc : AvoidsCore a u) : u < 1 / 2 := by
  by_contra! hu
  have hx : 0 ≤ a - 1 / 2 := by linarith [h.half_le]
  have hy : 0 ≤ u - 1 / 2 := by linarith
  have hd : coreRadius ^ 2 ≤ (a - 1 / 2) ^ 2 + (u - 1 / 2) ^ 2 := by
    simpa only [AvoidsCore, max_eq_left hy] using hc
  have hsum : coreRadius ≤ a + u - 1 := by
    by_contra! hs
    have hp := mul_pos (sub_pos.mpr hs)
      (show 0 < coreRadius + (a + u - 1) by linarith [coreRadius_pos])
    nlinarith [mul_nonneg hx hy]
  have ht := h.containment
  norm_num [Q0] at ht
  nlinarith [coreRadius_bounds.1, sq_nonneg (coreRadius - 77 / 200)]

/-- A square that avoids the core has `a ≥ aMin`: its nearest point is on its
near edge. -/
lemma aMin_le (hc : AvoidsCore a u) : aMin ≤ a := by
  have hu := h.u_lt_half hc
  have hd : coreRadius ^ 2 ≤ (a - 1 / 2) ^ 2 := by
    simpa only [AvoidsCore, max_eq_right (by linarith : u - 1 / 2 ≤ 0),
      zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using hc
  have hr : coreRadius ≤ a - 1 / 2 := by
    by_contra! hs
    have hp := mul_pos (sub_pos.mpr hs)
      (show 0 < coreRadius + (a - 1 / 2) by linarith [coreRadius_pos, h.half_le])
    nlinarith
  rw [aMin_eq_coreRadius_add_half]
  linarith

/-- A square that avoids the core has `u ≤ U0`, by its far corner at
`a ≥ aMin`. -/
lemma u_le_U0 (hc : AvoidsCore a u) : u ≤ U0 := by
  have ha := h.aMin_le hc
  have hp := mul_nonneg (sub_nonneg.mpr ha)
    (show 0 ≤ a + aMin + 1 by linarith [h.half_le, aMin_bounds.1])
  dsimp [aMin] at hp
  have hs : (u + 1 / 2) ^ 2 ≤ Q0 - (5 / 2 - rho0) ^ 2 := by
    nlinarith [h.containment]
  have hr := Real.le_sqrt_of_sq_le hs
  dsimp [U0]
  linarith

/-- Rational bounds for a square that avoids the core: `177/200 < a < 223/200`
and `u < 117/250`. -/
lemma bounds (hc : AvoidsCore a u) :
    177 / 200 < a ∧ a < 223 / 200 ∧ u < 117 / 250 := by
  have ha := h.aMin_le hc
  have hu := h.u_le_U0 hc
  exact ⟨by linarith [aMin_bounds.1],by linarith [h.a_le_rho0,rho0_bounds.2],
    by linarith [U0_upper]⟩

end ContainedChart

/-- The containment of a contained chart with absolute values, as for an
oriented square. -/
lemma ContainedChart.abs_box {a b : ℝ} (h : ContainedChart a |b|) :
    (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0 := by
  rw [abs_of_nonneg (show 0 ≤ a by linarith [h.half_le])]
  exact h.containment

private lemma clipped_distance {x v : ℝ}
    (hv : |v| = min |x| (1 / 2))
    (hprod : x * v = min |x| (1 / 2) * |x|) :
    (v - x) ^ 2 = (max (|x| - 1 / 2) 0) ^ 2 := by
  have hv2 : v ^ 2 = (min |x| (1 / 2)) ^ 2 := by
    rw [← sq_abs v, hv]
  have hx2 := sq_abs x
  rcases le_total |x| (1 / 2) with h | h
  · rw [min_eq_left h] at hv2 hprod
    rw [max_eq_right (by linarith : |x| - 1 / 2 ≤ 0)]
    nlinarith
  · rw [min_eq_right h] at hv2 hprod
    rw [max_eq_left (by linarith : 0 ≤ |x| - 1 / 2)]
    nlinarith

/-- A point of the closed square at squared distance
`(max (α - 1/2) 0)² + (max (β - 1/2) 0)²` from `o`. -/
lemma exists_clipped_point (S : UnitSquare) (o : Point) :
    ∃ p : Point, closedSquare S p ∧
      normSq (sub p o) = (max (alpha S o - 1 / 2) 0) ^ 2 +
        (max (beta S o - 1 / 2) 0) ^ 2 := by
  obtain ⟨u, hu, hxu⟩ := exists_signed (localX S o)
    (c := min |localX S o| (1 / 2))
    (le_min (abs_nonneg _) (by norm_num))
  obtain ⟨v, hv, hyv⟩ := exists_signed (localY S o)
    (c := min |localY S o| (1 / 2))
    (le_min (abs_nonneg _) (by norm_num))
  refine ⟨add S.center (rotate S (u, v)), ?_, ?_⟩
  · constructor
    · rw [localX_rotated, hu]
      exact min_le_right _ _
    · rw [localY_rotated, hv]
      exact min_le_right _ _
  · rw [← frame_distance S, localX_rotated, localY_rotated,
      clipped_distance hu hxu, clipped_distance hv hyv]
    rfl

/-- The point of the closed square nearest to `o`, at the squared distance
`max (a - 1/2) 0 ^ 2 + max (b - 1/2) 0 ^ 2`. -/
lemma chart_exists_clipped_point {S : UnitSquare} {o : Point} (T : SquareChart S o) :
    ∃ p : Point, closedSquare S p ∧
      normSq (sub p o) = (max (T.a - 1 / 2) 0) ^ 2 +
        (max (T.b - 1 / 2) 0) ^ 2 := by
  apply T.transfer
    (fun a b => ∃ p : Point, closedSquare S p ∧
      normSq (sub p o) = (max (a - 1 / 2) 0) ^ 2 + (max (b - 1 / 2) 0) ^ 2)
  · rintro a b ⟨p, hp, hd⟩
    exact ⟨p, hp, by simpa only [add_comm] using hd⟩
  · exact exists_clipped_point S o

/-- If the local coordinates of `o` in the frame of C are at most `c0`, an
exterior square whose interior is disjoint from that of C avoids the core
disk. -/
lemma avoidsCore_of_disjoint {S C : UnitSquare} {o : Point} (T : SquareChart S o)
    (hsort : T.b ≤ T.a) (hout : ¬ openSquare S o)
    (hc : alpha C o ≤ c0 ∧ beta C o ≤ c0)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare C p)) :
    AvoidsCore T.a T.b := by
  obtain ⟨p, hp, hdist⟩ := chart_exists_clipped_point T
  have hn := closed_open_disjoint S C hd hp
  have hcore : coreRadius ^ 2 ≤ normSq (sub p o) := by
    by_contra! ht
    exact hn (inscribed_disk_mem C o coreRadius_pos c0_add_coreRadius hc.1 hc.2 ht)
  have ha : 0 ≤ T.a - 1 / 2 := by linarith [T.exterior hsort hout]
  rw [hdist, max_eq_left ha] at hcore
  exact hcore

lemma radial_sq_le_of_phi {a b ρ : ℝ} (hρ : 0 < ρ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : phi a b ≤ ρ ^ 2 + ρ + 1 / 2) : a ^ 2 + b ^ 2 ≤ ρ ^ 2 := by
  by_contra! hr
  have hsum : a + b < ρ := by
    dsimp [phi] at hc
    nlinarith
  have hp := mul_pos (sub_pos.mpr hsum) (show 0 < ρ + a + b by linarith)
  nlinarith [mul_nonneg ha hb]

/-- A square in the disk of squared radius `Q0` has its centre within `rho0`
of `o`. -/
theorem center_radius_sq {S : UnitSquare} {o : Point}
    (hc : phi (alpha S o) (beta S o) ≤ Q0) :
    normSq (sub S.center o) ≤ rho0 ^ 2 := by
  rw [local_center_norm]
  exact radial_sq_le_of_phi (by linarith [rho0_bounds.1]) (alpha_nonneg S o) (beta_nonneg S o)
    (by rw [rho0_sq]; exact hc)

lemma projection_abs_le_rho0 {x y c s : ℝ}
    (hp : x ^ 2 + y ^ 2 ≤ rho0 ^ 2) (hu : c ^ 2 + s ^ 2 = 1) :
    |x*c + y*s| ≤ rho0 := by
  have hid : (x*c+y*s)^2 + (x*s-y*c)^2 = (x^2+y^2)*(c^2+s^2) := by ring
  rw [hu,mul_one] at hid
  have hsq : (x*c+y*s)^2 ≤ rho0^2 := by nlinarith [sq_nonneg (x*s-y*c)]
  apply abs_le.mpr
  constructor <;> nlinarith [rho0_bounds.1]

lemma chart_center_radius_sq {a b : ℝ} (hc : ContainedChart a |b|) :
    a ^ 2 + b ^ 2 ≤ rho0 ^ 2 := by
  have hh := radial_sq_le_of_phi (ρ := rho0) (by linarith [rho0_bounds.1])
    (by linarith [hc.half_le])
    (abs_nonneg b) (by rw [rho0_sq]; exact hc.containment)
  simpa only [sq_abs] using hh

lemma chart_center_east_bound {a b t : ℝ} (hc : ContainedChart a |b|) :
    a * Real.cos t - b * Real.sin t ≤ rho0 := by
  have hh := projection_abs_le_rho0 (chart_center_radius_sq hc)
    (c := Real.cos t) (s := -Real.sin t)
    (by nlinarith [Real.sin_sq_add_cos_sq t])
  have hu := (abs_le.mp hh).2
  nlinarith

/-! ### Oriented squares -/

/-- The unit square with frame angle `t` whose centre has the coordinates
`(a, b)` in that frame. -/
def orientedSquare (t a b : ℝ) : UnitSquare where
  center := (a * Real.cos t - b * Real.sin t, a * Real.sin t + b * Real.cos t)
  cosine := Real.cos t
  sine := Real.sin t
  unit := by nlinarith [Real.sin_sq_add_cos_sq t]

lemma orientedSquare_localX (t a b : ℝ) (p : Point) :
    localX (orientedSquare t a b) p = p.1 * Real.cos t + p.2 * Real.sin t - a := by
  dsimp [localX, orientedSquare]
  linear_combination -a * (Real.sin_sq_add_cos_sq t)

lemma orientedSquare_localY (t a b : ℝ) (p : Point) :
    localY (orientedSquare t a b) p = -p.1 * Real.sin t + p.2 * Real.cos t - b := by
  dsimp [localY, orientedSquare]
  linear_combination -b * (Real.sin_sq_add_cos_sq t)

@[simp] lemma orientedSquare_alpha (t a b : ℝ) :
    alpha (orientedSquare t a b) (0, 0) = |a| := by
  simp [alpha, orientedSquare_localX]

@[simp] lemma orientedSquare_beta (t a b : ℝ) :
    beta (orientedSquare t a b) (0, 0) = |b| := by
  simp [beta, orientedSquare_localY]

/-- In its own frame, the centre of `orientedSquare t a b` has first coordinate
`a`. -/
lemma oriented_frame_centerX (t a b : ℝ) :
    frameX (orientedSquare t a b) (sub (orientedSquare t a b).center (0,0)) = a := by
  dsimp [frameX,orientedSquare,sub]
  linear_combination a*(Real.sin_sq_add_cos_sq t)

lemma orientedSquare_eq_modelSquare (t a b : ℝ) :
    orientedSquare t a b = modelSquare (0, 0) (t : Direction) (a, b) := by
  unfold orientedSquare modelSquare
  congr 1
  simp only [pointInDirection, Real.Angle.cos_coe, Real.Angle.sin_coe]
  ext <;> ring

lemma signedB_abs {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    |C.signedB| = C.b := by
  cases h : C.reversed <;>
    simp [SquareChart.signedB, h, abs_of_nonneg C.nonneg.2]

/-- The open square of a chart is the model square at its phase and signed
coordinates. -/
theorem chart_same_open_model {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    ∀ p, openSquare S p ↔ openSquare (modelSquare o C.phase (C.a, C.signedB)) p := by
  intro p
  obtain ⟨q, rfl⟩ := (frameEquiv o C.phase).surjective p
  rw [frameEquiv_apply]
  have hm := modelSquare_local o C.phase (C.a, C.signedB) q.1 q.2
  simp only [openSquare, hm.1, hm.2]
  exact C.cartesian q.1 q.2

/-- The open square of a chart about the origin is the oriented square at a
real representative of its phase. -/
theorem chart_same_open_oriented {S : UnitSquare} (C : SquareChart S (0, 0))
    {t : ℝ} (ht : (t : Direction) = C.phase) :
    ∀ p, openSquare S p ↔ openSquare (orientedSquare t C.a C.signedB) p := by
  rw [orientedSquare_eq_modelSquare, ht]
  exact chart_same_open_model C

/-- A sorted chart of an exterior square in the disk of squared radius `Q0` is a
contained chart. -/
lemma chart_signed_containment {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hsort : C.b ≤ C.a) (hout : ¬ openSquare S o)
    (hQ : phi (alpha S o) (beta S o) ≤ Q0) :
    ContainedChart C.a |C.signedB| := by
  rw [signedB_abs]
  exact ⟨C.exterior hsort hout, C.nonneg.2, hsort, chart_phi C hQ⟩

lemma coordinate_le_rho0 {a b : ℝ}
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0) : |a| ≤ rho0 := by
  have hb : 1 / 4 ≤ (|b| + 1 / 2) ^ 2 := by nlinarith [abs_nonneg b]
  have hs : (|a| + 1 / 2) ^ 2 ≤ Q0 - 1 / 4 := by linarith
  have hr := Real.le_sqrt_of_sq_le hs
  dsimp [rho0]
  linarith

/-! ### Phases -/

/-- Every phase lies within `π/4` of one of the four axes: it is `v`, `π/2 - v`,
`π + v` or `-π/2 - v` as a direction, for some `|v| ≤ π/4`. -/
theorem four_primary_quadrants (t:ℝ) :
    (∃ v : ℝ, |v|≤Real.pi/4 ∧ (t:Direction)=(v:Direction)) ∨
    (∃ v, |v|≤Real.pi/4 ∧ (t:Direction)=(Real.pi/2-v:ℝ)) ∨
    (∃ v, |v|≤Real.pi/4 ∧ (t:Direction)=(Real.pi+v:ℝ)) ∨
    (∃ v, |v|≤Real.pi/4 ∧ (t:Direction)=(-Real.pi/2-v:ℝ)) := by
  let z := (t:Direction).toReal
  have hz0 : -Real.pi≤z := (t:Direction).neg_pi_lt_toReal.le
  have hz1 : z≤Real.pi := (t:Direction).toReal_le_pi
  have hz : (z:Direction)=(t:Direction) := Real.Angle.coe_toReal _
  by_cases h0 : -Real.pi/4≤z
  · by_cases h1 : z≤Real.pi/4
    · exact Or.inl ⟨z,abs_le.mpr ⟨by linarith,h1⟩,hz.symm⟩
    · by_cases h2 : z≤3*Real.pi/4
      · right; left
        refine ⟨Real.pi/2-z,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
        have h : Real.pi/2-(Real.pi/2-z)=z := by ring
        rw [h]; exact hz.symm
      · right; right; left
        refine ⟨z-Real.pi,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
        have h : Real.pi+(z-Real.pi)=z := by ring
        rw [h]; exact hz.symm
  · by_cases h2 : z≤-3*Real.pi/4
    · right; right; left
      refine ⟨z+Real.pi,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
      have h : Real.pi+(z+Real.pi)=z+2*Real.pi := by ring
      rw [h,Real.Angle.coe_add,Real.Angle.coe_two_pi,add_zero]
      exact hz.symm
    · right; right; right
      refine ⟨-Real.pi/2-z,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
      have h : -Real.pi/2-(-Real.pi/2-z)=z := by ring
      rw [h]; exact hz.symm

/-- Two lifts of one direction less than `2π` apart are equal. -/
lemma phase_eq_of_short_difference {t u:ℝ} (he:(t:Direction)=(u:Direction))
    (hshort:|t-u|<2*Real.pi) : t=u := by
  obtain ⟨k,hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp he
  have hb := abs_lt.mp hshort
  rw [hk] at hb
  have hp : 0<2*Real.pi := by positivity
  have hlo : (-1:ℝ)<(k:ℝ) := by
    by_contra! hc
    have := mul_le_mul_of_nonneg_left hc hp.le
    linarith [hb.1]
  have hhi : (k:ℝ)<1 := by
    by_contra! hc
    have := mul_le_mul_of_nonneg_left hc hp.le
    linarith [hb.2]
  have hlo' : (-1:ℤ)<k := by exact_mod_cast hlo
  have hhi' : k<1 := by exact_mod_cast hhi
  have hz : k=0 := by omega
  simp only [hz,Int.cast_zero,mul_zero] at hk
  linarith

end SquaresInCircles.Six.Normalization

namespace SquaresInCircles.Six

/-! ### Projections of a square -/

/-- If `phi` of the local coordinates of `o` is at most `R ^ 2`, the closed
square lies in the closed disk of radius `R` about `o`: the converse of the
farthest-vertex bound. -/
lemma inDisk_of_phi_le {S : UnitSquare} {o : Point} {R : ℝ}
    (hphi : phi (alpha S o) (beta S o) ≤ R ^ 2)
    {p : Point} (hp : closedSquare S p) : inDisk o R p := by
  have hx : |localX S p - localX S o| ≤ alpha S o + 1 / 2 := by
    have hh := abs_add_le (localX S p) (-localX S o)
    rw [abs_neg, ← sub_eq_add_neg] at hh
    dsimp [alpha]
    linarith [hp.1]
  have hy : |localY S p - localY S o| ≤ beta S o + 1 / 2 := by
    have hh := abs_add_le (localY S p) (-localY S o)
    rw [abs_neg, ← sub_eq_add_neg] at hh
    dsimp [beta]
    linarith [hp.2]
  have hxp := mul_nonneg (sub_nonneg.mpr hx)
    (show 0 ≤ alpha S o + 1 / 2 + |localX S p - localX S o| by
      linarith [alpha_nonneg S o, abs_nonneg (localX S p - localX S o)])
  have hyp := mul_nonneg (sub_nonneg.mpr hy)
    (show 0 ≤ beta S o + 1 / 2 + |localY S p - localY S o| by
      linarith [beta_nonneg S o, abs_nonneg (localY S p - localY S o)])
  change normSq (sub p o) ≤ R ^ 2
  rw [← frame_distance S]
  dsimp [phi] at hphi
  nlinarith [sq_abs (localX S p - localX S o), sq_abs (localY S p - localY S o)]

/-- The unit normal to the sides `x = ±1/2` of `S`, its first frame axis. -/
def normalX (S : UnitSquare) : Point := (S.cosine,S.sine)

/-- The unit normal to the sides `y = ±1/2` of `S`, its second frame axis. -/
def normalY (S : UnitSquare) : Point := (-S.sine,S.cosine)

lemma projection_local (S : UnitSquare) (n p : Point) :
    dot n (sub p S.center) = frameX S n * localX S p + frameY S n * localY S p := by
  have hh := frame_dot S n (sub p S.center)
  exact hh.symm

lemma closed_projection_bounds (S : UnitSquare) (n : Point) {p : Point}
    (hp : closedSquare S p) :
    dot n S.center - width S n ≤ dot n p ∧ dot n p ≤ dot n S.center + width S n := by
  have hh := abs_le.mp (closed_dot_bound S n hp)
  rw [dot_sub_right] at hh
  constructor <;> linarith [hh.1,hh.2]

lemma open_projection_bounds (S : UnitSquare) {n p : Point} (hn : n ≠ (0,0))
    (hp : openSquare S p) :
    dot n S.center - width S n < dot n p ∧ dot n p < dot n S.center + width S n := by
  have hh := abs_lt.mp (dot_open_bound_of_ne S hn hp)
  rw [dot_sub_right] at hh
  constructor <;> linarith [hh.1,hh.2]

/-- If `n` separates S from T, every point of the open square S projects below
every point of the open square T. -/
lemma separator_orients_pins {S T : UnitSquare} {n p q : Point}
    (hn : n ≠ (0,0)) (hp : openSquare S p) (hq : openSquare T q)
    (hsep : width S n + width T n ≤ dot n (sub T.center S.center)) :
    dot n p < dot n q := by
  have hS := open_projection_bounds S hn hp
  have hT := open_projection_bounds T hn hq
  rw [dot_sub_right] at hsep
  linarith [hS.2,hT.1]

end SquaresInCircles.Six

namespace SquaresInCircles.Six.Normalization

/-! ### Separating axes of the central square -/

/-- A square whose chart is contained lies in the closed disk of radius `R0`. -/
lemma oriented_contained_of_chart {t a b : ℝ} (hc : ContainedChart a |b|) :
    ∀ p, closedSquare (orientedSquare t a b) p → inDisk (0,0) R0 p := by
  intro p hp
  apply Six.inDisk_of_phi_le (S := orientedSquare t a b) (o := (0,0)) (R := R0) _ hp
  rw [orientedSquare_alpha,orientedSquare_beta,R0_sq]
  simpa [phi,abs_of_nonneg (show 0 ≤ a by linarith [hc.half_le])] using hc.containment

/-- The seven axes along which an exterior square can be separated from the
central square: its own axis, its secondary axis in either direction, and the
four sides of the central square. -/
inductive CentralAxis where
  | own | secPlus | secMinus | east | west | north | south
  deriving DecidableEq

/-- `(|cos t| + |sin t|)/2`, the half-width along a coordinate axis of a unit
square at angle `t`. -/
def angularWidth (t : ℝ) : ℝ := (|Real.cos t|+|Real.sin t|)/2

/-- The half-width of a square at an angle in `[0, π/2]`. -/
lemma angularWidth_eq {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
    angularWidth x=(Real.cos x+Real.sin x)/2 := by
  obtain ⟨hc,hs⟩ := cos_sin_nonneg hx
  simp only [angularWidth,abs_of_nonneg hc,abs_of_nonneg hs]

lemma angularWidth_neg (t : ℝ) : angularWidth (-t)=angularWidth t := by
  simp [angularWidth,Real.cos_neg,Real.sin_neg,abs_neg]

lemma angularWidth_pi_add (t : ℝ) : angularWidth (Real.pi+t)=angularWidth t := by
  simp [angularWidth,Real.cos_add,Real.sin_add,abs_neg]

lemma angularWidth_half_pi_add (t : ℝ) : angularWidth (Real.pi/2+t)=angularWidth t := by
  simp [angularWidth,Real.cos_add,Real.sin_add,abs_neg,add_comm]

lemma angularWidth_half_pi_sub (t : ℝ) : angularWidth (Real.pi/2-t)=angularWidth t := by
  simp [angularWidth,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,add_comm]

lemma angularWidth_three_half_pi_add (t : ℝ) :
    angularWidth (3*Real.pi/2+t)=angularWidth t := by
  rw [show 3*Real.pi/2+t=Real.pi+(Real.pi/2+t) by ring,angularWidth_pi_add,
    angularWidth_half_pi_add]

/-- The half-width is at least the mean of `cos t` and `sin t`. -/
lemma angularWidth_lower (t : ℝ) : (Real.cos t+Real.sin t)/2 ≤ angularWidth t := by
  dsimp [angularWidth]
  linarith [le_abs_self (Real.cos t),le_abs_self (Real.sin t)]

/-- The first coordinate of the centre of `orientedSquare t a b`. -/
def centerX (t a b : ℝ) : ℝ := a*Real.cos t-b*Real.sin t
/-- The second coordinate of the centre of `orientedSquare t a b`. -/
def centerY (t a b : ℝ) : ℝ := a*Real.sin t+b*Real.cos t

/-- The projection of the centre `(cx, cy)` of C on the axis `(cos t, sin t)`. -/
def centralNormal (t cx cy : ℝ) : ℝ := cx*Real.cos t+cy*Real.sin t
/-- The projection of `(cx, cy)` on the axis `(-sin t, cos t)`. -/
def centralTransverse (t cx cy : ℝ) : ℝ := -cx*Real.sin t+cy*Real.cos t

/-- The separating inequality of the exterior square and the central square
along the axis `k`, as a margin: it is nonnegative when they are separated
along `k`. -/
def centralMargin (k : CentralAxis) (t a b cx cy : ℝ) : ℝ :=
  match k with
  | .own => a-1/2-centralNormal t cx cy-angularWidth t
  | .secPlus => b-1/2-centralTransverse t cx cy-angularWidth t
  | .secMinus => centralTransverse t cx cy-1/2-angularWidth t-b
  | .east => centerX t a b-angularWidth t-cx-1/2
  | .west => cx-1/2-centerX t a b-angularWidth t
  | .north => centerY t a b-angularWidth t-cy-1/2
  | .south => cy-1/2-centerY t a b-angularWidth t

/-- At the phase `π + t`, the own margin of a square exceeds its margin along the
west side of C by `(1 - cos t)(a - cx) + sin t (b + cy)`. -/
lemma own_sub_west_margin (t a b cx cy : ℝ) :
    centralMargin .own (Real.pi+t) a b cx cy-centralMargin .west (Real.pi+t) a b cx cy=
      (1-Real.cos t)*(a-cx)+Real.sin t*(b+cy) := by
  simp only [centralMargin,centralNormal,centerX,cos_pi_add,sin_pi_add]
  ring

lemma centralNormal_le_width {t cx cy : ℝ}
    (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy) (hx : cx ≤ 1/2) (hy : cy ≤ 1/2) :
    centralNormal t cx cy ≤ angularWidth t := by
  have hc := mul_le_mul_of_nonneg_left (le_abs_self (Real.cos t)) hx0
  have hs := mul_le_mul_of_nonneg_left (le_abs_self (Real.sin t)) hy0
  have hcx := mul_le_mul_of_nonneg_right hx (abs_nonneg (Real.cos t))
  have hcy := mul_le_mul_of_nonneg_right hy (abs_nonneg (Real.sin t))
  dsimp [centralNormal,angularWidth]
  linarith

lemma central_threshold (t a b cx cy : ℝ) :
    SAT.threshold (axisSquare (cx,cy)) (orientedSquare t a b) = 1/2+angularWidth t := by
  simp only [SAT.threshold,relativeC,relativeS,axisSquare,orientedSquare,
    one_mul,zero_mul,zero_add,add_zero,neg_zero]
  dsimp [angularWidth]
  ring

lemma primary_difference (t a b cx cy : ℝ) :
    frameX (orientedSquare t a b)
      (sub (orientedSquare t a b).center (cx,cy)) = a-centralNormal t cx cy := by
  dsimp [frameX,orientedSquare,sub,centralNormal]
  linear_combination a*(Real.sin_sq_add_cos_sq t)

lemma secondary_difference (t a b cx cy : ℝ) :
    frameY (orientedSquare t a b)
      (sub (orientedSquare t a b).center (cx,cy)) = b-centralTransverse t cx cy := by
  dsimp [frameY,orientedSquare,sub,centralTransverse]
  linear_combination b*(Real.sin_sq_add_cos_sq t)

/-- An exterior square with interior disjoint from the central square has a
nonnegative margin along one of the seven axes. -/
theorem central_separators_complete {t a b cx cy : ℝ}
    (ha : 1/2 ≤ a) (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy)
    (hx : cx ≤ 1/2) (hy : cy ≤ 1/2)
    (hd : ∀ p, ¬ (openSquare (axisSquare (cx,cy)) p ∧
      openSquare (orientedSquare t a b) p)) :
    ∃ k : CentralAxis, 0 ≤ centralMargin k t a b cx cy := by
  have hs := SAT.separating_axes (axisSquare (cx,cy)) (orientedSquare t a b) hd
  rw [central_threshold,primary_difference,secondary_difference] at hs
  have hX : frameX (axisSquare (cx,cy))
      (sub (orientedSquare t a b).center (axisSquare (cx,cy)).center) = centerX t a b-cx := by
    simp [frameX,axisSquare,orientedSquare,sub,centerX]
  have hY : frameY (axisSquare (cx,cy))
      (sub (orientedSquare t a b).center (axisSquare (cx,cy)).center) = centerY t a b-cy := by
    simp [frameY,axisSquare,orientedSquare,sub,centerY]
  rw [hX,hY] at hs
  have hN : centralNormal t (axisSquare (cx,cy)).center.1 (axisSquare (cx,cy)).center.2 =
      centralNormal t cx cy := rfl
  have hT : centralTransverse t (axisSquare (cx,cy)).center.1 (axisSquare (cx,cy)).center.2 =
      centralTransverse t cx cy := rfl
  rw [hN,hT] at hs
  rcases hs with hs | hs | hs | hs
  · by_cases h0 : 0 ≤ centerX t a b-cx
    · rw [abs_of_nonneg h0] at hs
      exact ⟨.east,by dsimp [centralMargin]; linarith⟩
    · rw [abs_of_neg (lt_of_not_ge h0)] at hs
      exact ⟨.west,by dsimp [centralMargin]; linarith⟩
  · by_cases h0 : 0 ≤ centerY t a b-cy
    · rw [abs_of_nonneg h0] at hs
      exact ⟨.north,by dsimp [centralMargin]; linarith⟩
    · rw [abs_of_neg (lt_of_not_ge h0)] at hs
      exact ⟨.south,by dsimp [centralMargin]; linarith⟩
  · by_cases h0 : 0 ≤ a-centralNormal t cx cy
    · rw [abs_of_nonneg h0] at hs
      exact ⟨.own,by dsimp [centralMargin]; linarith⟩
    · rw [abs_of_neg (lt_of_not_ge h0)] at hs
      have hc := centralNormal_le_width (t := t) hx0 hy0 hx hy
      linarith
  · by_cases h0 : 0 ≤ b-centralTransverse t cx cy
    · rw [abs_of_nonneg h0] at hs
      exact ⟨.secPlus,by dsimp [centralMargin]; linarith⟩
    · rw [abs_of_neg (lt_of_not_ge h0)] at hs
      exact ⟨.secMinus,by dsimp [centralMargin]; linarith⟩

lemma oriented_x_width (t a b : ℝ) : width (orientedSquare t a b) (1,0) = angularWidth t := by
  simp [width,frameX,frameY,orientedSquare,angularWidth,abs_neg]

lemma oriented_y_width (t a b : ℝ) : width (orientedSquare t a b) (0,1) = angularWidth t := by
  simp [width,frameX,frameY,orientedSquare,angularWidth,add_comm]

lemma closed_center_coordinate_bounds {t a b : ℝ} {p : Point}
    (hp : closedSquare (orientedSquare t a b) p) :
    (centerX t a b-angularWidth t ≤ p.1 ∧ p.1 ≤ centerX t a b+angularWidth t) ∧
    (centerY t a b-angularWidth t ≤ p.2 ∧ p.2 ≤ centerY t a b+angularWidth t) := by
  have hx := Six.closed_projection_bounds (orientedSquare t a b) (1,0) hp
  have hy := Six.closed_projection_bounds (orientedSquare t a b) (0,1) hp
  rw [oriented_x_width] at hx
  rw [oriented_y_width] at hy
  simpa [dot,orientedSquare,centerX,centerY] using And.intro hx hy

lemma east_margin_cap {t a b cx cy : ℝ} (he : 0 ≤ centralMargin .east t a b cx cy) :
    ∀ p, closedSquare (orientedSquare t a b) p → cx+1/2 ≤ p.1 := by
  intro p hp
  have hh := (closed_center_coordinate_bounds hp).1.1
  dsimp [centralMargin] at he
  linarith

lemma west_margin_cap {t a b cx cy : ℝ} (hw : 0 ≤ centralMargin .west t a b cx cy) :
    ∀ p, closedSquare (orientedSquare t a b) p → p.1 ≤ cx-1/2 := by
  intro p hp
  have hh := (closed_center_coordinate_bounds hp).1.2
  dsimp [centralMargin] at hw
  linarith

lemma north_margin_cap {t a b cx cy : ℝ} (hn : 0 ≤ centralMargin .north t a b cx cy) :
    ∀ p, closedSquare (orientedSquare t a b) p → cy+1/2 ≤ p.2 := by
  intro p hp
  have hh := (closed_center_coordinate_bounds hp).2.1
  dsimp [centralMargin] at hn
  linarith

lemma south_margin_cap {t a b cx cy : ℝ} (hs : 0 ≤ centralMargin .south t a b cx cy) :
    ∀ p, closedSquare (orientedSquare t a b) p → p.2 ≤ cy-1/2 := by
  intro p hp
  have hh := (closed_center_coordinate_bounds hp).2.2
  dsimp [centralMargin] at hs
  linarith

/-- If `cx > c0`, a square in the disk is not separated from C along the east
side of C, at any angle `t`. -/
theorem east_separator_negative {a b t cx : ℝ} (hc : ContainedChart a |b|)
    (hx : c0 < cx) :
    a * Real.cos t - b * Real.sin t -
      (|Real.cos t| + |Real.sin t|) / 2 - cx - 1 / 2 < 0 := by
  have hw := one_le_abs_cos_add_abs_sin t
  have hP := chart_center_east_bound (t := t) hc
  dsimp [c0] at hx
  linarith

lemma transverse_distance_lt_one {b cx cy t : ℝ}
    (hb : |b| ≤ U0) (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy)
    (hx : cx ≤ c0) (hy : cy ≤ c0) :
    |b - (-cx * Real.sin t + cy * Real.cos t)| < 1 := by
  have hb' := abs_le.mp hb
  have hslo := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin t) hx0
  have hshi := mul_le_mul_of_nonneg_left (Real.sin_le_one t) hx0
  have hclo := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos t) hy0
  have hchi := mul_le_mul_of_nonneg_left (Real.cos_le_one t) hy0
  apply abs_lt.mpr
  constructor <;> nlinarith [U0_upper, c0_bounds.2]

/-- Both margins of separation along the secondary axis are negative. -/
theorem secondary_separators_fail {b cx cy t : ℝ}
    (hb : |b| ≤ U0) (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy)
    (hx : cx ≤ c0) (hy : cy ≤ c0) :
    b - 1 / 2 - (-cx * Real.sin t + cy * Real.cos t) -
        (|Real.cos t| + |Real.sin t|) / 2 < 0 ∧
      (-cx * Real.sin t + cy * Real.cos t) - 1 / 2 - b -
        (|Real.cos t| + |Real.sin t|) / 2 < 0 := by
  have hd := abs_lt.mp (transverse_distance_lt_one (t := t) hb hx0 hy0 hx hy)
  have hw := one_le_abs_cos_add_abs_sin t
  constructor <;> linarith

end SquaresInCircles.Six.Normalization

module

public import SquaresInCircles.Eight.Exterior
public import SquaresInCircles.Eight.Arithmetic.CentralBandPolynomials
public import SquaresInCircles.Eight.Boundary.Reduction
public import SquaresInCircles.Eight.Frames.Central.ForbiddenWidths

/-!
# Eight squares: the central square and the one-twelfth core

In a packing of eight unit squares in a closed disk of squared radius at most `98/25` about the
origin, exactly one square contains the origin in its interior (`central_square_exists`): a
square that avoids it has `3 L₁ + L_{5/4} ≥ π` (`one_square_two_circle_inequality`), and eight
such squares do not fit.

At squared radius at most `Q0` the central square contains the closed disk of radius `1/12`
about the origin in its interior, and every other closed square lies at distance more than
`1/12` from the origin (`central_core_and_exteriors`). Moving the disk centre to a nearest
boundary point of the central square would give a packing in a disk of squared radius below
`98/25` with no central square, so that boundary is more than `1/1000` from the origin
(`centralDepth_gt_milli`). Every exterior square then contains the segment
`{(11/12, y) : |y| ≤ 7/20}` of its centre direction, turned to the horizontal
(`CentralBand.RayData.segment`), and a common point at a fixed distance in every direction near
its centre direction (`CentralBand.RayData.common_point_A`, `common_point_B`), so the seven centre
directions are pairwise far apart. If a side of the central square came within `1/12` of the
origin, the rectangles of `CentralForbidden.bandA_forbidden` and `CentralForbidden.bandB_forbidden`
would forbid these segments an interval of directions too long to leave room for the seven
directions (`seven_rays_avoid_interval_budget`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal Topology
open MeasureTheory Set
namespace SquaresInCircles.Eight
/-- In a packing of eight squares in the disk of squared radius at most `98/25` about the
origin, exactly one square contains the origin in its interior. -/
theorem central_square_exists {S : Fin 8 → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0, 0) q) (hq : q ≤ 98 / 25) :
    ∃! i, openSquare (S i) (0, 0) := by
  have hc (i : Fin 8) : SqContained (98 / 25) (S i) := by
    apply (SqContained.iff_points (by norm_num) (S i)).2
    intro p hp'
    have h := hp.2.1 i p hp'
    simpa only [sub, sub_zero] using h.trans hq
  obtain ⟨i, hi⟩ := central_exists_from_one_square_inequality hp.2.2
    (fun i hi => (one_square_two_circle_inequality (S i) (hc i) hi).1)
    (fun i hi => (one_square_two_circle_inequality (S i) (hc i) hi).2)
  exact ⟨i, hi, fun j hj => central_square_unique hp.2.2 hj hi⟩

namespace CentralBand

/-- A unit vector `(c, s)` of the closed first quadrant, both ends included, for the half-angle
substitution `u = s/(1 + c)`. -/
structure Quadrant (c s : ℝ) : Prop where
  c_nonneg : 0 ≤ c
  s_nonneg : 0 ≤ s
  unit : c^2+s^2 = 1

def halfAngle (c s : ℝ) : ℝ := s/(1+c)

lemma Quadrant.swap {c s : ℝ} (h : Quadrant c s) : Quadrant s c :=
  ⟨h.s_nonneg,h.c_nonneg,by linarith [h.unit]⟩

lemma Quadrant.halfAngle_mem {c s : ℝ} (h : Quadrant c s) :
    0 ≤ halfAngle c s ∧ halfAngle c s ≤ 1 := by
  have hc : 0 < 1+c := by linarith [h.c_nonneg]
  have hs : s ≤ 1 := (abs_le_of_sq_le_sq' (by linarith [h.unit,sq_nonneg c]) zero_le_one).2
  exact ⟨div_nonneg h.s_nonneg hc.le,(div_le_iff₀ hc).2 (by linarith [h.c_nonneg])⟩

lemma Quadrant.halfAngle_identities {c s : ℝ} (h : Quadrant c s) :
    (1-(halfAngle c s)^2)/(1+(halfAngle c s)^2) = c ∧
    2*halfAngle c s/(1+(halfAngle c s)^2) = s := by
  have hc : (1+c : ℝ) ≠ 0 := ne_of_gt (by linarith [h.c_nonneg])
  have hz : (1+(halfAngle c s)^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  constructor
  · dsimp [halfAngle] at *
    field_simp [hc] at ⊢
    linarith [h.unit,congrArg (fun x : ℝ => c*x) h.unit]
  · dsimp [halfAngle] at *
    field_simp [hc] at ⊢
    linarith [h.unit,congrArg (fun x : ℝ => s*x) h.unit]

lemma Quadrant.near_halfAngle_mem {c s : ℝ} (h : Quadrant c s) (hne : s ≤ c) :
    0 ≤ halfAngle c s ∧ halfAngle c s ≤ 3/7 := by
  have hc : 2/3 ≤ c := by
    have hs₂ := mul_nonneg (sub_nonneg.mpr hne) (add_nonneg h.c_nonneg h.s_nonneg)
    nlinarith only [hs₂,h.unit,h.c_nonneg]
  have hs : s ≤ 5/7 := by
    have hs₂ := mul_nonneg (sub_nonneg.mpr hne) (add_nonneg h.c_nonneg h.s_nonneg)
    nlinarith only [hs₂,h.unit,h.s_nonneg]
  refine ⟨h.halfAngle_mem.1,?_⟩
  apply (div_le_iff₀ (by linarith : 0 < 1+c)).2
  linarith

/-- If the polynomial `Arithmetic.centralBandP C D` is positive on `[0, 1]`, a square in the disk
of squared radius `Q0` with state `(r c, r s)` has `r c < 1/2 + C c - D s`: containment puts
`r c` below the positive root of a quadratic, and the polynomial, in the half-angle variable of
`(c, s)`, puts `1/2 + C c - D s` above it. -/
lemma primary_upper {r c s C D : ℝ}
    (h : Quadrant c s) (hr : 0 ≤ r) (hC : 0 ≤ C) (hD : 0 ≤ D ∧ D < 1/2)
    (hcontained : phi (r*c) (r*s) ≤ Q0)
    (hP : ∀ u, 0 ≤ u ∧ u ≤ 1 → 0 < Arithmetic.centralBandP C D u) :
    r*c < 1/2+C*c-D*s := by
  let u := halfAngle c s
  obtain ⟨hc,hs⟩ := h.halfAngle_identities
  have hp := hP u h.halfAngle_mem
  have hz : 0 < (1+u^2)^3 := by positivity
  have hnormalized := Arithmetic.centralBandP_normalized C D u
  have hpoly := div_pos hp hz
  rw [hnormalized,hc,hs] at hpoly
  have hs₁ : s ≤ 1 := (abs_le_of_sq_le_sq' (by linarith only [h.unit, sq_nonneg c]) zero_le_one).2
  have hY : 0 < 1/2+C*c-D*s := by
    have hp := mul_nonneg hC h.c_nonneg
    have hd := mul_le_mul_of_nonneg_left hs₁ hD.1
    linarith only [hD.2, hp, hd]
  have hX : 0 ≤ r*c := mul_nonneg hr h.c_nonneg
  have hB : 0 ≤ c*(c+s) := mul_nonneg h.c_nonneg (add_nonneg h.c_nonneg h.s_nonneg)
  have hquadratic : (r*c)^2+(r*c)*c*(c+s)+(1/2-Q0)*c^2 ≤ 0 := by
    have hm := mul_le_mul_of_nonneg_right hcontained (sq_nonneg c)
    have hu := congrArg (fun x : ℝ => r^2*c^2*x) h.unit
    dsimp [phi] at hm
    linarith only [hm, hu]
  by_contra! hn
  have hprod := mul_nonneg (sub_nonneg.mpr hn)
    (show 0 ≤ r*c+(1/2+C*c-D*s)+c*(c+s) by linarith only [hY, hB, hn])
  dsimp [Q0] at hquadratic
  linarith only [hpoly, hquadratic, hprod]

lemma secondary_upper {c s A C D : ℝ} (h : Quadrant c s) (hne : s ≤ c)
    (hV : ∀ u, 0 ≤ u ∧ u ≤ 3/7 → 0 < Arithmetic.centralBandV A C D u) :
    C*s+D*c-A*(s/c) < 1/2 := by
  have hc : 0 < c := by nlinarith only [h.unit,h.c_nonneg,h.s_nonneg,hne]
  obtain ⟨hcos,hsin⟩ := h.halfAngle_identities
  have hu := h.near_halfAngle_mem hne
  set u := halfAngle c s with hu_def
  have hp := Arithmetic.centralBandV_normalized hu (hV u hu)
  have hratio : 2*u/(1-u^2) = s/c := by
    have hz : (1+u^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hu₂ : u^2 ≤ 9/49 := by linarith [mul_nonneg (show 0 ≤ 3/7-u by linarith [hu.2]) (show 0 ≤ 3/7+u by linarith [hu.1])]
    have hu₀ : (1-u^2 : ℝ) ≠ 0 := ne_of_gt (by linarith)
    rw [← hsin,← hcos]
    field_simp
  rw [hcos,hsin,hratio] at hp
  exact hp

/-- The four side inequalities of the square hold strictly at every point of the transverse
segment, its two endpoints included. They follow from `primary_upper` and `secondary_upper` with
the polynomials of the segment (`Arithmetic.segment_P_positive`,
`Arithmetic.segment_V_positive`), for the whole segment at once. -/
theorem transverse_segment_sides {r c s y : ℝ} (h : Quadrant c s) (hne : s ≤ c)
    (hr : 0 ≤ r) (ha : 1/2 < r*c)
    (hcontained : phi (r*c) (r*s) ≤ Q0) (hy : |y| ≤ 7/20) :
    |(11/12)*c+y*s-r*c| < 1/2 ∧
      |-(11/12)*s+y*c+r*s| < 1/2 := by
  have hp := primary_upper h hr (by norm_num : (0 : ℝ) ≤ 11/12)
    (by norm_num : (0 : ℝ) ≤ 7/20 ∧ (7/20 : ℝ) < 1/2)
    hcontained (fun _ hu => Arithmetic.segment_P_positive hu)
  have hp' := primary_upper h.swap hr (by norm_num : (0 : ℝ) ≤ 11/12)
    (by norm_num : (0 : ℝ) ≤ 7/20 ∧ (7/20 : ℝ) < 1/2)
    (by simpa [phi,add_comm] using hcontained)
    (fun _ hu => Arithmetic.segment_P_positive hu)
  have hv := secondary_upper h hne (fun _ hu => Arithmetic.segment_V_positive hu)
  have hc : 0 < c := by linarith only [h.unit, h.c_nonneg, h.s_nonneg, ha, hp]
  have hratio : (1/2)*(s/c) ≤ r*s := by
    have hh := mul_le_mul_of_nonneg_right ha.le h.s_nonneg
    rw [← mul_div_assoc, div_le_iff₀ hc]
    linarith only [hh]
  have hupper : (11/12)*c+y*s < 1 := by
    have hcauchy := cauchy_sq ((11/12 : ℝ),y) (c,s)
    have hy₂ : y^2 ≤ (7/20 : ℝ)^2 := by
      linarith only [sq_abs y,
        mul_nonneg (show 0 ≤ 7/20-|y| by linarith) (show 0 ≤ 7/20+|y| by positivity), hy]
    dsimp [dot,normSq] at hcauchy
    rw [h.unit] at hcauchy
    have hsq : ((11/12)*c+y*s)^2 < 1^2 := by linarith only [hcauchy, hy₂]
    exact (abs_lt.mp (abs_lt_of_sq_lt_sq hsq zero_le_one)).2
  obtain ⟨hylo,hyhi⟩ := abs_le.mp hy
  have hyslo := mul_le_mul_of_nonneg_right hylo h.s_nonneg
  have hyshi := mul_le_mul_of_nonneg_right hyhi h.s_nonneg
  have hyclo := mul_le_mul_of_nonneg_right hylo h.c_nonneg
  have hychi := mul_le_mul_of_nonneg_right hyhi h.c_nonneg
  constructor <;> apply abs_lt.mpr <;> constructor <;> linarith only [hp, hyslo, ha, hupper, hv,
    hratio, hyclo, hp', hychi]

lemma cos_upper_eight {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1-x^2/2+x^4/24-x^6/720+x^8/40320 := by
  have h := nonneg_of_deriv_nonneg
    (fun t => 1-t^2/2+t^4/24-t^6/720+t^8/40320-Real.cos t)
    (by fun_prop) (by norm_num) (fun t ht => by
      simp (disch := fun_prop)
      linarith [sin_lower_seven ht]) hx
  linarith

lemma sin_upper_nine {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x-x^3/6+x^5/120-x^7/5040+x^9/362880 := by
  have h := nonneg_of_deriv_nonneg
    (fun t => t-t^3/6+t^5/120-t^7/5040+t^9/362880-Real.sin t)
    (by fun_prop) (by norm_num) (fun t ht => by
      simp (disch := fun_prop)
      linarith [cos_upper_eight ht]) hx
  linarith

lemma bandA_trig :
    Arithmetic.bandA_Cminus < (10007/10000)*Real.cos (3741/10000 : ℝ) ∧
    (10007/10000)*Real.cos (3741/10000 : ℝ) < Arithmetic.bandA_Cplus ∧
    (10007/10000)*Real.sin (3741/10000 : ℝ) < Arithmetic.bandA_D := by
  have hc₁ := cos_lower_six (x := (3741/10000 : ℝ)) (by norm_num)
  have hc₂ := cos_upper_eight (x := (3741/10000 : ℝ)) (by norm_num)
  have hs := sin_upper_nine (x := (3741/10000 : ℝ)) (by norm_num)
  norm_num [Arithmetic.bandA_Cminus,Arithmetic.bandA_Cplus,Arithmetic.bandA_D] at *
  exact ⟨by linarith,by linarith,by linarith⟩

lemma bandB_trig :
    Arithmetic.bandB_Cminus < (41/40)*Real.cos (19/50 : ℝ) ∧
    (41/40)*Real.cos (19/50 : ℝ) < Arithmetic.bandB_Cplus ∧
    (41/40)*Real.sin (19/50 : ℝ) < Arithmetic.bandB_D := by
  have hc₁ := cos_lower_six (x := (19/50 : ℝ)) (by norm_num)
  have hc₂ := cos_upper_eight (x := (19/50 : ℝ)) (by norm_num)
  have hs := sin_upper_nine (x := (19/50 : ℝ)) (by norm_num)
  norm_num [Arithmetic.bandB_Cminus,Arithmetic.bandB_Cplus,Arithmetic.bandB_D] at *
  exact ⟨by linarith,by linarith,by linarith⟩

/-- The common-point calculation: from the containment inequality and a lower bound `A` on the
primary coordinate, the point at distance `lam` in a direction within `h` of the centre direction
satisfies the four side inequalities of the square strictly. They are read as membership in the
open square in `RayData.common_point_A` and `RayData.common_point_B`. -/
theorem angular_band_sides {r α β h lam A Cminus Cplus D : ℝ}
    (hα : 0 ≤ α ∧ α ≤ Real.pi/4) (hβ : |β| ≤ h) (hh : 0 ≤ h ∧ h ≤ 2/5)
    (hr : 0 ≤ r) (hlam : 0 < lam) (hA : A ≤ r*Real.cos α)
    (hupper : lam-r*Real.cos α < 1/2)
    (hcontained : phi (r*Real.cos α) (r*Real.sin α) ≤ Q0)
    (hC : 0 ≤ Cminus) (hD : 0 ≤ D ∧ D < 1/2)
    (htrig : Cminus ≤ lam*Real.cos h ∧ lam*Real.cos h ≤ Cplus ∧ lam*Real.sin h ≤ D)
    (hP : ∀ u, 0 ≤ u ∧ u ≤ 1 → 0 < Arithmetic.centralBandP Cminus D u)
    (hV : ∀ u, 0 ≤ u ∧ u ≤ 3/7 → 0 < Arithmetic.centralBandV A Cplus D u) :
    |lam*Real.cos (α+β)-r*Real.cos α| < 1/2 ∧
    |-lam*Real.sin (α+β)+r*Real.sin α| < 1/2 := by
  have hc := cos_sin_nonneg (x := α) ⟨hα.1,by linarith only [hα.2, Real.pi_pos]⟩
  have hquad : Quadrant (Real.cos α) (Real.sin α) :=
    ⟨hc.1,hc.2,by linarith only [Real.sin_sq_add_cos_sq α]⟩
  have hnear := sin_le_cos_of_small hα
  have hprimary := primary_upper hquad hr hC hD hcontained hP
  have hother := primary_upper hquad.swap hr hC hD
    (by simpa [phi,add_comm] using hcontained) hP
  have hsecondary := secondary_upper hquad hnear hV
  have hcospos : 0 < Real.cos α := by
    have hh := east_quadrant_trig hα.1 hα.2
    linarith only [hh]
  have hratio : A*(Real.sin α/Real.cos α) ≤ r*Real.sin α := by
    have hm := mul_le_mul_of_nonneg_right hA hc.2
    rw [← mul_div_assoc, div_le_iff₀ hcospos]
    linarith only [hm]
  have hb := abs_le.mp hβ
  have hcosβ : Real.cos h ≤ Real.cos β := by
    rw [← Real.cos_abs β]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg β)
      (by linarith only [hh.2, Real.pi_gt_three, hα]) hβ
  have hsinβ : -Real.sin h ≤ Real.sin β ∧ Real.sin β ≤ Real.sin h := by
    constructor
    · have he := Real.sin_le_sin_of_le_of_le_pi_div_two
        (show -(Real.pi/2) ≤ -h by linarith only [hh.2, Real.pi_gt_three, hα])
        (show β ≤ Real.pi/2 by linarith only [hb.2, hh.2, Real.pi_gt_three, hα]) hb.1
      simpa using he
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith only [hb.1, hh.2, Real.pi_gt_three, hα])
        (by linarith only [hh.2, Real.pi_gt_three, hα]) hb.2
  have hcoslow : Cminus ≤ lam*Real.cos β := htrig.1.trans (mul_le_mul_of_nonneg_left hcosβ hlam.le)
  have hsinlo : -D ≤ lam*Real.sin β := by
    have hm := mul_le_mul_of_nonneg_left hsinβ.1 hlam.le
    linarith only [htrig.2.2, hm]
  have hsinhi : lam*Real.sin β ≤ D :=
    (mul_le_mul_of_nonneg_left hsinβ.2 hlam.le).trans htrig.2.2
  have hde : Cminus*Real.cos α-D*Real.sin α ≤ lam*Real.cos (α+β) := by
    have h₁ := mul_le_mul_of_nonneg_right hcoslow hc.1
    have h₂ := mul_le_mul_of_nonneg_right hsinhi hc.2
    rw [Real.cos_add]
    linarith only [h₁, h₂]
  have hdf : Cminus*Real.sin α-D*Real.cos α ≤ lam*Real.sin (α+β) := by
    have h₁ := mul_le_mul_of_nonneg_right hcoslow hc.2
    have h₂ := mul_le_mul_of_nonneg_right hsinlo hc.1
    rw [Real.sin_add]
    linarith only [h₁, h₂]
  have hdfupper : lam*Real.sin (α+β) ≤ Cplus*Real.sin α+D*Real.cos α := by
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi/2) ≤ α+β by linarith only [hb.1, hh.2, hα.1, Real.pi_gt_three])
      (show α+h ≤ Real.pi/2 by linarith only [hα.2, hh.2, Real.pi_gt_three])
      (show α+β ≤ α+h by linarith only [hb.2])
    have hmlam := mul_le_mul_of_nonneg_left hm hlam.le
    have h₁ := mul_le_mul_of_nonneg_right htrig.2.1 hc.2
    have h₂ := mul_le_mul_of_nonneg_right htrig.2.2 hc.1
    rw [Real.sin_add α h] at hmlam
    linarith only [hmlam, h₁, h₂]
  have hdeupper := mul_le_mul_of_nonneg_left (Real.cos_le_one (α+β)) hlam.le
  constructor <;> apply abs_lt.mpr <;> constructor <;> linarith only [hprimary, hde, hupper,
    hdeupper, hsecondary, hratio, hdfupper, hother, hdf]

theorem bandA_sides {r α β : ℝ}
    (hα : 0 ≤ α ∧ α ≤ Real.pi/4) (hβ : |β| ≤ 3741/10000)
    (hr : 0 ≤ r) (ha : 5007/10000 < r*Real.cos α)
    (hcontained : phi (r*Real.cos α) (r*Real.sin α) ≤ Q0) :
    |(10007/10000)*Real.cos (α+β)-r*Real.cos α| < 1/2 ∧
    |-(10007/10000)*Real.sin (α+β)+r*Real.sin α| < 1/2 := by
  exact angular_band_sides hα hβ (by norm_num) hr (by norm_num) ha.le
    (by linarith) hcontained
    (by norm_num [Arithmetic.bandA_Cminus]) (by norm_num [Arithmetic.bandA_D])
    ⟨bandA_trig.1.le,bandA_trig.2.1.le,bandA_trig.2.2.le⟩
    (fun _ hu => Arithmetic.bandA_P_positive hu) (fun _ hu => Arithmetic.bandA_V_positive hu)

theorem bandB_sides {r α β : ℝ}
    (hα : 0 ≤ α ∧ α ≤ Real.pi/4) (hβ : |β| ≤ 19/50)
    (hr : 0 ≤ r) (ha : 107/200 ≤ r*Real.cos α)
    (hcontained : phi (r*Real.cos α) (r*Real.sin α) ≤ Q0) :
    |(41/40)*Real.cos (α+β)-r*Real.cos α| < 1/2 ∧
    |-(41/40)*Real.sin (α+β)+r*Real.sin α| < 1/2 := by
  exact angular_band_sides hα hβ (by norm_num) hr (by norm_num) ha
    (by linarith) hcontained
    (by norm_num [Arithmetic.bandB_Cminus]) (by norm_num [Arithmetic.bandB_D])
    ⟨bandB_trig.1.le,bandB_trig.2.1.le,bandB_trig.2.2.le⟩
    (fun _ hu => Arithmetic.bandB_P_positive hu) (fun _ hu => Arithmetic.bandB_V_positive hu)

end CentralBand

theorem central_square_exists_at {S : Fin 8 → UnitSquare} {o : Point} {q : ℝ}
    (hp : SqPacking S o q) (hq : q ≤ 98/25) : ∃! i, openSquare (S i) o := by
  have hpack := (sqPacking_iff_packing S o hp.1).mp hp
  have hrot := packing_pull hpack (0 : Direction)
  have hsquare : SqPacking (fun i => pullSquare o 0 (S i)) (0,0) q :=
    (sqPacking_iff_packing _ _ hp.1).mpr hrot
  obtain ⟨i,hi,hunique⟩ := central_square_exists hsquare hq
  have hmem (j : Fin 8) : openSquare (pullSquare o 0 (S j)) (0,0) ↔ openSquare (S j) o := by
    rw [pullSquare_open,frameEquiv_zero]
  exact ⟨i,(hmem i).mp hi,fun j hj => hunique j ((hmem j).mpr hj)⟩

def centralDepth (K : UnitSquare) : ℝ :=
  1/2-max (alpha K (0,0)) (beta K (0,0))

lemma centralDepth_pos {K : UnitSquare} (h : openSquare K (0,0)) : 0 < centralDepth K := by
  dsimp [centralDepth]
  exact sub_pos.mpr (max_lt h.1 h.2)

lemma centralDepth_disk {K : UnitSquare} (h : openSquare K (0,0)) {p : Point}
    (hp : normSq p < centralDepth K^2) : openSquare K p := by
  apply inscribed_disk_mem K (0,0) (centralDepth_pos h)
    (show max (alpha K (0,0)) (beta K (0,0))+centralDepth K=1/2 by dsimp [centralDepth]; ring)
    (le_max_left _ _) (le_max_right _ _)
  simpa [sub] using hp

/-- A boundary point of the square at distance `centralDepth K` from the origin, constructed in
the frame of the square. The second coordinate is held fixed, so the construction also covers a
tie between the two nearest sides. -/
lemma centralDepth_boundary_point {K : UnitSquare} (h : openSquare K (0,0)) :
    ∃ p, closedSquare K p ∧ ¬ openSquare K p ∧ normSq p = centralDepth K^2 := by
  have hd := centralDepth_pos h
  by_cases hxy : alpha K (0,0) ≤ beta K (0,0)
  · obtain ⟨u,hu,hprod⟩ := exists_signed (localY K (0,0)) (c := 1) (by norm_num)
    let p := scale (centralDepth K) (rotate K (0,u))
    have hu₂ : u^2=1 := by rw [← sq_abs,hu]; norm_num
    have hx : localX K p = localX K (0,0) := by
      dsimp [p,scale,rotate,localX]
      ring
    have hy : localY K p = localY K (0,0)+centralDepth K*u := by
      dsimp [p,scale,rotate,localY]
      linear_combination centralDepth K*u*K.unit
    have hy₂ : (localY K p)^2=1/4 := by
      rw [hy]
      dsimp [centralDepth]
      rw [max_eq_right hxy]
      dsimp [beta]
      linear_combination (2*(1/2-|localY K (0,0)|))*hprod+(1/2-|localY K (0,0)|)^2*hu₂-
        sq_abs (localY K (0,0))
    have hyabs : |localY K p|=1/2 := by
      rw [(sq_eq_sq_iff_abs_eq_abs (localY K p) (1/2)).1 (by rw [hy₂]; norm_num)]; norm_num
    refine ⟨p,⟨by simpa [hx] using h.1.le,by rw [hyabs]⟩,?_,?_⟩
    · intro hp
      linarith only [hp.2, hyabs]
    · dsimp [p,scale,rotate,normSq]
      linear_combination (centralDepth K)^2*u^2*K.unit+(centralDepth K)^2*hu₂
  · have hyx : beta K (0,0) ≤ alpha K (0,0) := le_of_lt (lt_of_not_ge hxy)
    obtain ⟨u,hu,hprod⟩ := exists_signed (localX K (0,0)) (c := 1) (by norm_num)
    let p := scale (centralDepth K) (rotate K (u,0))
    have hu₂ : u^2=1 := by rw [← sq_abs,hu]; norm_num
    have hx : localX K p = localX K (0,0)+centralDepth K*u := by
      dsimp [p,scale,rotate,localX]
      linear_combination centralDepth K*u*K.unit
    have hy : localY K p = localY K (0,0) := by
      dsimp [p,scale,rotate,localY]
      ring
    have hx₂ : (localX K p)^2=1/4 := by
      rw [hx]
      dsimp [centralDepth]
      rw [max_eq_left hyx]
      dsimp [alpha]
      linear_combination (2*(1/2-|localX K (0,0)|))*hprod+(1/2-|localX K (0,0)|)^2*hu₂-
        sq_abs (localX K (0,0))
    have hxabs : |localX K p|=1/2 := by
      rw [(sq_eq_sq_iff_abs_eq_abs (localX K p) (1/2)).1 (by rw [hx₂]; norm_num)]; norm_num
    refine ⟨p,⟨by rw [hxabs],by simpa [hy] using h.2.le⟩,?_,?_⟩
    · intro hp
      linarith only [hp.1, hxabs]
    · dsimp [p,scale,rotate,normSq]
      linear_combination (centralDepth K)^2*u^2*K.unit+(centralDepth K)^2*hu₂

lemma translated_containment_reserve {S : Fin 8 → UnitSquare} {q δ : ℝ} {p : Point}
    (hp : SqPacking S (0,0) q) (hq : q ≤ Q0)
    (hδ : 0 ≤ δ ∧ δ ≤ 1/1000) (hpδ : normSq p = δ^2) :
    SqPacking S p (Q0+4/1000+(1/1000 : ℝ)^2) := by
  refine ⟨by norm_num [Q0],?_,hp.2.2⟩
  intro i z hz
  have hnorm : normSq z ≤ Q0 := by
    simpa [sub] using (hp.2.1 i z hz).trans hq
  have hc := cauchy_sq z p
  rw [hpδ] at hc
  have hm := mul_le_mul_of_nonneg_right hnorm (sq_nonneg δ)
  have hd : -2*δ ≤ dot z p := by
    have hQ : Q0 < 4 := radius_levels.2.2.2
    have hm' := mul_le_mul_of_nonneg_right hQ.le (sq_nonneg δ)
    by_contra! hh
    have hs := mul_pos (show 0 < -dot z p-2*δ by linarith)
      (show 0 < -dot z p+2*δ by linarith [hδ.1])
    linarith
  have he : normSq (sub z p) = normSq z-2*dot z p+normSq p := by
    dsimp [normSq,dot,sub]
    ring
  rw [he,hpδ]
  have hs := mul_nonneg (show 0 ≤ 1/1000-δ by linarith [hδ.2])
    (show 0 ≤ 1/1000+δ by linarith [hδ.1])
  linarith

/-- In a packing at squared radius at most `Q0`, the boundary of the square that contains the
origin is more than `1/1000` from the origin. Otherwise the disk of squared radius
`Q0 + 4/1000 + (1/1000)² < 98/25` about a nearest boundary point would hold the packing, and no
square would contain its centre in its interior. -/
theorem centralDepth_gt_milli {S : Fin 8 → UnitSquare} {q : ℝ} {i : Fin 8}
    (hp : SqPacking S (0,0) q) (hq : q ≤ Q0) (hi : openSquare (S i) (0,0)) :
    1/1000 < centralDepth (S i) := by
  by_contra! hδ
  obtain ⟨p,hclosed,hnot,hdist⟩ := centralDepth_boundary_point hi
  have htranslated := translated_containment_reserve hp hq
    ⟨(centralDepth_pos hi).le,hδ⟩ hdist
  obtain ⟨j,hj,_⟩ := central_square_exists_at htranslated translated_ceiling_reserve.le
  by_cases hij : i=j
  · subst j
    exact hnot hj
  · exact open_closed_disjoint (hp.2.2 j i (Ne.symm hij)) p ⟨hj,hclosed⟩

lemma exterior_distance_from_centralDepth {S : Fin 8 → UnitSquare} {i j : Fin 8}
    (hd : InteriorDisjoint S) (hi : openSquare (S i) (0,0)) (hij : i ≠ j) :
    centralDepth (S i)^2 ≤ coreDistanceSq (S j) := by
  obtain ⟨p,hp,he⟩ := coreDistanceSq_attained (S j)
  by_contra! hh
  have hin : openSquare (S i) p := centralDepth_disk hi (by simpa [he] using hh)
  exact open_closed_disjoint (hd i j hij) p ⟨hin,hp⟩

lemma primary_distance_lower {K : UnitSquare} {δ : ℝ}
    (hδ : 0 < δ) (hd : δ^2 ≤ coreDistanceSq K) :
    1/2 < max (alpha K (0,0)) (beta K (0,0)) ∧
    δ^2 ≤ 2*(max (alpha K (0,0)) (beta K (0,0))-1/2)^2 := by
  let A := max (alpha K (0,0)) (beta K (0,0))
  have hx : alpha K (0,0) ≤ A := le_max_left _ _
  have hy : beta K (0,0) ≤ A := le_max_right _ _
  have hA : 1/2 < A := by
    by_contra! h
    have hα : max (alpha K (0,0)-1/2) 0=0 := max_eq_right (by linarith)
    have hβ : max (beta K (0,0)-1/2) 0=0 := max_eq_right (by linarith)
    dsimp [coreDistanceSq] at hd
    rw [hα,hβ] at hd
    nlinarith only [hd, hδ]
  have hα : max (alpha K (0,0)-1/2) 0 ≤ A-1/2 := max_le (by linarith) (by linarith)
  have hβ : max (beta K (0,0)-1/2) 0 ≤ A-1/2 := max_le (by linarith) (by linarith)
  have hx₂ := pow_le_pow_left₀ (le_max_right _ _) hα 2
  have hy₂ := pow_le_pow_left₀ (le_max_right _ _) hβ 2
  exact ⟨hA,by dsimp [coreDistanceSq] at hd; linarith⟩

theorem exterior_primary_bandA {S : Fin 8 → UnitSquare} {q : ℝ} {i j : Fin 8}
    (hp : SqPacking S (0,0) q) (hq : q ≤ Q0) (hi : openSquare (S i) (0,0))
    (hij : i ≠ j) : 5007/10000 < max (alpha (S j) (0,0)) (beta (S j) (0,0)) := by
  have hδ := centralDepth_gt_milli hp hq hi
  have hd := exterior_distance_from_centralDepth hp.2.2 hi hij
  obtain ⟨hA,hA₂⟩ := primary_distance_lower (centralDepth_pos hi) hd
  by_contra! hn
  nlinarith only [hA₂, hn, hδ, hA]

theorem exterior_primary_bandB {S : Fin 8 → UnitSquare} {i j : Fin 8}
    (hd : InteriorDisjoint S) (hi : openSquare (S i) (0,0)) (hij : i ≠ j)
    (hshallow : max (alpha (S i) (0,0)) (beta (S i) (0,0)) ≤ 9/20) :
    107/200 < max (alpha (S j) (0,0)) (beta (S j) (0,0)) := by
  have hδ : 1/20 ≤ centralDepth (S i) := by dsimp [centralDepth]; linarith
  have hd' := exterior_distance_from_centralDepth hd hi hij
  obtain ⟨hA,hA₂⟩ := primary_distance_lower (centralDepth_pos hi) hd'
  by_contra! hn
  nlinarith only [hδ, hA₂, hn, hA]

namespace CentralBand

structure RayData (K : UnitSquare) where
  chart : SquareChart K (0,0)
  sorted : chart.b ≤ chart.a
  radius : ℝ
  angle : ℝ
  radius_pos : 0 < radius
  angle_range : 0 ≤ angle ∧ angle ≤ Real.pi/4
  primary : radius*Real.cos angle = chart.a
  secondary : radius*Real.sin angle = chart.b

lemma RayData.primary_max {K : UnitSquare} (R : RayData K) :
    R.chart.a = max (alpha K (0,0)) (beta K (0,0)) := by
  rcases R.chart.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [← ha,← hb,max_eq_left R.sorted]
  · rw [← hb,← ha,max_eq_right R.sorted]

lemma ray_data_exists (K : UnitSquare)
    (h : 0 < max (alpha K (0,0)) (beta K (0,0))) : Nonempty (RayData K) := by
  obtain ⟨C,hsort⟩ := sorted_square_chart K (0,0)
  have hmax : C.a = max (alpha K (0,0)) (beta K (0,0)) := by
    rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [← ha,← hb,max_eq_left hsort]
    · rw [← hb,← ha,max_eq_right hsort]
  have ha : 0 < C.a := by simpa [hmax] using h
  by_cases hb : C.b=0
  · exact ⟨⟨C,hsort,C.a,0,ha,⟨by norm_num,by positivity⟩,
      by simp,by simp [hb]⟩⟩
  · have hb' : 0 < C.b := lt_of_le_of_ne C.nonneg.2 (Ne.symm hb)
    obtain ⟨r,θ,hr,hθ,hθq,_,hc,hs⟩ := first_octant_polar ha hb' hsort
    exact ⟨⟨C,hsort,r,θ,hr,⟨hθ.le,hθq⟩,hc,hs⟩⟩

def RayData.direction {K : UnitSquare} (R : RayData K) : Direction :=
  chartAngle R.chart.phase R.chart.reversed R.angle

lemma RayData.quadrant {K : UnitSquare} (R : RayData K) :
    Quadrant (Real.cos R.angle) (Real.sin R.angle) := by
  have hh := cos_sin_nonneg ⟨R.angle_range.1,by linarith [R.angle_range.2,Real.pi_pos]⟩
  exact ⟨hh.1,hh.2,by linarith [Real.sin_sq_add_cos_sq R.angle]⟩

lemma RayData.segment {K : UnitSquare} (R : RayData K)
    (ha : 1/2 < R.chart.a) (hc : SqContained Q0 K) :
    ∀ v, |v| ≤ 7/20 → openSquare K (pointInDirection (0,0) R.direction (11/12) v) := by
  have hφ : phi (R.radius*Real.cos R.angle) (R.radius*Real.sin R.angle) ≤ Q0 := by
    rw [R.primary,R.secondary]
    exact chart_phi R.chart hc
  have hsides (v : ℝ) (hv : |v| ≤ 7/20) := transverse_segment_sides R.quadrant
    (sin_le_cos_of_small R.angle_range) R.radius_pos.le (by simpa [R.primary] using ha) hφ hv
  intro v hv
  cases hrev : R.chart.reversed
  · have h := hsides (-v) (by simpa using hv)
    have he : pointInDirection (0,0) R.direction (11/12) v =
        pointInDirection (0,0) R.chart.phase
          ((11/12)*Real.cos R.angle-v*Real.sin R.angle)
          ((11/12)*Real.sin R.angle+v*Real.cos R.angle) := by
      apply Prod.ext <;>
        simp [RayData.direction,chartAngle,hrev,pointInDirection,Real.Angle.cos_add,Real.Angle.sin_add] <;> ring
    rw [he,R.chart.cartesian]
    simp only [SquareChart.signedB,hrev,Bool.false_eq_true,ite_false]
    rw [← R.primary,← R.secondary]
    constructor
    · convert h.1 using 2
      ring
    · convert h.2 using 1
      rw [← abs_neg]
      congr 1
      ring
  · have h := hsides v hv
    have he : pointInDirection (0,0) R.direction (11/12) v =
        pointInDirection (0,0) R.chart.phase
          ((11/12)*Real.cos R.angle+v*Real.sin R.angle)
          (-(11/12)*Real.sin R.angle+v*Real.cos R.angle) := by
      apply Prod.ext <;>
        simp [RayData.direction,chartAngle,hrev,pointInDirection,Real.Angle.cos_add,Real.Angle.sin_add] <;> ring
    rw [he,R.chart.cartesian]
    simp only [SquareChart.signedB,hrev,ite_true]
    rw [← R.primary,← R.secondary]
    simpa only [sub_neg_eq_add] using h

lemma RayData.direction_parameter {K : UnitSquare} (R : RayData K) (θ : Direction) :
    let t := (θ-R.direction).toReal
    chartAngle R.chart.phase R.chart.reversed
      (R.angle+(if R.chart.reversed then -t else t)) = θ := by
  intro t
  have ht : ((t : ℝ) : Direction) = θ-R.direction := Real.Angle.coe_toReal _
  have hdir : R.direction = chartAngle R.chart.phase R.chart.reversed R.angle := rfl
  cases hrev : R.chart.reversed
  · rw [hrev] at hdir
    simp only [chartAngle,Bool.false_eq_true,ite_false] at hdir ⊢
    rw [Real.Angle.coe_add,ht,hdir]
    abel
  · rw [hrev] at hdir
    simp only [chartAngle,ite_true] at hdir ⊢
    rw [show -(R.angle+-t) = -R.angle+t by ring,Real.Angle.coe_add,ht,hdir]
    abel

lemma RayData.common_point_A {K : UnitSquare} (R : RayData K)
    (ha : 5007/10000 < R.chart.a) (hc : SqContained Q0 K) :
    ∀ θ, dist θ R.direction ≤ 3741/10000 →
      openSquare K (circlePoint (0,0) (10007/10000) θ) := by
  intro θ hθ
  let t := (θ-R.direction).toReal
  let β := if R.chart.reversed then -t else t
  have hβ : |β| ≤ 3741/10000 := by
    have ht : |t| ≤ 3741/10000 := by
      rw [direction_dist] at hθ
      exact hθ
    show |if R.chart.reversed then -t else t| ≤ 3741/10000
    split_ifs
    · rw [abs_neg]
      exact ht
    · exact ht
  have hs := bandA_sides R.angle_range hβ R.radius_pos.le
    (by simpa [R.primary] using ha)
    (by rw [R.primary,R.secondary]; exact chart_phi R.chart hc)
  rw [← R.direction_parameter θ,R.chart.membership]
  rw [← R.primary,← R.secondary]
  refine ⟨hs.1,?_⟩
  rw [← abs_neg]
  convert hs.2 using 2
  ring

lemma RayData.common_point_B {K : UnitSquare} (R : RayData K)
    (ha : 107/200 ≤ R.chart.a) (hc : SqContained Q0 K) :
    ∀ θ, dist θ R.direction ≤ 19/50 →
      openSquare K (circlePoint (0,0) (41/40) θ) := by
  intro θ hθ
  let t := (θ-R.direction).toReal
  let β := if R.chart.reversed then -t else t
  have hβ : |β| ≤ 19/50 := by
    have ht : |t| ≤ 19/50 := by
      rw [direction_dist] at hθ
      exact hθ
    show |if R.chart.reversed then -t else t| ≤ 19/50
    split_ifs
    · rw [abs_neg]
      exact ht
    · exact ht
  have hs := bandB_sides R.angle_range hβ R.radius_pos.le
    (by simpa [R.primary] using ha)
    (by rw [R.primary,R.secondary]; exact chart_phi R.chart hc)
  rw [← R.direction_parameter θ,R.chart.membership]
  rw [← R.primary,← R.secondary]
  refine ⟨hs.1,?_⟩
  rw [← abs_neg]
  convert hs.2 using 2
  ring

lemma closed_caps_strictly_separated {K J : UnitSquare} {θ φ : Direction} {r h : ℝ}
    (hK : ∀ ψ, dist ψ θ ≤ h → openSquare K (circlePoint (0,0) r ψ))
    (hJ : ∀ ψ, dist ψ φ ≤ h → openSquare J (circlePoint (0,0) r ψ))
    (hd : ∀ p, ¬ (openSquare K p ∧ openSquare J p)) : 2*h < dist θ φ := by
  by_contra! hn
  let t := (φ-θ).toReal
  let ψ : Direction := θ+((t/2 : ℝ) : Direction)
  have ht : |t| ≤ 2*h := by
    rw [dist_comm,direction_dist] at hn
    exact hn
  have hψθ : dist ψ θ ≤ h := by
    have hb := direction_coe_norm_le (t/2)
    have he : ψ-θ=((t/2 : ℝ) : Direction) := by dsimp [ψ]; abel
    rw [dist_eq_norm,he]
    exact hb.trans (by rw [abs_div]; norm_num; linarith)
  have hψφ : dist ψ φ ≤ h := by
    have hb := direction_coe_norm_le (-t/2)
    have he : ψ-φ=((-t/2 : ℝ) : Direction) := by
      rw [direction_offset φ θ]
      dsimp [ψ,t]
      rw [show (-((φ-θ).toReal)/2 : ℝ)=((φ-θ).toReal)/2-((φ-θ).toReal) by ring,
        Real.Angle.coe_sub]
      abel
    rw [dist_eq_norm,he]
    exact hb.trans (by rw [abs_div,abs_neg]; norm_num; linarith)
  exact hd _ ⟨hK ψ hψθ,hJ ψ hψφ⟩

end CentralBand

def chartPoint {K : UnitSquare} (C : SquareChart K (0,0)) (x y : ℝ) : Point :=
  pointInDirection (0,0) C.phase x (if C.reversed then -y else y)

lemma chartPoint_closed {K : UnitSquare} (C : SquareChart K (0,0)) (x y : ℝ) :
    closedSquare K (chartPoint C x y) ↔ |x-C.a| ≤ 1/2 ∧ |y-C.b| ≤ 1/2 := by
  obtain ⟨r,t,hx,hy⟩ := plane_polar x y
  have he : chartPoint C x y=circlePoint (0,0) r (chartAngle C.phase C.reversed t) := by
    rw [← hx,← hy]
    cases hrev : C.reversed <;>
      apply Prod.ext <;> simp [chartPoint,chartAngle,hrev,pointInDirection,circlePoint,
        Real.Angle.cos_add,Real.Angle.sin_add] <;> ring
  rw [he,SquareChart.closed_membership C,hx,hy]

lemma chartPoint_segment {K : UnitSquare} (C : SquareChart K (0,0)) (β v : ℝ) :
    chartPoint C (pointInDirection (0,0) (β : Direction) (11/12) v).1
      (pointInDirection (0,0) (β : Direction) (11/12) v).2 =
    pointInDirection (0,0) (chartAngle C.phase C.reversed β) (11/12)
      (if C.reversed then -v else v) := by
  cases hrev : C.reversed <;>
    apply Prod.ext <;> simp [chartPoint,chartAngle,hrev,pointInDirection,
      Real.Angle.cos_add,Real.Angle.sin_add] <;> ring

/-- A forbidden closed interval leaves only one complementary arc for the
seven rays. Sorting their representatives in that arc produces six strict
gaps. -/
lemma seven_rays_avoid_interval_budget (rays : Vertex → Direction)
    {phase : Direction} {reversed : Bool} {l u g : ℝ}
    (hwidth : 0 < u-l ∧ u-l ≤ 4)
    (hsep : ∀ i j, i ≠ j → g < dist (rays i) (rays j))
    (havoid : ∀ i β, l ≤ β ∧ β ≤ u → rays i ≠ chartAngle phase reversed β) :
    (u-l)+6*g < 2*Real.pi := by
  let mid := (l+u)/2
  let center := chartAngle phase reversed mid
  have hfar (i : Vertex) : (u-l)/2 < dist (rays i) center := by
    by_contra! hn
    let t := (rays i-center).toReal
    let β := mid+(if reversed then -t else t)
    have ht : |t| ≤ (u-l)/2 := by simpa [direction_dist,t] using hn
    have hβ : l ≤ β ∧ β ≤ u := by
      rcases abs_le.mp ht with ⟨hl,hu⟩
      cases reversed <;> dsimp [β,mid] <;> constructor <;> linarith only [hl, hu]
    apply havoid i β hβ
    have he : ((t : ℝ) : Direction) = rays i-center := Real.Angle.coe_toReal _
    have hshift : chartAngle phase reversed β = center+((t : ℝ) : Direction) := by
      cases reversed
      · simp only [β,center,chartAngle,Bool.false_eq_true,ite_false,Real.Angle.coe_add]
        abel
      · simp only [β,center,chartAngle,ite_true,neg_add,neg_neg,Real.Angle.coe_add]
        abel
    rw [hshift,he]
    abel
  let t : Vertex → ℝ := fun i => (rays i-center).toReal
  let p : Vertex → ℝ := fun i => if t i < 0 then t i+2*Real.pi else t i
  have hp (i : Vertex) : (u-l)/2 < p i ∧ p i < 2*Real.pi-(u-l)/2 := by
    have ht : (u-l)/2 < |t i| := by simpa [direction_dist,t] using hfar i
    have hl := Real.Angle.neg_pi_lt_toReal (rays i-center)
    have hu := Real.Angle.toReal_le_pi (rays i-center)
    have hw : (u-l)/2 < Real.pi := by linarith only [hwidth.2, Real.pi_gt_three]
    by_cases h : t i < 0
    · simp only [p,ite_eq_left h,abs_of_neg h] at *
      dsimp [t] at *
      constructor <;> linarith only [hl, ht]
    · simp only [p,ite_eq_right h,abs_of_nonneg (le_of_not_gt h)] at *
      dsimp [t] at *
      constructor <;> linarith only [ht, hu, hw]
  have hrepr (i : Vertex) : rays i=center+(p i : Direction) := by
    rw [direction_offset (rays i) center]
    dsimp [p]
    split_ifs
    · simp [Real.Angle.coe_add,Real.Angle.coe_two_pi,t]
    · rfl
  let σ := Tuple.sort p
  let z : Vertex → ℝ := fun i => p (σ i)
  have hz : Monotone z := Tuple.monotone_sort p
  have hstep (i : Fin 6) : g < z i.succ-z i.castSucc := by
    have h := hsep (σ i.succ) (σ i.castSucc) (σ.injective.ne i.castSucc_lt_succ.ne')
    rw [hrepr,hrepr,dist_eq_norm] at h
    have he : center+(p (σ i.succ) : Direction)-(center+(p (σ i.castSucc) : Direction)) =
        ((z i.succ-z i.castSucc : ℝ) : Direction) := by
      dsimp only [z]
      rw [Real.Angle.coe_sub]
      abel
    rw [he] at h
    have hb := direction_coe_norm_le (z i.succ-z i.castSucc)
    rw [abs_of_nonneg (sub_nonneg.mpr (hz i.castSucc_lt_succ.le))] at hb
    exact h.trans_le hb
  have hsum := Finset.sum_lt_sum (s := Finset.univ)
    (fun i _ => (hstep i).le) ⟨0,Finset.mem_univ _,hstep 0⟩
  have htel : (∑ i : Fin 6, (z i.succ-z i.castSucc))=z 6-z 0 := by
    norm_num [Fin.sum_univ_succ]
    ring
  rw [htel] at hsum
  norm_num at hsum
  have hlo := (hp (σ 0)).1
  have hhi := (hp (σ 6)).2
  dsimp [z] at hsum
  linarith only [hsum, hlo, hhi]

lemma central_rectangle_forbids {K : UnitSquare} (C : SquareChart K (0,0))
    {A l u : ℝ} (hinside : C.a < 1/2 ∧ C.b < 1/2) (hreach : A ≤ C.a+1/2)
    (hrectangle : ∀ β, l ≤ β ∧ β ≤ u → ∃ v, |v| ≤ 7/20 ∧
      let p := pointInDirection (0,0) (β : Direction) (11/12) v
      0 ≤ p.1 ∧ p.1 ≤ A ∧ -(1/2-C.b) ≤ p.2 ∧ p.2 ≤ 1-(1/2-C.b))
    {J : UnitSquare} (ray : Direction)
    (hsegment : ∀ v, |v| ≤ 7/20 → openSquare J (pointInDirection (0,0) ray (11/12) v))
    (hd : ∀ p, ¬ (openSquare J p ∧ openSquare K p)) :
    ∀ β, l ≤ β ∧ β ≤ u → ray ≠ chartAngle C.phase C.reversed β := by
  intro β hβ he
  obtain ⟨v,hv,hx₀,hx₁,hy₀,hy₁⟩ := hrectangle β hβ
  let p := pointInDirection (0,0) (β : Direction) (11/12) v
  have hclosed : closedSquare K (chartPoint C p.1 p.2) := by
    rw [chartPoint_closed]
    constructor <;> apply abs_le.mpr <;> constructor <;>
      linarith [C.nonneg.1,C.nonneg.2]
  have hmem := hsegment (if C.reversed then -v else v)
    (by cases C.reversed <;> simpa using hv)
  rw [he,← chartPoint_segment C β v] at hmem
  exact open_closed_disjoint hd _ ⟨hmem,hclosed⟩

/-- The one-twelfth core: in a packing at squared radius at most `Q0`, one square contains the
closed disk of radius `1/12` about the origin in its interior, and every other closed square is at
distance more than `1/12` from the origin. The central square comes from the two-circle
inequality, the rays of the exterior squares from their charts, and the forbidden intervals from
`CentralForbidden.bandA_forbidden` and `CentralForbidden.bandB_forbidden`. -/
theorem central_core_and_exteriors {S : Fin 8 → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0,0) q) (hq : q ≤ Q0) :
    ∃ i : Fin 8, ContainsCore (S i) ∧
      ∀ j, i ≠ j → StrictCoreAvoiding (S j) := by
  obtain ⟨i,hi,_⟩ := central_square_exists hp
    (hq.trans (by norm_num [Q0] : Q0 ≤ 98/25))
  obtain ⟨C,hsort⟩ := sorted_square_chart (S i) (0,0)
  have hmax : C.a=max (alpha (S i) (0,0)) (beta (S i) (0,0)) := by
    rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [← ha,← hb,max_eq_left hsort]
    · rw [← hb,← ha,max_eq_right hsort]
  let E : Vertex → UnitSquare := fun j => S (i.succAbove j)
  have hne (j : Vertex) : i ≠ i.succAbove j := (Fin.succAbove_ne i j).symm
  have hEdisjoint : InteriorDisjoint E := by
    intro j k hjk p h
    exact hp.2.2 _ _ (Fin.succAbove_right_injective.ne hjk) p h
  have hEcontain (j : Vertex) : SqContained Q0 (E j) := by
    apply (SqContained.iff_points (by norm_num [Q0]) _).2
    intro p h
    simpa [sub] using (hp.2.1 (i.succAbove j) p h).trans hq
  have hprimary (j : Vertex) : 5007/10000 < max (alpha (E j) (0,0)) (beta (E j) (0,0)) :=
    exterior_primary_bandA hp hq hi (hne j)
  let R : (j : Vertex) → CentralBand.RayData (E j) := fun j =>
    Classical.choice (CentralBand.ray_data_exists (E j) (by linarith only [hprimary j, hprimary]))
  let rays : Vertex → Direction := fun j => (R j).direction
  have hsegments (j : Vertex) :
      ∀ v, |v| ≤ 7/20 → openSquare (E j) (pointInDirection (0,0) (rays j) (11/12) v) := by
    apply (R j).segment
    · rw [(R j).primary_max]
      linarith only [hprimary j, hprimary]
    · exact hEcontain j
  have hcore_a : C.a < 5/12 := by
    by_contra! ha
    let d := 1/2-C.b
    have hd : 0 ≤ d ∧ d ≤ 1/2 := by
      have hc := C.origin.mp hi
      dsimp [d]
      constructor <;> linarith only [C.nonneg.2, hsort, hc]
    by_cases hband : C.a ≤ 9/20
    · obtain ⟨l,u,hl,hu,hw,hw₄,hrect⟩ := CentralForbidden.bandA_forbidden hd
      have hsep (j k : Vertex) (hjk : j ≠ k) : 19/25 < dist (rays j) (rays k) := by
        have hj := exterior_primary_bandB hp.2.2 hi (hne j) (by simpa [← hmax] using hband)
        have hk := exterior_primary_bandB hp.2.2 hi (hne k) (by simpa [← hmax] using hband)
        have h := CentralBand.closed_caps_strictly_separated
          ((R j).common_point_B (by simpa [(R j).primary_max] using hj.le) (hEcontain j))
          ((R k).common_point_B (by simpa [(R k).primary_max] using hk.le) (hEcontain k))
          (hEdisjoint j k hjk)
        norm_num at h
        exact h
      have havoid (j : Vertex) := central_rectangle_forbids C (C.origin.mp hi)
        (show (11/12 : ℝ) ≤ C.a+1/2 by linarith only [ha])
        (by simpa [CentralForbidden.L,CentralForbidden.c,d] using hrect)
        (rays j) (hsegments j) (hp.2.2 (i.succAbove j) i (hne j).symm)
      have hb := seven_rays_avoid_interval_budget rays ⟨by linarith only [hw],hw₄⟩ hsep havoid
      linarith only [pi_lt_22_over_7, hw, hb]
    · obtain ⟨l,u,hl,hu,hw,hw₄,hrect⟩ := CentralForbidden.bandB_forbidden hd
      have hsep (j k : Vertex) (hjk : j ≠ k) : 3741/5000 < dist (rays j) (rays k) := by
        have h := CentralBand.closed_caps_strictly_separated
          ((R j).common_point_A (by simpa [(R j).primary_max] using hprimary j) (hEcontain j))
          ((R k).common_point_A (by simpa [(R k).primary_max] using hprimary k) (hEcontain k))
          (hEdisjoint j k hjk)
        norm_num at h
        exact h
      have havoid (j : Vertex) := central_rectangle_forbids C (C.origin.mp hi)
        (show (19/20 : ℝ) ≤ C.a+1/2 by linarith only [hband])
        (by simpa [CentralForbidden.L,CentralForbidden.c,d] using hrect)
        (rays j) (hsegments j) (hp.2.2 (i.succAbove j) i (hne j).symm)
      have hb := seven_rays_avoid_interval_budget rays ⟨by linarith only [hw],hw₄⟩ hsep havoid
      linarith only [pi_lt_22_over_7, hw, hb]
  have hmax' : max (alpha (S i) (0,0)) (beta (S i) (0,0)) < 5/12 := by
    rw [← hmax]
    exact hcore_a
  have hcore : ContainsCore (S i) := containsCore_of_center_bounds
    ((le_max_left _ _).trans_lt hmax') ((le_max_right _ _).trans_lt hmax')
  exact ⟨i,hcore,fun j hij => strictCoreAvoiding_of_containsCore hcore (hp.2.2 i j hij)⟩

end SquaresInCircles.Eight

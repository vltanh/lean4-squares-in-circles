import SquaresInCircles.Six.Normalization.Caps
import SquaresInCircles.Six.Normalization.CentralSquare
import SquaresInCircles.Common.Trigonometry

/-!
# The pins

The pins are the five points at distance `9/10` from the origin in the
directions `0`, `π/2`, `11π/12`, `5π/4` and `19π/12`; the reflection in the
diagonal exchanges those of E and N, and of W and S. In the frame of the central
square, with its centre in `[0, c0]²`, every exterior square holds a pin
(`five_pin_cover`), and its phase lies in a quadrant about one of the sides of
C, with finer conditions on the pins it may hold there (`PinLocation`). A square
separated from C along a side lies in a deep cap beyond it and faces it; beyond
a side at least `1/2` deep it contains the point `(h + 1/2, 0)` and with it the
pin. A square separated along its own axis is confined by concave profiles of
its radial coordinate against `a ≤ ρ0`: near the east axis its phase lies in
`(-5/12, 3/10)` and a completed square in its transverse coordinate keeps the
east pin inside; near the west axis it holds the pin of W or of D, by the
sixty-degree lemma (two points `π/3` apart at distance `9/10`) or, on the left
flank, by a completed square. North and south are the reflections of east and
west in the diagonal, and the secondary axes never separate. Disjoint squares
hold distinct pins, so each holds exactly one, which is its label; holding no
other pin puts its phase in the window of its label (`labelled_window`), and the
coordinates of the pins give the axes along which it may be separated
(`allowed_axis_of_pin`).
-/

noncomputable section

namespace SquaresInCircles.Six.Normalization
noncomputable def pin (i : Fin 5) : Point :=
  ![(9/10,0),(0,9/10),
    ((9/10)*Real.cos ((11/12)*Real.pi),(9/10)*Real.sin ((11/12)*Real.pi)),
    ((9/10)*Real.cos ((5/4)*Real.pi),(9/10)*Real.sin ((5/4)*Real.pi)),
    ((9/10)*Real.cos ((19/12)*Real.pi),(9/10)*Real.sin ((19/12)*Real.pi))] i

/-- The phases of E, N, W, D, S in the model: the centres of their windows. -/
noncomputable def modelPhase : Fin 5 → ℝ := ![0,Real.pi/2,Real.pi,5*Real.pi/4,3*Real.pi/2]

/-- The windows of the phases about their centres: `(-5/12, 3/10)` for E,
`(-3/10, 5/12)` for N, `(-2/3, 5/8)` for W, `(-15/14, 15/14)` for D and
`(-5/8, 2/3)` for S. -/
def windowLower : Fin 5 → ℚ := ![-5/12,-3/10,-2/3,-15/14,-5/8]
def windowUpper : Fin 5 → ℚ := ![3/10,5/12,5/8,15/14,2/3]

/-- The axes along which a square with each label may be separated from C. -/
def allowed : Fin 5 → List CentralAxis :=
  ![[.own,.east],[.own,.north],[.own,.west],[.own,.west,.south],[.own,.south]]

end SquaresInCircles.Six.Normalization

namespace SquaresInCircles.Six.Normalization

/-- If each of five interior-disjoint squares holds a pin, a permutation `σ`
labels them: the square `σ j` holds the pin `j`, no other square holds the
pin `j`, and the square `σ j` holds no other pin. -/
theorem pin_labels_of_covering (S : Fin 5 → UnitSquare) (pins : Fin 5 → Point)
    (hd : InteriorDisjoint S)
    (hcover : ∀ i, ∃ j, openSquare (S i) (pins j)) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ j,
      openSquare (S (σ j)) (pins j) ∧
      (∀ i, openSquare (S i) (pins j) → i = σ j) ∧
      (∀ k, openSquare (S (σ j)) (pins k) → k = j) := by
  classical
  choose f hf using hcover
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hj : openSquare (S j) (pins (f i)) := by rw [hij]; exact hf j
    exact hd i j hne (pins (f i)) ⟨hf i, hj⟩
  let e : Equiv.Perm (Fin 5) := Equiv.ofBijective f hinj.bijective_of_finite
  have hmem (j : Fin 5) : openSquare (S (e.symm j)) (pins j) := by
    simpa only [show f (e.symm j) = j from e.apply_symm_apply j] using hf (e.symm j)
  refine ⟨e.symm, ?_⟩
  intro j
  refine ⟨hmem j, ?_, ?_⟩
  · intro i hi
    by_contra hne
    exact hd i (e.symm j) hne (pins j) ⟨hi, hmem j⟩
  · intro k hk
    have he : e.symm j = e.symm k := by
      by_contra hne
      exact hd (e.symm j) (e.symm k) hne (pins k) ⟨hk, hmem k⟩
    exact (e.symm.injective he).symm

/-! ### The pins in polar form -/

/-- The relabelling by the reflection in the diagonal: it exchanges E and N, and
W and S, and keeps D. -/
def mirrorPin : Equiv.Perm (Fin 5) where
  toFun := ![1,0,4,3,2]
  invFun := ![1,0,4,3,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The directions of the pins: `0`, `π/2`, `11π/12`, `5π/4` and `19π/12`. -/
def pinAngle : Fin 5 → ℝ :=
  ![0,Real.pi/2,11*Real.pi/12,5*Real.pi/4,19*Real.pi/12]

lemma mirror_pin_angle (i : Fin 5) :
    (pinAngle (mirrorPin i) : Direction) = (Real.pi/2-pinAngle i : ℝ) := by
  apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr
  fin_cases i
  · exact ⟨0,by norm_num [pinAngle,mirrorPin]⟩
  · exact ⟨0,by norm_num [pinAngle,mirrorPin]⟩
  · exact ⟨1,by dsimp [pinAngle,mirrorPin]; ring⟩
  · exact ⟨1,by dsimp [pinAngle,mirrorPin]; ring⟩
  · exact ⟨1,by dsimp [pinAngle,mirrorPin]; ring⟩

lemma pin_polar (i : Fin 5) :
    pin i = ((9/10)*Real.cos (pinAngle i),(9/10)*Real.sin (pinAngle i)) := by
  fin_cases i <;> simp [pin,pinAngle] <;> constructor <;> ring_nf

/-- The reflection in the diagonal exchanges the pins of E and N, and of W and
S, and fixes the pin of D. -/
lemma pin_diagonal (i : Fin 5) : Six.diagonalPoint (pin i) = pin (mirrorPin i) := by
  have hc := congrArg (fun z : Direction => z.cos) (mirror_pin_angle i)
  have hs := congrArg (fun z : Direction => z.sin) (mirror_pin_angle i)
  simp only [Real.Angle.cos_coe,Real.Angle.sin_coe,Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub] at hc hs
  rw [pin_polar,pin_polar]
  apply Prod.ext <;> simp only [Six.diagonalPoint,hc,hs]

end SquaresInCircles.Six.Normalization

namespace SquaresInCircles.Six
open Normalization

/-- The point at distance `r` from the origin in the direction `t`. -/
def polar (r t : ℝ) : Point := (r*Real.cos t,r*Real.sin t)

lemma polar_localX (r q t a b : ℝ) :
    localX (orientedSquare t a b) (polar r q) = r*Real.cos (q-t)-a := by
  rw [orientedSquare_localX,Real.cos_sub]
  dsimp [polar]
  ring

lemma polar_localY (r q t a b : ℝ) :
    localY (orientedSquare t a b) (polar r q) = r*Real.sin (q-t)-b := by
  rw [orientedSquare_localY,Real.sin_sub]
  dsimp [polar]
  ring

lemma polar_mem_iff (r q t a b : ℝ) :
    openSquare (orientedSquare t a b) (polar r q) ↔
      |r*Real.cos (q-t)-a|<1/2 ∧ |r*Real.sin (q-t)-b|<1/2 := by
  simp only [openSquare,polar_localX,polar_localY]

lemma pin_eq_polar (i : Fin 5) : pin i=polar (9/10) (pinAngle i) := by
  rw [pin_polar]
  rfl

/-! ### Phases -/

open Normalization

lemma square_phase_open {t u a b : ℝ} (h:(t:Direction)=(u:Direction)) (p:Point) :
    openSquare (orientedSquare t a b) p ↔ openSquare (orientedSquare u a b) p := by
  have hc := congrArg (fun z:Direction => z.cos) h
  have hs := congrArg (fun z:Direction => z.sin) h
  simp only [Real.Angle.cos_coe,Real.Angle.sin_coe] at hc hs
  simp only [openSquare,orientedSquare_localX,orientedSquare_localY,hc,hs]

lemma margin_phase_eq {t u : ℝ} (h:(t:Direction)=(u:Direction))
    (k:CentralAxis) (a b cx cy:ℝ) : centralMargin k t a b cx cy=centralMargin k u a b cx cy := by
  have hc := congrArg (fun z:Direction => z.cos) h
  have hs := congrArg (fun z:Direction => z.sin) h
  simp only [Real.Angle.cos_coe,Real.Angle.sin_coe] at hc hs
  cases k <;> simp only [centralMargin,centralNormal,centralTransverse,centerX,centerY,
    angularWidth,hc,hs]

lemma own_margin_diagonal_identity (t a b cx cy:ℝ) :
    centralMargin .own (Real.pi/2-t) a (-b) cy cx=centralMargin .own t a b cx cy := by
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub]
  ring

lemma square_diagonal_membership (t a b:ℝ) (p:Point) :
    openSquare (orientedSquare (Real.pi/2-t) a (-b)) p ↔
      openSquare (orientedSquare t a b) (Six.diagonalPoint p) := by
  have hx : localX (orientedSquare (Real.pi/2-t) a (-b)) p=
      localX (orientedSquare t a b) (Six.diagonalPoint p) := by
    simp only [orientedSquare_localX,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,
      Six.diagonalPoint]
    ring
  have hy : localY (orientedSquare (Real.pi/2-t) a (-b)) p=
      -localY (orientedSquare t a b) (Six.diagonalPoint p) := by
    simp only [orientedSquare_localY,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,
      Six.diagonalPoint]
    ring
  simp only [openSquare,hx,hy,abs_neg]

/-- Two lifts of one direction, within `π` of `c` and strictly within `π` of
`c`, are equal. -/
lemma phase_eq_in_centered_window {t u c:ℝ}
    (ht:-Real.pi≤t-c ∧ t-c≤Real.pi) (hu:|u-c|<Real.pi)
    (he:(t:Direction)=(u:Direction)) : t=u := by
  apply phase_eq_of_short_difference he
  have h1 : |t-c|≤Real.pi := abs_le.mpr ht
  have h2 := abs_sub (t-c) (u-c)
  have hid : (t-c)-(u-c)=t-u := by ring
  rw [hid] at h2
  linarith

/-! ### Two pins `π/3` apart -/

open Normalization

/-- The chord bound `1 - v/2 ≤ cos v` on `[0, π/3]`. -/
lemma cos_sixty_chord {v : ℝ} (hv0 : 0≤v) (hv1 : v≤Real.pi/3) :
    1-v/2≤Real.cos v := by
  by_cases hv : v≤1
  · have hp := mul_nonneg hv0 (sub_nonneg.mpr hv)
    nlinarith [Real.one_sub_sq_div_two_le_cos (x:=v)]
  · have hc := Real.cos_le_cos_of_nonneg_of_le_pi hv0
      (show Real.pi/3≤Real.pi by linarith [Real.pi_pos]) hv1
    rw [Real.cos_pi_div_three] at hc
    linarith

lemma sixty_sine_sum (v : ℝ) :
    Real.sin v+Real.sin (Real.pi/3-v)=Real.cos (v-Real.pi/6) := by
  calc
    _ = Real.sin ((v-Real.pi/6)+Real.pi/6)+
        Real.sin (Real.pi/6-(v-Real.pi/6)) := by congr 1 <;> congr 1 <;> ring
    _ = _ := by rw [Real.sin_add,Real.sin_sub (Real.pi/6),Real.sin_pi_div_six]; ring

/-- By a completed square, the quadratic exceeds `Q0` by at least
`304609/2450000`. -/
lemma sixty_cross_quadratic (v : ℝ) :
    Q0 < (19/10-(9/20)*v)^2+(2/35+(9/10)*v)^2 := by
  have hid : (19/10-(9/20)*v)^2+(2/35+(9/10)*v)^2-Q0 =
      (81/80)*(v-50/63)^2+304609/2450000 := by norm_num [Q0]; ring
  have h := sq_nonneg (v-50/63)
  nlinarith only [hid,h]

/-- The far corner of a contained square does not reach both `1 + (9/10) cos v`
and `1 - (9/10) sin (π/3 - v)`: the core of the sixty-degree lemma. -/
lemma sixty_cross_obstruction {a b v : ℝ} (hc : ContainedChart a |b|)
    (hv0 : 0≤v) (hv1 : v≤Real.pi/3)
    (ha : 1+(9/10)*Real.cos v≤a+1/2)
    (hb : 1-(9/10)*Real.sin (Real.pi/3-v)≤|b|+1/2) : False := by
  have hpi : Real.pi < (22:ℝ)/7 := by linarith [Real.pi_lt_d4]
  have hcoss := cos_sixty_chord hv0 hv1
  have hsins := Real.sin_le (show 0≤Real.pi/3-v by linarith)
  have hA : 19/10-(9/20)*v≤a+1/2 := by nlinarith
  have hB : 2/35+(9/10)*v≤|b|+1/2 := by nlinarith
  have hA0 : 0≤19/10-(9/20)*v := by linarith
  have hB0 : 0≤2/35+(9/10)*v := by linarith
  linarith [corner_sq_le hA0 hB0 hA hB hc.containment,sixty_cross_quadratic v]

private lemma near_thirty_cos {v : ℝ} (hv0 : 0≤v) (hv1 : v≤Real.pi/6) :
    41/50≤Real.cos v := by
  linarith [(small_angle (show |v|≤3/5 by rw [abs_of_nonneg hv0]; linarith [Real.pi_lt_d2])).1]

/-- One of the two points lies beyond the near edge, since the angle of the
square is within `π/6` of its direction. -/
lemma sixty_one_normal {a b v : ℝ} (hc : ContainedChart a |b|)
    (hv0 : 0≤v) (hv1 : v≤Real.pi/3) :
    a-1/2<(9/10)*Real.cos v ∨ a-1/2<(9/10)*Real.cos (Real.pi/3-v) := by
  have ha := hc.a_le_rho0
  by_cases hv : v≤Real.pi/6
  · exact Or.inl (by nlinarith [near_thirty_cos hv0 hv,rho0_bounds.2])
  · right
    have hz0 : 0≤Real.pi/3-v := by linarith
    have hz1 : Real.pi/3-v≤Real.pi/6 := by linarith
    nlinarith [near_thirty_cos hz0 hz1,rho0_bounds.2]

/-- In the chart of the square, one of the points at distance `9/10` and angles
`-v` and `π/3 - v` lies in the open square. -/
theorem sixty_coordinates_cover {a b v : ℝ} (hc : ContainedChart a |b|)
    (hb : |b|<1/2) (hv0 : 0≤v) (hv1 : v≤Real.pi/3) :
    (|(9/10)*Real.cos v-a|<1/2 ∧ |-(9/10)*Real.sin v-b|<1/2) ∨
    (|(9/10)*Real.cos (Real.pi/3-v)-a|<1/2 ∧
      |(9/10)*Real.sin (Real.pi/3-v)-b|<1/2) := by
  have hbb := abs_lt.mp hb
  have hsinL : 0≤Real.sin v := Real.sin_nonneg_of_nonneg_of_le_pi hv0
    (by linarith [Real.pi_pos])
  have hsinR : 0≤Real.sin (Real.pi/3-v) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hgap : (9/10)*(Real.sin v+Real.sin (Real.pi/3-v))<1 := by
    rw [sixty_sine_sum]
    nlinarith [Real.cos_le_one (v-Real.pi/6)]
  have hupperL : (9/10)*Real.cos v<a+1/2 := by
    nlinarith [Real.cos_le_one v,hc.half_le]
  have hupperR : (9/10)*Real.cos (Real.pi/3-v)<a+1/2 := by
    nlinarith [Real.cos_le_one (Real.pi/3-v),hc.half_le]
  have hnorm := sixty_one_normal hc hv0 hv1
  by_cases hL : a-1/2<(9/10)*Real.cos v
  · by_cases htL : b<1/2-(9/10)*Real.sin v
    · left
      constructor <;> apply abs_lt.mpr <;> constructor <;>
        linarith [hbb.1,hbb.2]
    · right
      have hnR : a-1/2<(9/10)*Real.cos (Real.pi/3-v) := by
        by_contra! hbad
        apply sixty_cross_obstruction hc (v:=Real.pi/3-v)
          (by linarith) (by linarith)
        · linarith
        · have hab := le_abs_self b
          have hid : Real.pi/3-(Real.pi/3-v)=v := by ring
          rw [hid]
          linarith
      constructor <;> apply abs_lt.mpr <;> constructor <;>
        linarith [hbb.1,hbb.2]
  · right
    have hnR : a-1/2<(9/10)*Real.cos (Real.pi/3-v) := hnorm.resolve_left hL
    have htR : (9/10)*Real.sin (Real.pi/3-v)-1/2<b := by
      by_contra! hbad
      apply sixty_cross_obstruction hc hv0 hv1
      · linarith
      · have hab := neg_le_abs b
        linarith
    constructor <;> apply abs_lt.mpr <;> constructor <;>
      linarith [hbb.1,hbb.2]

/-- A square at an angle between `q` and `q + π/3` contains one of the points at
distance `9/10` in the directions `q` and `q + π/3`. -/
theorem sixty_pin_cover {t q a b : ℝ} (hc : ContainedChart a |b|)
    (hb : |b|<1/2) (ht : q≤t ∧ t≤q+Real.pi/3) :
    openSquare (orientedSquare t a b) (polar (9/10) q) ∨
      openSquare (orientedSquare t a b) (polar (9/10) (q+Real.pi/3)) := by
  have hv := sixty_coordinates_cover hc hb (v:=t-q) (by linarith) (by linarith)
  rw [polar_mem_iff,polar_mem_iff]
  have hL : q-t=-(t-q) := by ring
  have hR : q+Real.pi/3-t=Real.pi/3-(t-q) := by ring
  simpa only [hL,hR,Real.cos_neg,Real.sin_neg,mul_neg,neg_mul] using hv

/-! ### Squares separated along their own axis -/

open Normalization

private def radialMinorant (v : ℝ) : ℝ := 3/2+(77/200)*v-(3/11)*v^2

lemma moving_pin_polynomial {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 5/12) :
    Q0 < (radialMinorant v)^2+(1-v)^2 := by
  have h3 := pow_le_pow_left₀ hv0 hv1 3
  have hrem : 0 ≤ (1+5929/40000-9/11 : ℝ)*v^2+(9/121)*v^4 := by
    exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg v))
      (mul_nonneg (by norm_num) (pow_nonneg hv0 4))
  have hid : (radialMinorant v)^2+(1-v)^2 =
      13/4-(169/200)*v-(231/1100)*v^3+
        ((1+5929/40000-9/11)*v^2+(9/121)*v^4) := by
    dsimp [radialMinorant]
    ring
  have hnum : Q0 < (13/4 : ℝ)-(169/200)*(5/12)-(231/1100)*(5/12)^3 := by
    norm_num [Q0]
  rw [hid]
  linarith

/-- The radial bound of a separation along the own axis keeps the transverse
coordinate below `1/2 - (1 + x) v`. -/
theorem own_transverse_obstruction {a u x c v : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 23/200)
    (hc0 : 5/6 ≤ c) (hc1 : c ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 5/12) (hunit : c^2+v^2=1)
    (hown : 1+(1/2+x)*c+(77/200)*v ≤ a+1/2)
    (hbox : (a+1/2)^2+(u+1/2)^2 ≤ Q0) :
    u+(1+x)*v < 1/2 := by
  by_contra! hfail
  let A0 : ℝ := 1+c/2+(77/200)*v
  let B0 : ℝ := 1-v
  let A : ℝ := A0+x*c
  let B : ℝ := B0-x*v
  have hc : 0 ≤ c := by linarith
  have hA0 : 1 ≤ A0 := by dsimp [A0]; linarith
  have hB0 : 0 ≤ B0 ∧ B0 ≤ 1 := by
    dsimp [B0]
    constructor <;> linarith
  have hxv := mul_le_mul
    (show 1+x ≤ (223:ℝ)/200 by linarith) hv1 hv0 (by norm_num)
  have hA : 0 ≤ A := by
    have hxc := mul_nonneg hx0 hc
    dsimp [A]
    linarith
  have hB : 0 ≤ B := by dsimp [B,B0]; nlinarith only [hxv]
  have hAa : A ≤ a+1/2 := by dsimp [A,A0]; nlinarith only [hown]
  have hBu : B ≤ u+1/2 := by dsimp [B,B0]; nlinarith only [hfail]
  have hAB : A^2+B^2 ≤ Q0 := corner_sq_le hA hB hAa hBu hbox
  have hAc := mul_nonneg (show 0 ≤ A0-1 by linarith) hc
  have hBv := mul_nonneg (show 0 ≤ 1-B0 by linarith [hB0.2]) hv0
  have hcross : 0 ≤ A0*c-B0*v := by
    nlinarith only [hAc,hBv,hc0,hv1]
  have hxx := mul_nonneg hx0 hcross
  have hid : A^2+B^2-(A0^2+B0^2) =
      2*x*(A0*c-B0*v)+x^2*(c^2+v^2) := by
    dsimp [A,B]
    ring
  rw [hunit] at hid
  have hbase : A0^2+B0^2 ≤ Q0 := by
    nlinarith only [hid,hxx,sq_nonneg x,hAB]
  have hcp := mul_nonneg (show 0 ≤ 1-c by linarith)
    (show 0 ≤ c-5/6 by linarith)
  have hcos : 1-(6/11)*v^2 ≤ c := by nlinarith only [hcp,hunit]
  have hv2 := pow_le_pow_left₀ hv0 hv1 2
  have hL : 0 ≤ radialMinorant v := by
    dsimp [radialMinorant]
    nlinarith only [hv0,hv2]
  have hLA : radialMinorant v ≤ A0 := by
    dsimp [radialMinorant,A0]
    linarith
  have hcmp := mul_nonneg (sub_nonneg.mpr hLA)
    (show 0 ≤ A0+radialMinorant v by linarith)
  have hbad := moving_pin_polynomial hv0 hv1
  change Q0 < (radialMinorant v)^2+B0^2 at hbad
  nlinarith only [hcmp,hbase,hbad]

open Normalization

lemma moving_pin_trig {t : ℝ} (ht : |t| ≤ 5/12) :
    (5/6 ≤ Real.cos t ∧ Real.cos t ≤ 1) ∧
      (0 ≤ |Real.sin t| ∧ |Real.sin t| ≤ 5/12) := by
  have h := small_angle ht
  exact ⟨⟨by linarith [h.1],Real.cos_le_one t⟩,abs_nonneg _,h.2⟩

/-- The own separator bounds the radial coordinate below. -/
lemma own_radial_lower {t a b cx cy : ℝ}
    (hcy0 : 0 ≤ cy) (hcy1 : cy ≤ 23/200) (hc : 0 ≤ Real.cos t)
    (hown : 0 ≤ centralMargin .own t a b cx cy) :
    1+(1/2+cx)*Real.cos t+(77/200)*|Real.sin t| ≤ a+1/2 := by
  have hy := mul_le_mul_of_nonneg_left (neg_le_abs (Real.sin t)) hcy0
  have hgap := mul_nonneg (show 0 ≤ 23/200-cy by linarith) (abs_nonneg (Real.sin t))
  dsimp [centralMargin,centralNormal,angularWidth] at hown
  rw [abs_of_nonneg hc] at hown
  nlinarith only [hy,hgap,hown]

open Normalization

lemma quarter_trig_lower : (7:ℝ)/10≤Real.cos (Real.pi/4) ∧
    (7:ℝ)/10≤Real.sin (Real.pi/4) := by
  rw [cos_quarter,sin_quarter]
  constructor <;> linarith [hStar_bounds.1]

lemma own_east_positive_profile {t a b cx cy : ℝ}
    (hx0 : 0≤cx) (hy0 : 0≤cy) (ht0 : 0≤t) (ht1 : t≤Real.pi/4)
    (ho : 0≤centralMargin .own t a b cx cy) :
    1/2+(1/2)*Real.cos t+(1/2)*Real.sin t≤a := by
  have hc : 0≤Real.cos t := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos])
  have hcx := mul_nonneg hx0 hc
  have hcy := mul_nonneg hy0 hs
  dsimp [centralMargin,centralNormal,angularWidth] at ho
  rw [abs_of_nonneg hc,abs_of_nonneg hs] at ho
  linarith

lemma own_east_negative_profile {v a b cx cy : ℝ}
    (hx0 : 0≤cx) (hy : cy≤c0) (hv0 : 0≤v) (hv1 : v≤Real.pi/4)
    (ho : 0≤centralMargin .own (-v) a b cx cy) :
    1/2+(1/2)*Real.cos v+(387/1000)*Real.sin v≤a := by
  have hc : 0≤Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hv0 (by linarith [Real.pi_pos])
  have hcx := mul_nonneg hx0 hc
  have hcy : cy≤113/1000 := by dsimp [c0] at hy; linarith [rho0_bounds.2]
  have hprod := mul_nonneg (sub_nonneg.mpr hcy) hs
  dsimp [centralMargin,centralNormal,angularWidth] at ho
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hc,abs_of_nonneg hs] at ho
  nlinarith

/-- A square at phase `t`, `|t| ≤ π/4`, separated from the central square along
its own axis has `-5/12 < t < 3/10`. -/
theorem own_east_window {t a b cx cy : ℝ} (hc : ContainedChart a |b|)
    (hx0 : 0≤cx) (hy0 : 0≤cy) (hy : cy≤c0) (ht : |t|≤Real.pi/4)
    (ho : 0≤centralMargin .own t a b cx cy) : -5/12<t ∧ t<3/10 := by
  have htb := abs_le.mp ht
  have ha := hc.a_le_rho0
  have hq := quarter_trig_lower
  constructor
  · by_contra! hbad
    have hp := own_east_negative_profile (a:=a) (b:=b) hx0 hy
      (show 0≤-t by linarith) (show -t≤Real.pi/4 by linarith)
      (by simpa only [neg_neg] using ho)
    have hl : (613:ℝ)/1000<(1/2)*Real.cos (5/12)+(387/1000)*Real.sin (5/12) := by
      have hs := Real.sin_ge_sub_cube (x:=(5:ℝ)/12) (by norm_num)
      have hc := Real.one_sub_sq_div_two_le_cos (x:=(5:ℝ)/12)
      norm_num at hs hc
      linarith
    have hu : (613:ℝ)/1000<(1/2)*Real.cos (Real.pi/4)+(387/1000)*Real.sin (Real.pi/4) := by
      linarith [hq.1,hq.2]
    have h := harmonic_pos_of_endpoints (K:=-(613/1000)) (A:=(1:ℝ)/2) (B:=(387:ℝ)/1000)
      (by norm_num) (by norm_num) (by norm_num : (0:ℝ)≤5/12)
      (by linarith [Real.pi_pos] : Real.pi/4≤Real.pi/2)
      (x:=-t) ⟨by linarith,by linarith⟩ (by linarith) (by linarith)
    linarith [rho0_bounds.2]
  · by_contra! hbad
    have hp := own_east_positive_profile hx0 hy0
      (show 0≤t by linarith) htb.2 ho
    have hl : (613:ℝ)/1000<(1/2)*Real.cos (3/10)+(1/2)*Real.sin (3/10) := by
      have hs := Real.sin_ge_sub_cube (x:=(3:ℝ)/10) (by norm_num)
      have hc := Real.one_sub_sq_div_two_le_cos (x:=(3:ℝ)/10)
      norm_num at hs hc
      linarith
    have hu : (613:ℝ)/1000<(1/2)*Real.cos (Real.pi/4)+(1/2)*Real.sin (Real.pi/4) := by
      linarith [hq.1,hq.2]
    have h := harmonic_pos_of_endpoints (K:=-(613/1000)) (A:=(1:ℝ)/2) (B:=(1:ℝ)/2)
      (by norm_num) (by norm_num) (by norm_num : (0:ℝ)≤3/10)
      (by linarith [Real.pi_pos] : Real.pi/4≤Real.pi/2)
      ⟨hbad,htb.2⟩ (by linarith) (by linarith)
    linarith [rho0_bounds.2]

lemma own_west_negative_profile {v a b cx cy : ℝ}
    (hx : cx≤c0) (hy0 : 0≤cy) (hv0 : 0≤v) (hv1 : v≤Real.pi/4)
    (ho : 0≤centralMargin .own (Real.pi-v) a b cx cy) :
    1/2+(387/1000)*Real.cos v+(1/2)*Real.sin v≤a := by
  have hc : 0≤Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hv0 (by linarith [Real.pi_pos])
  have hcx : cx≤113/1000 := by dsimp [c0] at hx; linarith [rho0_bounds.2]
  have hp := mul_nonneg (sub_nonneg.mpr hcx) hc
  have hcy := mul_nonneg hy0 hs
  dsimp [centralMargin,centralNormal,angularWidth] at ho
  rw [Real.cos_pi_sub,Real.sin_pi_sub,abs_neg,abs_of_nonneg hc,abs_of_nonneg hs] at ho
  nlinarith

lemma own_west_positive_profile {t a b cx cy : ℝ}
    (hx : cx≤c0) (hy : cy≤c0) (ht0 : 0≤t) (ht1 : t≤Real.pi/4)
    (ho : 0≤centralMargin .own (Real.pi+t) a b cx cy) :
    1/2+(387/1000)*(Real.cos t+Real.sin t)≤a := by
  have hc : 0≤Real.cos t := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos])
  have hcx : cx≤113/1000 := by dsimp [c0] at hx; linarith [rho0_bounds.2]
  have hcy : cy≤113/1000 := by dsimp [c0] at hy; linarith [rho0_bounds.2]
  have hp := mul_nonneg (sub_nonneg.mpr hcx) hc
  have hq := mul_nonneg (sub_nonneg.mpr hcy) hs
  dsimp [centralMargin,centralNormal,angularWidth] at ho
  have hcpi : Real.cos (Real.pi+t)=-Real.cos t := by rw [add_comm]; exact Real.cos_add_pi t
  have hspi : Real.sin (Real.pi+t)=-Real.sin t := by rw [add_comm]; exact Real.sin_add_pi t
  rw [hcpi,hspi,abs_neg,abs_neg,abs_of_nonneg hc,abs_of_nonneg hs] at ho
  nlinarith

lemma own_west_lower_window {t a b cx cy : ℝ} (hc : ContainedChart a |b|)
    (hx : cx≤c0) (hy0 : 0≤cy) (ht : |t|≤Real.pi/4)
    (ho : 0≤centralMargin .own (Real.pi+t) a b cx cy) : -2/3<t := by
  by_contra! hbad
  have htb := abs_le.mp ht
  have hp := own_west_negative_profile (v:=-t) hx hy0
    (by linarith) (by linarith) (by simpa only [sub_neg_eq_add] using ho)
  have hl : (613:ℝ)/1000<(387/1000)*Real.cos (2/3)+(1/2)*Real.sin (2/3) := by
    have hs := sin_lower_seven (x:=(2:ℝ)/3) (by norm_num)
    have hc := cos_lower_six (x:=(2:ℝ)/3) (by norm_num)
    norm_num at hs hc
    linarith
  have hu : (613:ℝ)/1000<(387/1000)*Real.cos (Real.pi/4)+(1/2)*Real.sin (Real.pi/4) := by
    linarith [quarter_trig_lower.1,quarter_trig_lower.2]
  have h := harmonic_pos_of_endpoints (K:=-(613/1000)) (A:=(387:ℝ)/1000) (B:=(1:ℝ)/2)
    (by norm_num) (by norm_num) (by norm_num : (0:ℝ)≤2/3)
    (by linarith [Real.pi_pos] : Real.pi/4≤Real.pi/2)
    (x:=-t) ⟨by linarith,by linarith⟩ (by linarith) (by linarith)
  linarith [hc.a_le_rho0,rho0_bounds.2]

/-- A square at phase `π + t`, `|t| ≤ π/4`, separated from the central square
along its own axis and holding the W pin has `t < 5/8`. -/
theorem own_west_pin_upper {t a b cx cy : ℝ} (hc : ContainedChart a |b|)
    (hx : cx≤c0) (hy : cy≤c0) (ht : |t|≤Real.pi/4)
    (ho : 0≤centralMargin .own (Real.pi+t) a b cx cy)
    (hpin : openSquare (orientedSquare (Real.pi+t) a b) (polar (9/10) (11*Real.pi/12))) :
    t<5/8 := by
  by_contra! hbad
  have htb := abs_le.mp ht
  have hrad := own_west_positive_profile hx hy (by linarith) htb.2 ho
  have hcs0 : (279:ℝ)/200<Real.cos (5/8)+Real.sin (5/8) := by
    have hs := sin_lower_seven (x:=(5:ℝ)/8) (by norm_num)
    have hc := cos_lower_six (x:=(5:ℝ)/8) (by norm_num)
    norm_num at hs hc
    linarith
  have hcs := cos_add_sin_mono (x:=(5:ℝ)/8) (by norm_num) hbad htb.2
  have hs0 : (387:ℝ)/500<Real.sin (133/150) := by
    have h := sin_lower_seven (x:=(133:ℝ)/150) (by norm_num)
    norm_num at h
    linarith
  have hangle : (133:ℝ)/150≤Real.pi/12+t := by linarith [Real.pi_gt_d2]
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤(133:ℝ)/150 by linarith [Real.pi_pos])
    (show Real.pi/12+t≤Real.pi/2 by linarith [Real.pi_pos]) hangle
  rw [polar_mem_iff] at hpin
  have harg : 11*Real.pi/12-(Real.pi+t)=-(Real.pi/12+t) := by ring
  rw [harg,Real.sin_neg,mul_neg] at hpin
  have hb := (abs_lt.mp hpin.2).1
  have hA : 1+(387/1000)*(279/200)≤a+1/2 := by nlinarith
  have hB : (9/10)*(387/500)≤|b|+1/2 := by
    have hn := neg_le_abs b
    nlinarith
  have hbadQ : Q0<(1+(387/1000)*(279/200))^2+((9/10)*(387/500))^2 := by norm_num [Q0]
  linarith [corner_sq_le (by norm_num) (by norm_num) hA hB hc.containment]

open Normalization

/-- A Taylor lower bound for `A cos t + B sin t`, affine in `t` on `[0, r]`. -/
lemma trig_affine_lower {A B r t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ r) :
    A+(B-A*r/2-B*r^2/6)*t ≤ A*Real.cos t+B*Real.sin t := by
  have hq := mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have ht2 := pow_le_pow_left₀ ht0 ht1 2
  have ht3 := mul_le_mul_of_nonneg_right ht2 ht0
  have hc := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := t)) hA
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube ht0) hB
  have hAq := mul_nonneg hA hq
  have hBq := mul_le_mul_of_nonneg_left ht3 hB
  nlinarith only [hc,hs,hAq,hBq]

lemma polar_rotate (v q t a b : ℝ) :
    openSquare (orientedSquare (t+v) a b) (polar (9/10) (q+v)) ↔
      openSquare (orientedSquare t a b) (polar (9/10) q) := by
  rw [polar_mem_iff,polar_mem_iff]
  have h : q+v-(t+v)=q-t := by ring
  rw [h]

lemma contract_transverse {L b s : ℝ} (hL : 9/10≤L)
    (hb : |b|<1/2) (hfar : |L*s+b|<1/2) : |(9/10)*s+b|<1/2 := by
  have hbb := abs_lt.mp hb
  have hff := abs_lt.mp hfar
  apply abs_lt.mpr
  by_cases hs : 0≤ s
  · have hlo := mul_nonneg (show (0:ℝ)≤9/10 by norm_num) hs
    have hhi := mul_nonneg (sub_nonneg.mpr hL) hs
    constructor <;> nlinarith [hbb.1,hbb.2,hff.1,hff.2]
  · have hlo := mul_nonpos_of_nonneg_of_nonpos
      (show (0:ℝ)≤9/10 by norm_num) (le_of_not_ge hs)
    have hhi := mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr hL) (le_of_not_ge hs)
    constructor <;> nlinarith [hbb.1,hbb.2,hff.1,hff.2]

/-- A square at angle `|t| ≤ 5/12` that contains a point `(L, 0)` with
`L ≥ 9/10` contains the pin `(9/10, 0)`. -/
theorem east_pin_of_axis_point {t a b L : ℝ} (hc : ContainedChart a |b|)
    (hb : |b|<1/2) (ht : |t|≤5/12) (hL : 9/10≤L)
    (hp : openSquare (orientedSquare t a b) (L,0)) :
    openSquare (orientedSquare t a b) (polar (9/10) 0) := by
  have htr := moving_pin_trig ht
  have hX : |(9/10)*Real.cos t-a|<1/2 := by
    apply abs_lt.mpr
    constructor <;> nlinarith [hc.a_le_rho0,rho0_bounds.2,htr.1.1,htr.1.2,hc.half_le]
  have hfar : |L*Real.sin t+b|<1/2 := by
    have h := hp.2
    rw [orientedSquare_localY] at h
    have hid : -L*Real.sin t+0*Real.cos t-b=-(L*Real.sin t+b) := by ring
    rw [hid,abs_neg] at h
    exact h
  have hY := contract_transverse hL hb hfar
  have hY' : |-((9/10)*Real.sin t)-b|<1/2 := by
    rw [show -((9/10)*Real.sin t)-b=-((9/10)*Real.sin t+b) by ring,abs_neg]
    exact hY
  rw [polar_mem_iff]
  simpa only [zero_sub,Real.cos_neg,Real.sin_neg,mul_neg,neg_sub,abs_neg] using And.intro hX hY'

/-- A square E separated from C along its own axis has its angle in
`(-5/12, 3/10)` and contains the pin `(9/10, 0)`: along its axis by the radial
bounds, and across it since `|b| + (1 + cx) |sin t| < 1/2`. -/
theorem own_east_pin {t a b cx cy : ℝ} (hc : ContainedChart a |b|)
    (hx0 : 0≤cx) (hy0 : 0≤cy) (hx : cx≤c0) (hy : cy≤c0)
    (ht : |t|≤Real.pi/4) (ho : 0≤centralMargin .own t a b cx cy) :
    (-5/12<t ∧ t<3/10) ∧ openSquare (orientedSquare t a b) (polar (9/10) 0) := by
  have hw := own_east_window hc hx0 hy0 hy ht ho
  have htr := moving_pin_trig (t := t) (abs_le.mpr ⟨by linarith [hw.1],by linarith [hw.2]⟩)
  have hcos0 : 0 ≤ Real.cos t := by linarith [htr.1.1]
  have hrad := own_radial_lower hy0 (by linarith [c0_bounds.2]) hcos0 ho
  have htrans := own_transverse_obstruction (u := |b|) hx0 (by linarith [c0_bounds.2])
    htr.1.1 htr.1.2 htr.2.1 htr.2.2 (by rw [sq_abs]; linarith [Real.sin_sq_add_cos_sq t])
    hrad hc.containment
  have hxs := mul_nonneg hx0 htr.2.1
  have hxc := mul_nonneg hx0 hcos0
  have hY : |-((9/10)*Real.sin t)-b| < 1/2 := by
    have h := abs_add_le ((9/10)*Real.sin t) b
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 9/10)] at h
    rw [show -((9/10)*Real.sin t)-b = -((9/10)*Real.sin t+b) by ring,abs_neg]
    linarith
  have hX : |(9/10)*Real.cos t-a| < 1/2 := by
    apply abs_lt.mpr
    constructor <;> nlinarith [hc.a_le_rho0,rho0_bounds.2,htr.1.1,htr.1.2,abs_nonneg (Real.sin t)]
  refine ⟨hw,?_⟩
  rw [polar_mem_iff]
  simpa only [zero_sub,Real.cos_neg,Real.sin_neg,mul_neg] using And.intro hX hY

lemma western_flank_quadratic (v : ℝ) :
    Q0<(277/200+v/3)^2+(49/40-(9/10)*v)^2 := by
  have hid : (277/200+v/3)^2+(49/40-(9/10)*v)^2-Q0 =
      (829/900)*(v-2307/3316)^2+20199561/165800000 := by norm_num [Q0]; ring
  have h := sq_nonneg (v-2307/3316)
  nlinarith only [hid,h]

/-- A square at phase `-v`, with `π/12 ≤ v ≤ 2/3`, contains the pin at angle
`-π/12` if its centre obeys the radial profile whenever `b < 0`. -/
theorem western_left_pin {v a b : ℝ} (hc : ContainedChart a |b|)
    (hb : |b|<1/2) (hv0 : Real.pi/12≤v) (hv1 : v≤2/3)
    (hprofile : b<0 → 1/2+(77/200)*Real.cos v+(1/2)*Real.sin v≤a) :
    openSquare (orientedSquare (-v) a b) (polar (9/10) (-Real.pi/12)) := by
  have hδ0 : 0≤v-Real.pi/12 := by linarith
  have hδ1 : v-Real.pi/12≤5/12 := by linarith [Real.pi_gt_d2]
  have htr := moving_pin_trig (abs_le.mpr ⟨by linarith, hδ1⟩ : |v-Real.pi/12|≤5/12)
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hδ0 (by linarith [Real.pi_gt_d2])
  have hs1 := (Real.sin_le hδ0).trans hδ1
  have hX : |(9/10)*Real.cos (v-Real.pi/12)-a|<1/2 := by
    apply abs_lt.mpr
    constructor <;> nlinarith [hc.a_le_rho0,rho0_bounds.2,htr.1.1,htr.1.2,hc.half_le]
  have hbb := abs_lt.mp hb
  have hY : |(9/10)*Real.sin (v-Real.pi/12)-b|<1/2 := by
    apply abs_lt.mpr
    refine ⟨by nlinarith [hbb.2],?_⟩
    by_contra! hbad
    have hbneg : b<0 := by nlinarith
    have hp := hprofile hbneg
    have hv : 0≤v := by linarith [Real.pi_pos]
    have haff := trig_affine_lower (A:=(77:ℝ)/200) (B:=(1:ℝ)/2)
      (r:=(2:ℝ)/3) (by norm_num) (by norm_num) hv hv1
    have hA : 277/200+v/3≤a+1/2 := by nlinarith
    have hB : 49/40-(9/10)*v≤|b|+1/2 := by
      have hs := Real.sin_le hδ0
      rw [abs_of_neg hbneg]
      nlinarith [Real.pi_gt_d2]
    have hA0 : 0≤277/200+v/3 := by linarith
    have hB0 : 0≤49/40-(9/10)*v := by linarith
    linarith [corner_sq_le hA0 hB0 hA hB hc.containment,western_flank_quadratic v]
  rw [polar_mem_iff]
  have harg : -Real.pi/12-(-v)=v-Real.pi/12 := by ring
  simpa only [harg] using And.intro hX hY

lemma own_west_left_pin {t a b cx cy : ℝ} (hc : ContainedChart a |b|)
    (hb : |b|<1/2) (hx : cx≤c0) (hy0 : 0≤cy)
    (ht : |t|≤Real.pi/4) (htleft : t≤-Real.pi/12)
    (ho : 0≤centralMargin .own (Real.pi+t) a b cx cy) :
    openSquare (orientedSquare (Real.pi+t) a b) (polar (9/10) (11*Real.pi/12)) := by
  have hw := own_west_lower_window hc hx hy0 ht ho
  have hp := own_west_negative_profile (v:=-t) hx hy0
    (by linarith [Real.pi_pos]) (by linarith [(abs_le.mp ht).1])
    (by simpa only [sub_neg_eq_add] using ho)
  have hcos : 0≤Real.cos (-t) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [(abs_le.mp ht).1,Real.pi_pos]⟩
  have hlocal := western_left_pin (v:=-t) hc hb (by linarith) (by linarith)
    (fun _ => by nlinarith)
  have hphase : Real.pi+t=t+Real.pi := by ring
  have hpin : 11*Real.pi/12=(-Real.pi/12)+Real.pi := by ring
  rw [hphase,hpin,polar_rotate]
  simpa only [neg_neg] using hlocal

/-- A square W separated from C along its own axis, at angle `|t| ≤ π/4`,
contains the pin at angle `11π/12` or the one at `5π/4`. -/
theorem own_west_pins {t a b cx cy : ℝ} (hc : ContainedChart a |b|)
    (hb : |b|<1/2) (hx : cx≤c0) (hy0 : 0≤cy) (ht : |t|≤Real.pi/4)
    (ho : 0≤centralMargin .own (Real.pi+t) a b cx cy) :
    openSquare (orientedSquare (Real.pi+t) a b) (polar (9/10) (11*Real.pi/12)) ∨
      openSquare (orientedSquare (Real.pi+t) a b) (polar (9/10) (5*Real.pi/4)) := by
  by_cases hleft : t≤-Real.pi/12
  · exact Or.inl (own_west_left_pin hc hb hx hy0 ht hleft ho)
  · have hcover := sixty_pin_cover (t:=Real.pi+t) (q:=11*Real.pi/12) hc hb
      ⟨by linarith,by linarith [(abs_le.mp ht).2]⟩
    have hsum : 11*Real.pi/12+Real.pi/3=5*Real.pi/4 := by ring
    simpa only [hsum] using hcover

/-! ### Squares beyond a side of the central square -/

open Normalization

/-- A square in a cap at least `1/2` deep contains the east pin, and its phase
is within `1/4` of the cap normal. -/
theorem east_cap_pin {t a b h:ℝ} (hc:ContainedChart a |b|)
    (hb:|b|<1/2) (hh:1/2≤h) (hm:h+angularWidth t≤centerX t a b) :
    ∃ v : ℝ, |v|<1/4 ∧ (t:Direction)=(v:Direction) ∧
      openSquare (orientedSquare t a b) (polar (9/10) 0) := by
  have hcore : coreRadius≤h := by dsimp [coreRadius]; linarith [rho0_bounds.1]
  obtain ⟨v,hv,he,hmv⟩ := deep_cap_faces (by linarith [hc.half_le]) hb hcore hc.abs_box hm
  have hvpi : |v|≤Real.pi/4 := by linarith [Real.pi_gt_d2]
  have hquarter := cap_angle_lt_quarter hh (cap_support_bound_signed hvpi hc.abs_box hmv) hvpi
  have hpin := east_pin_of_axis_point hc hb (by linarith : |v|≤5/12)
    (show 9/10≤h+1/2 by linarith) (cap_piercing hvpi hcore hc.abs_box hmv)
  exact ⟨v,hquarter,he,(square_phase_open he _).mpr hpin⟩

lemma west_cap_rotated_identity (t a b cx cy:ℝ) :
    centralMargin .west t a b cx cy =
      centerX (t-Real.pi) a b-angularWidth (t-Real.pi)-(1/2-cx) := by
  simp only [centralMargin,centerX,angularWidth,Real.cos_sub_pi,Real.sin_sub_pi,abs_neg]
  ring

/-- On the left flank, `v ≤ -π/12`, a square in a deep cap contains the pin at
angle `-π/12`. -/
lemma west_cap_left_pin {v a b h:ℝ} (hc:ContainedChart a |b|) (hb:|b|<1/2)
    (hh:coreRadius≤h) (hv:|v|<2/5) (hleft:v≤-Real.pi/12)
    (hm:h+angularWidth v≤centerX v a b) :
    openSquare (orientedSquare v a b) (polar (9/10) (-Real.pi/12)) := by
  have hvs := abs_lt.mp hv
  have hcos : 0≤Real.cos (-v) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_gt_d2]⟩
  have hsin : 0≤Real.sin (-v) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d2])
  apply (by simpa only [neg_neg] using
    (western_left_pin (v:=-v) hc hb (by linarith) (by linarith)))
  intro hbneg
  have harg : v=-(-v) := by ring
  have hm' := hm
  conv at hm' => lhs; arg 2; arg 1; rw [harg]
  have hmv : h+(Real.cos (-v)+Real.sin (-v))/2≤a*Real.cos (-v)+b*Real.sin (-v) := by
    simp only [Real.cos_neg,Real.sin_neg] at hcos hsin ⊢
    have h1 : |Real.cos v|=Real.cos v := abs_of_nonneg hcos
    have h2 : |Real.sin v|=-Real.sin v := abs_of_nonpos (by linarith)
    simp only [angularWidth,centerX,h1,h2] at hm
    linarith
  have hprod := mul_nonneg (show 0≤a-1/2 by linarith [hc.half_le])
    (show 0≤1-Real.cos (-v) by linarith [Real.cos_le_one (-v)])
  have hbprod := mul_nonpos_of_nonpos_of_nonneg hbneg.le hsin
  have hcore : (77:ℝ)/200<h := by linarith [coreRadius_bounds.1]
  have hcprod := mul_nonneg (show 0≤(77:ℝ)/200 by norm_num)
    (show 0≤1-Real.cos (-v) by linarith [Real.cos_le_one (-v)])
  nlinarith

/-- A square in a deep cap contains the pin at angle `-π/12` or the one at
`π/4`; turned by `π`, these are the W and D pins. -/
theorem west_cap_pins {v a b h:ℝ} (hc:ContainedChart a |b|) (hb:|b|<1/2)
    (hh:coreRadius≤h) (hv:|v|<2/5) (hm:h+angularWidth v≤centerX v a b) :
    openSquare (orientedSquare v a b) (polar (9/10) (-Real.pi/12)) ∨
      openSquare (orientedSquare v a b) (polar (9/10) (Real.pi/4)) := by
  by_cases hl:v≤-Real.pi/12
  · exact Or.inl (west_cap_left_pin hc hb hh hv hl hm)
  · have h := sixty_pin_cover (t:=v) (q:=-Real.pi/12) hc hb
      ⟨by linarith,by linarith [(abs_lt.mp hv).2,Real.pi_gt_d2]⟩
    have hid : -Real.pi/12+Real.pi/3=Real.pi/4 := by ring
    simpa only [hid] using h

/-! ### Pin locations -/

open Normalization

/-- A square near the east axis that holds the pin of E. -/
def EastPinData (t a b:ℝ) : Prop :=
  ∃ v : ℝ, (-5/12<v ∧ v<3/10) ∧ (t:Direction)=(v:Direction) ∧
    openSquare (orientedSquare t a b) (pin 0)

/-- A square near the north axis that holds the pin of N. -/
def NorthPinData (t a b:ℝ) : Prop :=
  ∃ v, (-3/10<v ∧ v<5/12) ∧ (t:Direction)=(Real.pi/2+v:ℝ) ∧
    openSquare (orientedSquare t a b) (pin 1)

/-- A square near the west axis that holds the pin of W or of D, with the pin of
W on its left flank and an upper bound on its phase when it holds that pin. -/
def WestPinData (t a b:ℝ) : Prop :=
  ∃ v, (-2/3<v ∧ v≤Real.pi/4) ∧ (t:Direction)=(Real.pi+v:ℝ) ∧
    (openSquare (orientedSquare t a b) (pin 2) ∨
      openSquare (orientedSquare t a b) (pin 3)) ∧
    (v≤-Real.pi/12 → openSquare (orientedSquare t a b) (pin 2)) ∧
    (openSquare (orientedSquare t a b) (pin 2) → v<5/8)

/-- The reflection of `WestPinData` in the diagonal: the pin of S or of D. -/
def SouthPinData (t a b:ℝ) : Prop :=
  ∃ v, (-Real.pi/4≤v ∧ v<2/3) ∧ (t:Direction)=(3*Real.pi/2+v:ℝ) ∧
    (openSquare (orientedSquare t a b) (pin 4) ∨
      openSquare (orientedSquare t a b) (pin 3)) ∧
    (Real.pi/12≤v → openSquare (orientedSquare t a b) (pin 4)) ∧
    (openSquare (orientedSquare t a b) (pin 4) → -5/8<v)

/-- The four locations of an exterior square in the frame of C. -/
def PinLocation (t a b:ℝ) : Prop :=
  EastPinData t a b ∨ NorthPinData t a b ∨ WestPinData t a b ∨ SouthPinData t a b

lemma own_east_data {t v a b cx cy:ℝ} (hc:ContainedChart a |b|)
    (hx0:0≤cx) (hy0:0≤cy) (hx:cx≤c0) (hy:cy≤c0)
    (hv:|v|≤Real.pi/4) (he:(t:Direction)=(v:Direction))
    (ho:0≤centralMargin .own t a b cx cy) : EastPinData t a b := by
  have hov : 0≤centralMargin .own v a b cx cy := by
    simpa only [margin_phase_eq he] using ho
  obtain ⟨hw,hp⟩ := own_east_pin hc hx0 hy0 hx hy hv hov
  refine ⟨v,hw,he,?_⟩
  apply (square_phase_open he _).mpr
  simpa [pin,polar] using hp

lemma own_west_data {t v a b cx cy:ℝ} (hc:ContainedChart a |b|) (hb:|b|<1/2)
    (hx:cx≤c0) (hy0:0≤cy) (hy:cy≤c0)
    (hv:|v|≤Real.pi/4) (he:(t:Direction)=(Real.pi+v:ℝ))
    (ho:0≤centralMargin .own t a b cx cy) : WestPinData t a b := by
  have hov : 0≤centralMargin .own (Real.pi+v) a b cx cy := by
    simpa only [margin_phase_eq he] using ho
  have hw := own_west_lower_window hc hx hy0 hv hov
  have hcover := own_west_pins hc hb hx hy0 hv hov
  have hW : openSquare (orientedSquare t a b) (pin 2) ↔
      openSquare (orientedSquare (Real.pi+v) a b) (polar (9/10) (11*Real.pi/12)) := by
    rw [square_phase_open he,pin_eq_polar]
    rfl
  have hD : openSquare (orientedSquare t a b) (pin 3) ↔
      openSquare (orientedSquare (Real.pi+v) a b) (polar (9/10) (5*Real.pi/4)) := by
    rw [square_phase_open he,pin_eq_polar]
    rfl
  refine ⟨v,⟨hw,(abs_le.mp hv).2⟩,he,?_,?_,?_⟩
  · exact hcover.elim (fun h => Or.inl (hW.mpr h)) (fun h => Or.inr (hD.mpr h))
  · intro hleft
    exact hW.mpr (own_west_left_pin hc hb hx hy0 hv hleft hov)
  · intro hp
    exact own_west_pin_upper hc hx hy hv hov (hW.mp hp)

lemma east_data_diagonal {t a b:ℝ} (h:EastPinData (Real.pi/2-t) a (-b)) : NorthPinData t a b := by
  obtain ⟨v,hv,he,hp⟩ := h
  have ht : (t:Direction)=(Real.pi/2-v:ℝ) := by
    have hid : t=Real.pi/2-(Real.pi/2-t) := by ring
    calc
      (t:Direction) = (Real.pi/2-(Real.pi/2-t):ℝ) := congrArg (fun x:ℝ => (x:Direction)) hid
      _ = _ := by simp only [Real.Angle.coe_sub,he]
  have hpoint := (square_diagonal_membership t a b (pin 0)).mp hp
  rw [pin_diagonal] at hpoint
  refine ⟨-v,⟨by linarith [hv.2],by linarith [hv.1]⟩,?_,?_⟩
  · simpa only [sub_eq_add_neg] using ht
  · exact hpoint

lemma west_data_diagonal {t a b:ℝ} (h:WestPinData (Real.pi/2-t) a (-b)) : SouthPinData t a b := by
  obtain ⟨v,hv,he,hcover,hleft,hupper⟩ := h
  have ht : (t:Direction)=(3*Real.pi/2-v:ℝ) := by
    have hid : t=Real.pi/2-(Real.pi/2-t) := by ring
    have hsum : 3*Real.pi/2-v=(Real.pi/2-(Real.pi+v))+2*Real.pi := by ring
    rw [hsum,Real.Angle.coe_add,Real.Angle.coe_two_pi,add_zero]
    calc
      (t:Direction) = (Real.pi/2-(Real.pi/2-t):ℝ) := congrArg (fun x:ℝ => (x:Direction)) hid
      _ = _ := by simp only [Real.Angle.coe_sub,he]
  have hW : openSquare (orientedSquare (Real.pi/2-t) a (-b)) (pin 2) ↔
      openSquare (orientedSquare t a b) (pin 4) := by
    have h := square_diagonal_membership t a b (pin 2)
    rw [pin_diagonal] at h
    exact h
  have hD : openSquare (orientedSquare (Real.pi/2-t) a (-b)) (pin 3) ↔
      openSquare (orientedSquare t a b) (pin 3) := by
    have h := square_diagonal_membership t a b (pin 3)
    rw [pin_diagonal] at h
    exact h
  refine ⟨-v,⟨by linarith [hv.2],by linarith [hv.1]⟩,?_,?_,?_,?_⟩
  · simpa only [sub_eq_add_neg] using ht
  · exact hcover.elim (fun h => Or.inl (hW.mp h)) (fun h => Or.inr (hD.mp h))
  · intro hlow
    exact hW.mp (hleft (by linarith))
  · intro hp
    linarith [hupper (hW.mpr hp)]

lemma own_pin_location {t a b cx cy:ℝ} (hc:ContainedChart a |b|) (hb:|b|<1/2)
    (hx0:0≤cx) (hy0:0≤cy) (hx:cx≤c0) (hy:cy≤c0)
    (ho:0≤centralMargin .own t a b cx cy) : PinLocation t a b := by
  have hcn : ContainedChart a |-b| := by simpa only [abs_neg] using hc
  have hbn : |-b|<1/2 := by simpa only [abs_neg] using hb
  have hor : 0≤centralMargin .own (Real.pi/2-t) a (-b) cy cx := by
    simpa only [own_margin_diagonal_identity] using ho
  rcases four_primary_quadrants t with hE | hN | hW | hS
  · obtain ⟨v,hv,he⟩ := hE
    exact Or.inl (own_east_data hc hx0 hy0 hx hy hv he ho)
  · obtain ⟨v,hv,he⟩ := hN
    have hr : ((Real.pi/2-t:ℝ):Direction)=(v:Direction) := by
      have hid : Real.pi/2-(Real.pi/2-v)=v := by ring
      calc
        ((Real.pi/2-t:ℝ):Direction) = (Real.pi/2-(Real.pi/2-v):ℝ) := by
          simp only [Real.Angle.coe_sub,he]
        _ = _ := congrArg (fun x:ℝ => (x:Direction)) hid
    exact Or.inr (Or.inl (east_data_diagonal (own_east_data hcn hy0 hx0 hy hx hv hr hor)))
  · obtain ⟨v,hv,he⟩ := hW
    exact Or.inr (Or.inr (Or.inl (own_west_data hc hb hx hy0 hy hv he ho)))
  · obtain ⟨v,hv,he⟩ := hS
    have hr : ((Real.pi/2-t:ℝ):Direction)=(Real.pi+v:ℝ) := by
      have hid : Real.pi/2-(-Real.pi/2-v)=Real.pi+v := by ring
      calc
        ((Real.pi/2-t:ℝ):Direction) = (Real.pi/2-(-Real.pi/2-v):ℝ) := by
          simp only [Real.Angle.coe_sub,he]
        _ = _ := congrArg (fun x:ℝ => (x:Direction)) hid
    exact Or.inr (Or.inr (Or.inr (west_data_diagonal (own_west_data hcn hbn hy hx0 hx hv hr hor))))

lemma east_cap_data {t a b cx cy:ℝ} (hc:ContainedChart a |b|) (hb:|b|<1/2)
    (hx0:0≤cx) (he:0≤centralMargin .east t a b cx cy) : EastPinData t a b := by
  have hm : (1/2+cx)+angularWidth t≤centerX t a b := by
    dsimp [centralMargin] at he
    linarith
  obtain ⟨v,hv,hphase,hpin⟩ := east_cap_pin hc hb (by linarith) hm
  have hbv := abs_lt.mp hv
  exact ⟨v,⟨by linarith [hbv.1],by linarith [hbv.2]⟩,hphase,
    by simpa [pin,polar] using hpin⟩

lemma west_cap_data {t a b cx cy:ℝ} (hc:ContainedChart a |b|) (hb:|b|<1/2)
    (hx:cx≤c0) (hw:0≤centralMargin .west t a b cx cy) : WestPinData t a b := by
  have hcore : coreRadius≤1/2-cx := by linarith [c0_add_coreRadius]
  have hm : (1/2-cx)+angularWidth (t-Real.pi)≤centerX (t-Real.pi) a b := by
    rw [west_cap_rotated_identity] at hw
    linarith
  obtain ⟨v,hv,he,hmv⟩ := deep_cap_faces (by linarith [hc.half_le]) hb hcore hc.abs_box hm
  have hphase : (t:Direction)=(Real.pi+v:ℝ) := by
    have hid : t=(t-Real.pi)+Real.pi := by ring
    have hcomm : v+Real.pi=Real.pi+v := by ring
    calc
      (t:Direction) = ((t-Real.pi)+Real.pi:ℝ) := congrArg (fun x:ℝ => (x:Direction)) hid
      _ = (v+Real.pi:ℝ) := by simp only [Real.Angle.coe_add,he]
      _ = _ := congrArg (fun x:ℝ => (x:Direction)) hcomm
  have hW : openSquare (orientedSquare t a b) (pin 2) ↔
      openSquare (orientedSquare v a b) (polar (9/10) (-Real.pi/12)) := by
    rw [square_phase_open hphase,pin_eq_polar]
    change openSquare (orientedSquare (Real.pi+v) a b) (polar (9/10) (11*Real.pi/12)) ↔ _
    have hT : Real.pi+v=v+Real.pi := by ring
    have hQ : 11*Real.pi/12=(-Real.pi/12)+Real.pi := by ring
    rw [hT,hQ,polar_rotate]
  have hD : openSquare (orientedSquare t a b) (pin 3) ↔
      openSquare (orientedSquare v a b) (polar (9/10) (Real.pi/4)) := by
    rw [square_phase_open hphase,pin_eq_polar]
    change openSquare (orientedSquare (Real.pi+v) a b) (polar (9/10) (5*Real.pi/4)) ↔ _
    have hT : Real.pi+v=v+Real.pi := by ring
    have hQ : 5*Real.pi/4=Real.pi/4+Real.pi := by ring
    rw [hT,hQ,polar_rotate]
  have hcovers := west_cap_pins hc hb hcore hv hmv
  have hvr := abs_lt.mp hv
  refine ⟨v,⟨by linarith [hvr.1],by linarith [hvr.2,Real.pi_gt_d2]⟩,hphase,?_,?_,?_⟩
  · exact hcovers.elim (fun h => Or.inl (hW.mpr h)) (fun h => Or.inr (hD.mpr h))
  · intro hleft
    exact hW.mpr (west_cap_left_pin hc hb hcore hv hleft hmv)
  · intro _
    linarith [hvr.2]

lemma north_east_diagonal_margin (t a b cx cy:ℝ) :
    centralMargin .east (Real.pi/2-t) a (-b) cy cx=centralMargin .north t a b cx cy := by
  simp only [centralMargin,centerX,centerY,angularWidth,Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub]
  ring

lemma south_west_diagonal_margin (t a b cx cy:ℝ) :
    centralMargin .west (Real.pi/2-t) a (-b) cy cx=centralMargin .south t a b cx cy := by
  simp only [centralMargin,centerX,centerY,angularWidth,Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub]
  ring

/-- An exterior square separated from C lies in one of the four pin locations. -/
theorem pin_location_of_separation {t a b cx cy:ℝ} (hc:ContainedChart a |b|)
    (hcore:AvoidsCore a |b|) (hx0:0≤cx) (hy0:0≤cy) (hx:cx≤c0) (hy:cy≤c0)
    (hs:∃ k,0≤centralMargin k t a b cx cy) : PinLocation t a b := by
  have hb := hc.u_lt_half hcore
  have hsec := Normalization.secondary_separators_fail (hc.u_le_U0 hcore) hx0 hy0 hx hy (t:=t)
  have hcn : ContainedChart a |-b| := by simpa only [abs_neg] using hc
  have hbn : |-b|<1/2 := by simpa only [abs_neg] using hb
  obtain ⟨k,hk⟩ := hs
  cases k
  · exact own_pin_location hc hb hx0 hy0 hx hy hk
  · change 0≤b-1/2-(-cx*Real.sin t+cy*Real.cos t)-(|Real.cos t|+|Real.sin t|)/2 at hk
    linarith [hsec.1]
  · change 0≤(-cx*Real.sin t+cy*Real.cos t)-1/2-(|Real.cos t|+|Real.sin t|)/2-b at hk
    linarith [hsec.2]
  · exact Or.inl (east_cap_data hc hb hx0 hk)
  · exact Or.inr (Or.inr (Or.inl (west_cap_data hc hb hx hk)))
  · have hr : 0≤centralMargin .east (Real.pi/2-t) a (-b) cy cx := by
      simpa only [north_east_diagonal_margin] using hk
    exact Or.inr (Or.inl (east_data_diagonal (east_cap_data hcn hbn hy0 hr)))
  · have hr : 0≤centralMargin .west (Real.pi/2-t) a (-b) cy cx := by
      simpa only [south_west_diagonal_margin] using hk
    exact Or.inr (Or.inr (Or.inr (west_data_diagonal (west_cap_data hcn hbn hy hr))))

/-- An exterior square separated from C covers one of the five pins. -/
theorem five_pin_cover {t a b cx cy:ℝ} (hc:ContainedChart a |b|) (hcore:AvoidsCore a |b|)
    (hx0:0≤cx) (hy0:0≤cy) (hx:cx≤c0) (hy:cy≤c0)
    (hs:∃ k,0≤centralMargin k t a b cx cy) :
    ∃ i:Fin 5,openSquare (orientedSquare t a b) (pin i) := by
  rcases pin_location_of_separation hc hcore hx0 hy0 hx hy hs with h | h | h | h
  · obtain ⟨v,hv,he,hp⟩ := h
    exact ⟨0,hp⟩
  · obtain ⟨v,hv,he,hp⟩ := h
    exact ⟨1,hp⟩
  · obtain ⟨v,hv,he,hp,_⟩ := h
    exact hp.elim (fun h=>⟨2,h⟩) (fun h=>⟨3,h⟩)
  · obtain ⟨v,hv,he,hp,_⟩ := h
    exact hp.elim (fun h=>⟨4,h⟩) (fun h=>⟨3,h⟩)

/-! ### Windows and allowed axes -/

open Normalization

private lemma window_inside_pi (i:Fin 5) {v:ℝ}
    (hv:(windowLower i:ℝ)<v ∧ v<(windowUpper i:ℝ)) : |v|<Real.pi := by
  apply abs_lt.mpr
  fin_cases i <;> norm_num [windowLower,windowUpper] at hv <;>
    constructor <;> linarith [hv.1,hv.2,Real.pi_gt_d2]

private lemma window_transport (i:Fin 5) {t u:ℝ}
    (ht:-Real.pi≤t-modelPhase i ∧ t-modelPhase i≤Real.pi)
    (he:(t:Direction)=(u:Direction))
    (hu:(windowLower i:ℝ)<u-modelPhase i ∧ u-modelPhase i<(windowUpper i:ℝ)) :
    (windowLower i:ℝ)<t-modelPhase i ∧ t-modelPhase i<(windowUpper i:ℝ) := by
  have htu := phase_eq_in_centered_window ht (window_inside_pi i hu) he
  simpa only [htu] using hu

/-- A square at a pin location that holds pin `i` and no other pin has its phase
in the window of `i`. -/
theorem window_for_unique_pin {t a b:ℝ} (i:Fin 5) (hloc:PinLocation t a b)
    (ht:-Real.pi≤t-modelPhase i ∧ t-modelPhase i≤Real.pi)
    (huniq:∀ j:Fin 5,openSquare (orientedSquare t a b) (pin j) → j=i) :
    (windowLower i:ℝ)<t-modelPhase i ∧ t-modelPhase i<(windowUpper i:ℝ) := by
  rcases hloc with hE | hN | hW | hS
  · obtain ⟨v,hv,he,hp⟩ := hE
    have hi : i=0 := (huniq 0 hp).symm
    subst i
    apply window_transport 0 ht he
    simpa [windowLower,windowUpper,modelPhase] using hv
  · obtain ⟨v,hv,he,hp⟩ := hN
    have hi : i=1 := (huniq 1 hp).symm
    subst i
    apply window_transport 1 ht he
    simpa [windowLower,windowUpper,modelPhase] using hv
  · obtain ⟨v,hv,he,hcover,hleft,hupper⟩ := hW
    rcases hcover with hpW | hpD
    · have hi : i=2 := (huniq 2 hpW).symm
      subst i
      apply window_transport 2 ht he
      simpa [windowLower,windowUpper,modelPhase] using And.intro hv.1 (hupper hpW)
    · have hi : i=3 := (huniq 3 hpD).symm
      subst i
      have hvlo : -Real.pi/12<v := by
        by_contra! hbad
        have hne := huniq 2 (hleft hbad)
        norm_num at hne
      apply window_transport 3 ht he
      norm_num [windowLower,windowUpper,modelPhase]
      constructor <;> linarith [hv.2,Real.pi_lt_d2]
  · obtain ⟨v,hv,he,hcover,hright,hlower⟩ := hS
    rcases hcover with hpS | hpD
    · have hi : i=4 := (huniq 4 hpS).symm
      subst i
      apply window_transport 4 ht he
      norm_num [windowLower,windowUpper,modelPhase]
      constructor <;> linarith [hlower hpS,hv.2]
    · have hi : i=3 := (huniq 3 hpD).symm
      subst i
      have hvhi : v<Real.pi/12 := by
        by_contra! hbad
        have hne := huniq 4 (hright hbad)
        norm_num at hne
      apply window_transport 3 ht he
      norm_num [windowLower,windowUpper,modelPhase]
      constructor <;> linarith [hv.1,Real.pi_lt_d2]

/-- A contained square that avoids the core, is separated from C, and holds pin
`i` and no other pin, has its phase in the window of `i`. -/
theorem labelled_window {t a b cx cy:ℝ} (i:Fin 5) (hc:ContainedChart a |b|)
    (hcore:AvoidsCore a |b|) (hx0:0≤cx) (hy0:0≤cy) (hx:cx≤c0) (hy:cy≤c0)
    (hs:∃ k,0≤centralMargin k t a b cx cy)
    (ht:-Real.pi≤t-modelPhase i ∧ t-modelPhase i≤Real.pi)
    (huniq:∀ j:Fin 5,openSquare (orientedSquare t a b) (pin j) → j=i) :
    (windowLower i:ℝ)<t-modelPhase i ∧ t-modelPhase i<(windowUpper i:ℝ) :=
  window_for_unique_pin i (pin_location_of_separation hc hcore hx0 hy0 hx hy hs) ht huniq

lemma pin_coordinates (i:Fin 5) : pin i =
    ![(9/10,0),(0,9/10),
      (-(9/10)*Real.cos (Real.pi/12),(9/10)*Real.sin (Real.pi/12)),
      (-(9/10)*Real.cos (Real.pi/4),-(9/10)*Real.sin (Real.pi/4)),
      ((9/10)*Real.sin (Real.pi/12),-(9/10)*Real.cos (Real.pi/12))] i := by
  fin_cases i
  · rfl
  · rfl
  · have h : (11/12)*Real.pi=Real.pi-Real.pi/12 := by ring
    simp [pin,h,Real.cos_pi_sub,Real.sin_pi_sub]
  · have h : (5/4)*Real.pi=Real.pi/4+Real.pi := by ring
    simp [pin,h,Real.cos_add_pi,Real.sin_add_pi]
  · have h : (19/12)*Real.pi=(Real.pi/12-Real.pi/2)+2*Real.pi := by ring
    simp [pin,h,Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub]

private lemma pin_trig_signs :
    0≤Real.cos (Real.pi/12) ∧ 0≤Real.sin (Real.pi/12) ∧
      Real.sin (Real.pi/12)≤1/3 ∧
      0≤Real.cos (Real.pi/4) ∧ 0≤Real.sin (Real.pi/4) := by
  have hcos : 0≤Real.cos (Real.pi/12) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0≤Real.pi/12 by positivity) (show Real.pi/12≤Real.pi by linarith [Real.pi_pos])
  have hu : Real.sin (Real.pi/12)≤1/3 := by
    have h := Real.sin_le (show 0≤Real.pi/12 by positivity)
    linarith [Real.pi_lt_d2]
  exact ⟨hcos,hsin,hu,by linarith [quarter_trig_lower.1],by linarith [quarter_trig_lower.2]⟩

lemma non_east_pin_x (i:Fin 5) (hi:i≠0) : (pin i).1≤3/10 := by
  rw [pin_coordinates]
  have h := pin_trig_signs
  revert hi
  fin_cases i <;> norm_num <;>
    nlinarith [h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,Real.sqrt_nonneg 2]

lemma non_north_pin_y (i:Fin 5) (hi:i≠1) : (pin i).2≤3/10 := by
  rw [pin_coordinates]
  have h := pin_trig_signs
  revert hi
  fin_cases i <;> norm_num <;>
    nlinarith [h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,Real.sqrt_nonneg 2]

lemma non_west_pin_x (i:Fin 5) (hiW:i≠2) (hiD:i≠3) : 0≤(pin i).1 := by
  rw [pin_coordinates]
  have h := pin_trig_signs
  revert hiW hiD
  fin_cases i <;> norm_num
  nlinarith [h.2.1]

lemma non_south_pin_y (i:Fin 5) (hiD:i≠3) (hiS:i≠4) : 0≤(pin i).2 := by
  rw [pin_coordinates]
  have h := pin_trig_signs
  revert hiD hiS
  fin_cases i <;> norm_num
  nlinarith [h.2.1]

/-- A square that holds pin `i` is separated from C only along an axis allowed
for `i`. -/
theorem allowed_axis_of_pin {t a b cx cy:ℝ} (i:Fin 5) (hc:ContainedChart a |b|)
    (hcore:AvoidsCore a |b|) (hx0:0≤cx) (hy0:0≤cy) (hx:cx≤c0) (hy:cy≤c0)
    (hpin:openSquare (orientedSquare t a b) (pin i))
    (k:CentralAxis) (hk:0≤centralMargin k t a b cx cy) : k∈allowed i := by
  have hp : closedSquare (orientedSquare t a b) (pin i) := ⟨hpin.1.le,hpin.2.le⟩
  have hsec := Normalization.secondary_separators_fail (hc.u_le_U0 hcore) hx0 hy0 hx hy (t:=t)
  cases k
  · fin_cases i <;> simp [allowed]
  · change 0≤b-1/2-(-cx*Real.sin t+cy*Real.cos t)-(|Real.cos t|+|Real.sin t|)/2 at hk
    linarith [hsec.1]
  · change 0≤(-cx*Real.sin t+cy*Real.cos t)-1/2-(|Real.cos t|+|Real.sin t|)/2-b at hk
    linarith [hsec.2]
  · by_cases hi:i=0
    · subst i; simp [allowed]
    · have hcap := east_margin_cap hk _ hp
      have hbound := non_east_pin_x i hi
      linarith
  · by_cases hiW:i=2
    · subst i; simp [allowed]
    · by_cases hiD:i=3
      · subst i; simp [allowed]
      · have hcap := west_margin_cap hk _ hp
        have hbound := non_west_pin_x i hiW hiD
        linarith [c0_bounds.2]
  · by_cases hi:i=1
    · subst i; simp [allowed]
    · have hcap := north_margin_cap hk _ hp
      have hbound := non_north_pin_y i hi
      linarith
  · by_cases hiD:i=3
    · subst i; simp [allowed]
    · by_cases hiS:i=4
      · subst i; simp [allowed]
      · have hcap := south_margin_cap hk _ hp
        have hbound := non_south_pin_y i hiD hiS
        linarith [c0_bounds.2]

end SquaresInCircles.Six

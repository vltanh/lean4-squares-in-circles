import SquaresInCircles.Six.Wings.WestSign
import SquaresInCircles.Six.Supports

/-!
# Six squares: the angle of D with W on its own axis

If W is separated from C along its own axis, the angle `d` of D exceeds `1/2`.
Suppose `d ≤ 1/2`; then `0 ≤ d`, and `0 ≤ v ≤ 2/3` with `v = -w`, since W turns
away from D; D is separated from C along its own axis, and W–D along the
secondary axis of W or of D. The stress with weights `(31, 44, 25)/100` or
`(42, 37, 21)/100` on C–D, C–W and W–D, whichever axis separates W and D, has a
nonpositive slack, the threshold sum minus the works of the forces. With the
centres kept as they are the slack is a constant plus harmonics in `v`, in `d`
and in `v + d`, and it is concave in each of `v` and `d` on
`[0, 2/3] × [0, 1/2]`, where the central terms compensate a negative coefficient
of `sin (v + d)`; at the four corners the far-vertex and cap supports bound it
below by positive numbers. So the slack is positive, a contradiction.
-/

noncomputable section
namespace SquaresInCircles.Six
open Normalization

/-- A constant plus harmonics in `v`, `d` and `v + d`: the form of the slack of a
stress, as a function of the angles, at given centres. -/
def threeHarmonics (C Av Bv Ad Bd Aq Bq v d : ℝ) : ℝ :=
  C+(Av*Real.cos v+Bv*Real.sin v)+(Ad*Real.cos d+Bd*Real.sin d)+
    (Aq*Real.cos (v+d)+Bq*Real.sin (v+d))

/-- `C + A cos x + B sin x + G cos (x + c) + H sin (x + c)` is concave where its
non-constant part is nonnegative. -/
lemma trig_sum_concave_of_nonnegative {C A B G H c l u : ℝ}
    (h : ∀ x∈Set.Icc l u,
      0≤A*Real.cos x+B*Real.sin x+G*Real.cos (x+c)+H*Real.sin (x+c)) :
    ConcaveOn ℝ (Set.Icc l u)
      (fun x => C+A*Real.cos x+B*Real.sin x+G*Real.cos (x+c)+H*Real.sin (x+c)) :=
  ((harmonic_concave (A := A+G*Real.cos c+H*Real.sin c) (B := B-G*Real.sin c+H*Real.cos c)
    fun x hx => (h x hx).trans_eq (by rw [Real.cos_add,Real.sin_add]; ring)).add_const C).congr
    fun x _ => by simp only [Pi.add_apply,harmonic]; rw [Real.cos_add,Real.sin_add]; ring

private lemma diagonal_trig {v d : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2) :
    (0≤Real.cos v ∧ 0≤Real.sin v ∧ Real.sin v≤5/8) ∧
    (7/8≤Real.cos d ∧ 0≤Real.sin d ∧ Real.sin d≤1/2) ∧
    (0≤Real.cos (v+d) ∧ 0≤Real.sin (v+d)) := by
  obtain ⟨hs,hs',hc,-⟩ := trig_bracket le_rfl (by linarith [Real.pi_gt_d2]) hv
  have hd' := small_angle_nonneg hd (by norm_num)
  norm_num at hs hs' hc hd'
  exact ⟨⟨by linarith,hs,by linarith⟩,⟨by linarith,hd'.2.1,hd'.2.2⟩,
    cos_sin_nonneg ⟨by linarith,by linarith [Real.pi_gt_d2]⟩⟩

private lemma compensated_v_curvature {A B G H v d : ℝ}
    (hA : 2849/20000≤A) (hB : 37/200≤B) (hG : 0≤G) (hH : -(613/4000)≤H)
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2) :
    0≤A*Real.cos v+B*Real.sin v+G*Real.cos (v+d)+H*Real.sin (v+d) := by
  obtain ⟨⟨hcv,hsv,_⟩,⟨hcd,hsd,hsdu⟩,⟨hcq,hsq⟩⟩ := diagonal_trig hv hd
  have h1 := mul_nonneg (sub_nonneg.mpr hA) hcv
  have h2 := mul_nonneg (sub_nonneg.mpr hB) hsv
  have h3 := mul_nonneg hG hcq
  have h4 := mul_nonneg (show 0≤H+613/4000 by linarith) hsq
  have h5 := mul_nonneg hsv (sub_nonneg.mpr (Real.cos_le_one d))
  have h6 := mul_nonneg hcv (sub_nonneg.mpr hsdu)
  have hq : Real.sin (v+d)≤Real.sin v+(1/2)*Real.cos v := by
    rw [Real.sin_add]
    nlinarith only [h5,h6]
  nlinarith only [h1,h2,h3,h4,hq,hcv,hsv]

private lemma compensated_d_curvature {A B G H v d : ℝ}
    (hA : 2387/20000≤A) (hB : 2387/20000≤B) (hG : 0≤G) (hH : -(613/4000)≤H)
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2) :
    0≤A*Real.cos d+B*Real.sin d+G*Real.cos (v+d)+H*Real.sin (v+d) := by
  obtain ⟨⟨_,_,hsvu⟩,⟨hcd,hsd,hsdu⟩,⟨hcq,hsq⟩⟩ := diagonal_trig hv hd
  have hcd0 : 0≤Real.cos d := by linarith
  have h1 := mul_nonneg (sub_nonneg.mpr hA) hcd0
  have h2 := mul_nonneg (sub_nonneg.mpr hB) hsd
  have h3 := mul_nonneg hG hcq
  have h4 := mul_nonneg (show 0≤H+613/4000 by linarith) hsq
  have h5 := mul_nonneg (sub_nonneg.mpr hsvu) hcd0
  have h6 := mul_nonneg (sub_nonneg.mpr (Real.cos_le_one v)) hsd
  have hq : Real.sin (v+d)≤(5/8)*Real.cos d+Real.sin d := by
    rw [Real.sin_add]
    nlinarith only [h5,h6]
  nlinarith only [h1,h2,h3,h4,hq,hcd,hsdu]

/-- Under the bounds on its coefficients, `threeHarmonics` is positive on
`[0, 2/3] × [0, 1/2]` as soon as it is positive at the four corners. -/
theorem threeHarmonics_positive {C Av Bv Ad Bd Aq Bq v d : ℝ}
    (hAv : 2849/20000≤Av) (hBv : 37/200≤Bv)
    (hAd : 2387/20000≤Ad) (hBd : 2387/20000≤Bd)
    (hAq : 0≤Aq) (hBq : -(613/4000)≤Bq)
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2)
    (h00 : 0<threeHarmonics C Av Bv Ad Bd Aq Bq 0 0)
    (h0D : 0<threeHarmonics C Av Bv Ad Bd Aq Bq 0 (1/2))
    (hV0 : 0<threeHarmonics C Av Bv Ad Bd Aq Bq (2/3) 0)
    (hVD : 0<threeHarmonics C Av Bv Ad Bd Aq Bq (2/3) (1/2)) :
    0<threeHarmonics C Av Bv Ad Bd Aq Bq v d := by
  have hfirst (y : ℝ) (hy : y∈Set.Icc 0 (1/2)) :
      ConcaveOn ℝ (Set.Icc 0 (2/3)) (fun x => threeHarmonics C Av Bv Ad Bd Aq Bq x y) := by
    have h := trig_sum_concave_of_nonnegative
      (C := C+Ad*Real.cos y+Bd*Real.sin y) (c := y)
      (fun x hx => compensated_v_curvature hAv hBv hAq hBq hx hy)
    apply h.congr
    intro x _
    dsimp [threeHarmonics]
    ring
  have hsecond (x : ℝ) (hx : x∈Set.Icc 0 (2/3)) :
      ConcaveOn ℝ (Set.Icc 0 (1/2)) (threeHarmonics C Av Bv Ad Bd Aq Bq x) := by
    have h := trig_sum_concave_of_nonnegative
      (C := C+Av*Real.cos x+Bv*Real.sin x) (c := x)
      (fun y hy => by simpa only [add_comm] using
        compensated_d_curvature hAd hBd hAq hBq hx hy)
    apply h.congr
    intro y _
    dsimp [threeHarmonics]
    ring_nf
  exact positive_on_separately_concave_rectangle hv hd hfirst
    (hsecond 0 (by constructor <;> norm_num))
    (hsecond (2/3) (by constructor <;> norm_num)) h00 h0D hV0 hVD

/-- The squared length of a constant vector plus a turning one. -/
lemma rotating_norm_sq (p mu q : ℝ) :
    (p+mu*Real.sin q)^2+(mu*Real.cos q)^2=p^2+mu^2+2*p*mu*Real.sin q := by
  linear_combination mu^2*(Real.sin_sq_add_cos_sq q)

namespace DiagonalAngle.Own

/-! W lies on its own axis at the angle `w = -v` and D at the angle `d`. W–D is
separated along the secondary axis of the source, D if `ds` and W otherwise; the
other square is the target. -/

/-- The weights on C–D, C–W and W–D. -/
def alpha (ds : Bool) : ℝ := if ds then 42/100 else 31/100
def beta (ds : Bool) : ℝ := if ds then 37/100 else 44/100
def mu (ds : Bool) : ℝ := if ds then 21/100 else 25/100

/-- The weights on the central edges of the square whose axis separates W and D
(the source, D if `ds`) and of the other square (the target). -/
def sourceWeight (ds : Bool) : ℝ := if ds then alpha ds else beta ds
def targetWeight (ds : Bool) : ℝ := if ds then beta ds else alpha ds

def westForce (ds : Bool) (q : ℝ) : Point :=
  if ds then (beta ds+mu ds*Real.sin q,-mu ds*Real.cos q)
  else (beta ds,-mu ds)

def diagonalForce (ds : Bool) (q : ℝ) : Point :=
  if ds then (alpha ds,mu ds)
  else (alpha ds+mu ds*Real.sin q,mu ds*Real.cos q)

/-- The threshold sum minus the works of the forces on W, D and C. -/
def slack (ds : Bool) (v d aw bw ad bd cx cy : ℝ) : ℝ :=
  1/2+(beta ds/2)*(Real.cos v+Real.sin v)+(alpha ds/2)*(Real.cos d+Real.sin d)+
    (mu ds/2)*(Real.cos (v+d)+Real.sin (v+d))-
    dot (westForce ds (v+d)) (aw,bw)-dot (diagonalForce ds (v+d)) (ad,bd)-
    ((beta ds*Real.cos v+alpha ds*Real.cos d)*cx+
      (alpha ds*Real.sin d-beta ds*Real.sin v)*cy)

/-- At given centres the slack is a constant plus harmonics in `v`, `d` and
`v + d`. -/
lemma slack_formula (ds : Bool) (v d aw bw ad bd cx cy : ℝ) :
    slack ds v d aw bw ad bd cx cy=
      threeHarmonics (1/2-beta ds*aw-alpha ds*ad+
        (if ds then -mu ds*bd else mu ds*bw))
        (beta ds*(1/2-cx)) (beta ds*(1/2+cy))
        (alpha ds*(1/2-cx)) (alpha ds*(1/2-cy))
        (mu ds*(if ds then 1/2+bw else 1/2-bd))
        (mu ds*(if ds then 1/2-aw else 1/2-ad)) v d := by
  cases ds <;> dsimp [slack,westForce,diagonalForce,threeHarmonics,dot] <;> ring

/-- A lower bound for `slack` from the far-vertex supports, given upper
bounds `L0` and `L` for the lengths of the force on the source, constant in its
frame, and of the force on the target. -/
lemma vertex_endpoint_lower (ds : Bool) {v d aw bw ad bd cx cy L0 L X Y : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hcos : 0≤Real.cos (v+d))
    (hL0 : 0≤L0) (hL : 0≤L)
    (hn0 : (sourceWeight ds)^2+(mu ds)^2≤L0^2)
    (hn : (targetWeight ds)^2+(mu ds)^2+
      2*targetWeight ds*mu ds*Real.sin (v+d)≤L^2)
    (hX : 0≤X) (hY : 0≤Y)
    (hcx : beta ds*Real.cos v+alpha ds*Real.cos d≤X)
    (hcy : alpha ds*Real.sin d-beta ds*Real.sin v≤Y) :
    1+(beta ds/2)*(Real.cos v+Real.sin v)+(alpha ds/2)*(Real.cos d+Real.sin d)+
      mu ds*(Real.cos (v+d)+Real.sin (v+d))-
      (1689/1000)*(L0+L)-(113/1000)*(X+Y)≤slack ds v d aw bw ad bd cx cy := by
  have hD' : ContainedChart ad |-bd| := by simpa only [abs_neg] using hD
  have hcentral := coarse_central_work hc hX hY hcx hcy
  cases ds
  · have hWb := vertex_linear_upper hW (U := 44/100) (V := 25/100) (by norm_num) hL0 hn0
    have hDb := vertex_linear_upper hD' (U := 31/100+(25/100)*Real.sin (v+d))
      (V := (25/100)*Real.cos (v+d)) (by positivity) hL
      (by rw [rotating_norm_sq]; exact hn)
    dsimp [slack,westForce,diagonalForce,alpha,beta,mu,dot] at hcentral ⊢
    nlinarith only [hWb,hDb,hcentral]
  · have hDb := vertex_linear_upper hD' (U := 42/100) (V := 21/100) (by norm_num) hL0 hn0
    have hWb := vertex_linear_upper hW (U := 37/100+(21/100)*Real.sin (v+d))
      (V := (21/100)*Real.cos (v+d)) (by positivity) hL
      (by rw [rotating_norm_sq]; exact hn)
    dsimp [slack,westForce,diagonalForce,alpha,beta,mu,dot] at hcentral ⊢
    nlinarith only [hWb,hDb,hcentral]

/-- The same with the cap bound for the force whose direction depends on the
angles, under its slope condition. -/
lemma cap_endpoint_lower (ds : Bool) {v d aw bw ad bd cx cy L0 X Y : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hcos : 0≤Real.cos (v+d)) (hsin : 0≤Real.sin (v+d))
    (hL0 : 0≤L0) (hn0 : (sourceWeight ds)^2+(mu ds)^2≤L0^2)
    (hslope : (rho0+1/2)*(mu ds*Real.cos (v+d))≤
      (targetWeight ds+mu ds*Real.sin (v+d))/2)
    (hX : 0≤X) (hY : 0≤Y)
    (hcx : beta ds*Real.cos v+alpha ds*Real.cos d≤X)
    (hcy : alpha ds*Real.sin d-beta ds*Real.sin v≤Y) :
    (1+sourceWeight ds+mu ds)/2+
      (beta ds/2)*(Real.cos v+Real.sin v)+(alpha ds/2)*(Real.cos d+Real.sin d)+
      (mu ds/2)*(Real.cos (v+d)+Real.sin (v+d))-
      (1689/1000)*L0-(1113/1000)*(targetWeight ds+mu ds*Real.sin (v+d))-
      (113/1000)*(X+Y)≤slack ds v d aw bw ad bd cx cy := by
  have hD' : ContainedChart ad |-bd| := by simpa only [abs_neg] using hD
  have hcentral := coarse_central_work hc hX hY hcx hcy
  cases ds
  · have hWb := vertex_linear_upper hW (U := 44/100) (V := 25/100) (by norm_num) hL0 hn0
    have hDb := cap_linear_upper hD' (U := 31/100+(25/100)*Real.sin (v+d))
      (V := (25/100)*Real.cos (v+d)) (by positivity) (by positivity) hslope
    dsimp [slack,westForce,diagonalForce,alpha,beta,mu,sourceWeight,targetWeight,
      dot] at hcentral ⊢
    nlinarith only [hWb,hDb,hcentral]
  · have hDb := vertex_linear_upper hD' (U := 42/100) (V := 21/100) (by norm_num) hL0 hn0
    have hWb := cap_linear_upper hW (U := 37/100+(21/100)*Real.sin (v+d))
      (V := (21/100)*Real.cos (v+d)) (by positivity) (by positivity) hslope
    dsimp [slack,westForce,diagonalForce,alpha,beta,mu,sourceWeight,targetWeight,
      dot] at hcentral ⊢
    nlinarith only [hWb,hDb,hcentral]

/-! Rational bounds for the lengths of the forces on the source and, at the
corners `v + d = 0`, `1/2` and `2/3`, on the target. -/

def sourceNorm (ds : Bool) : ℝ := if ds then 4696/10000 else 5061/10000
def normZero (ds : Bool) : ℝ := if ds then 4255/10000 else 3983/10000
def normHalf (ds : Bool) : ℝ := if ds then 5056/10000 else 4827/10000
def normFar (ds : Bool) : ℝ := if ds then 5265/10000 else 5046/10000

lemma sourceNorm_bound (ds : Bool) :
    0≤sourceNorm ds ∧ (sourceWeight ds)^2+(mu ds)^2≤(sourceNorm ds)^2 := by
  cases ds <;> norm_num [sourceNorm,sourceWeight,alpha,beta,mu]

lemma corner_zero (ds : Bool) {aw bw ad bd cx cy : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<slack ds 0 0 aw bw ad bd cx cy := by
  have h := vertex_endpoint_lower ds (v := 0) (d := 0)
    (L0 := sourceNorm ds) (L := normZero ds)
    (X := beta ds+alpha ds) (Y := 0)
    hW hD hc (by norm_num)
    (sourceNorm_bound ds).1
    (by cases ds <;> norm_num [normZero]) (sourceNorm_bound ds).2
    (by cases ds <;> norm_num [targetWeight,alpha,beta,mu,normZero])
    (by cases ds <;> norm_num [alpha,beta]) (by norm_num)
    (by norm_num) (by norm_num)
  cases ds <;> norm_num [alpha,beta,mu,sourceNorm,normZero] at h <;> linarith

lemma corner_half (ds : Bool) {aw bw ad bd cx cy : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<slack ds 0 (1/2) aw bw ad bd cx cy := by
  obtain ⟨hcl,hcu,hsl,hsu⟩ := trig_bracket_half
  have h := vertex_endpoint_lower ds (v := 0) (d := (1:ℝ)/2)
    (L0 := sourceNorm ds) (L := normHalf ds)
    (X := beta ds+alpha ds*Real.cos (1/2))
    (Y := alpha ds*Real.sin (1/2))
    hW hD hc (by simp only [zero_add]; linarith)
    (sourceNorm_bound ds).1
    (by cases ds <;> norm_num [normHalf]) (sourceNorm_bound ds).2
    (by cases ds <;> norm_num [targetWeight,alpha,beta,mu,normHalf] <;> nlinarith)
    (by cases ds <;> dsimp [alpha,beta] <;> nlinarith)
    (by cases ds <;> dsimp [alpha] <;> nlinarith)
    (by norm_num) (by norm_num)
  cases ds <;> norm_num [alpha,beta,mu,sourceNorm,normHalf] at h <;> linarith

lemma corner_far (ds : Bool) {aw bw ad bd cx cy : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<slack ds (2/3) 0 aw bw ad bd cx cy := by
  obtain ⟨hcl,hcu,hsl,hsu⟩ := trig_bracket_two_thirds
  have h := vertex_endpoint_lower ds (v := (2:ℝ)/3) (d := 0)
    (L0 := sourceNorm ds) (L := normFar ds)
    (X := beta ds*Real.cos (2/3)+alpha ds) (Y := 0)
    hW hD hc (by simp only [add_zero]; linarith)
    (sourceNorm_bound ds).1
    (by cases ds <;> norm_num [normFar]) (sourceNorm_bound ds).2
    (by cases ds <;> norm_num [targetWeight,alpha,beta,mu,normFar] <;> nlinarith)
    (by cases ds <;> dsimp [alpha,beta] <;> nlinarith) (by norm_num)
    (by norm_num)
    (by cases ds <;> norm_num [alpha,beta] <;> linarith)
  cases ds <;> norm_num [alpha,beta,mu,sourceNorm,normFar] at h <;> linarith

lemma corner_mixed (ds : Bool) {aw bw ad bd cx cy : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<slack ds (2/3) (1/2) aw bw ad bd cx cy := by
  obtain ⟨hvcl,hvcu,hvsl,hvsu⟩ := trig_bracket_two_thirds
  obtain ⟨hdcl,hdcu,hdsl,hdsu⟩ := trig_bracket_half
  obtain ⟨hqcl,hqcu,hqsl,hqsu⟩ := trig_bracket_seven_sixths
  have hq : (2:ℝ)/3+1/2=7/6 := by norm_num
  have hroot := mul_le_mul
    (show rho0+1/2≤1613/1000 by linarith [rho0_bounds.2]) hqcu
    (show 0≤Real.cos (7/6) by linarith) (by norm_num : (0:ℝ)≤1613/1000)
  have hslope : (rho0+1/2)*(mu ds*Real.cos (2/3+1/2))≤
      (targetWeight ds+mu ds*Real.sin (2/3+1/2))/2 := by
    rw [hq]
    cases ds <;> dsimp [mu,targetWeight,alpha,beta] <;> nlinarith
  have h := cap_endpoint_lower ds (v := (2:ℝ)/3) (d := (1:ℝ)/2)
    (L0 := sourceNorm ds)
    (X := beta ds*Real.cos (2/3)+alpha ds*Real.cos (1/2)) (Y := 0)
    hW hD hc (by rw [hq]; linarith) (by rw [hq]; linarith)
    (sourceNorm_bound ds).1 (sourceNorm_bound ds).2 hslope
    (by cases ds <;> dsimp [alpha,beta] <;> nlinarith) (by norm_num)
    le_rfl
    (by cases ds <;> dsimp [alpha,beta] <;> nlinarith)
  rw [hq] at h
  cases ds <;> norm_num [alpha,beta,mu,targetWeight,sourceWeight,sourceNorm] at h <;> linarith

/-- `slack` is positive at the four corners of `[0, 2/3] × [0, 1/2]`. -/
theorem corners (ds : Bool) {aw bw ad bd cx cy : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<slack ds 0 0 aw bw ad bd cx cy ∧
    0<slack ds 0 (1/2) aw bw ad bd cx cy ∧
    0<slack ds (2/3) 0 aw bw ad bd cx cy ∧
    0<slack ds (2/3) (1/2) aw bw ad bd cx cy :=
  ⟨corner_zero ds hW hD hc,corner_half ds hW hD hc,
    corner_far ds hW hD hc,corner_mixed ds hW hD hc⟩

/-- The slack is positive on `[0, 2/3] × [0, 1/2]`. -/
lemma slack_positive (ds : Bool) {v d aw bw ad bd cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hbW : |bw|<1/2) (hbD : |bd|<1/2)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<slack ds v d aw bw ad bd cx cy := by
  obtain ⟨h00,h0D,hV0,hVD⟩ := corners ds hW hD hc
  rw [slack_formula] at h00 h0D hV0 hVD ⊢
  have hcx : 77/200≤1/2-cx := by linarith [hc.1.2,c0_bounds.2]
  have hcy : 77/200≤1/2-cy := by linarith [hc.2.2,c0_bounds.2]
  have hplus : 1/2≤1/2+cy := by linarith [hc.2.1]
  have haw : aw≤1113/1000 := by linarith [hW.a_le_rho0,rho0_bounds.2]
  have had : ad≤1113/1000 := by linarith [hD.a_le_rho0,rho0_bounds.2]
  apply threeHarmonics_positive
    (by cases ds <;> dsimp [beta] <;> linarith)
    (by cases ds <;> dsimp [beta] <;> linarith)
    (by cases ds <;> dsimp [alpha] <;> linarith)
    (by cases ds <;> dsimp [alpha] <;> linarith)
    (by cases ds <;> dsimp [mu] <;> linarith [(abs_lt.mp hbW).1,(abs_lt.mp hbD).2])
    (by cases ds <;> dsimp [mu] <;> linarith)
    hv hd h00 h0D hV0 hVD

private lemma trig_bounds {v d : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2) :
    (0≤Real.cos v ∧ 0≤Real.sin v) ∧ (0≤Real.cos d ∧ 0≤Real.sin d) ∧
      (0≤Real.cos (v+d) ∧ 0≤Real.sin (v+d)) := by
  have h (x : ℝ) (hx : 0≤x ∧ x≤7/6) : 0≤Real.cos x ∧ 0≤Real.sin x :=
    ⟨Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2,Real.pi_gt_d2]⟩,
     Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_gt_d2])⟩
  exact ⟨h v ⟨hv.1,by linarith [hv.2]⟩,h d ⟨hd.1,by linarith [hd.2]⟩,
    h (v+d) ⟨by linarith [hv.1,hd.1],by linarith [hv.2,hd.2]⟩⟩

/-- The weighted sum of the separating inequalities of C–W, C–D and W–D:
`slack` is nonpositive. -/
lemma slack_nonpositive (ds : Bool) {v d aw bw ad bd cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2)
    (hCW : 0≤centralMargin .own (Real.pi-v) aw bw cx cy)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (if ds then normalY (orientedSquare (Real.pi+d) ad bd)
        else normalY (orientedSquare (Real.pi-v) aw bw))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center)) :
    slack ds v d aw bw ad bd cx cy≤0 := by
  obtain ⟨⟨hcv,hsv⟩,⟨hcd,hsd⟩,⟨hcq,hsq⟩⟩ := trig_bounds hv hd
  have hW : 1/2-aw+(1/2-cx)*Real.cos v+(1/2+cy)*Real.sin v≤0 := by
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
      abs_neg,abs_of_nonneg hcv,abs_of_nonneg hsv] at hCW
    nlinarith only [hCW]
  have hD : 1/2-ad+(1/2-cx)*Real.cos d+(1/2-cy)*Real.sin d≤0 := by
    have hcpi : Real.cos (Real.pi+d)=-Real.cos d := by rw [add_comm]; exact Real.cos_add_pi d
    have hspi : Real.sin (Real.pi+d)=-Real.sin d := by rw [add_comm]; exact Real.sin_add_pi d
    simp only [centralMargin,centralNormal,angularWidth,hcpi,hspi,
      abs_neg,abs_of_nonneg hcd,abs_of_nonneg hsd] at hCD
    nlinarith only [hCD]
  have hq : (Real.pi+d)-(Real.pi-v)=v+d := by ring
  cases ds
  · change SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      frameY (orientedSquare (Real.pi-v) aw bw)
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center) at hWD
    rw [oriented_pair_threshold,pair_frameY_left,hq,
      angularWidth,abs_of_nonneg hcq,abs_of_nonneg hsq] at hWD
    dsimp [slack,westForce,diagonalForce,alpha,beta,mu,dot]
    nlinarith only [hW,hD,hWD]
  · change SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      frameY (orientedSquare (Real.pi+d) ad bd)
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center) at hWD
    rw [oriented_pair_threshold,pair_frameY_right,hq,
      angularWidth,abs_of_nonneg hcq,abs_of_nonneg hsq] at hWD
    dsimp [slack,westForce,diagonalForce,alpha,beta,mu,dot]
    nlinarith only [hW,hD,hWD]

/-- For `0 ≤ v ≤ 2/3` and `0 ≤ d ≤ 1/2`, the separating inequalities of C–W,
C–D and W–D are inconsistent. -/
theorem impossible (ds : Bool) {v d aw bw ad bd cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hWcore : AvoidsCore aw |bw|) (hDcore : AvoidsCore ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hCW : 0≤centralMargin .own (Real.pi-v) aw bw cx cy)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (if ds then normalY (orientedSquare (Real.pi+d) ad bd)
        else normalY (orientedSquare (Real.pi-v) aw bw))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center)) : False := by
  have hpositive := slack_positive ds hv hd hW hD
    (hW.u_lt_half hWcore) (hD.u_lt_half hDcore) hc
  have hnegative := slack_nonpositive ds hv hd hCW hCD hWD
  linarith

end DiagonalAngle.Own

/-- If W is separated from C along its own axis, then `d > 1/2`. -/
theorem own_west_diagonal_gt_half {R : ℝ} (P : NormalizedPacking R)
    (hown : P.ownAxis 2=true) : 1/2<P.diagonalAngle := by
  by_contra! hd
  have hwneg := own_west_negative P hown
  have hv : 0≤-P.deviation 2 ∧ -P.deviation 2≤2/3 := by
    constructor <;> linarith [P.deviation_windows.2.2.1.1]
  have hdiag : 0≤P.diagonalAngle ∧ P.diagonalAngle≤1/2 :=
    ⟨P.diagonal_angle_range.1.le,hd⟩
  have hWphase : P.phase 2=Real.pi-(-P.deviation 2) := by
    rw [P.phase_from_deviation 2,show cardinalCenter (matchingCardinal 2)=Real.pi from rfl]
    ring
  have hDphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  obtain ⟨k,hsep,hcases⟩ := westDiagonal_secondary P
  rcases hcases with rfl | rfl
  · apply DiagonalAngle.Own.impossible false hv hdiag (P.contained 2) (P.contained 3)
      (P.avoidsCore 2) (P.avoidsCore 3) P.box
      (by simpa only [hWphase] using P.own_separator 2 hown)
      (by simpa only [hDphase] using P.own_separator 3 P.diagonal_own)
    change SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center) at hsep
    simpa only [Bool.false_eq_true,ite_false,P.square_def,hWphase,hDphase] using hsep
  · apply DiagonalAngle.Own.impossible true hv hdiag (P.contained 2) (P.contained 3)
      (P.avoidsCore 2) (P.avoidsCore 3) P.box
      (by simpa only [hWphase] using P.own_separator 2 hown)
      (by simpa only [hDphase] using P.own_separator 3 P.diagonal_own)
    simpa [pairNormal,P.square_def,hWphase,hDphase] using hsep

end SquaresInCircles.Six

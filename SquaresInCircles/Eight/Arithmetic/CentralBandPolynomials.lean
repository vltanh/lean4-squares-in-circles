module

public import Mathlib.Tactic
public import SquaresInCircles.Common.Analysis

/-!
# Eight squares: the polynomials of the central bands

In the half-angle variable `u`, with `c = (1 - u²)/(1 + u²)` and `s = 2u/(1 + u²)`, the sextic
`centralBandP C D u` is `(1 + u²)³` times `H² + H c (c + s) + (1/2 - Q0) c²`,
`H = 1/2 + C c - D s`, `Q0 = 9789/2500` (`centralBandP_normalized`), and a positive value of the
quartic `centralBandV A C D u` gives `C s + D c - A · 2u/(1 - u²) < 1/2`
(`centralBandV_normalized`). `Containing.lean` reads them as bounds on the two coordinates of an
exterior square, for the segment `{(11/12, y) : |y| ≤ 7/20}` and for the bands A and B of the
common points.

The sextics of the segment and of the bands are positive on `[0, 1]` (`segment_P_positive`,
`bandA_P_positive`, `bandB_P_positive`). Each is `c + b (u - u₀) + r(u) (u - u₀)²` with `b² < 4ac`
for a lower bound `a` of `r` on `[0, 1]`, which follows from writing `r` as a positive
combination of `u`, `u (1 - u)`, `u² (1 - u)` and `u² (1 - u²)`; one completed square concludes.
The constants of the bands reach their rational neighbours by monotonicity
(`centralBandP_mono`). The quartics are positive on `[0, 3/7]` (`segment_V_positive`,
`bandA_V_positive`, `bandB_V_positive`): their second derivative is at least `7/5` there
(`centralBandV_curvature`), and the tangent parabola at `u = 1/4` with that curvature is
positive.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.Arithmetic

def centralBandP (Cminus D u : ℝ) : ℝ :=
  let z := 1+u^2
  let c := 1-u^2
  let s := 2*u
  let H := z/2+Cminus*c-D*s
  H^2*z+H*c*(c+s)+(1/2-(9789 : ℝ)/2500)*c^2*z

def centralBandV (A Cplus D u : ℝ) : ℝ :=
  let z := 1+u^2
  let c := 1-u^2
  let s := 2*u
  c*z/2+A*s*z-Cplus*s*c-D*c^2

/-- The constants of the band A: `bandA_Cminus` and `bandA_Cplus` bracket
`(10007/10000) cos (3741/10000)`, and `bandA_D` exceeds `(10007/10000) sin (3741/10000)`
(`bandA_trig`). Those of the band B are the same with `41/40` and `19/50` (`bandB_trig`). -/
def bandA_Cminus : ℝ := (10007/10000)*(9308368/10000000)
def bandA_Cplus : ℝ := (10007/10000)*(9308369/10000000)
def bandA_D : ℝ := (10007/10000)*(365435/1000000)
def bandB_Cminus : ℝ := (41/40)*(9286/10000)
def bandB_Cplus : ℝ := (41/40)*(9287/10000)
def bandB_D : ℝ := (41/40)*(371/1000)

private theorem nonnegative_factors {u : ℝ} (hu : u∈Icc 0 1) :
    0≤u ∧ 0≤u*(1-u) ∧ 0≤u^2*(1-u) ∧ 0≤u^2*(1-u^2) := by
  have hs : u^2≤1 := by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
  exact ⟨hu.1,mul_nonneg hu.1 (sub_nonneg.mpr hu.2),
    mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu.2),
    mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hs)⟩

/-- If `p = c + b x + r x²` with `0 < a ≤ r` and `b² < 4 a c`, then `0 < p`, by one completed
square. -/
private theorem positive_of_remainder {p r a b c x : ℝ}
    (ha : 0<a) (hdisc : b^2<4*a*c) (hr : a≤r)
    (hid : p=c+b*x+r*x^2) : 0<p := by
  have hterm : 0≤4*a*(r-a)*x^2 :=
    mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hr)) (sq_nonneg x)
  have hscaled : 0<4*a*p := by
    calc
      0 < (2*a*x+b)^2+(4*a*c-b^2)+4*a*(r-a)*x^2 := by
        have hs := sq_nonneg (2*a*x+b)
        linarith
      _ = 4*a*p := by rw [hid]; ring
  exact pos_of_mul_pos_right hscaled (by positivity)

private def segmentR (u : ℝ) : ℝ :=
  (80651+5361332*u+5659640*u*(1-u)+24865400*u^2*(1-u)+
    41159875*u^2*(1-u^2))/11250000

private theorem segment_remainder (u : ℝ) :
    centralBandP (11/12) (7/20) u=
      1009541/156250000-(11807/11718750)*(u-2/5)+(u-2/5)^2*segmentR u := by
  norm_num [centralBandP,segmentR]
  ring

private theorem segmentR_lower {u : ℝ} (hu : u∈Icc 0 1) :
    1/200 ≤ segmentR u := by
  obtain ⟨hu0,h1,h2,h3⟩ := nonnegative_factors hu
  dsimp [segmentR]
  nlinarith

theorem segment_P_positive {u : ℝ} (hu : 0≤u ∧ u≤1) :
    0<centralBandP (11/12) (7/20) u := by
  apply positive_of_remainder (a := (1/200 : ℝ))
    (b := -(11807/11718750)) (c := 1009541/156250000)
    (r := segmentR u) (x := u-2/5)
  · norm_num
  · norm_num
  · exact segmentR_lower hu
  · simpa [sub_eq_add_neg,mul_comm] using segment_remainder u

private def bandAR (u : ℝ) : ℝ :=
  (2036745397849+1029147845214*u+8456151284640*u*(1-u)+
    16795576114200*u^2*(1-u)+23166664513875*u^2*(1-u^2))/6328125000000

private theorem bandA_remainder (u : ℝ) :
    centralBandP (23287/25000) (3657/10000) u=
      1127543919953/3559570312500000+
      (304816277161/26367187500000)*(u-7/15)+(u-7/15)^2*bandAR u := by
  norm_num [centralBandP,bandAR]
  ring

private theorem bandAR_lower {u : ℝ} (hu : u∈Icc 0 1) : 8/25≤bandAR u := by
  obtain ⟨hu0,h1,h2,h3⟩ := nonnegative_factors hu
  dsimp [bandAR]
  nlinarith

theorem bandA_coarse_P_positive {u : ℝ} (hu : 0≤u ∧ u≤1) :
    0<centralBandP (23287/25000) (3657/10000) u := by
  apply positive_of_remainder (a := (8/25 : ℝ))
    (b := 304816277161/26367187500000) (c := 1127543919953/3559570312500000)
    (r := bandAR u) (x := u-7/15)
  · norm_num
  · norm_num
  · exact bandAR_lower hu
  · simpa [mul_comm] using bandA_remainder u

private def bandBR (u : ℝ) : ℝ :=
  (179518421+38557484*u+660186260*u*(1-u)+1133199440*u^2*(1-u)+
    1465310704*u^2*(1-u^2))/400000000

private theorem bandB_remainder (u : ℝ) :
    centralBandP (4759/5000) (3803/10000) u=
      1608241/320000000-(21358779/400000000)*(u-1/2)+(u-1/2)^2*bandBR u := by
  norm_num [centralBandP,bandBR]
  ring

private theorem bandBR_lower {u : ℝ} (hu : u∈Icc 0 1) : 11/25≤bandBR u := by
  obtain ⟨hu0,h1,h2,h3⟩ := nonnegative_factors hu
  dsimp [bandBR]
  nlinarith

theorem bandB_coarse_P_positive {u : ℝ} (hu : 0≤u ∧ u≤1) :
    0<centralBandP (4759/5000) (3803/10000) u := by
  apply positive_of_remainder (a := (11/25 : ℝ))
    (b := -(21358779/400000000)) (c := 1608241/320000000)
    (r := bandBR u) (x := u-1/2)
  · norm_num
  · norm_num
  · exact bandBR_lower hu
  · simpa [sub_eq_add_neg,mul_comm] using bandB_remainder u

/-- On `[0, 1]`, `centralBandP C D u` increases with the cosine coefficient `C ≥ 0` and decreases
with the transverse coefficient `D` in `[0, 1/2)`. -/
theorem centralBandP_mono {u C C' D D' : ℝ}
    (hu : u∈Icc 0 1) (hC0 : 0≤C) (hC : C≤C')
    (hD0 : 0≤D') (hD : D'≤D) (hDhalf : D<1/2) :
    centralBandP C D u ≤ centralBandP C' D' u := by
  let z := 1+u^2
  let c := 1-u^2
  let s := 2*u
  let H := z/2+C*c-D*s
  let H' := z/2+C'*c-D'*s
  have hz : 0<z := by dsimp [z]; positivity
  have hc : 0≤c := by dsimp [c]; nlinarith [hu.1,hu.2,mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
  have hs : 0≤s := by dsimp [s]; linarith [hu.1]
  have hsz : s≤z := by dsimp [s,z]; nlinarith [sq_nonneg (u-1)]
  have hCc := mul_nonneg hC0 hc
  have hDs := mul_le_mul_of_nonneg_left hsz (show 0≤D by linarith)
  have hH : 0≤H := by
    dsimp [H]
    have hpos := mul_pos (show 0<1/2-D by linarith) hz
    nlinarith
  have hincC := mul_nonneg (sub_nonneg.mpr hC) hc
  have hincD := mul_nonneg (sub_nonneg.mpr hD) hs
  have hHH : H≤H' := by dsimp [H,H']; nlinarith
  have hdiff : centralBandP C' D' u-centralBandP C D u=
      (H'-H)*((H'+H)*z+c*(c+s)) := by
    dsimp [centralBandP,H,H',z,c,s]
    ring
  have hprod : 0≤(H'-H)*((H'+H)*z+c*(c+s)) := by
    apply mul_nonneg (sub_nonneg.mpr hHH)
    exact add_nonneg (mul_nonneg (by linarith) hz.le)
      (mul_nonneg hc (add_nonneg hc hs))
  linarith

theorem bandA_P_positive {u : ℝ} (hu : 0≤u ∧ u≤1) :
    0<centralBandP bandA_Cminus bandA_D u := by
  exact (bandA_coarse_P_positive hu).trans_le
    (centralBandP_mono hu (by norm_num) (by norm_num [bandA_Cminus])
      (by norm_num [bandA_D]) (by norm_num [bandA_D]) (by norm_num))

theorem bandB_P_positive {u : ℝ} (hu : 0≤u ∧ u≤1) :
    0<centralBandP bandB_Cminus bandB_D u := by
  exact (bandB_coarse_P_positive hu).trans_le
    (centralBandP_mono hu (by norm_num) (by norm_num [bandB_Cminus])
      (by norm_num [bandB_D]) (by norm_num [bandB_D]) (by norm_num))

theorem centralBandV_expanded (A C D u : ℝ) :
    centralBandV A C D u=
      1/2-D+2*(A-C)*u+2*D*u^2+2*(A+C)*u^3-(1/2+D)*u^4 := by
  dsimp [centralBandV]
  ring

def centralBandV1 (A C D u : ℝ) : ℝ :=
  2*(A-C)+4*D*u+6*(A+C)*u^2-4*(1/2+D)*u^3

def centralBandV2 (A C D u : ℝ) : ℝ :=
  4*D+12*u*(A+C-(1/2+D)*u)

theorem centralBandV_derivatives (A C D u : ℝ) :
    HasDerivAt (centralBandV A C D) (centralBandV1 A C D u) u ∧
      HasDerivAt (centralBandV1 A C D) (centralBandV2 A C D u) u := by
  constructor
  · have hf : centralBandV A C D=
        fun x => 1/2-D+2*(A-C)*x+2*D*x^2+2*(A+C)*x^3-(1/2+D)*x^4 := by
      funext x
      exact centralBandV_expanded A C D x
    rw [hf]
    have h := (((((hasDerivAt_id u).const_mul (2*(A-C))).const_add (1/2-D)).add
        ((hasDerivAt_pow 2 u).const_mul (2*D))).add
        ((hasDerivAt_pow 3 u).const_mul (2*(A+C)))).sub
        ((hasDerivAt_pow 4 u).const_mul (1/2+D))
    convert h using 1
    · funext x
      simp only [id,Pi.add_apply,Pi.sub_apply]
    · norm_num [centralBandV1]
      ring
  · have h := ((((hasDerivAt_id u).const_mul (4*D)).const_add (2*(A-C))).add
        ((hasDerivAt_pow 2 u).const_mul (6*(A+C)))).sub
        ((hasDerivAt_pow 3 u).const_mul (4*(1/2+D)))
    convert h using 1
    · funext x
      simp only [centralBandV1,id,Pi.add_apply,Pi.sub_apply]
    · norm_num [centralBandV2]
      ring

/-- For `A ≥ 1/2`, `C ≥ 9/10` and `7/20 ≤ D ≤ 2/5`, the second derivative of
`centralBandV A C D` is at least `7/5` on `[0, 3/7]`. -/
theorem centralBandV_curvature {A C D u : ℝ}
    (hA : 1/2≤A) (hC : 9/10≤C) (hD : 7/20≤D) (hD' : D≤2/5)
    (hu : u∈Icc 0 (3/7 : ℝ)) : 7/5≤centralBandV2 A C D u := by
  have hm := mul_le_mul_of_nonneg_right (show 1/2+D≤9/10 by linarith) hu.1
  have hm' := mul_le_mul_of_nonneg_left hu.2 (by norm_num : (0:ℝ)≤9/10)
  have hbrace : 0≤A+C-(1/2+D)*u := by linarith
  have hp := mul_nonneg hu.1 hbrace
  unfold centralBandV2
  nlinarith

private theorem centralBandV_positive_of_base {A C D u : ℝ}
    (hA : 1/2≤A) (hC : 9/10≤C) (hD : 7/20≤D) (hD' : D≤2/5)
    (hu : u∈Icc 0 (3/7 : ℝ))
    (hbase : (centralBandV1 A C D (1/4))^2 <
      2*(7/5)*centralBandV A C D (1/4)) : 0<centralBandV A C D u := by
  exact positive_of_curvature (κ := (7/5 : ℝ)) (t := (1/4 : ℝ)) (by norm_num)
    hu (by norm_num)
    (fun x hx => (centralBandV_derivatives A C D x).1)
    (fun x hx => (centralBandV_derivatives A C D x).2)
    (fun x hx => centralBandV_curvature hA hC hD hD' hx) hbase

theorem segment_V_positive {u : ℝ} (hu : 0≤u ∧ u≤3/7) :
    0<centralBandV (1/2) (11/12) (7/20) u := by
  apply centralBandV_positive_of_base (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hu
  norm_num [centralBandV,centralBandV1]

theorem bandA_V_positive {u : ℝ} (hu : 0≤u ∧ u≤3/7) :
    0<centralBandV (5007/10000) bandA_Cplus bandA_D u := by
  apply centralBandV_positive_of_base (by norm_num) (by norm_num [bandA_Cplus])
    (by norm_num [bandA_D]) (by norm_num [bandA_D]) hu
  norm_num [centralBandV,centralBandV1,bandA_Cplus,bandA_D]

theorem bandB_V_positive {u : ℝ} (hu : 0≤u ∧ u≤3/7) :
    0<centralBandV (107/200) bandB_Cplus bandB_D u := by
  apply centralBandV_positive_of_base (by norm_num) (by norm_num [bandB_Cplus])
    (by norm_num [bandB_D]) (by norm_num [bandB_D]) hu
  norm_num [centralBandV,centralBandV1,bandB_Cplus,bandB_D]

theorem centralBandP_normalized (Cminus D u : ℝ) :
    centralBandP Cminus D u/(1+u^2)^3 =
      (1/2+Cminus*((1-u^2)/(1+u^2))-D*(2*u/(1+u^2)))^2+
      (1/2+Cminus*((1-u^2)/(1+u^2))-D*(2*u/(1+u^2)))*
        ((1-u^2)/(1+u^2))*(((1-u^2)/(1+u^2))+(2*u/(1+u^2)))+
      (1/2-(9789 : ℝ)/2500)*((1-u^2)/(1+u^2))^2 := by
  have hz : (1+u^2 : ℝ)≠0 := ne_of_gt (by positivity)
  unfold centralBandP
  field_simp [hz]

theorem centralBandV_normalized {A Cplus D u : ℝ} (hu : 0≤u ∧ u≤3/7)
    (hp : 0<centralBandV A Cplus D u) :
    Cplus*(2*u/(1+u^2))+D*((1-u^2)/(1+u^2))-
      A*(2*u/(1-u^2))<1/2 := by
  have hu2 : u^2≤9/49 := by
    nlinarith [mul_nonneg (show 0≤3/7-u by linarith) (show 0≤3/7+u by linarith)]
  have hc : 0<1-u^2 := by linarith
  have hz : 0<1+u^2 := by positivity
  have hid : centralBandV A Cplus D u/((1-u^2)*(1+u^2))=
      1/2-Cplus*(2*u/(1+u^2))-D*((1-u^2)/(1+u^2))+A*(2*u/(1-u^2)) := by
    unfold centralBandV
    field_simp [ne_of_gt hc,ne_of_gt hz]
    ring
  have hq := div_pos hp (mul_pos hc hz)
  rw [hid] at hq
  linarith

end SquaresInCircles.Eight.Arithmetic
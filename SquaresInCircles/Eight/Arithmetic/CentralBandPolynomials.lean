module

public import SquaresInCircles.Common.Analysis
public import SquaresInCircles.Common.Trigonometry
public import Mathlib.Tactic

/-!
# Central bands from whole-interval polynomial identities

Uncompiled replacement of the nineteen generated Bernstein cells.
Source: HAND_CENTRAL_BANDS_WITHOUT_TABLES.md, Sections 2--4.

The sextics use one Taylor remainder identity on [0,1], written as a
positive combination of u, u(1-u), u²(1-u), u²(1-u²). The quartics share
one curvature bound on [0,3/7]. No subdivision, recursive box decision,
generated certificate module, or external oracle is imported.

The old public constants and normalized interfaces are retained. Their
comparison with the slightly coarser hand-proof constants is monotone.
The three positivity theorems quantify the entire original closed domains.
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

/-- Historical aliases are preserved for the surrounding geometric adapters. -/
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

/-- A Taylor remainder lower bound implies positivity by one completed square.
All coefficients are real; the concrete substitutions below are exact rationals. -/
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
  exact pos_of_mul_pos_left hscaled (by positivity)

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

/-- Increasing the cosine coefficient or decreasing the transverse allowance
increases the outer-circle comparison polynomial on the entire quadrant. -/
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
  · have h := ((((hasDerivAt_const u (1/2-D)).add
        ((hasDerivAt_id u).const_mul (2*(A-C)))).add
        (((hasDerivAt_id u).pow 2).const_mul (2*D))).add
        (((hasDerivAt_id u).pow 3).const_mul (2*(A+C)))).sub
        (((hasDerivAt_id u).pow 4).const_mul (1/2+D))
    convert h using 1
    · funext x
      rw [centralBandV_expanded]
    · dsimp [centralBandV1]
      ring
  · convert ((((hasDerivAt_const u (2*(A-C))).add
        ((hasDerivAt_id u).const_mul (4*D))).add
        (((hasDerivAt_id u).pow 2).const_mul (6*(A+C)))).sub
        (((hasDerivAt_id u).pow 3).const_mul (4*(1/2+D))) using 1 <;>
      dsimp [centralBandV1,centralBandV2] <;> ring

/-- One common curvature estimate, not three collections of interval cells. -/
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

/-- Coarser hand constants are also exported for new geometric proofs. -/
theorem bandA_coarse_V_positive {u : ℝ} (hu : 0≤u ∧ u≤3/7) :
    0<centralBandV (5007/10000) (93149/100000) (3657/10000) u := by
  apply centralBandV_positive_of_base (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hu
  norm_num [centralBandV,centralBandV1]

theorem bandB_coarse_V_positive {u : ℝ} (hu : 0≤u ∧ u≤3/7) :
    0<centralBandV (107/200) (119/125) (3803/10000) u := by
  apply centralBandV_positive_of_base (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hu
  norm_num [centralBandV,centralBandV1]

theorem centralBandP_normalized (Cminus D u : ℝ) :
    centralBandP Cminus D u/(1+u^2)^3 =
      (1/2+Cminus*((1-u^2)/(1+u^2))-D*(2*u/(1+u^2)))^2+
      (1/2+Cminus*((1-u^2)/(1+u^2))-D*(2*u/(1+u^2)))*
        ((1-u^2)/(1+u^2))*(((1-u^2)/(1+u^2))+(2*u/(1+u^2)))+
      (1/2-(9789 : ℝ)/2500)*((1-u^2)/(1+u^2))^2 := by
  have hz : (1+u^2 : ℝ)≠0 := ne_of_gt (by positivity)
  unfold centralBandP
  field_simp [hz]
  ring

/-- Increasing quadratic comparison, with the positive branch explicit. -/
theorem root_lt_of_quadratic_positive {X Y B C : ℝ}
    (hX : 0≤X) (hY : 0<Y) (hB : 0≤B)
    (hroot : X^2+B*X+C=0) (hpoly : 0<Y^2+B*Y+C) : X<Y := by
  by_contra h
  have hYX : Y≤X := le_of_not_gt h
  have hp := mul_nonneg (sub_nonneg.mpr hYX) (show 0≤X+Y+B by linarith)
  nlinarith

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
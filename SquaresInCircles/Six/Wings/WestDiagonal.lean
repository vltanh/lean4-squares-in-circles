import SquaresInCircles.Six.Wings.WestRange

/-!
# Six squares: a missing west wing with W on its own axis

Let W be separated from C along its own axis at the angle `v`, W and D along
the secondary axis of D, and D and S along the secondary axis of S, so that
`16/25 ≤ d ≤ 11/14` and `53/50 - d ≤ v ≤ 31/50` (`WestRange`). Weights `41/20`
on C–W, `γ` on C–S and `1` on W–D and on D–S give D the force
`(cos r, 1 - sin r)`, `r = d - s`, of length `√2 (cos (r/2) - sin (r/2))`; with
`√2 < 1.415` its far vertex leaves the concave `diagonalTerm` in `r`. W takes
the cone support and C the corner of the box. The rest of the profile is
concave in `v`, along the wall `d + v = 53/50` and increasing in `d` along
`v = 31/50`, so it is positive once it is at three boundary points in `(v, d)`.
With S on the south side of C, `γ = 3/2` and the far vertex of S, with the
tangent at `9/5` to the square root of the squared length of its force, make
the profile concave in `|s|`. With S on its own axis, `γ` is constant on each of
the pieces `[0, 3/20]`, `[3/20, 3/10]` and `[3/10, 12/25]` of the range of `s`,
so that the force `(γ, 1)` on S has a constant length and the profile is
concave in `s` on each piece.
-/

noncomputable section
namespace SquaresInCircles.Six.Wings.WestDiagonal
open Normalization

/-! ### The term of D

With the weights `1` on W–D and on D–S the force on D is `(cos r, 1 - sin r)`,
`r = d - s`, of length `√2 · halfDifference r` (`norm_identity`), at most
`rootSlope · halfDifference r` with the bracket `rootSlope` of `√2`. With its
far-vertex support it leaves in the profile the term `diagonalTerm r`, where
`rootCoefficient = radiusBound · rootSlope`; `diagonalFirst` and
`diagonalSecond` are its derivatives. -/

def rootSlope : ℝ := 1.415
def halfDifference (r : ℝ) : ℝ := Real.cos (r/2)-Real.sin (r/2)
def rootCoefficient : ℝ := radiusBound*rootSlope

def diagonalTerm (r : ℝ) : ℝ :=
  Real.cos r-rootCoefficient*Real.cos (r/2)+rootCoefficient*Real.sin (r/2)
def diagonalFirst (r : ℝ) : ℝ :=
  -Real.sin r+(rootCoefficient/2)*(Real.sin (r/2)+Real.cos (r/2))
def diagonalSecond (r : ℝ) : ℝ :=
  -Real.cos r+(rootCoefficient/4)*(Real.cos (r/2)-Real.sin (r/2))

lemma half_difference_lower {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 6/5) :
    0 ≤ halfDifference r := by
  have h := sin_le_cos_of_small (x := r/2)
    ⟨by linarith [hr.1],by linarith [hr.2,Real.pi_gt_d2]⟩
  dsimp [halfDifference]
  linarith

lemma norm_identity (r : ℝ) :
    (Real.cos r)^2+(1-Real.sin r)^2=2*(halfDifference r)^2 := by
  have hs : Real.sin r=2*Real.sin (r/2)*Real.cos (r/2) := by
    simpa only [show 2*(r/2)=r by ring] using Real.sin_two_mul (r/2)
  dsimp [halfDifference]
  linear_combination Real.sin_sq_add_cos_sq r-2*Real.sin_sq_add_cos_sq (r/2)-2*hs

lemma norm_upper {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 6/5) :
    Real.sqrt ((Real.cos r)^2+(1-Real.sin r)^2) ≤ rootSlope*halfDifference r := by
  have hu := half_difference_lower hr
  rw [norm_identity]
  refine Real.sqrt_le_iff.mpr ⟨mul_nonneg (by norm_num [rootSlope]) hu,?_⟩
  dsimp [rootSlope]
  nlinarith [sq_nonneg (halfDifference r)]

/-- The far-vertex bound for the work of the force on D. -/
def diagonalUpper (r : ℝ) : ℝ :=
  radiusBound*(rootSlope*halfDifference r)-(Real.cos r+1-Real.sin r)/2

lemma support {a b r : ℝ} (hc : ContainedChart a |b|) (hr : 0 ≤ r ∧ r ≤ 6/5) :
    Real.cos r*a+(1-Real.sin r)*b ≤ diagonalUpper r := by
  have h := local_vertex_support hc (Real.cos r) (1-Real.sin r)
  have hm := mul_le_mul ceiling_bounds.1 (norm_upper hr) (Real.sqrt_nonneg _)
    (by norm_num [radiusBound])
  have hw : Real.cos r+1-Real.sin r ≤ |Real.cos r|+|1-Real.sin r| := by
    linarith [le_abs_self (Real.cos r),le_abs_self (1-Real.sin r)]
  dsimp only [diagonalUpper]
  linarith

lemma diagonal_hasDeriv (r : ℝ) : HasDerivAt diagonalTerm (diagonalFirst r) r := by
  convert (((Real.hasDerivAt_cos r).sub
    ((((hasDerivAt_id r).div_const 2).cos).const_mul rootCoefficient)).add
    ((((hasDerivAt_id r).div_const 2).sin).const_mul rootCoefficient)) using 1
  · funext y; simp only [diagonalTerm,Pi.add_apply,Pi.sub_apply,id_eq]
  · dsimp [diagonalFirst]; ring

lemma diagonal_first_hasDeriv (r : ℝ) : HasDerivAt diagonalFirst (diagonalSecond r) r := by
  convert (((Real.hasDerivAt_sin r).const_mul (-1)).add
    (((((hasDerivAt_id r).div_const 2).sin).add
      (((hasDerivAt_id r).div_const 2).cos)).const_mul (rootCoefficient/2))) using 1
  · funext y; simp only [diagonalFirst,Pi.add_apply,id_eq]; ring
  · dsimp [diagonalSecond]; ring

lemma diagonal_second_nonpositive {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 6/5) :
    diagonalSecond r ≤ 0 := by
  have hu := half_difference_lower hr
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ r/2 by linarith [hr.1])
    (show r/2 ≤ Real.pi by linarith [hr.2,Real.pi_gt_d2])
  have hc := Real.cos_nonneg_of_mem_Icc
    (show r/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hr.1,hr.2,Real.pi_gt_d2])
  have hsum : 1 ≤ Real.cos (r/2)+Real.sin (r/2) := by
    have hp := mul_nonneg hs hc
    nlinarith [Real.sin_sq_add_cos_sq (r/2)]
  have hcoef : -(Real.cos (r/2)+Real.sin (r/2))+rootCoefficient/4 ≤ 0 := by
    dsimp [rootCoefficient,rootSlope,radiusBound]
    linarith
  have hp := mul_nonpos_of_nonneg_of_nonpos hu hcoef
  have hid : Real.cos r=halfDifference r*(Real.cos (r/2)+Real.sin (r/2)) := by
    have h := Real.cos_two_mul (r/2)
    rw [show 2*(r/2)=r by ring] at h
    dsimp [halfDifference]
    nlinarith only [h,Real.sin_sq_add_cos_sq (r/2)]
  dsimp [diagonalSecond]
  rw [hid]
  dsimp [halfDifference] at hp ⊢
  nlinarith only [hp]

lemma diagonal_concave : ConcaveOn ℝ (Set.Icc 0 (6/5)) diagonalTerm :=
  concave_of_deriv2 (fun x _ => diagonal_hasDeriv x) (fun x _ => diagonal_first_hasDeriv x)
    fun _ h => diagonal_second_nonpositive h

lemma diagonal_first_lower {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 6/5) :
    7/10 ≤ diagonalFirst r := by
  have hm : MonotoneOn (fun x => -diagonalFirst x) (Set.Icc 0 (6/5)) := by
    have hd (x : ℝ) : HasDerivAt (fun x => -diagonalFirst x) (-diagonalSecond x) x :=
      (diagonal_first_hasDeriv x).neg
    apply monoOn_of_hasDeriv_nonneg (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => hd x)
    intro x hx
    exact neg_nonneg.mpr (diagonal_second_nonpositive ⟨hx.1.le,hx.2.le⟩)
  have h := hm hr (by norm_num : (6:ℝ)/5 ∈ Set.Icc 0 (6/5)) hr.2
  have he : 7/10 ≤ diagonalFirst (6/5) := by
    have hs := sin_upper_five (x := (6:ℝ)/5) (by norm_num)
    have hc := cos_lower_six (x := (3:ℝ)/5) (by norm_num)
    have ht := sin_lower_seven (x := (3:ℝ)/5) (by norm_num)
    dsimp [diagonalFirst,rootCoefficient,rootSlope,radiusBound]
    norm_num
    nlinarith only [hs,hc,ht]
  linarith

/-! ### The profile in `v` and `d`

With the weight `beta` on C–W, the terms of W, of the separation W–D and of D
make up `base v s d = beta · wing v + gapTerm (v + d) + diagonalTerm (d - s)`. It
is concave in `v`, concave along the wall `d + v = 53/50` and increasing in `d`
along `v = 31/50`, so it is positive once it is positive at three boundary
points. -/

def beta : ℝ := 41/20

def wing (v : ℝ) : ℝ := A*Real.cos v+B*Real.sin v
def gapTerm (q : ℝ) : ℝ := (1/2)*Real.cos q-B*Real.sin q

def base (v s d : ℝ) : ℝ := beta*wing v+gapTerm (v+d)+diagonalTerm (d-s)

/-- The three boundary points `(v, d)` of the domain. -/
def pointV : Fin 3 → ℝ := ![53/50-16/25,53/50-11/14,31/50]
def pointD : Fin 3 → ℝ := ![16/25,11/14,16/25]

private lemma wing_concave : ConcaveOn ℝ (Set.Icc 0 (2/3)) wing :=
  harmonic_concave fun _ hx => harmonic_nonneg (by norm_num [A]) (by norm_num [B])
    ⟨hx.1,by linarith [hx.2,Real.pi_gt_d2]⟩

lemma west_concave {s d : ℝ} (hd : 16/25 ≤ d ∧ d ≤ 11/14) :
    ConcaveOn ℝ (Set.Icc 0 (31/50)) (fun v => base v s d) := by
  let a := beta*A+(1/2)*Real.cos d-B*Real.sin d
  let b := beta*B-(1/2)*Real.sin d-B*Real.cos d
  have hcd := Real.cos_nonneg_of_mem_Icc
    (show d ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_gt_d2])
  have hA : 0 ≤ a := by
    dsimp [a,beta,A,B]
    linarith [Real.sin_le_one d]
  have hB : 0 ≤ b := by
    have h := adverse_harmonic d
    dsimp [b,beta,B,B] at *
    linarith
  have h := (concaveOn_const (diagonalTerm (d-s)) (convex_Icc 0 (31/50))).add
    (harmonic_concave fun _ hx => harmonic_nonneg hA hB ⟨hx.1,by linarith [hx.2,Real.pi_gt_d2]⟩)
  convert h using 1
  funext v
  dsimp [base,wing,gapTerm,harmonic,a,b]
  rw [Real.cos_add,Real.sin_add]
  ring

lemma wall_concave {s : ℝ} (hs : -(2/5) ≤ s ∧ s ≤ 12/25) :
    ConcaveOn ℝ (Set.Icc (16/25) (11/14)) (fun d => base (53/50-d) s d) := by
  have hw0 := concave_affine_argument (a := -1) (b := 53/50) wing_concave
    (l := 16/25) (u := 11/14) (by
      intro d hd
      constructor <;> linarith [hd.1,hd.2])
  have hw : ConcaveOn ℝ (Set.Icc (16/25) (11/14)) (fun d => beta*wing (53/50-d)) := by
    have h := hw0.smul (by norm_num [beta] : 0 ≤ beta)
    convert h using 1
    funext d
    simp only [smul_eq_mul]
    congr 2
    ring
  have hr0 := concave_affine_argument (a := 1) (b := -s) diagonal_concave
    (l := 16/25) (u := 11/14) (by
      intro d hd
      constructor <;> linarith [hd.1,hd.2,hs.1,hs.2])
  have hr : ConcaveOn ℝ (Set.Icc (16/25) (11/14)) (fun d => diagonalTerm (d-s)) := by
    simpa only [one_mul,sub_eq_add_neg] using hr0
  have h := (hw.add (concaveOn_const (gapTerm (53/50)) (convex_Icc (16/25) (11/14)))).add hr
  convert h using 1
  funext d
  dsimp [base]
  rw [show 53/50-d+d=(53:ℝ)/50 by ring]

lemma top_monotone {s : ℝ} (hs : -(2/5) ≤ s ∧ s ≤ 12/25) :
    MonotoneOn (fun d => base (31/50) s d) (Set.Icc (16/25) (11/14)) := by
  have hf (d : ℝ) : HasDerivAt (fun x => base (31/50) s x)
      (-(1/2)*Real.sin (31/50+d)-B*Real.cos (31/50+d)+diagonalFirst (d-s)) d := by
    have hc := (((hasDerivAt_id d).const_add (31/50)).cos).const_mul (1/2)
    have hs' := (((hasDerivAt_id d).const_add (31/50)).sin).const_mul B
    have hr := (diagonal_hasDeriv (d-s)).comp d ((hasDerivAt_id d).sub_const s)
    convert ((hc.sub hs').add hr).const_add (beta*wing (31/50)) using 1
    · funext y
      simp only [base,gapTerm,Pi.add_apply,Pi.sub_apply,Function.comp_apply,id_eq]
      ring
    · dsimp [base,gapTerm]; ring
  apply monoOn_of_hasDeriv_nonneg
    (by dsimp [base,gapTerm,diagonalTerm]; fun_prop) (fun d _ => hf d)
  intro d hd
  have hr : 0 ≤ d-s ∧ d-s ≤ 6/5 := by
    constructor <;> linarith [hd.1,hd.2,hs.1,hs.2]
  have hD := diagonal_first_lower hr
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ) ≤ 63/50)
    (show 31/50+d ≤ Real.pi by linarith [hd.2,Real.pi_gt_d2])
    (show (63:ℝ)/50 ≤ 31/50+d by linarith [hd.1])
  have ht := cos_upper_four (x := (63:ℝ)/50) (by norm_num)
  have hcos : Real.cos (31/50+d) ≤ 8/25 := by nlinarith only [hmono,ht]
  dsimp [B]
  linarith [Real.sin_le_one (31/50+d)]

/-- Positivity on the domain from the three boundary points; the constant `K`
may depend on `s`. -/
theorem positive_of_three_points {K v s d : ℝ}
    (hs : -(2/5) ≤ s ∧ s ≤ 12/25) (hd : 16/25 ≤ d ∧ d ≤ 11/14)
    (hv : 53/50-d ≤ v ∧ v ≤ 31/50)
    (h : ∀ i, 0 < K+base (pointV i) s (pointD i)) :
    0 < K+base v s d := by
  have hwallc := (concaveOn_const K (convex_Icc (16/25) (11/14))).add (wall_concave hs)
  have hl : 0 < K+base (53/50-16/25) s (16/25) := by
    convert h 0 using 1
    norm_num [pointV,pointD]
  have hu : 0 < K+base (53/50-11/14) s (11/14) := by
    convert h 1 using 1
    norm_num [pointV,pointD]
  have htop : 0 < K+base (31/50) s (16/25) := by
    simpa [pointV,pointD] using h 2
  have hwall := concave_gt_of_endpoints hwallc hd hl hu
  have hm := top_monotone hs (by norm_num : (16:ℝ)/25 ∈ Set.Icc (16/25) (11/14)) hd hd.1
  have htop' : 0 < K+base (31/50) s d := by linarith
  have hc := (concaveOn_const K (convex_Icc 0 (31/50))).add (west_concave (s := s) hd)
  have hmin := hc.min_le_of_mem_Icc
    (show 53/50-d ∈ Set.Icc 0 (31/50) by constructor <;> linarith [hd.1,hd.2])
    (by norm_num : (31:ℝ)/50 ∈ Set.Icc 0 (31/50)) hv
  exact (lt_min hwall htop').trans_le hmin

lemma west_support {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 1 ≤ q ∧ q ≤ Real.pi/2) :
    (beta+Real.sin q)*a-Real.cos q*b ≤
      rhoBound*(beta+Real.sin q) := by
  have h := Wings.WestRange.west_cone hc (b := beta) (by norm_num [beta]) hq
  linarith

/-! ### S on the south side of C -/

namespace SideSouth

/-! With S on the south side of C at the angle `s = ±x`, the weight `gamma` on
C–S and the far-vertex support of S, whose force has length at most
`rootIntercept - rootSin sin s`, add to `base` the term `southTerm` in `x` and
the constant `constantTerm`. -/

def gamma : ℝ := 3/2
/-- The tangent `(y + c²)/(2c)` at `c = 9/5` to the square root of the squared
length `y = γ² + 1 - 2γ sin s` of the force on S is
`rootIntercept - rootSin sin s`. -/
def rootIntercept : ℝ := (gamma^2+1+(9/5)^2)/(2*(9/5))
def rootSin : ℝ := gamma/(9/5)

def constantTerm : ℝ := A*gamma-B*beta+2-radiusBound*rootIntercept
def side (negative : Bool) : ℝ := if negative then -1 else 1
def sineCoefficient (negative : Bool) : ℝ :=
  if negative then gamma-radiusBound*rootSin else radiusBound*rootSin

def southTerm (negative : Bool) (x : ℝ) : ℝ :=
  gamma*Real.cos x+sineCoefficient negative*Real.sin x

def profile (negative : Bool) (v x d : ℝ) : ℝ :=
  constantTerm+base v (side negative*x) d+southTerm negative x

private lemma south_term_concave (negative : Bool) :
    ConcaveOn ℝ (Set.Icc 0 (2/5)) (southTerm negative) :=
  harmonic_concave fun _ hx => harmonic_nonneg (by norm_num [gamma])
    (by cases negative <;> norm_num [sineCoefficient,gamma,rootSin,radiusBound])
    ⟨hx.1,by linarith [hx.2,Real.pi_gt_d2]⟩

lemma south_concave (negative : Bool) {v d : ℝ}
    (hd : 16/25 ≤ d ∧ d ≤ 11/14) :
    ConcaveOn ℝ (Set.Icc 0 (2/5)) (fun x => profile negative v x d) := by
  have hD0 := concave_affine_argument (a := -side negative) (b := d) diagonal_concave
    (l := 0) (u := 2/5) (by
      intro x hx
      cases negative <;> dsimp [side] <;> constructor <;>
        linarith [hd.1,hd.2,hx.1,hx.2])
  have hD : ConcaveOn ℝ (Set.Icc 0 (2/5))
      (fun x => diagonalTerm (d-side negative*x)) := by
    convert hD0 using 1
    funext x
    congr 1
    ring
  have h := ((concaveOn_const (constantTerm+beta*wing v+gapTerm (v+d)) (convex_Icc 0 (2/5))).add
    hD).add (south_term_concave negative)
  convert h using 1
  funext x
  dsimp [profile,base]
  ring

private def lowerPolynomial (negative : Bool) (v x d : ℝ) : ℝ :=
  constantTerm+beta*(A*cosLower v+B*sinLower v)+
  (1/2)*cosLower (v+d)-B*sinUpper (v+d)+
  cosLower (d-side negative*x)-rootCoefficient*cosUpper ((d-side negative*x)/2)+
  rootCoefficient*sinLower ((d-side negative*x)/2)+
  gamma*cosLower x+sineCoefficient negative*sinLower x

private lemma polynomial_le (negative : Bool) {v x d : ℝ}
    (hv : 0 ≤ v) (hx : 0 ≤ x) (hd : 0 ≤ d) (hr : 0 ≤ d-side negative*x) :
    lowerPolynomial negative v x d ≤ profile negative v x d := by
  have cv := cos_lower_six hv
  have sv := sin_lower_seven hv
  have cq := cos_lower_six (add_nonneg hv hd)
  have sq := sin_upper_five (add_nonneg hv hd)
  have cr := cos_lower_six hr
  have ch := cos_upper_four (x := (d-side negative*x)/2) (by linarith)
  have sh := sin_lower_seven (x := (d-side negative*x)/2) (by linarith)
  have cx := cos_lower_six hx
  have sx := sin_lower_seven hx
  cases negative <;>
    dsimp [lowerPolynomial,profile,base,wing,gapTerm,diagonalTerm,southTerm,
      beta,A,B,rootCoefficient,rootSlope,radiusBound,
      gamma,sineCoefficient,rootSin,cosLower,cosUpper,sinLower,sinUpper] <;>
    nlinarith only [cv,sv,cq,sq,cr,ch,sh,cx,sx]

private def endpoint (upper : Bool) : ℝ := if upper then 2/5 else 0

private lemma endpoint_margin (negative upper : Bool) (i : Fin 3) :
    0 < lowerPolynomial negative (pointV i) (endpoint upper) (pointD i) := by
  cases negative <;> cases upper <;> fin_cases i <;>
    norm_num [lowerPolynomial,constantTerm,beta,A,B,rootCoefficient,rootSlope,
      radiusBound,gamma,sineCoefficient,rootIntercept,rootSin,side,
      cosLower,cosUpper,sinLower,sinUpper,pointV,pointD,endpoint]

lemma boundary_positive (negative : Bool) (i : Fin 3) {x : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 2/5) : 0 < profile negative (pointV i) x (pointD i) := by
  have endpos (upper : Bool) :
      0 < profile negative (pointV i) (endpoint upper) (pointD i) := by
    have hv : 0 ≤ pointV i := by fin_cases i <;> norm_num [pointV]
    have hx : 0 ≤ endpoint upper := by cases upper <;> norm_num [endpoint]
    have hd : 0 ≤ pointD i := by fin_cases i <;> norm_num [pointD]
    have hr : 0 ≤ pointD i-side negative*endpoint upper := by
      cases negative <;> cases upper <;> fin_cases i <;> norm_num [pointD,side,endpoint]
    exact (endpoint_margin negative upper i).trans_le (polynomial_le negative hv hx hd hr)
  have hd : 16/25 ≤ pointD i ∧ pointD i ≤ 11/14 := by
    fin_cases i <;> norm_num [pointD]
  have h0 := endpos false
  have h1 := endpos true
  have he0 : endpoint false=0 := by simp [endpoint]
  have he1 : endpoint true=2/5 := by simp [endpoint]
  rw [he0] at h0
  rw [he1] at h1
  exact concave_gt_of_endpoints (f := fun x => profile negative (pointV i) x (pointD i))
    (south_concave negative hd) hx h0 h1

/-- The profile is positive on its whole domain, for either sign of `s`. -/
theorem positive (negative : Bool) {v x d : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 2/5) (hd : 16/25 ≤ d ∧ d ≤ 11/14)
    (hv : 53/50-d ≤ v ∧ v ≤ 31/50) : 0 < profile negative v x d := by
  have hs : -(2/5) ≤ side negative*x ∧ side negative*x ≤ 12/25 := by
    cases negative <;> dsimp [side] <;> constructor <;> linarith [hx.1,hx.2]
  have h := positive_of_three_points (K := constantTerm+southTerm negative x) hs hd hv
    fun i => by
      have hi := boundary_positive negative i hx
      dsimp only [profile] at hi
      linarith
  dsimp only [profile]
  linarith

/-! The `defect` is the threshold sum less the bounds for the works: `southUpper`
on S, `diagonalUpper` on D, `centerUpper` on C, and `rhoBound (beta + sin q)` on
W in the cone. -/

def southUpper (s : ℝ) : ℝ :=
  radiusBound*(rootIntercept-rootSin*Real.sin s)-
    (gamma*Real.cos s+1-gamma*Real.sin s)/2

def centerUpper (v : ℝ) : ℝ :=
  coreUpper*(beta*Real.cos v+gamma-beta*Real.sin v)

def thresholdSum (v s d : ℝ) : ℝ :=
  beta*(1/2+angularWidth v)+gamma*(1/2+angularWidth s)+
    (1/2+angularWidth (v+d))+(1/2+angularWidth (d-s))

def defect (v s d : ℝ) : ℝ :=
  thresholdSum v s d-rhoBound*(beta+Real.sin (v+d))-
    southUpper s-diagonalUpper (d-s)-centerUpper v

lemma south_root (s : ℝ) :
    Real.sqrt (gamma^2+1-2*gamma*Real.sin s) ≤ rootIntercept-rootSin*Real.sin s := by
  have hr : 0 ≤ gamma^2+1-2*gamma*Real.sin s := by
    dsimp [gamma]
    linarith [Real.sin_le_one s]
  have h := sqrt_le_tangent (c := 9/5) (by norm_num) hr
  have e : (gamma^2+1-2*gamma*Real.sin s+(9/5)^2)/(2*(9/5))=
      rootIntercept-rootSin*Real.sin s := by
    dsimp [rootIntercept,rootSin]
    ring
  linarith

lemma south_support {a b s : ℝ} (hc : ContainedChart a |b|) :
    gamma*Real.cos s*a+(1-gamma*Real.sin s)*b ≤ southUpper s := by
  have h := local_vertex_support hc (gamma*Real.cos s) (1-gamma*Real.sin s)
  have hi : (gamma*Real.cos s)^2+(1-gamma*Real.sin s)^2 =
      gamma^2+1-2*gamma*Real.sin s := by
    linear_combination gamma^2*(Real.sin_sq_add_cos_sq s)
  rw [hi] at h
  have hm := mul_le_mul ceiling_bounds.1 (south_root s) (Real.sqrt_nonneg _)
    (by norm_num [radiusBound])
  have hw : gamma*Real.cos s+1-gamma*Real.sin s ≤
      |gamma*Real.cos s|+|1-gamma*Real.sin s| := by
    linarith [le_abs_self (gamma*Real.cos s),le_abs_self (1-gamma*Real.sin s)]
  dsimp [southUpper]
  linarith

lemma center_support {v cx cy : ℝ} (hv : 0 ≤ v ∧ v ≤ 31/50)
    (hx : cx ≤ c0) (hy : cy ≤ c0) :
    beta*Real.cos v*cx+(gamma-beta*Real.sin v)*cy ≤ centerUpper v := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show v ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hv.1,hv.2,Real.pi_gt_d2])
  have hX : 0 ≤ beta*Real.cos v := by dsimp [beta]; positivity
  have hs := Real.sin_le hv.1
  have hY : 0 ≤ gamma-beta*Real.sin v := by dsimp [gamma,beta]; linarith [hv.2]
  refine (center_corner hX hY hx hy).trans_eq ?_
  dsimp [centerUpper]
  ring

lemma profile_eq_defect (negative : Bool) {v x d : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 2/5) (hd : 16/25 ≤ d ∧ d ≤ 11/14)
    (hv : 53/50-d ≤ v ∧ v ≤ 31/50) :
    profile negative v x d=defect v (side negative*x) d := by
  have hv0 : 0 ≤ v := by linarith [hv.1,hd.2]
  have hW := angularWidth_eq (x := v) ⟨hv0,by linarith [hv.2,Real.pi_gt_d2]⟩
  have hQ := angularWidth_eq (x := v+d) (by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2])
  have hr : 0 ≤ d-side negative*x ∧ d-side negative*x ≤ Real.pi/2 := by
    cases negative <;> dsimp [side] <;> constructor <;>
      linarith [hx.1,hx.2,hd.1,hd.2,Real.pi_gt_d2]
  have hR := angularWidth_eq hr
  have hcx := Real.cos_nonneg_of_mem_Icc
    (show x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hx.1,hx.2,Real.pi_gt_d2])
  have hsx := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_gt_d2])
  have hS : angularWidth (side negative*x)=(Real.cos x+Real.sin x)/2 := by
    cases negative <;> simp [side,angularWidth,abs_of_nonneg hcx,abs_of_nonneg hsx]
  dsimp [profile,base,wing,gapTerm,diagonalTerm,southTerm,defect,thresholdSum,
    southUpper,diagonalUpper,centerUpper,constantTerm,sineCoefficient,rootIntercept,rootSin,
    beta,gamma,A,B,rootCoefficient,rootSlope,halfDifference,
    radiusBound,rhoBound,coreUpper]
  rw [hW,hQ,hR,hS]
  cases negative <;> simp only [side,Bool.false_eq_true,ite_true,ite_false,
    neg_one_mul,one_mul,Real.cos_neg,Real.sin_neg] <;> ring

/-- On the domain of the profile, the separations of a missing west wing with W
on its own axis and S on the south side of C are incompatible. -/
theorem impossible {X : Chart} (hW : X.WestOwn) (hS : X.SouthSide)
    (h : X.MissingWest) (hs : |X.s| ≤ 2/5) (hd : 16/25 ≤ X.d ∧ X.d ≤ 11/14)
    (hv : 53/50-X.d ≤ X.v ∧ X.v ≤ 31/50) : False := by
  have hWD := h.west
  have hDS := h.south
  simp only [Chart.WestOwn,Chart.SouthSide,Chart.WestDiagonal,
    Chart.SouthWing] at hW hS hWD hDS
  rw [add_comm X.d X.v] at hWD
  have hsum : thresholdSum X.v X.s X.d ≤
      ((beta+Real.sin (X.v+X.d))*X.aW-Real.cos (X.v+X.d)*X.bW)+
      (gamma*Real.cos X.s*X.aS+(1-gamma*Real.sin X.s)*X.bS)+
      (Real.cos (X.d-X.s)*X.aD+(1-Real.sin (X.d-X.s))*X.bD)+
      beta*Real.cos X.v*X.cx+(gamma-beta*Real.sin X.v)*X.cy := by
    dsimp [thresholdSum,beta,gamma]
    linear_combination (41/20)*hW+(3/2)*hS+hWD+hDS
  obtain ⟨hs1,hs2⟩ := abs_le.mp hs
  have hv0 : 0 ≤ X.v := by linarith [hv.1,hd.2]
  have hq : 1 ≤ X.v+X.d ∧ X.v+X.d ≤ Real.pi/2 := by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2]
  have hr : 0 ≤ X.d-X.s ∧ X.d-X.s ≤ 6/5 := by
    constructor <;> linarith [hd.1,hd.2]
  have hc := center_support ⟨hv0,hv.2⟩ X.box.1.2 X.box.2.2
  have hn : defect X.v X.s X.d ≤ 0 := by
    dsimp [defect]
    linarith only [hsum,west_support X.west hq,support X.diagonal hr,
      south_support (s := X.s) X.south,hc]
  by_cases hs0 : 0 ≤ X.s
  · have hp := positive false ⟨hs0,hs2⟩ hd hv
    rw [profile_eq_defect false ⟨hs0,hs2⟩ hd hv] at hp
    simp only [side,Bool.false_eq_true,ite_false,one_mul] at hp
    exact (not_lt_of_ge hn) hp
  · have hx' : 0 ≤ -X.s ∧ -X.s ≤ 2/5 := by constructor <;> linarith
    have hp := positive true hx' hd hv
    rw [profile_eq_defect true hx' hd hv] at hp
    simp only [side,ite_true,neg_one_mul,neg_neg] at hp
    linarith

end SideSouth

/-! ### S on its own axis -/

namespace OwnSouth

/-! With S on its own axis the range `[0, 12/25]` of `s` is cut at `3/20` and
`3/10`. On the piece `j` the weight on C–S is the constant `gamma j`, and the
force `(γ, 1)` on S has length at most `length j`. -/

def pieceStart : Fin 3 → ℝ := ![0,3/20,3/10]
def pieceEnd : Fin 3 → ℝ := ![3/20,3/10,12/25]
def gamma : Fin 3 → ℝ := ![8/5,2,13/5]
def length : Fin 3 → ℝ := ![1.887,2.237,2.786]

def constantTerm : ℝ := 2-B*beta

/-- The threshold sum of the stress minus its support bounds. -/
def profile (j : Fin 3) (v s d : ℝ) : ℝ :=
  constantTerm+base v s d+gamma j*(1+wing s)-radiusBound*length j

lemma gamma_bounds (j : Fin 3) : 8/5 ≤ gamma j ∧ gamma j ≤ 13/5 := by
  fin_cases j <;> norm_num [gamma]

lemma length_bound (j : Fin 3) : 0 ≤ length j ∧ gamma j^2+1 ≤ length j^2 := by
  fin_cases j <;> norm_num [gamma,length]

lemma piece_range (j : Fin 3) : 0 ≤ pieceStart j ∧ pieceEnd j ≤ 12/25 := by
  fin_cases j <;> norm_num [pieceStart,pieceEnd]

/-- The profile is concave in `s`: the term of D is concave in `d - s` and `wing`
is a harmonic with nonnegative coefficients. -/
lemma south_concave (j : Fin 3) {v d : ℝ} (hd : 16/25 ≤ d ∧ d ≤ 11/14) :
    ConcaveOn ℝ (Set.Icc 0 (12/25)) (fun s => profile j v s d) := by
  have hD0 := concave_affine_argument (a := -1) (b := d) diagonal_concave
    (l := 0) (u := 12/25) (by
      intro s hs
      constructor <;> linarith [hd.1,hd.2,hs.1,hs.2])
  have hD : ConcaveOn ℝ (Set.Icc 0 (12/25)) (fun s => diagonalTerm (d-s)) := by
    convert hD0 using 1
    funext s
    congr 1
    ring
  have hW := (wing_concave.subset (Set.Icc_subset_Icc le_rfl (by norm_num))
    (convex_Icc 0 (12/25))).smul (show 0 ≤ gamma j by linarith [(gamma_bounds j).1])
  have h := ((concaveOn_const (constantTerm+beta*wing v+gapTerm (v+d)+gamma j-
    radiusBound*length j) (convex_Icc 0 (12/25))).add hD).add hW
  convert h using 1
  funext s
  simp only [profile,base,Pi.add_apply,smul_eq_mul]
  ring

private def lowerPolynomial (j : Fin 3) (v s d : ℝ) : ℝ :=
  constantTerm+beta*(A*cosLower v+B*sinLower v)+
  (1/2)*cosLower (v+d)-B*sinUpper (v+d)+
  cosLower (d-s)-rootCoefficient*cosUpper ((d-s)/2)+rootCoefficient*sinLower ((d-s)/2)+
  gamma j*(1+A*cosLower s+B*sinLower s)-radiusBound*length j

private lemma polynomial_le (j : Fin 3) {v s d : ℝ} (hv : 0 ≤ v) (hs : 0 ≤ s)
    (hd : 0 ≤ d) (hr : s ≤ d) :
    lowerPolynomial j v s d ≤ profile j v s d := by
  have hg : 0 ≤ gamma j := by linarith [(gamma_bounds j).1]
  have cv := cos_lower_six hv
  have sv := sin_lower_seven hv
  have cq := cos_lower_six (add_nonneg hv hd)
  have sq := sin_upper_five (add_nonneg hv hd)
  have cr := cos_lower_six (x := d-s) (by linarith)
  have ch := cos_upper_four (x := (d-s)/2) (by linarith)
  have sh := sin_lower_seven (x := (d-s)/2) (by linarith)
  have hcs := mul_nonneg (mul_nonneg hg (by norm_num [A] : 0 ≤ A))
    (sub_nonneg.mpr (cos_lower_six hs))
  have hss := mul_nonneg (mul_nonneg hg (by norm_num [B] : 0 ≤ B))
    (sub_nonneg.mpr (sin_lower_seven hs))
  dsimp [lowerPolynomial,profile,base,wing,gapTerm,diagonalTerm,beta,A,B,rootCoefficient,
    rootSlope,radiusBound,cosLower,cosUpper,sinLower,sinUpper] at *
  nlinarith only [cv,sv,cq,sq,cr,ch,sh,hcs,hss]

private lemma endpoint_margin (j i : Fin 3) (upper : Bool) :
    0 < lowerPolynomial j (pointV i) (if upper then pieceEnd j else pieceStart j) (pointD i) := by
  fin_cases j <;> fin_cases i <;> cases upper <;>
    norm_num [lowerPolynomial,constantTerm,beta,A,B,rootCoefficient,rootSlope,radiusBound,
      gamma,length,pieceStart,pieceEnd,cosLower,cosUpper,sinLower,sinUpper,pointV,pointD]

lemma boundary_positive (j i : Fin 3) {s : ℝ} (hs : pieceStart j ≤ s ∧ s ≤ pieceEnd j) :
    0 < profile j (pointV i) s (pointD i) := by
  have hp := piece_range j
  have hv : 0 ≤ pointV i := by fin_cases i <;> norm_num [pointV]
  have hd : 16/25 ≤ pointD i ∧ pointD i ≤ 11/14 := by fin_cases i <;> norm_num [pointD]
  have endpos (upper : Bool) :
      0 < profile j (pointV i) (if upper then pieceEnd j else pieceStart j) (pointD i) := by
    have hx : 0 ≤ (if upper then pieceEnd j else pieceStart j) ∧
        (if upper then pieceEnd j else pieceStart j) ≤ 12/25 := by
      cases upper <;> simp only [Bool.false_eq_true,ite_true,ite_false] <;>
        constructor <;> linarith
    exact (endpoint_margin j i upper).trans_le
      (polynomial_le j hv hx.1 (by linarith) (by linarith))
  have h0 := endpos false
  have h1 := endpos true
  simp only [Bool.false_eq_true,ite_true,ite_false] at h0 h1
  exact concave_gt_of_endpoints (f := fun s => profile j (pointV i) s (pointD i))
    ((south_concave j hd).subset (Set.Icc_subset_Icc hp.1 hp.2) (convex_Icc _ _)) hs h0 h1

/-- The profile is positive for `s` in the piece `j`, `16/25 ≤ d ≤ 11/14` and
`53/50 - d ≤ v ≤ 31/50`. -/
theorem positive (j : Fin 3) {v s d : ℝ} (hs : pieceStart j ≤ s ∧ s ≤ pieceEnd j)
    (hd : 16/25 ≤ d ∧ d ≤ 11/14) (hv : 53/50-d ≤ v ∧ v ≤ 31/50) :
    0 < profile j v s d := by
  have hp := piece_range j
  have h := positive_of_three_points (K := constantTerm+gamma j*(1+wing s)-
      radiusBound*length j)
    (show -(2/5) ≤ s ∧ s ≤ 12/25 by constructor <;> linarith [hs.1,hs.2]) hd hv
    fun i => by
      have hi := boundary_positive j i hs
      dsimp only [profile] at hi
      linarith
  dsimp only [profile]
  linarith

/-! The `defect` is the threshold sum less the bounds for the works on W, S, D
and C, with the force `(forceX, forceY)` on C. -/

def southUpper (j : Fin 3) : ℝ := radiusBound*length j-(gamma j+1)/2

def forceX (j : Fin 3) (v s : ℝ) : ℝ := beta*Real.cos v-gamma j*Real.sin s
def forceY (j : Fin 3) (v s : ℝ) : ℝ := gamma j*Real.cos s-beta*Real.sin v

def centerUpper (j : Fin 3) (v s : ℝ) : ℝ := coreUpper*(forceX j v s+forceY j v s)

def thresholdSum (j : Fin 3) (v s d : ℝ) : ℝ :=
  beta*(1/2+angularWidth v)+gamma j*(1/2+angularWidth s)+
    (1/2+angularWidth (v+d))+(1/2+angularWidth (d-s))

def defect (j : Fin 3) (v s d : ℝ) : ℝ :=
  thresholdSum j v s d-rhoBound*(beta+Real.sin (v+d))-
    southUpper j-diagonalUpper (d-s)-centerUpper j v s

lemma south_support (j : Fin 3) {a b : ℝ} (hc : ContainedChart a |b|) :
    gamma j*a+b ≤ southUpper j := by
  have hg := gamma_bounds j
  have hl := length_bound j
  have h := vertex_support hc (U := gamma j) (V := 1) hl.1 (by linarith [hl.2])
  rw [abs_of_nonneg (by linarith [hg.1]),abs_one] at h
  dsimp [southUpper]
  linarith

lemma central_forces (j : Fin 3) {v s : ℝ} (hv : 0 ≤ v ∧ v ≤ 31/50)
    (hs : 0 ≤ s ∧ s ≤ 12/25) : 0 ≤ forceX j v s ∧ 0 ≤ forceY j v s := by
  have hv2 := mul_nonneg (sub_nonneg.mpr hv.2) (show 0 ≤ 31/50+v by linarith [hv.1])
  have hs2 := mul_nonneg (sub_nonneg.mpr hs.2) (show 0 ≤ 12/25+s by linarith [hs.1])
  have hcv : 4/5 ≤ Real.cos v := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]
  have hcs : 22/25 ≤ Real.cos s := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := s)]
  have hsv : Real.sin v ≤ 31/50 := (Real.sin_le hv.1).trans hv.2
  have hss : Real.sin s ≤ 12/25 := (Real.sin_le hs.1).trans hs.2
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hs.1
    (by linarith [hs.2,Real.pi_gt_d2])
  have hg := gamma_bounds j
  have hprodS := mul_le_mul hg.2 hss hs0 (by norm_num : (0:ℝ) ≤ 13/5)
  have hprodC := mul_le_mul hg.1 hcs (by norm_num : (0:ℝ) ≤ 22/25)
    (show 0 ≤ gamma j by linarith [hg.1])
  dsimp [forceX,forceY,beta]
  constructor <;> nlinarith only [hcv,hsv,hprodS,hprodC]

lemma profile_eq_defect (j : Fin 3) {v s d : ℝ} (hs : 0 ≤ s ∧ s ≤ 12/25)
    (hd : 16/25 ≤ d ∧ d ≤ 11/14) (hv : 53/50-d ≤ v ∧ v ≤ 31/50) :
    profile j v s d=defect j v s d := by
  have hW := angularWidth_eq (x := v) (by
    constructor <;> linarith [hv.1,hv.2,hd.2,Real.pi_gt_d2])
  have hS := angularWidth_eq (x := s) ⟨hs.1,by linarith [hs.2,Real.pi_gt_d2]⟩
  have hQ := angularWidth_eq (x := v+d) (by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2])
  have hR := angularWidth_eq (x := d-s) (by
    constructor <;> linarith [hs.1,hs.2,hd.1,hd.2,Real.pi_gt_d2])
  dsimp [profile,base,wing,gapTerm,diagonalTerm,defect,thresholdSum,southUpper,
    diagonalUpper,centerUpper,forceX,forceY,constantTerm,beta,A,B,
    rootCoefficient,rootSlope,halfDifference,radiusBound,rhoBound,coreUpper]
  rw [hW,hS,hQ,hR]
  ring

/-- The separations of a missing west wing with W and S on their own axes are
incompatible for `0 ≤ s ≤ 12/25`, `16/25 ≤ d ≤ 11/14` and
`53/50 - d ≤ v ≤ 31/50`. -/
theorem impossible {X : Chart} (hW : X.WestOwn) (hS : X.SouthOwn)
    (h : X.MissingWest) (hs : 0 ≤ X.s ∧ X.s ≤ 12/25) (hd : 16/25 ≤ X.d ∧ X.d ≤ 11/14)
    (hv : 53/50-X.d ≤ X.v ∧ X.v ≤ 31/50) : False := by
  obtain ⟨j,hj⟩ : ∃ j : Fin 3, pieceStart j ≤ X.s ∧ X.s ≤ pieceEnd j := by
    rcases le_total X.s (3/20) with h1 | h1
    · exact ⟨0,by norm_num [pieceStart,pieceEnd]; exact ⟨hs.1,h1⟩⟩
    rcases le_total X.s (3/10) with h2 | h2
    · exact ⟨1,by norm_num [pieceStart,pieceEnd]; exact ⟨h1,h2⟩⟩
    · exact ⟨2,by norm_num [pieceStart,pieceEnd]; exact ⟨h2,hs.2⟩⟩
  have hWD := h.west
  have hDS := h.south
  simp only [Chart.WestOwn,Chart.SouthOwn,Chart.WestDiagonal,
    Chart.SouthWing] at hW hS hWD hDS
  rw [add_comm X.d X.v] at hWD
  have hg : 0 ≤ gamma j := by linarith [(gamma_bounds j).1]
  have hsum : thresholdSum j X.v X.s X.d ≤
      ((beta+Real.sin (X.v+X.d))*X.aW-Real.cos (X.v+X.d)*X.bW)+
      (gamma j*X.aS+X.bS)+
      (Real.cos (X.d-X.s)*X.aD+(1-Real.sin (X.d-X.s))*X.bD)+
      forceX j X.v X.s*X.cx+forceY j X.v X.s*X.cy := by
    dsimp [thresholdSum,forceX,forceY,beta]
    linear_combination (41/20)*hW+(gamma j)*hS+hWD+hDS
  have hv0 : 0 ≤ X.v := by linarith [hv.1,hd.2]
  have hq : 1 ≤ X.v+X.d ∧ X.v+X.d ≤ Real.pi/2 := by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2]
  have hr : 0 ≤ X.d-X.s ∧ X.d-X.s ≤ 6/5 := by
    constructor <;> linarith [hs.1,hs.2,hd.1,hd.2]
  have hforce := central_forces j ⟨hv0,hv.2⟩ hs
  have hc := center_corner hforce.1 hforce.2 X.box.1.2 X.box.2.2
  have hn : defect j X.v X.s X.d ≤ 0 := by
    dsimp [defect,centerUpper]
    linarith only [hsum,west_support X.west hq,support X.diagonal hr,
      south_support j X.south,hc]
  have hp := positive j hj hd hv
  rw [profile_eq_defect j hs hd hv] at hp
  linarith

end OwnSouth

end SquaresInCircles.Six.Wings.WestDiagonal

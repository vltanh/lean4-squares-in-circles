import SquaresInCircles.Six.Wings.WestRange

/-!
# A missing west wing with W on its own axis

Let W be separated from C along its own axis at the angle `v`, W and D along
the secondary axis of D, and D and S along the secondary axis of S, so that
`16/25 ≤ d ≤ 11/14` and `53/50 - d ≤ v ≤ 31/50` (`WestRange`). Weights `41/20`
on C–W, `γ` on C–S, `1` on W–D and `ν = 211/200` on D–S give D the force
`(ν cos r, 1 - ν sin r)`, `r = d - s`, of squared length `(ν - 1)² + 2ν u²` with
`u = cos (r/2) - sin (r/2) ≥ 13/50`, at most `((7263/5000) u + 1/250)²`; the
far vertex of D then leaves the concave `diagonalTerm` in `r`. W takes the cone
support and C the corner of the box. The rest of the profile is concave in `v`,
along the wall `d + v = 53/50` and increasing in `d` along `v = 31/50`, so it is
positive once it is at three boundary points in `(v, d)`. With S on the south
side of C, `γ = 38/25` and the far vertex of S with a tangent to its length make
the profile concave in `|s|`; with S on its own axis, `γ = 38/25 + 3s` and the
length `√(γ² + ν²)` of the force on S is handled by a polynomial majorant, so
`γ⁵` times the profile is at least a polynomial in `s`, positive on
`[0, 12/25]`.
-/

noncomputable section
namespace SquaresInCircles.Six.Wings.WestDiagonal
open Normalization

/-! ### The term of D

With the weights `1` on W–D and `nu` on D–S the force on D is
`(ν cos r, 1 - ν sin r)`, `r = d - s`, of length at most
`rootSlope · halfDifference r + rootError` (`norm_upper`). With its far-vertex
support it leaves in the profile the term `diagonalTerm r`, where
`rootCoefficient = radiusBound · rootSlope`; `diagonalFirst` and
`diagonalSecond` are its derivatives. -/

def nu : ℝ := 211/200
def rootSlope : ℝ := 7263/5000
def rootError : ℝ := 1/250
def halfDifference (r : ℝ) : ℝ := Real.cos (r/2)-Real.sin (r/2)
def rootCoefficient : ℝ := radiusBound*rootSlope

def diagonalTerm (r : ℝ) : ℝ :=
  nu*Real.cos r-rootCoefficient*Real.cos (r/2)+rootCoefficient*Real.sin (r/2)
def diagonalFirst (r : ℝ) : ℝ :=
  -nu*Real.sin r+(rootCoefficient/2)*(Real.sin (r/2)+Real.cos (r/2))
def diagonalSecond (r : ℝ) : ℝ :=
  -nu*Real.cos r+(rootCoefficient/4)*(Real.cos (r/2)-Real.sin (r/2))

lemma half_difference_lower {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 6/5) :
    13/50 ≤ halfDifference r := by
  obtain ⟨-,hs,hc,-⟩ := trig_bracket (l := 0) (u := 3/5) (x := r/2) le_rfl
    (by linarith [Real.pi_gt_d2]) ⟨by linarith [hr.1],by linarith [hr.2]⟩
  norm_num at hs hc
  dsimp [halfDifference]
  linarith

lemma norm_identity (r : ℝ) :
    (nu*Real.cos r)^2+(1-nu*Real.sin r)^2 =
      (nu-1)^2+2*nu*(halfDifference r)^2 := by
  have hs : Real.sin r=2*Real.sin (r/2)*Real.cos (r/2) := by
    simpa only [show 2*(r/2)=r by ring] using Real.sin_two_mul (r/2)
  dsimp [halfDifference]
  rw [hs]
  linear_combination nu^2*(Real.sin_sq_add_cos_sq r)-2*nu*(Real.sin_sq_add_cos_sq (r/2))-
    nu^2*(Real.sin r+2*Real.sin (r/2)*Real.cos (r/2))*hs

lemma norm_upper {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 6/5) :
    Real.sqrt ((nu*Real.cos r)^2+(1-nu*Real.sin r)^2) ≤
      rootSlope*halfDifference r+rootError := by
  have hu := half_difference_lower hr
  have hsq := mul_nonneg (show 0 ≤ halfDifference r-13/50 by linarith)
    (show 0 ≤ halfDifference r+13/50 by linarith)
  have hp : (nu-1)^2+2*nu*(halfDifference r)^2 ≤
      (rootSlope*halfDifference r+rootError)^2 := by
    dsimp [nu,rootSlope,rootError]
    nlinarith only [hu,hsq]
  have hnonneg : 0 ≤ rootSlope*halfDifference r+rootError := by
    dsimp [rootSlope,rootError]
    linarith
  have hs := Real.sq_sqrt
    (show 0 ≤ (nu*Real.cos r)^2+(1-nu*Real.sin r)^2 by positivity)
  have hn := Real.sqrt_nonneg ((nu*Real.cos r)^2+(1-nu*Real.sin r)^2)
  rw [norm_identity] at hs hn ⊢
  nlinarith only [hp,hnonneg,hs,hn]

/-- The far-vertex bound for the work of the force on D. -/
def diagonalUpper (r : ℝ) : ℝ :=
  radiusBound*(rootSlope*halfDifference r+rootError)-(nu*Real.cos r+1-nu*Real.sin r)/2

lemma support {a b r : ℝ} (hc : ContainedChart a |b|) (hr : 0 ≤ r ∧ r ≤ 6/5) :
    nu*Real.cos r*a+(1-nu*Real.sin r)*b ≤ diagonalUpper r := by
  have h := local_vertex_support hc (nu*Real.cos r) (1-nu*Real.sin r)
  have hm := mul_le_mul ceiling_bounds.1 (norm_upper hr) (Real.sqrt_nonneg _)
    (by norm_num [radiusBound])
  have hw : nu*Real.cos r+1-nu*Real.sin r ≤ |nu*Real.cos r|+|1-nu*Real.sin r| := by
    linarith [le_abs_self (nu*Real.cos r),le_abs_self (1-nu*Real.sin r)]
  dsimp only [diagonalUpper]
  linarith

lemma diagonal_hasDeriv (r : ℝ) : HasDerivAt diagonalTerm (diagonalFirst r) r := by
  convert ((((Real.hasDerivAt_cos r).const_mul nu).sub
    ((((hasDerivAt_id r).div_const 2).cos).const_mul rootCoefficient)).add
    ((((hasDerivAt_id r).div_const 2).sin).const_mul rootCoefficient)) using 1
  · funext y; simp only [diagonalTerm,Pi.add_apply,Pi.sub_apply,id_eq]
  · dsimp [diagonalFirst]; ring

lemma diagonal_first_hasDeriv (r : ℝ) : HasDerivAt diagonalFirst (diagonalSecond r) r := by
  convert (((Real.hasDerivAt_sin r).const_mul (-nu)).add
    (((((hasDerivAt_id r).div_const 2).sin).add
      (((hasDerivAt_id r).div_const 2).cos)).const_mul (rootCoefficient/2))) using 1
  · funext y; simp only [diagonalFirst,Pi.add_apply,id_eq]
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
  have hcoef : -nu*(Real.cos (r/2)+Real.sin (r/2))+rootCoefficient/4 ≤ 0 := by
    dsimp [nu,rootCoefficient,rootSlope,radiusBound]
    linarith
  have hp := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ halfDifference r by linarith) hcoef
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
    dsimp [diagonalFirst,nu,rootCoefficient,rootSlope,radiusBound]
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
def pointV : Fin 3 → ℝ := ![21/50,48/175,31/50]
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

def gamma : ℝ := 38/25
def rootIntercept : ℝ := 273901/148000
def rootSin : ℝ := 8018/9250

def constantTerm : ℝ := -51639691/29600000
def side (negative : Bool) : ℝ := if negative then -1 else 1
def sineCoefficient (negative : Bool) : ℝ :=
  if negative then 1302013/23125000 else 33847987/23125000

def southTerm (negative : Bool) (x : ℝ) : ℝ :=
  gamma*Real.cos x+sineCoefficient negative*Real.sin x

def profile (negative : Bool) (v x d : ℝ) : ℝ :=
  constantTerm+base v (side negative*x) d+southTerm negative x

private lemma south_term_concave (negative : Bool) :
    ConcaveOn ℝ (Set.Icc 0 (2/5)) (southTerm negative) :=
  harmonic_concave fun _ hx => harmonic_nonneg (by norm_num [gamma])
    (by cases negative <;> norm_num [sineCoefficient]) ⟨hx.1,by linarith [hx.2,Real.pi_gt_d2]⟩

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
  nu*cosLower (d-side negative*x)-rootCoefficient*cosUpper ((d-side negative*x)/2)+
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
      beta,A,B,nu,rootCoefficient,rootSlope,radiusBound,
      gamma,sineCoefficient,cosLower,cosUpper,sinLower,sinUpper] <;>
    nlinarith only [cv,sv,cq,sq,cr,ch,sh,cx,sx]

private def endpoint (upper : Bool) : ℝ := if upper then 2/5 else 0

private lemma endpoint_margin (negative upper : Bool) (i : Fin 3) :
    (1:ℝ)/1000 < lowerPolynomial negative (pointV i) (endpoint upper) (pointD i) := by
  cases negative <;> cases upper <;> fin_cases i <;>
    norm_num [lowerPolynomial,constantTerm,beta,A,B,nu,rootCoefficient,rootSlope,
      radiusBound,gamma,sineCoefficient,side,
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
    have hp := polynomial_le negative hv hx hd hr
    have hm := endpoint_margin negative upper i
    linarith
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
    (gamma*Real.cos s+nu-gamma*Real.sin s)/2

def centerUpper (v : ℝ) : ℝ :=
  coreUpper*(beta*Real.cos v+gamma-beta*Real.sin v)

def thresholdSum (v s d : ℝ) : ℝ :=
  beta*(1/2+angularWidth v)+gamma*(1/2+angularWidth s)+
    (1/2+angularWidth (v+d))+nu*(1/2+angularWidth (d-s))

def defect (v s d : ℝ) : ℝ :=
  thresholdSum v s d-rhoBound*(beta+Real.sin (v+d))-
    southUpper s-diagonalUpper (d-s)-centerUpper v

lemma south_root (s : ℝ) :
    Real.sqrt (gamma^2+nu^2-2*gamma*nu*Real.sin s) ≤ rootIntercept-rootSin*Real.sin s := by
  have hr : 0 ≤ gamma^2+nu^2-2*gamma*nu*Real.sin s := by
    dsimp [gamma,nu]
    linarith [Real.sin_le_one s]
  have hs := Real.sq_sqrt hr
  have hp := sq_nonneg (Real.sqrt (gamma^2+nu^2-2*gamma*nu*Real.sin s)-37/20)
  dsimp [gamma,nu,rootIntercept,rootSin] at *
  nlinarith only [hs,hp]

lemma south_support {a b s : ℝ} (hc : ContainedChart a |b|) :
    gamma*Real.cos s*a+(nu-gamma*Real.sin s)*b ≤ southUpper s := by
  have h := local_vertex_support hc (gamma*Real.cos s) (nu-gamma*Real.sin s)
  have hi : (gamma*Real.cos s)^2+(nu-gamma*Real.sin s)^2 =
      gamma^2+nu^2-2*gamma*nu*Real.sin s := by
    linear_combination gamma^2*(Real.sin_sq_add_cos_sq s)
  rw [hi] at h
  have hm := mul_le_mul ceiling_bounds.1 (south_root s) (Real.sqrt_nonneg _)
    (by norm_num [radiusBound])
  have hw : gamma*Real.cos s+nu-gamma*Real.sin s ≤
      |gamma*Real.cos s|+|nu-gamma*Real.sin s| := by
    linarith [le_abs_self (gamma*Real.cos s),le_abs_self (nu-gamma*Real.sin s)]
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
    southUpper,diagonalUpper,centerUpper,constantTerm,rootIntercept,rootSin,
    beta,gamma,nu,A,B,rootCoefficient,rootSlope,rootError,halfDifference,
    radiusBound,rhoBound,coreUpper]
  rw [hW,hQ,hR,hS]
  cases negative <;> simp only [side,sineCoefficient,Bool.false_eq_true,ite_true,ite_false,
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
      (gamma*Real.cos X.s*X.aS+(nu-gamma*Real.sin X.s)*X.bS)+
      (nu*Real.cos (X.d-X.s)*X.aD+(1-nu*Real.sin (X.d-X.s))*X.bD)+
      beta*Real.cos X.v*X.cx+(gamma-beta*Real.sin X.v)*X.cy := by
    dsimp [thresholdSum,beta,gamma,nu]
    linear_combination (41/20)*hW+(38/25)*hS+hWD+(211/200)*hDS
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

/-- `a⁶` times the cubic Taylor polynomial of `√(1 + x)` at `x = b²/a²`. -/
def numerator (a b : ℝ) : ℝ :=
  a^6+(b^2*a^4)/2-(b^4*a^2)/8+b^6/16

lemma positive_form (a b : ℝ) :
    numerator a b=a^6+(b^2/16)*((b^2-a^2)^2+7*a^4) := by
  dsimp [numerator]
  ring

lemma square_error (a b : ℝ) :
    (numerator a b)^2-a^10*(a^2+b^2)=
      (b^8/256)*((b^2-2*a^2)^2+16*a^4) := by
  dsimp [numerator]
  ring

/-- `a⁵ √(a² + b²) ≤ numerator a b` for `a ≥ 0`. -/
theorem scaled_sqrt_upper (a b : ℝ) (ha : 0 ≤ a) :
    a^5*Real.sqrt (a^2+b^2) ≤ numerator a b := by
  have hN : 0 ≤ numerator a b := by rw [positive_form]; positivity
  have hs := Real.sq_sqrt (show 0 ≤ a^2+b^2 by positivity)
  have hid : (a^5*Real.sqrt (a^2+b^2))^2=a^10*(a^2+b^2) := by
    linear_combination a^10*hs
  have he := square_error a b
  have hp : 0 ≤ (b^8/256)*((b^2-2*a^2)^2+16*a^4) := by positivity
  have hu : 0 ≤ a^5*Real.sqrt (a^2+b^2) := by positivity
  nlinarith only [hN,hid,he,hp,hu]

/-! With S on its own axis the weight on C–S is `gamma s`, and the force on S has
length `√(γ² + ν²)`. -/

def gamma (s : ℝ) : ℝ := 38/25+3*s
def constantTerm : ℝ := 3959823/5000000

/-- The threshold sum of the stress minus its support bounds. -/
def profile (v s d : ℝ) : ℝ :=
  constantTerm+base v s d+gamma s*(1+wing s)-
    radiusBound*Real.sqrt ((gamma s)^2+nu^2)

private def trigLower (v s d : ℝ) : ℝ :=
  constantTerm+beta*(A*cosLower v+B*sinLower v)+
  (1/2)*cosLower (v+d)-B*sinUpper (v+d)+
  nu*cosLower (d-s)-rootCoefficient*cosUpper ((d-s)/2)+rootCoefficient*sinLower ((d-s)/2)+
  gamma s*(1+A*cosLower s+B*sinLower s)

private def lowerPolynomial (v s d : ℝ) : ℝ :=
  (gamma s)^5*trigLower v s d-
    radiusBound*numerator (gamma s) nu

private lemma polynomial_le {v s d : ℝ} (hv : 0 ≤ v) (hs : 0 ≤ s)
    (hd : 0 ≤ d) (hr : s ≤ d) :
    lowerPolynomial v s d ≤ (gamma s)^5*profile v s d := by
  have hg : 0 ≤ gamma s := by dsimp [gamma]; linarith
  have cv := cos_lower_six hv
  have sv := sin_lower_seven hv
  have cq := cos_lower_six (add_nonneg hv hd)
  have sq := sin_upper_five (add_nonneg hv hd)
  have cr := cos_lower_six (x := d-s) (by linarith)
  have ch := cos_upper_four (x := (d-s)/2) (by linarith)
  have sh := sin_lower_seven (x := (d-s)/2) (by linarith)
  have cs := cos_lower_six hs
  have ss := sin_lower_seven hs
  have hcs := mul_nonneg (mul_nonneg hg (by norm_num [A] : 0 ≤ A))
    (show 0 ≤ Real.cos s-cosLower s by exact sub_nonneg.mpr cs)
  have hss := mul_nonneg (mul_nonneg hg (by norm_num [B] : 0 ≤ B))
    (show 0 ≤ Real.sin s-sinLower s by exact sub_nonneg.mpr ss)
  have htrig : trigLower v s d ≤ constantTerm+base v s d+gamma s*(1+wing s) := by
    dsimp [trigLower,base,wing,gapTerm,diagonalTerm,beta,A,B,nu,rootCoefficient,
      rootSlope,radiusBound,cosLower,cosUpper,sinLower,sinUpper] at *
    nlinarith only [cv,sv,cq,sq,cr,ch,sh,hcs,hss]
  have hm := mul_le_mul_of_nonneg_left htrig (show 0 ≤ (gamma s)^5 by positivity)
  have hroot := scaled_sqrt_upper (gamma s) nu hg
  have hR := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ radiusBound by norm_num [radiusBound])
  dsimp [lowerPolynomial,profile]
  nlinarith only [hm,hR]

/-- A polynomial below the three boundary ones, positive on `[0, 1/2]`. -/
def coarse (s : ℝ) : ℝ :=
  1/50+s+3*s^2+16*s^3+68*s^4+144*s^5+34*s^6-
    302*s^7-307*s^8-17*s^9-s^12-s^13

lemma coarse_factor (s : ℝ) :
    coarse s=1/50+s+3*s^2+16*s^3+68*s^4+34*s^6+
      s^5*(144-302*s^2-307*s^3-17*s^4-s^7-s^8) := by
  dsimp [coarse]
  ring

lemma coarse_positive {s : ℝ} (hs : 0 ≤ s ∧ s ≤ 12/25) : 0 < coarse s := by
  have hhalf : s ≤ (1:ℝ)/2 := by linarith [hs.2]
  have h2 : s^2 ≤ ((1:ℝ)/2)^2 := pow_le_pow_left₀ hs.1 hhalf 2
  have h3 : s^3 ≤ ((1:ℝ)/2)^3 := pow_le_pow_left₀ hs.1 hhalf 3
  have h4 : s^4 ≤ ((1:ℝ)/2)^4 := pow_le_pow_left₀ hs.1 hhalf 4
  have h7 : s^7 ≤ ((1:ℝ)/2)^7 := pow_le_pow_left₀ hs.1 hhalf 7
  have h8 : s^8 ≤ ((1:ℝ)/2)^8 := pow_le_pow_left₀ hs.1 hhalf 8
  have htail : 7437/256 ≤ 144-302*s^2-307*s^3-17*s^4-s^7-s^8 := by
    norm_num at h2 h3 h4 h7 h8
    linarith
  have hprod := mul_nonneg (pow_nonneg hs.1 5)
    (show 0 ≤ 144-302*s^2-307*s^3-17*s^4-s^7-s^8 by linarith)
  rw [coarse_factor]
  have p2 := pow_nonneg hs.1 2
  have p3 := pow_nonneg hs.1 3
  have p4 := pow_nonneg hs.1 4
  have p6 := pow_nonneg hs.1 6
  exact add_pos_of_pos_of_nonneg (by linarith [hs.1]) hprod

/-- For `s ≥ 0`, `coarse s` is at most each boundary polynomial: the differences
have nonnegative coefficients. -/
lemma coarse_le_boundary (i : Fin 3) {s : ℝ} (hs : 0 ≤ s) :
    coarse s ≤ lowerPolynomial (pointV i) s (pointD i) := by
  apply sub_nonneg.mp
  fin_cases i <;>
    dsimp [coarse,lowerPolynomial,trigLower,numerator,
      gamma,constantTerm,beta,A,B,nu,rootCoefficient,rootSlope,
      radiusBound,cosLower,cosUpper,sinLower,sinUpper,pointV,pointD] <;>
    ring_nf <;> positivity

lemma boundary_positive (i : Fin 3) {s : ℝ} (hs : 0 ≤ s ∧ s ≤ 12/25) :
    0 < profile (pointV i) s (pointD i) := by
  have hv : 0 ≤ pointV i := by fin_cases i <;> norm_num [pointV]
  have hd : 0 ≤ pointD i := by fin_cases i <;> norm_num [pointD]
  have hr : s ≤ pointD i := by fin_cases i <;> norm_num [pointD] <;> linarith [hs.2]
  have hp := polynomial_le hv hs.1 hd hr
  have hlo := (coarse_positive hs).trans_le (coarse_le_boundary i hs.1)
  have hg : 0 ≤ (gamma s)^5 := pow_nonneg (by dsimp [gamma]; linarith [hs.1]) 5
  by_contra! h
  have hm := mul_nonpos_of_nonneg_of_nonpos hg h
  linarith

/-- The profile is positive for `0 ≤ s ≤ 12/25`, `16/25 ≤ d ≤ 11/14` and
`53/50 - d ≤ v ≤ 31/50`. -/
theorem positive {v s d : ℝ} (hs : 0 ≤ s ∧ s ≤ 12/25)
    (hd : 16/25 ≤ d ∧ d ≤ 11/14) (hv : 53/50-d ≤ v ∧ v ≤ 31/50) :
    0 < profile v s d := by
  have h := positive_of_three_points (K := constantTerm+gamma s*(1+wing s)-
      radiusBound*Real.sqrt ((gamma s)^2+nu^2))
    (show -(2/5) ≤ s ∧ s ≤ 12/25 by constructor <;> linarith [hs.1,hs.2]) hd hv
    fun i => by
      have hi := boundary_positive i hs
      dsimp only [profile] at hi
      linarith
  dsimp only [profile]
  linarith

/-! The `defect` is the threshold sum less the bounds for the works on W, S, D
and C, with the force `(forceX, forceY)` on C. -/

def southUpper (s : ℝ) : ℝ :=
  radiusBound*Real.sqrt ((gamma s)^2+nu^2)-(gamma s+nu)/2

def forceX (v s : ℝ) : ℝ := beta*Real.cos v-gamma s*Real.sin s
def forceY (v s : ℝ) : ℝ := gamma s*Real.cos s-beta*Real.sin v

def centerUpper (v s : ℝ) : ℝ := coreUpper*(forceX v s+forceY v s)

def thresholdSum (v s d : ℝ) : ℝ :=
  beta*(1/2+angularWidth v)+gamma s*(1/2+angularWidth s)+
    (1/2+angularWidth (v+d))+nu*(1/2+angularWidth (d-s))

def defect (v s d : ℝ) : ℝ :=
  thresholdSum v s d-rhoBound*(beta+Real.sin (v+d))-
    southUpper s-diagonalUpper (d-s)-centerUpper v s

lemma gamma_bounds {s : ℝ} (hs : 0 ≤ s ∧ s ≤ 12/25) :
    38/25 ≤ gamma s ∧ gamma s ≤ 74/25 := by
  dsimp [gamma]
  constructor <;> linarith [hs.1,hs.2]

lemma south_support {a b s : ℝ} (hc : ContainedChart a |b|)
    (hs : 0 ≤ s ∧ s ≤ 12/25) : gamma s*a+nu*b ≤ southUpper s := by
  have hg : 0 ≤ gamma s := by linarith [(gamma_bounds hs).1]
  have hn : 0 ≤ nu := by norm_num [nu]
  have h := local_vertex_support hc (gamma s) nu
  rw [abs_of_nonneg hg,abs_of_nonneg hn] at h
  have hm := mul_le_mul_of_nonneg_right ceiling_bounds.1
    (Real.sqrt_nonneg ((gamma s)^2+nu^2))
  dsimp [southUpper]
  linarith

lemma central_forces {v s : ℝ} (hv : 0 ≤ v ∧ v ≤ 31/50)
    (hs : 0 ≤ s ∧ s ≤ 12/25) : 0 ≤ forceX v s ∧ 0 ≤ forceY v s := by
  have hv2 := mul_nonneg (sub_nonneg.mpr hv.2)
    (show 0 ≤ 31/50+v by linarith [hv.1])
  have hs2 := mul_nonneg (sub_nonneg.mpr hs.2)
    (show 0 ≤ 12/25+s by linarith [hs.1])
  have hcv : 4039/5000 ≤ Real.cos v := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]
  have hcs : 553/625 ≤ Real.cos s := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := s)]
  have hsv : Real.sin v ≤ 31/50 := (Real.sin_le hv.1).trans hv.2
  have hss : Real.sin s ≤ 12/25 := (Real.sin_le hs.1).trans hs.2
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hs.1
    (by linarith [hs.2,Real.pi_gt_d2])
  have hg := gamma_bounds hs
  have hprodS := mul_le_mul hg.2 hss hs0 (by norm_num : (0:ℝ) ≤ 74/25)
  have hprodC := mul_le_mul hg.1 hcs (by norm_num : (0:ℝ) ≤ 553/625)
    (show 0 ≤ gamma s by linarith [hg.1])
  dsimp [forceX,forceY,beta]
  constructor <;> nlinarith only [hcv,hsv,hprodS,hprodC]

lemma profile_eq_defect {v s d : ℝ} (hs : 0 ≤ s ∧ s ≤ 12/25)
    (hd : 16/25 ≤ d ∧ d ≤ 11/14) (hv : 53/50-d ≤ v ∧ v ≤ 31/50) :
    profile v s d=defect v s d := by
  have hW := angularWidth_eq (x := v) (by
    constructor <;> linarith [hv.1,hv.2,hd.2,Real.pi_gt_d2])
  have hS := angularWidth_eq (x := s) ⟨hs.1,by linarith [hs.2,Real.pi_gt_d2]⟩
  have hQ := angularWidth_eq (x := v+d) (by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2])
  have hR := angularWidth_eq (x := d-s) (by
    constructor <;> linarith [hs.1,hs.2,hd.1,hd.2,Real.pi_gt_d2])
  dsimp [profile,base,wing,gapTerm,diagonalTerm,defect,thresholdSum,southUpper,
    diagonalUpper,centerUpper,forceX,forceY,constantTerm,beta,nu,A,B,
    rootCoefficient,rootSlope,rootError,halfDifference,radiusBound,
    rhoBound,coreUpper]
  rw [hW,hS,hQ,hR]
  ring

/-- The separations of a missing west wing with W and S on their own axes are
incompatible for `0 ≤ s ≤ 12/25`, `16/25 ≤ d ≤ 11/14` and
`53/50 - d ≤ v ≤ 31/50`. -/
theorem impossible {X : Chart} (hW : X.WestOwn) (hS : X.SouthOwn)
    (h : X.MissingWest) (hs : 0 ≤ X.s ∧ X.s ≤ 12/25) (hd : 16/25 ≤ X.d ∧ X.d ≤ 11/14)
    (hv : 53/50-X.d ≤ X.v ∧ X.v ≤ 31/50) : False := by
  have hWD := h.west
  have hDS := h.south
  simp only [Chart.WestOwn,Chart.SouthOwn,Chart.WestDiagonal,
    Chart.SouthWing] at hW hS hWD hDS
  rw [add_comm X.d X.v] at hWD
  have hg : 0 ≤ gamma X.s := by linarith [(gamma_bounds hs).1]
  have hsum : thresholdSum X.v X.s X.d ≤
      ((beta+Real.sin (X.v+X.d))*X.aW-Real.cos (X.v+X.d)*X.bW)+
      (gamma X.s*X.aS+nu*X.bS)+
      (nu*Real.cos (X.d-X.s)*X.aD+(1-nu*Real.sin (X.d-X.s))*X.bD)+
      forceX X.v X.s*X.cx+forceY X.v X.s*X.cy := by
    dsimp [thresholdSum,forceX,forceY,beta,nu]
    linear_combination (41/20)*hW+(gamma X.s)*hS+hWD+(211/200)*hDS
  have hv0 : 0 ≤ X.v := by linarith [hv.1,hd.2]
  have hq : 1 ≤ X.v+X.d ∧ X.v+X.d ≤ Real.pi/2 := by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2]
  have hr : 0 ≤ X.d-X.s ∧ X.d-X.s ≤ 6/5 := by
    constructor <;> linarith [hs.1,hs.2,hd.1,hd.2]
  have hforce := central_forces ⟨hv0,hv.2⟩ hs
  have hc := center_corner hforce.1 hforce.2 X.box.1.2 X.box.2.2
  have hn : defect X.v X.s X.d ≤ 0 := by
    dsimp [defect,centerUpper]
    linarith only [hsum,west_support X.west hq,support X.diagonal hr,
      south_support X.south hs,hc]
  have hp := positive hs hd hv
  rw [profile_eq_defect hs hd hv] at hp
  linarith

end OwnSouth

end SquaresInCircles.Six.Wings.WestDiagonal

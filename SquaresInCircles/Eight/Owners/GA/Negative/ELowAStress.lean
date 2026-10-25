module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcavity
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Data
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3DEndpoints
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeADCorrection
public import SquaresInCircles.Eight.Owners.GA.Paired.ELowASource
public import SquaresInCircles.Eight.Owners.GA.Sorted.Support

/-!
# Eight squares: the small-A stress with negative flat-core E primaries

Both A primary errors are kept, each with its own sign, and their total is nonnegative and at most
`1/6`. Each negative E primary and a selected nonpositive TD2 carry their own positive secant
multiplier. The E tangent cancels exactly (`decomposition`).

`actual_false` covers secondary E edges with signed errors of either sign, and simultaneous
negative DE3 and EH1.
-/

section
/-!
## Whole-interval domains for the reference BT3 weights

The low quadratic ratios use their exact endpoint
chords and completed square. The rotating coefficient uses the stated
Taylor polynomials: the low upper polynomial has negative second
derivative, and the high upper polynomial is convex. No angular
subdivision is introduced by these coefficient estimates.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

namespace Explicit
theorem low_ranges {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    k .low z∈Icc (2/3:ℝ) (163/240) ∧
    l .low z∈Icc (513/500:ℝ) (533/500) ∧
    (241/250:ℝ)< m .low z ∧ m .low z<1181/1000 := by
  have hchord := mul_nonneg hz.1 (sub_nonneg.mpr hz.2)
  dsimp [k,l,m]
  refine ⟨⟨by linarith [hz.1],by linarith [hz.2]⟩,
    ⟨by linarith [hz.2],by linarith [hz.1]⟩,?_,?_⟩
  · nlinarith [hz.2]
  · nlinarith [sq_nonneg (z-(1/10)/(2*(769/200)))]

theorem low_ratios {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    (11/20)*l .low z<k .low z ∧ k .low z<(2/3)*l .low z ∧
    (47/50)*l .low z< m .low z ∧ m .low z<(113/100)*l .low z ∧ k .low z< m .low z := by
  have hb := low_ranges hz
  have hchord := mul_nonneg hz.1 (sub_nonneg.mpr hz.2)
  refine ⟨by linarith [hb.1.1,hb.2.1.2],by linarith [hb.1.2,hb.2.1.1],?_,?_,
    by linarith [hb.1.2,hb.2.2.1]⟩
  · dsimp [l,m]
    nlinarith [hz.2]
  · dsimp [l,m]
    nlinarith [sq_nonneg (z-(351/1250)/(2*(769/200)))]

private theorem r68e_low_dom {z : ℝ}
    (hz : z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ)) : z∈Icc 0 (1/4:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split] at hz
  exact hz

private theorem r68e_high_dom {z : ℝ}
    (hz : z∈Icc (Certificate.left .high:ℝ) (Certificate.right .high:ℝ)) :
    z∈Icc (1/4:ℝ) (7/10) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split] at hz
  exact hz

theorem high_k_derivative (z : ℝ) :
    HasDerivAt (k .high) (1/5+(9/5)*(z-1/5)-(39/10)*(z-1/5)^2) z := by
  have h0 : HasDerivAt (fun x : ℝ => x-1/5) 1 z := (hasDerivAt_id z).sub_const _
  have h1 := h0.div_const 5
  have h2 := (h0.pow 2).const_mul (9/10:ℝ)
  have h3 := (h0.pow 3).const_mul (13/10:ℝ)
  have h := ((h1.const_add (169/250:ℝ)).add h2).sub h3
  convert h using 1
  · funext x
    simp only [k,Pi.add_apply,Pi.sub_apply,Pi.pow_apply]
  · norm_num
    ring

theorem high_k_monotone : MonotoneOn (k .high) (Icc (1/4:ℝ) (7/10)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun x _ => (high_k_derivative x).continuousAt.continuousWithinAt)
    (fun z _ => high_k_derivative z)
  intro z hz
  have ht : z-1/5∈Icc (1/20:ℝ) (1/2) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)]

theorem high_ranges {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    k .high z∈Icc (55047/80000:ℝ) (1677/2000) ∧
    l .high z∈Icc (4141/4000:ℝ) (799/750) ∧
    (8579/10000:ℝ)< m .high z ∧ m .high z≤24/25 := by
  have hk0 := high_k_monotone (show (1/4:ℝ)∈Icc (1/4:ℝ) (7/10) by norm_num) hz hz.1
  have hk1 := high_k_monotone hz (show (7/10:ℝ)∈Icc (1/4:ℝ) (7/10) by norm_num) hz.2
  have e0 : k .high (1/4)=55047/80000 := by norm_num [k]
  have e1 : k .high (7/10)=1677/2000 := by norm_num [k]
  rw [e0] at hk0
  rw [e1] at hk1
  have ht : z-1/5∈Icc (1/20:ℝ) (1/2) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hr : z-1/4∈Icc (0:ℝ) (9/20) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hlchord := mul_nonneg (show 0≤z-1/5-1/20 by linarith [ht.1])
    (show 0≤1/2-(z-1/5) by linarith [ht.2])
  have hmchord := mul_nonneg hr.1 (sub_nonneg.mpr hr.2)
  refine ⟨⟨hk0,hk1⟩,?_,?_,?_⟩
  · simp only [l]
    exact ⟨by nlinarith [ht.1],by nlinarith [sq_nonneg (z-1/5-11/30)]⟩
  · simp only [m]
    nlinarith [sq_nonneg (z-1/4-7/24)]
  · simp only [m]
    nlinarith [hr.1]

theorem high_ratios {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    (659/1000)*l .high z<k .high z ∧ k .high z<(41/50)*l .high z ∧
    (4/5)*l .high z< m .high z ∧ m .high z<(129/125)*l .high z ∧ m .high z<l .high z := by
  have hb := high_ranges hz
  have hh := NegativeAPositiveTD.Explicit.high_ratio_lower
    (show z∈Icc (1/5:ℝ) (7/10) from ⟨by linarith [hz.1],hz.2⟩)
  have hkl : (659/1000)*l .high z<k .high z := by
    simpa [k,l,NegativeAPositiveTD.Explicit.k,NegativeAPositiveTD.Explicit.l,
      NegativeAPositiveTD.Explicit.highKAt,NegativeAPositiveTD.Explicit.highLAt] using hh
  exact ⟨hkl,by linarith [hb.1.2,hb.2.1.1],by linarith [hb.2.1.2,hb.2.2.1],
    by linarith [hb.2.1.1,hb.2.2.2],by linarith [hb.2.1.1,hb.2.2.2]⟩

theorem high_ratio_late {z : ℝ} (hz : z∈Icc (1/3:ℝ) (7/10:ℝ)) :
    m .high z<(23/25)*l .high z := by
  have hb := high_ranges (show z∈Icc (1/4:ℝ) (7/10) from ⟨by linarith [hz.1],hz.2⟩)
  have hr : z-1/4∈Icc (1/12:ℝ) (9/20) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hprod := mul_nonneg (show 0≤z-1/4-1/12 by linarith [hr.1])
    (show 0≤9/20-(z-1/4) by linarith [hr.2])
  have hm : m .high z≤91/100 := by dsimp [m]; nlinarith [hr.1,hr.2]
  linarith [hb.2.1.1]

theorem positive (f : Certificate.Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    0<k f z ∧ 1023/1000<l f z ∧ 0< m f z := by
  cases f
  · have hb := low_ranges (r68e_low_dom hz)
    exact ⟨by linarith [hb.1.1],by linarith [hb.2.1.1],by linarith [hb.2.2.1]⟩
  · have hb := high_ranges (r68e_high_dom hz)
    exact ⟨by linarith [hb.1.1],by linarith [hb.2.1.1],by linarith [hb.2.2.1]⟩
end Explicit

namespace Certificate
def rotationLo (f : Family) : ℚ[X] := m f*(PositiveTD.Certificate.C10+
  C (293/1000)*PositiveTD.Certificate.S11)
def rotationHi (f : Family) : ℚ[X] := m f*(PositiveTD.Certificate.C12+
  C (293/1000)*PositiveTD.Certificate.S9)
def highDifference : ℚ[X] := rotationLo .high-k .high

/-! Integer certificates: each polynomial is represented by a scaled integer list
(`WholeIntervalPolynomial.Certificate.Scaled`) and the kernel checks integer facts only. -/

open WholeIntervalPolynomial.Certificate (Scaled lowerZ upperZ chebList lowerOn_eq_of_rep
  upperOn_eq_of_rep)

private theorem r68_rep_lit {l : List ℤ} {s : ℕ} {p : ℚ[X]}
    (h : ∀ x : ℚ,(WholeIntervalPolynomial.Certificate.toPoly l).eval x=(s:ℚ)*p.eval x) :
    (⟨l,s⟩ : Scaled).Rep p := by
  unfold Scaled.Rep
  apply Polynomial.funext
  intro x
  rw [h x,eval_mul,eval_C]

private def r68Qlo : Scaled :=
  ⟨[39916800000,11695622400,-19958400000,-1949270400,1663200000,97463520,-55440000,-2320560,
    990000,32230,-11000,-293],39916800000⟩
private theorem r68Qlo_rep : r68Qlo.Rep
    (PositiveTD.Certificate.C10+C (293/1000)*PositiveTD.Certificate.S11) :=
  r68_rep_lit fun x => by
    simp only [WholeIntervalPolynomial.Certificate.toPoly,PositiveTD.Certificate.C10,
      PositiveTD.Certificate.C4,PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,
      PositiveTD.Certificate.S5,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_pow,eval_one,
      eval_zero]
    push_cast
    ring

private def r68Qhi : Scaled :=
  ⟨[11975040000,3508686720,-5987520000,-584781120,498960000,29239056,-16632000,-696168,297000,
    9669,-3300,0,25],11975040000⟩
private theorem r68Qhi_rep : r68Qhi.Rep
    (PositiveTD.Certificate.C12+C (293/1000)*PositiveTD.Certificate.S9) :=
  r68_rep_lit fun x => by
    simp only [WholeIntervalPolynomial.Certificate.toPoly,PositiveTD.Certificate.C12,
      PositiveTD.Certificate.C10,PositiveTD.Certificate.C4,PositiveTD.Certificate.S9,
      PositiveTD.Certificate.S5,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_pow,eval_one,
      eval_zero]
    push_cast
    ring

private def r68m : Family→Scaled
  | .low => ⟨[236,20,-769],200⟩
  | .high => ⟨[121,-130,120],100⟩
private theorem r68m_rep : ∀ f,(r68m f).Rep (m f)
  | .low => r68_rep_lit fun x => by
      simp only [WholeIntervalPolynomial.Certificate.toPoly,m,eval_add,eval_sub,eval_mul,eval_C,
        eval_X,eval_pow,eval_zero]
      push_cast
      ring
  | .high => r68_rep_lit fun x => by
      simp only [WholeIntervalPolynomial.Certificate.toPoly,m,eval_add,eval_sub,eval_mul,eval_C,
        eval_X,eval_pow,eval_zero]
      push_cast
      ring

private def r68kHigh : Scaled := ⟨[6824,-3160,16800,-13000],10000⟩
private theorem r68kHigh_rep : r68kHigh.Rep (k .high) :=
  r68_rep_lit fun x => by
    simp only [WholeIntervalPolynomial.Certificate.toPoly,k,eval_add,eval_sub,eval_mul,eval_C,
      eval_X,eval_pow,eval_zero]
    push_cast
    ring

private def r68Lo (f : Family) : Scaled := (r68m f).mul r68Qlo
private theorem r68Lo_rep (f : Family) : (r68Lo f).Rep (rotationLo f) := (r68m_rep f).mul r68Qlo_rep
private def r68Hi (f : Family) : Scaled := (r68m f).mul r68Qhi
private theorem r68Hi_rep (f : Family) : (r68Hi f).Rep (rotationHi f) := (r68m_rep f).mul r68Qhi_rep
private def r68Diff : Scaled := (r68Lo .high).sub r68kHigh
private theorem r68Diff_rep : r68Diff.Rep highDifference := (r68Lo_rep .high).sub r68kHigh_rep

/-! The derivative of a coefficient list. -/

private def r68dAux : ℕ→List ℤ→List ℤ
  | _,[] => []
  | n,a :: t => ((n:ℤ)*a) :: r68dAux (n+1) t
private def r68dList : List ℤ→List ℤ
  | [] => []
  | _ :: t => r68dAux 1 t
private theorem r68dAux_spec : ∀ (l : List ℤ) (n : ℕ),
    WholeIntervalPolynomial.Certificate.toPoly (r68dAux n l)=
      C (n:ℚ)*WholeIntervalPolynomial.Certificate.toPoly l+
        X*derivative (WholeIntervalPolynomial.Certificate.toPoly l)
  | [],n => by simp [r68dAux,WholeIntervalPolynomial.Certificate.toPoly]
  | a :: t,n => by
    simp only [r68dAux,WholeIntervalPolynomial.Certificate.toPoly,r68dAux_spec t (n+1),
      derivative_add,derivative_C,derivative_mul,derivative_X,zero_add,one_mul]
    push_cast
    rw [map_mul,map_add,map_one]
    ring
private theorem r68dList_spec (l : List ℤ) :
    WholeIntervalPolynomial.Certificate.toPoly (r68dList l)=
      derivative (WholeIntervalPolynomial.Certificate.toPoly l) := by
  cases l with
  | nil => simp [r68dList,WholeIntervalPolynomial.Certificate.toPoly]
  | cons a t =>
    simp only [r68dList,r68dAux_spec,WholeIntervalPolynomial.Certificate.toPoly,derivative_add,
      derivative_C,derivative_mul,derivative_X,zero_add,one_mul,Nat.cast_one,map_one]
private def r68deriv (c : Scaled) : Scaled := ⟨r68dList c.l,c.s⟩
private theorem r68deriv_rep {c : Scaled} {p : ℚ[X]} (h : c.Rep p) :
    (r68deriv c).Rep (derivative p) := by
  unfold Scaled.Rep at *
  simp only [r68deriv,r68dList_spec,h,derivative_mul,derivative_C,zero_mul,zero_add]

/-! Rational values from integer data. -/

private theorem r68_rep_eval {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s : ℤ)
    {a : ℚ} (hden : den≠0) (ha : a=num*s/den) : (S.center num den s 0).Rep (C (p.eval a)) := by
  have hc := hp.centered num den s 0 (a:=a) (b:=a) hden (by rw [← ha]; ring) (by simp)
  have he : WholeIntervalPolynomial.centered a a p=C (p.eval a) := by
    rw [WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,sub_self,zero_div,
      map_zero,zero_mul,add_zero,add_self_div_two,comp_C]
  rwa [he] at hc

private theorem r68_val {S : Scaled} {v : ℚ} (h : S.Rep (C v)) (hs : S.s≠0) :
    v=(S.l.getD 0 0:ℚ)/S.s := by
  have hh := h.coeff hs 0
  rwa [coeff_C_zero] at hh

private theorem r68_lt_of {v q : ℚ} {N a : ℤ} {s b : ℕ} (hv : v=(N:ℚ)/s) (hs : s≠0)
    (hq : q=(a:ℚ)/b) (hb : 0<b) (h : N*b<a*s) : v<q := by
  have hs' : (0:ℚ)<s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  rw [hv,hq,div_lt_div_iff₀ hs' hb']
  exact_mod_cast h

private theorem r68_gt_of {v q : ℚ} {N a : ℤ} {s b : ℕ} (hv : v=(N:ℚ)/s) (hs : s≠0)
    (hq : q=(a:ℚ)/b) (hb : 0<b) (h : a*s<N*b) : q<v := by
  have hs' : (0:ℚ)<s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  rw [hv,hq,div_lt_div_iff₀ hb' hs']
  exact_mod_cast h

private theorem r68_eq_of {v q : ℚ} {N a : ℤ} {s b : ℕ} (hv : v=(N:ℚ)/s) (hs : s≠0)
    (hq : q=(a:ℚ)/b) (hb : 0<b) (h : N*b=a*s) : v=q := by
  have hs' : (s:ℚ)≠0 := by exact_mod_cast hs
  have hb' : (b:ℚ)≠0 := by exact_mod_cast hb.ne'
  rw [hv,hq,div_eq_div_iff hs' hb']
  exact_mod_cast h

private theorem r68_div_form {Z : ℤ} {s L : ℕ} :
    (Z:ℚ)/((s:ℚ)*2^L/2)=((2*Z:ℤ):ℚ)/((s*2^L:ℕ):ℚ) := by
  push_cast
  ring

private theorem r68_scale_ne {s L : ℕ} (hs : s≠0) : s*2^L≠0 :=
  mul_ne_zero hs (pow_ne_zero _ two_ne_zero)

/-! The kernel checks. -/

private def r68A : Scaled := (r68Lo .low).center 1 8 1 1
private def r68B : Scaled := (r68deriv (r68deriv (r68Hi .low))).center 1 8 1 1

private theorem r68A_check : r68A.s≠0 ∧ r68A.l.length≤15 ∧
    (2009:ℤ)*((r68A.s*2^r68A.l.length:ℕ):ℤ)<
      2*lowerZ 14 (fun j => (chebList r68A.l).getD j 0)*((2000:ℕ):ℤ) := by
  decide +kernel

private theorem r68B_check : r68B.s≠0 ∧ r68B.l.length≤15 ∧
    2*upperZ 14 (fun j => (chebList r68B.l).getD j 0)*((5:ℕ):ℤ)<
      (-44:ℤ)*((r68B.s*2^r68B.l.length:ℕ):ℤ) := by
  decide +kernel

private theorem r68low_values_check : (r68Hi .low).s≠0 ∧
    (r68Hi .low).l.getD 0 0*((50:ℕ):ℤ)=(59:ℤ)*((r68Hi .low).s:ℤ) ∧
    (r68deriv (r68Hi .low)).l.getD 0 0*((50000:ℕ):ℤ)=(22287:ℤ)*((r68deriv (r68Hi .low)).s:ℤ) := by
  decide +kernel

private def r68H1 : Scaled := (r68Lo .high).center 1 40 19 9
private def r68H2 : Scaled := (r68deriv r68Diff).center 1 40 19 9
private def r68H5 : Scaled := r68Diff.center 7 10 1 0
private def r68H6 : Scaled := (r68deriv (r68deriv (r68Hi .high))).center 1 40 19 9
private def r68H8 : Scaled := (r68Hi .high).center 1 4 1 0
private def r68H9 : Scaled := (r68Hi .high).center 7 10 1 0

private theorem r68H1_check : r68H1.s≠0 ∧ r68H1.l.length≤15 ∧
    (2017:ℤ)*((r68H1.s*2^r68H1.l.length:ℕ):ℤ)<
      2*lowerZ 14 (fun j => (chebList r68H1.l).getD j 0)*((2500:ℕ):ℤ) := by
  decide +kernel

private theorem r68H2_check : r68H2.s≠0 ∧ r68H2.l.length≤15 ∧
    2*upperZ 14 (fun j => (chebList r68H2.l).getD j 0)*((500:ℕ):ℤ)<
      (-61:ℤ)*((r68H2.s*2^r68H2.l.length:ℕ):ℤ) := by
  decide +kernel

private theorem r68H6_check : r68H6.s≠0 ∧ r68H6.l.length≤15 ∧
    (111:ℤ)*((r68H6.s*2^r68H6.l.length:ℕ):ℤ)<
      2*lowerZ 14 (fun j => (chebList r68H6.l).getD j 0)*((100:ℕ):ℤ) := by
  decide +kernel

private theorem r68high_values_check : r68H5.s≠0 ∧
    (829:ℤ)*(r68H5.s:ℤ)<r68H5.l.getD 0 0*((100000:ℕ):ℤ) ∧
    r68H8.s≠0 ∧ r68H8.l.getD 0 0*((500000:ℕ):ℤ)<(499873:ℤ)*(r68H8.s:ℤ) ∧
    r68H9.s≠0 ∧ r68H9.l.getD 0 0*((250000:ℕ):ℤ)<(211699:ℤ)*(r68H9.s:ℤ) := by
  decide +kernel

theorem low_rotation_certificate :
    WholeIntervalPolynomial.centered 0 (1/4) (rotationLo .low)=
      WholeIntervalPolynomial.expansion 14 (WholeIntervalPolynomial.centered 0 (1/4) (rotationLo .low)) ∧
    (2009/2000:ℚ)<WholeIntervalPolynomial.lowerOn 14 0 (1/4) (rotationLo .low) ∧
    WholeIntervalPolynomial.centered 0 (1/4) (rotationHi .low).derivative.derivative=
      WholeIntervalPolynomial.expansion 14
        (WholeIntervalPolynomial.centered 0 (1/4) (rotationHi .low).derivative.derivative) ∧
    WholeIntervalPolynomial.upperOn 14 0 (1/4) (rotationHi .low).derivative.derivative< -(44/5:ℚ) ∧
    (rotationHi .low).eval 0=59/50 ∧ (rotationHi .low).derivative.eval 0=22287/50000 := by
  obtain ⟨h1,h2,h3⟩ := r68A_check
  obtain ⟨h4,h5,h6⟩ := r68B_check
  obtain ⟨h7,h8,h9⟩ := r68low_values_check
  have hA : r68A.Rep (WholeIntervalPolynomial.centered 0 (1/4) (rotationLo .low)) :=
    (r68Lo_rep .low).centered 1 8 1 1 (by norm_num) (by norm_num) (by norm_num)
  have hB : r68B.Rep
      (WholeIntervalPolynomial.centered 0 (1/4) (rotationHi .low).derivative.derivative) :=
    (r68deriv_rep (r68deriv_rep (r68Hi_rep .low))).centered 1 8 1 1 (by norm_num) (by norm_num)
      (by norm_num)
  refine ⟨hA.eq_expansion h1 h2,?_,hB.eq_expansion h4 h5,?_,?_,?_⟩
  · rw [lowerOn_eq_of_rep hA h1 h2,r68_div_form]
    exact r68_gt_of rfl (r68_scale_ne h1) (by norm_num) (by norm_num) h3
  · rw [upperOn_eq_of_rep hB h4 h5,r68_div_form]
    exact r68_lt_of rfl (r68_scale_ne h4) (by norm_num) (by norm_num) h6
  · rw [← coeff_zero_eq_eval_zero]
    exact r68_eq_of ((r68Hi_rep .low).coeff h7 0) h7 (by norm_num) (by norm_num) h8
  · rw [← coeff_zero_eq_eval_zero]
    exact r68_eq_of ((r68deriv_rep (r68Hi_rep .low)).coeff h7 0) h7 (by norm_num) (by norm_num) h9

theorem high_rotation_certificate :
    WholeIntervalPolynomial.centered (1/4) (7/10) (rotationLo .high)=
      WholeIntervalPolynomial.expansion 14
        (WholeIntervalPolynomial.centered (1/4) (7/10) (rotationLo .high)) ∧
    (2017/2500:ℚ)<WholeIntervalPolynomial.lowerOn 14 (1/4) (7/10) (rotationLo .high) ∧
    WholeIntervalPolynomial.centered (1/4) (7/10) highDifference.derivative=
      WholeIntervalPolynomial.expansion 14
        (WholeIntervalPolynomial.centered (1/4) (7/10) highDifference.derivative) ∧
    WholeIntervalPolynomial.upperOn 14 (1/4) (7/10) highDifference.derivative< -(61/500:ℚ) ∧
    (829/100000:ℚ)<highDifference.eval (7/10) ∧
    WholeIntervalPolynomial.centered (1/4) (7/10) (rotationHi .high).derivative.derivative=
      WholeIntervalPolynomial.expansion 14
        (WholeIntervalPolynomial.centered (1/4) (7/10) (rotationHi .high).derivative.derivative) ∧
    (111/100:ℚ)<WholeIntervalPolynomial.lowerOn 14 (1/4) (7/10) (rotationHi .high).derivative.derivative ∧
    (rotationHi .high).eval (1/4)<499873/500000 ∧
    (rotationHi .high).eval (7/10)<211699/250000 := by
  obtain ⟨h1,h2,h3⟩ := r68H1_check
  obtain ⟨h4,h5,h6⟩ := r68H2_check
  obtain ⟨h7,h8,h9⟩ := r68H6_check
  obtain ⟨g1,g2,g3,g4,g5,g6⟩ := r68high_values_check
  have hA : r68H1.Rep (WholeIntervalPolynomial.centered (1/4) (7/10) (rotationLo .high)) :=
    (r68Lo_rep .high).centered 1 40 19 9 (by norm_num) (by norm_num) (by norm_num)
  have hB : r68H2.Rep
      (WholeIntervalPolynomial.centered (1/4) (7/10) highDifference.derivative) :=
    (r68deriv_rep r68Diff_rep).centered 1 40 19 9 (by norm_num) (by norm_num) (by norm_num)
  have hD : r68H6.Rep
      (WholeIntervalPolynomial.centered (1/4) (7/10) (rotationHi .high).derivative.derivative) :=
    (r68deriv_rep (r68deriv_rep (r68Hi_rep .high))).centered 1 40 19 9 (by norm_num)
      (by norm_num) (by norm_num)
  have v5 := r68_val (r68_rep_eval r68Diff_rep 7 10 1 (a:=7/10) (by norm_num) (by norm_num)) g1
  have v8 := r68_val (r68_rep_eval (r68Hi_rep .high) 1 4 1 (a:=1/4) (by norm_num) (by norm_num)) g3
  have v9 := r68_val (r68_rep_eval (r68Hi_rep .high) 7 10 1 (a:=7/10) (by norm_num)
    (by norm_num)) g5
  refine ⟨hA.eq_expansion h1 h2,?_,hB.eq_expansion h4 h5,?_,?_,hD.eq_expansion h7 h8,?_,?_,?_⟩
  · rw [lowerOn_eq_of_rep hA h1 h2,r68_div_form]
    exact r68_gt_of rfl (r68_scale_ne h1) (by norm_num) (by norm_num) h3
  · rw [upperOn_eq_of_rep hB h4 h5,r68_div_form]
    exact r68_lt_of rfl (r68_scale_ne h4) (by norm_num) (by norm_num) h6
  · exact r68_gt_of v5 g1 (by norm_num) (by norm_num) g2
  · rw [lowerOn_eq_of_rep hD h7 h8,r68_div_form]
    exact r68_gt_of rfl (r68_scale_ne h7) (by norm_num) (by norm_num) h9
  · exact r68_lt_of v8 g3 (by norm_num) (by norm_num) g4
  · exact r68_lt_of v9 g5 (by norm_num) (by norm_num) g6
end Certificate

namespace Explicit
open Certificate (Family)

private theorem r68_aeval (p : ℚ[X]) (q : ℚ) : aeval (q:ℝ) p=((p.eval q:ℚ):ℝ) := by
  have h := Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A:=ℝ) q p
  simpa only [eq_ratCast] using h

private theorem r68_low_dom' {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]
  exact hz

private theorem r68_high_dom' {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    z∈Icc (Certificate.left .high:ℝ) (Certificate.right .high:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]
  exact hz

theorem rotation_bounds (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    aeval z (Certificate.rotationLo f)≤c f z ∧ c f z≤aeval z (Certificate.rotationHi f) := by
  have ht := PositiveTD.Certificate.taylor_bounds (frame_domain f hz)
  have hm := (positive f hz).2.2
  have hlo := mul_le_mul_of_nonneg_left
    (show aeval z PositiveTD.Certificate.C10+(293/1000)*aeval z PositiveTD.Certificate.S11≤
      Real.cos z+(293/1000)*Real.sin z by linarith [ht.2.2.2.2.1,ht.2.1]) hm.le
  have hhi := mul_le_mul_of_nonneg_left
    (show Real.cos z+(293/1000)*Real.sin z≤
      aeval z PositiveTD.Certificate.C12+(293/1000)*aeval z PositiveTD.Certificate.S9 by
        linarith [ht.2.2.2.2.2,ht.2.2.1]) hm.le
  have e1 : aeval z (Certificate.rotationLo f)=m f z*(aeval z PositiveTD.Certificate.C10+
      (293/1000)*aeval z PositiveTD.Certificate.S11) := by
    simp [Certificate.rotationLo]
  have e2 : aeval z (Certificate.rotationHi f)=m f z*(aeval z PositiveTD.Certificate.C12+
      (293/1000)*aeval z PositiveTD.Certificate.S9) := by
    simp [Certificate.rotationHi]
  have e3 : c f z=m f z*(Real.cos z+(293/1000)*Real.sin z) := by
    simp [c,PositiveBT3.tilted,PositiveTD.eta]
  rw [e1,e2,e3]
  exact ⟨hlo,hhi⟩

theorem low_rotation_upper {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    aeval z (Certificate.rotationHi .low)<149/125 := by
  let p := Certificate.rotationHi .low
  have hc := Certificate.low_rotation_certificate
  have hsecond (x : ℝ) (hx : x∈Icc 0 (1/4:ℝ)) : aeval x p.derivative.derivative< -(44/5:ℝ) := by
    have hb := (WholeIntervalPolynomial.interval_bounds (D:=14) (a:=0) (b:=1/4) (by norm_num)
      hc.2.2.1 (x:=x) (by push_cast; exact hx)).2
    have hu : ((WholeIntervalPolynomial.upperOn 14 0 (1/4) p.derivative.derivative:ℚ):ℝ)<
        ((-(44/5):ℚ):ℝ) := by exact_mod_cast hc.2.2.2.1
    push_cast at hu
    linarith
  have hDanti : AntitoneOn (fun x : ℝ => aeval x p.derivative+(44/5)*x) (Icc 0 (1/4:ℝ)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x _ => ((CenteredMonomialBounds.aeval_hasDerivAt p.derivative x).add
        ((hasDerivAt_id x).const_mul (44/5))).continuousAt.continuousWithinAt)
      (fun x _ => (CenteredMonomialBounds.aeval_hasDerivAt p.derivative x).add
        ((hasDerivAt_id x).const_mul (44/5)))
    intro x hx
    linarith [hsecond x (Ioo_subset_Icc_self hx)]
  have hD (x : ℝ) (hx : x∈Icc 0 (1/4:ℝ)) : aeval x p.derivative≤22287/50000-(44/5)*x := by
    have hh := hDanti (show (0:ℝ)∈Icc 0 (1/4:ℝ) by norm_num) hx hx.1
    have he : aeval (0:ℝ) p.derivative=22287/50000 := by
      have h0 := r68_aeval p.derivative 0
      rw [hc.2.2.2.2.2] at h0
      push_cast at h0
      exact h0
    simp only [he,mul_zero,add_zero] at hh
    linarith
  have hanti : AntitoneOn (fun x : ℝ => aeval x p-(22287/50000)*x+(22/5)*x^2)
      (Icc 0 (1/4:ℝ)) := by
    have hd (x : ℝ) : HasDerivAt (fun x : ℝ => aeval x p-(22287/50000)*x+(22/5)*x^2)
        (aeval x p.derivative-(22287/50000)*1+(22/5)*(↑2*x^(2-1)*1)) x :=
      ((CenteredMonomialBounds.aeval_hasDerivAt p x).sub
        ((hasDerivAt_id x).const_mul (22287/50000))).add
        (((hasDerivAt_id x).pow 2).const_mul (22/5))
    apply antiOn_of_hasDeriv_nonpos
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
    intro x hx
    have hh := hD x (Ioo_subset_Icc_self hx)
    norm_num
    linarith
  have hh := hanti (show (0:ℝ)∈Icc 0 (1/4:ℝ) by norm_num) hz hz.1
  have he : aeval (0:ℝ) p=59/50 := by
    have h0 := r68_aeval p 0
    rw [hc.2.2.2.2.1] at h0
    push_cast at h0
    exact h0
  simp only [he,mul_zero,sub_zero] at hh
  norm_num at hh
  nlinarith [sq_nonneg (z-(22287/50000)/(2*(22/5)))]

theorem low_rotation {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) : 1<c .low z ∧ c .low z<6/5 := by
  have hc := Certificate.low_rotation_certificate
  have hlo := WholeIntervalPolynomial.positive_on_interval (D:=14) (a:=0) (b:=1/4) (by norm_num)
    hc.1 hc.2.1 (x:=z) (by push_cast; exact hz)
  have hb := rotation_bounds .low (r68_low_dom' hz)
  push_cast at hlo
  exact ⟨by linarith [hb.1],by linarith [hb.2,low_rotation_upper hz]⟩

theorem high_rotation {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    (2017/2500:ℝ)<c .high z ∧ k .high z<c .high z ∧ c .high z<1 := by
  have hc := Certificate.high_rotation_certificate
  have hz' : z∈Icc ((1/4:ℚ):ℝ) ((7/10:ℚ):ℝ) := by push_cast; exact hz
  have hlo := WholeIntervalPolynomial.positive_on_interval (D:=14) (by norm_num) hc.1 hc.2.1 hz'
  push_cast at hlo
  have hdiff : AntitoneOn (fun z : ℝ => aeval z Certificate.highDifference)
      (Icc (1/4:ℝ) (7/10)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun z _ => (CenteredMonomialBounds.aeval_hasDerivAt Certificate.highDifference
        z).continuousAt.continuousWithinAt)
      (fun z _ => CenteredMonomialBounds.aeval_hasDerivAt Certificate.highDifference z)
    intro x hx
    have hx' : x∈Icc ((1/4:ℚ):ℝ) ((7/10:ℚ):ℝ) := by
      push_cast; exact Ioo_subset_Icc_self hx
    have hh := (WholeIntervalPolynomial.interval_bounds (D:=14) (by norm_num) hc.2.2.1 hx').2
    have hu : ((WholeIntervalPolynomial.upperOn 14 (1/4) (7/10)
        Certificate.highDifference.derivative:ℚ):ℝ)<((-(61/500):ℚ):ℝ) := by
      exact_mod_cast hc.2.2.2.1
    push_cast at hu
    linarith
  have hright : (829/100000:ℝ)<aeval (7/10:ℝ) Certificate.highDifference := by
    have h0 := r68_aeval Certificate.highDifference (7/10)
    have h1 : ((829/100000:ℚ):ℝ)<((Certificate.highDifference.eval (7/10):ℚ):ℝ) := by
      exact_mod_cast hc.2.2.2.2.1
    push_cast at h0 h1
    linarith
  have hmin := hdiff hz (show (7/10:ℝ)∈Icc (1/4:ℝ) (7/10) by norm_num) hz.2
  have hconc : ConcaveOn ℝ (Icc (1/4:ℝ) (7/10))
      (fun x : ℝ => 1-aeval x (Certificate.rotationHi .high)) := by
    apply concave_of_deriv2
      (fun x _ => (hasDerivAt_const x (1:ℝ)).sub
        (CenteredMonomialBounds.aeval_hasDerivAt (Certificate.rotationHi .high) x))
      (fun x _ => (hasDerivAt_const x (0:ℝ)).sub (CenteredMonomialBounds.aeval_hasDerivAt
        (Certificate.rotationHi .high).derivative x))
    intro x hx
    have hx' : x∈Icc ((1/4:ℚ):ℝ) ((7/10:ℚ):ℝ) := by push_cast; exact hx
    have hh := WholeIntervalPolynomial.positive_on_interval (D:=14) (by norm_num)
      hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hx'
    push_cast at hh
    linarith
  have hleft : 0<1-aeval (1/4:ℝ) (Certificate.rotationHi .high) := by
    have h0 := r68_aeval (Certificate.rotationHi .high) (1/4)
    have h1 : (((Certificate.rotationHi .high).eval (1/4):ℚ):ℝ)<((499873/500000:ℚ):ℝ) := by
      exact_mod_cast hc.2.2.2.2.2.2.2.1
    push_cast at h0 h1
    linarith
  have hright' : 0<1-aeval (7/10:ℝ) (Certificate.rotationHi .high) := by
    have h0 := r68_aeval (Certificate.rotationHi .high) (7/10)
    have h1 : (((Certificate.rotationHi .high).eval (7/10):ℚ):ℝ)<((211699/250000:ℚ):ℝ) := by
      exact_mod_cast hc.2.2.2.2.2.2.2.2
    push_cast at h0 h1
    linarith
  have hupper := concave_gt_of_endpoints hconc hz hleft hright'
  have hb := rotation_bounds .high (r68_high_dom' hz)
  simp only [Certificate.highDifference,map_sub,k_eval] at hmin hright
  exact ⟨hlo.trans_le hb.1,by linarith [hb.1],by linarith [hb.2]⟩

end Explicit
end SquaresInCircles.Eight.GlobalGA.NegativeABT3
end
end
end

section
/-!
## Ordered coefficient domains including the actual A secant

The high family retains D as a fourth ordinary
pair. On the low family D uses H's negative envelope and its separate
linear positive cost. Every bound includes the entire actual A cut.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.Explicit
open Candidate Secondary
open Certificate (Family)

abbrev GA_cut_cosine := @NegativeAPositiveTD.Explicit.GA_cut_cosine
abbrev AB_cut_cosine := @NegativeAPositiveTD.Explicit.AB_cut_cosine

def p (f : Family) (atG : Bool) (z s : ℝ) : Fin 4→ℝ :=
  pWeights f atG (k f z) (l f z) (m f z) (c f z) s
def q (f : Family) (atG : Bool) (z s : ℝ) : Fin 4→ℝ :=
  qWeights f atG (k f z) (l f z) (m f z) (c f z) s

private theorem r68_low_dom {z : ℝ} :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ)↔z∈Icc 0 (1/4:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]

private theorem r68_high_dom {z : ℝ} :
    z∈Icc (Certificate.left .high:ℝ) (Certificate.right .high:ℝ)↔z∈Icc (1/4:ℝ) (7/10) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]

theorem basic_domain (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    k f z∈Icc (1/2:ℝ) (17/20:ℝ) ∧ (1023/1000:ℝ)<l f z ∧
    (11/20)*l f z<k f z ∧ k f z<(17/20)*l f z ∧
    (4/5)*l f z< m f z ∧ m f z<(113/100)*l f z ∧
    k f z<c f z ∧ c f z<6/5 := by
  cases f
  · have hz' := r68_low_dom.1 hz
    obtain ⟨hk,hl,hm₀,hm₁⟩ := low_ranges hz'
    obtain ⟨hkl₀,hkl₁,hml₀,hml₁,hkm⟩ := low_ratios hz'
    obtain ⟨hc₀,hc₁⟩ := low_rotation hz'
    exact ⟨⟨by linarith [hk.1],by linarith [hk.2]⟩,by linarith [hl.1],
      hkl₀,by linarith [hl.1,hk.2],by linarith [hl.1],hml₁,by linarith [hk.2],hc₁⟩
  · have hz' := r68_high_dom.1 hz
    obtain ⟨hk,hl,hm₀,hm₁⟩ := high_ranges hz'
    obtain ⟨hkl₀,hkl₁,hml₀,hml₁,hml⟩ := high_ratios hz'
    obtain ⟨hc₀,hkc,hc₁⟩ := high_rotation hz'
    exact ⟨⟨by linarith [hk.1],by linarith [hk.2]⟩,by linarith [hl.1],
      by linarith [hl.1],by linarith [hl.1],hml₀,by linarith [hl.1],hkc,by linarith⟩

theorem family_positive (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    0<k f z ∧ 0<l f z ∧ 0<c f z ∧ 0< m f z := by
  have hb := basic_domain f hz
  have hk : 0<k f z := by linarith [hb.1.1]
  exact ⟨hk,by linarith [hb.2.1],hk.trans hb.2.2.2.2.2.2.1,
    by linarith [hb.2.1,hb.2.2.2.2.1]⟩

theorem family_basic_domain (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    k f z∈Icc (1/2:ℝ) (17/20:ℝ) ∧ c f z∈Icc (k f z) 2 ∧
    1<l f z ∧ k f z<l f z ∧ (11/20)*l f z<k f z ∧
    (77/100)*l f z< m f z ∧ m f z<(71/50)*l f z := by
  have hb := basic_domain f hz
  exact ⟨hb.1,⟨hb.2.2.2.2.2.2.1.le,by linarith [hb.2.2.2.2.2.2.2]⟩,
    by linarith [hb.2.1],by linarith [hb.2.1,hb.2.2.2.1],hb.2.2.1,
    by linarith [hb.2.1,hb.2.2.2.2.1],by linarith [hb.2.1,hb.2.2.2.2.2.1]⟩

theorem low_ratio {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    (11/20)*l .low z<k .low z ∧ k .low z<(2/3)*l .low z :=
  ⟨(low_ratios hz).1,(low_ratios hz).2.1⟩

theorem secant_bounds (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) :
    l f z≤ secant (l f z) s ∧ secant (l f z) s<2*k f z ∧
      secant (l f z) s<2*m f z := by
  have hb := basic_domain f hz
  have hl : 0<l f z := by linarith [hb.2.1]
  have hcos := AB_cut_cosine (angle_domain atG hs).1
  have hc : 0<Real.cos s := by linarith
  have hw : l f z≤ secant (l f z) s := by
    apply (le_div_iff₀ hc).2
    nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one s) hl.le]
  have hk₁ := mul_lt_mul_of_pos_right hb.2.2.1 hc
  have hk₂ := mul_lt_mul_of_pos_left hcos (show 0<(11/20)*l f z by positivity)
  have hm₁ := mul_lt_mul_of_pos_right hb.2.2.2.2.1 hc
  have hm₂ := mul_lt_mul_of_pos_left hcos (show 0<(4/5)*l f z by positivity)
  refine ⟨hw,?_,?_⟩
  · exact (div_lt_iff₀ hc).2 (by nlinarith)
  · exact (div_lt_iff₀ hc).2 (by nlinarith)

theorem ordered_pair_domain (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) (i : Fin 4) :
    0<p f atG z s i ∧ p f atG z s i≤q f atG z s i ∧
      q f atG z s i≤2*p f atG z s i := by
  have hb := basic_domain f hz
  have hl : 0<l f z := by linarith [hb.2.1]
  have hm : 0< m f z := by linarith [hb.2.2.2.2.1]
  have hk : 0<k f z := by linarith [hb.1.1]
  obtain ⟨hw,hwk,hwm⟩ := secant_bounds f atG hz hs
  have hkl : k f z<l f z := by linarith [hb.2.2.2.1]
  have hml : m f z<2*l f z := by linarith [hb.2.2.2.2.2.1]
  have hB : 0<lambdaB atG (l f z) s ∧
      lambdaB atG (l f z) s≤2*m f z ∧ m f z≤2*lambdaB atG (l f z) s := by
    cases atG <;> simp only [lambdaB,NegativeAPositiveTD.lambdaB,↓reduceIte,Bool.false_eq_true]
    · exact ⟨hl.trans_le hw,hwm.le,by linarith⟩
    · exact ⟨hl,by linarith,by linarith⟩
  have hG : 0<k f z ∧ k f z≤lambdaG atG (l f z) s ∧
      lambdaG atG (l f z) s≤2*k f z := by
    cases atG <;> simp only [lambdaG,NegativeAPositiveTD.lambdaG,↓reduceIte,Bool.false_eq_true]
    · exact ⟨hk,hkl.le,by linarith⟩
    · exact ⟨hk,hkl.le.trans hw,hwk.le⟩
  fin_cases i
  · simpa [p,q,pWeights,qWeights] using And.intro hk
      (And.intro (by linarith [hb.1.2] : k f z≤1) (by linarith [hb.1.1] : 1≤2*k f z))
  · simpa [p,q,pWeights,qWeights] using hG
  · simp only [p,q,pWeights,qWeights,Fin.reduceFinMk,Matrix.cons_val]
    rcases le_total (lambdaB atG (l f z) s) (m f z) with hh|hh
    · rw [min_eq_left hh,max_eq_right hh]
      exact ⟨hB.1,hh,hB.2.2⟩
    · rw [min_eq_right hh,max_eq_left hh]
      exact ⟨hm,hh,hB.2.1⟩
  · cases f
    · simpa [p,q,pWeights,qWeights] using And.intro hk
        (And.intro (by linarith [hb.1.2] : k .low z≤1) (by linarith [hb.1.1] : 1≤2*k .low z))
    · have hc := high_rotation (r68_high_dom.1 hz)
      simpa [p,q,pWeights,qWeights,min_eq_right hc.2.2.le,max_eq_left hc.2.2.le] using
        And.intro (by linarith [hc.1] : 0<c .high z)
          (And.intro hc.2.2.le (by linarith [hc.1] : 1≤2*c .high z))

theorem low_q_upper (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) (i : Fin 4) : q .low atG z s i<5/4 := by
  have hb := low_ranges hz
  have hc := AB_cut_cosine (angle_domain atG hs).1
  have hcos : 0<Real.cos s := by linarith
  have hsec : secant (l .low z) s<5/4 := (div_lt_iff₀ hcos).2 (by nlinarith [hb.2.1.2])
  cases atG <;> fin_cases i <;> simp only [q,qWeights,lambdaG,lambdaB,
    NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,↓reduceIte,Bool.false_eq_true,
    Fin.reduceFinMk,Matrix.cons_val,max_lt_iff] <;>
    (try constructor) <;> first | exact hsec | linarith [hb.2.1.2,hb.2.2.2]

theorem low_G_ratio (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) : lambdaG atG (l .low z) s<(5/3)*k .low z := by
  have hb := low_ranges hz
  cases atG
  · simp only [lambdaG,NegativeAPositiveTD.lambdaG,↓reduceIte,Bool.false_eq_true]
    linarith [hb.1.1,hb.2.1.2]
  · have hs' : s∈Icc 0 (1/4:ℝ) := by
      simpa [angleCut,NegativeAPositiveTD.Explicit.angleCut] using hs
    have hc := GA_cut_cosine hs'
    have hcos : 0<Real.cos s := by linarith
    simp only [lambdaG,NegativeAPositiveTD.lambdaG,↓reduceIte]
    exact (div_lt_iff₀ hcos).2 (by nlinarith [hb.1.1,hb.2.1.2])

theorem low_HB_ratio (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) (i : Fin 4) (hi : i=0∨i=2) :
    q .low atG z s i≤(3/2)*p .low atG z s i := by
  have hb := low_ranges hz
  have hsec := (secant_bounds .low atG (r68_low_dom.2 hz) hs).1
  have hc := AB_cut_cosine (angle_domain atG hs).1
  have hcos : 0<Real.cos s := by linarith
  have hw : secant (l .low z) s<(3/2)*m .low z :=
    (div_lt_iff₀ hcos).2 (by nlinarith [hb.2.1.2,hb.2.2.1])
  rcases hi with rfl|rfl
  · simp [p,q,pWeights,qWeights]
    linarith [hb.1.1]
  · cases atG <;> simp only [p,q,pWeights,qWeights,lambdaB,NegativeAPositiveTD.lambdaB,
      ↓reduceIte,Bool.false_eq_true,Matrix.cons_val]
    · rcases le_total (secant (l .low z) s) (m .low z) with hh|hh
      · rw [min_eq_left hh,max_eq_right hh]
        linarith [hb.2.1.1,hb.2.2.2]
      · rw [min_eq_right hh,max_eq_left hh]
        exact hw.le
    · rcases le_total (l .low z) (m .low z) with hh|hh
      · rw [min_eq_left hh,max_eq_right hh]
        linarith [hb.2.1.1,hb.2.2.2]
      · rw [min_eq_right hh,max_eq_left hh]
        linarith [hb.2.1.2,hb.2.2.1]

theorem high_GA_pair_bounds {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) (i : Fin 4) :
    (51/80)*q .high true z s i<p .high true z s i ∧
    1≤q .high true z s i ∧ q .high true z s i<11/10 := by
  have hb := high_ranges hz
  have hr := high_ratios hz
  have hc := high_rotation hz
  have hcos := GA_cut_cosine hs
  have hcos0 : 0<Real.cos s := by linarith
  have hl : 0<l .high z := by linarith [hb.2.1.1]
  have hs' : s∈Icc 0 (angleCut true) := by
    simpa [angleCut,NegativeAPositiveTD.Explicit.angleCut] using hs
  have hw := (secant_bounds .high true (r68_high_dom.2 hz) hs').1
  have hwHi : secant (l .high z) s<11/10 :=
    (div_lt_iff₀ hcos0).2 (by nlinarith [hb.2.1.2])
  have hG : (51/80)*secant (l .high z) s<k .high z := by
    have h₁ := mul_lt_mul_of_pos_right hr.1 hcos0
    have h₂ := mul_lt_mul_of_pos_left hcos (show 0<(659/1000)*l .high z by linarith)
    show (51/80)*(l .high z/Real.cos s)<k .high z
    rw [←mul_div_assoc,div_lt_iff₀ hcos0]
    linarith
  fin_cases i
  · simp only [p,q,pWeights,qWeights,Fin.reduceFinMk,Matrix.cons_val]
    exact ⟨by linarith [hb.1.1],by norm_num,by norm_num⟩
  · simpa [p,q,pWeights,qWeights,lambdaG,NegativeAPositiveTD.lambdaG] using
      (⟨hG,(by linarith [hb.2.1.1] : (1:ℝ)≤ secant (l .high z) s),hwHi⟩ :
        (51/80)*secant (l .high z) s<k .high z ∧ 1≤ secant (l .high z) s ∧
          secant (l .high z) s<11/10)
  · simp only [p,q,pWeights,qWeights,lambdaB,NegativeAPositiveTD.lambdaB,↓reduceIte,
      Fin.reduceFinMk,Matrix.cons_val,min_eq_right hr.2.2.2.2.le,max_eq_left hr.2.2.2.2.le]
    exact ⟨by linarith [hr.2.2.1],by linarith [hb.2.1.1],by linarith [hb.2.1.2]⟩
  · simp only [p,q,pWeights,qWeights,Fin.reduceFinMk,Matrix.cons_val,reduceCtorEq,↓reduceIte,
      min_eq_right hc.2.2.le,max_eq_left hc.2.2.le]
    exact ⟨by linarith [hc.1],by norm_num,by norm_num⟩

theorem high_AB_pair_bounds {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (19/50:ℝ)) (i : Fin 4) :
    (13/20)*q .high false z s i<p .high false z s i ∧
    1≤q .high false z s i ∧ q .high false z s i<23/20 := by
  have hb := high_ranges hz
  have hr := high_ratios hz
  have hc := high_rotation hz
  have hcos := AB_cut_cosine hs
  have hcos0 : 0<Real.cos s := by linarith
  have hl : 0<l .high z := by linarith [hb.2.1.1]
  have hs' : s∈Icc 0 (angleCut false) := by
    simpa [angleCut,NegativeAPositiveTD.Explicit.angleCut] using hs
  have hw := (secant_bounds .high false (r68_high_dom.2 hz) hs').1
  have hwHi : secant (l .high z) s<23/20 :=
    (div_lt_iff₀ hcos0).2 (by nlinarith [hb.2.1.2])
  have hB : (13/20)*secant (l .high z) s< m .high z := by
    have h₁ := mul_lt_mul_of_pos_right hr.2.2.1 hcos0
    have h₂ := mul_lt_mul_of_pos_left hcos (show 0<(4/5)*l .high z by linarith)
    show (13/20)*(l .high z/Real.cos s)< m .high z
    rw [←mul_div_assoc,div_lt_iff₀ hcos0]
    linarith
  have hmw : m .high z≤ secant (l .high z) s := hr.2.2.2.2.le.trans hw
  fin_cases i
  · simp only [p,q,pWeights,qWeights,Fin.reduceFinMk,Matrix.cons_val]
    exact ⟨by linarith [hb.1.1],by norm_num,by norm_num⟩
  · simp only [p,q,pWeights,qWeights,lambdaG,NegativeAPositiveTD.lambdaG,↓reduceIte,
      Bool.false_eq_true,Fin.reduceFinMk,Matrix.cons_val]
    exact ⟨by linarith [hr.1],by linarith [hb.2.1.1],by linarith [hb.2.1.2]⟩
  · simp only [p,q,pWeights,qWeights,lambdaB,NegativeAPositiveTD.lambdaB,↓reduceIte,
      Bool.false_eq_true,Fin.reduceFinMk,Matrix.cons_val]
    rw [min_eq_right hmw,max_eq_left hmw]
    exact ⟨hB,(by linarith [hb.2.1.1] : (1:ℝ)≤ secant (l .high z) s),hwHi⟩
  · simp only [p,q,pWeights,qWeights,Fin.reduceFinMk,Matrix.cons_val,reduceCtorEq,↓reduceIte,
      min_eq_right hc.2.2.le,max_eq_left hc.2.2.le]
    exact ⟨by linarith [hc.1],by norm_num,by norm_num⟩

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.Explicit
end
end
end

section
/-!
## The small-A D support with a negative DE3 secant

The secant coefficient ranges over the complete interval [1,1.308].
Negative angles are diagonal. On positive angles the diagonal branch
increases and the full-circle branch is concave. The transition is an
actual equality of the force components, obtained by the intermediate
value theorem. Thus the only angle endpoint comparisons are zero and
the original variation cap. A rational affine upper bound for the cap
norm is proved on the entire coefficient interval by a single quadratic
comparison; it retains a 19/100 endpoint reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDESecant
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity Secondary

abbrev c : ℝ := 9/5
abbrev L : ℝ := 103/100

def forceF (u z : ℝ) : ℝ := u+c*Real.sin z
def forceG (z : ℝ) : ℝ := c*Real.cos z
def baseline (u : ℝ) : ℝ := (u+c)*(1-GlobalGA.Secondary.diagonal)

def stress (u z : ℝ) : ℝ :=
  c*edgeWidth z+u-clippedSupport (forceF u z) (forceG z)+L*z

def diagonalPositive (u z : ℝ) : ℝ :=
  c*(1+Real.cos z+Real.sin z)/2+u-
    GlobalGA.Secondary.diagonal*(u+c*Real.sin z+c*Real.cos z)+L*z

def fullPositive (u z : ℝ) : ℝ :=
  c*(1+Real.cos z+Real.sin z)/2+u-R*pairNorm u c z+
    (u+c*Real.sin z+c*Real.cos z)/2+L*z

def fullPositiveD (u z : ℝ) : ℝ :=
  c*(Real.cos z-Real.sin z)-R*normD1 u c z+L

def diagonalNegative (u w : ℝ) : ℝ :=
  c*(1+Real.cos w+Real.sin w)/2+u-
    GlobalGA.Secondary.diagonal*(u-c*Real.sin w+c*Real.cos w)-L*w

theorem coefficient_range {u : ℝ} (hu : u∈Icc 1 (327/250:ℝ)) :
    0<u ∧ u≤c ∧ c≤2*u := by
  dsimp [c]
  exact ⟨by linarith [hu.1],by linarith [hu.2],by linarith [hu.1]⟩

theorem phi_lower {z : ℝ} (hz : z∈Icc 0 frameCap) : 1≤PositiveAngularEnvelope.phi z := by
  have ht := transport_trig hz
  have hp := mul_nonneg (by linarith [ht.1] : 0≤Real.cos z) ht.2.2.1
  dsimp [PositiveAngularEnvelope.phi]
  nlinarith [Real.sin_sq_add_cos_sq z]

theorem force_positive {u z : ℝ} (hu : u∈Icc 1 (327/250:ℝ))
    (hz : |z|≤frameCap) : 0<forceF u z+forceG z ∧ 0<forceG z := by
  have ht := small_angle hz
  have hsin := (abs_le.mp ht.2).1
  dsimp [forceF,forceG,c,frameCap] at *
  constructor <;> linarith [hu.1,ht.1]

theorem force_norm (u z : ℝ) :
    Real.sqrt ((forceF u z)^2+(forceG z)^2)=pairNorm u c z := by
  have he : (forceF u z)^2+(forceG z)^2=u^2+c^2+2*u*c*Real.sin z := by
    dsimp [forceF,forceG]
    nlinarith only [congrArg (fun x : ℝ => c^2*x) (Real.sin_sq_add_cos_sq z)]
  rw [he]
  rfl

theorem diagonalPositive_eq {u z : ℝ} (hz : z∈Icc 0 frameCap) :
    diagonalPositive u z=c*edgeWidth z+u-
      diagonalSupport (forceF u z) (forceG z)+L*z := by
  rw [edgeWidth_positive_formula hz]
  dsimp [diagonalPositive,diagonalSupport,forceF,forceG]
  ring

theorem fullPositive_eq {u z : ℝ} (hz : z∈Icc 0 frameCap) :
    fullPositive u z=c*edgeWidth z+u-
      fullSupport (forceF u z) (forceG z)+L*z := by
  rw [edgeWidth_positive_formula hz]
  unfold fullSupport
  rw [force_norm]
  dsimp [fullPositive,forceF,forceG]
  ring

theorem positive_match {u z : ℝ} (hu : u∈Icc 1 (327/250:ℝ))
    (hz : z∈Icc 0 frameCap) (he : forceF u z-forceG z=0) :
    diagonalPositive u z=fullPositive u z := by
  have hforce := force_positive hu (by rw [abs_of_nonneg hz.1]; exact hz.2)
  rw [diagonalPositive_eq hz,fullPositive_eq hz,
    full_at_diagonal (by linarith) hforce.1.le]

theorem diagonalPositive_hasDerivAt (u z : ℝ) :
    HasDerivAt (diagonalPositive u)
      (c*(1/2-GlobalGA.Secondary.diagonal)*(Real.cos z-Real.sin z)+L) z := by
  have h := ((((((((Real.hasDerivAt_cos z).const_add 1).fun_add
    (Real.hasDerivAt_sin z)).const_mul c).div_const 2).add_const u).fun_sub
      (((((Real.hasDerivAt_sin z).const_mul c).const_add u).fun_add
        ((Real.hasDerivAt_cos z).const_mul c)).const_mul GlobalGA.Secondary.diagonal)).fun_add
          ((hasDerivAt_id' z).const_mul L))
  exact h.congr_deriv (by ring)

theorem diagonalPositive_monotone (u : ℝ) :
    MonotoneOn (diagonalPositive u) (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun z _ => (diagonalPositive_hasDerivAt u z).continuousAt.continuousWithinAt)
    (fun z _ => diagonalPositive_hasDerivAt u z)
  intro z hz
  have ht := transport_trig (Ioo_subset_Icc_self hz)
  have hm := mul_le_mul_of_nonneg_left
    (show Real.cos z-Real.sin z≤1 by linarith [ht.2.1,ht.2.2.1])
    (show 0≤c*(GlobalGA.Secondary.diagonal-1/2) by dsimp [c]; linarith [diagonal_bounds.1])
  dsimp [c,L] at *
  nlinarith [diagonal_bounds.2]

theorem diagonalPositive_lower {u z : ℝ} (hz : z∈Icc 0 frameCap) :
    baseline u≤diagonalPositive u z := by
  have hm := diagonalPositive_monotone u
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) hz hz.1
  have h0 : diagonalPositive u 0=baseline u := by
    simp [diagonalPositive,baseline]
    ring
  rwa [h0] at hm

theorem fullPositive_hasDerivAt {u z : ℝ} (hu : u∈Icc 1 (327/250:ℝ))
    (hz : z∈Icc 0 frameCap) :
    HasDerivAt (fullPositive u) (fullPositiveD u z) z := by
  have hr := coefficient_range hu
  have hn := pairNorm_hasDerivAt hr.1 (by norm_num [c] : 0<c)
    (by rw [abs_of_nonneg hz.1]; exact hz.2)
  have h := ((((((((Real.hasDerivAt_cos z).const_add 1).fun_add
    (Real.hasDerivAt_sin z)).const_mul c).div_const 2).add_const u).fun_sub
      (hn.const_mul R)).fun_add
    (((((Real.hasDerivAt_sin z).const_mul c).const_add u).fun_add
      ((Real.hasDerivAt_cos z).const_mul c)).div_const 2)).fun_add
        ((hasDerivAt_id' z).const_mul L)
  exact h.congr_deriv (by dsimp [fullPositiveD]; ring)

theorem fullPositiveD_hasDerivAt {u z : ℝ} (hu : u∈Icc 1 (327/250:ℝ))
    (hz : z∈Icc 0 frameCap) :
    HasDerivAt (fullPositiveD u) (curvature R u c z-c*PositiveAngularEnvelope.phi z) z := by
  have hr := coefficient_range hu
  have hn := normD1_hasDerivAt hr.1 (by norm_num [c] : 0<c)
    (by rw [abs_of_nonneg hz.1]; exact hz.2)
  have h := ((((Real.hasDerivAt_cos z).fun_sub (Real.hasDerivAt_sin z)).const_mul c).fun_sub
    (hn.const_mul R)).add_const L
  exact h.congr_deriv (by dsimp [curvature,PositiveAngularEnvelope.phi]; ring)

theorem fullPositive_concave {u : ℝ} (hu : u∈Icc 1 (327/250:ℝ)) :
    ConcaveOn ℝ (Icc 0 frameCap) (fullPositive u) := by
  have hr := coefficient_range hu
  apply concave_of_deriv2 (fun z hz => fullPositive_hasDerivAt hu hz)
    (fun z hz => fullPositiveD_hasDerivAt hu hz)
  intro z hz
  have hcurv := curvature_positive_upper (Real.sqrt_nonneg qCap) hr.1 hr.2.1 hr.2.2 hz
  have hslope := curvatureSlope_nonneg (Real.sqrt_nonneg qCap) hr.1
    (by norm_num [c] : 0<c)
  have hcap := mul_le_mul_of_nonneg_left hz.2 hslope
  have hconstants := curvature_constant_bounds (R := R) (Real.sqrt_nonneg qCap)
    (by rw [radius_sq]) hr.1 hr.2.1 hr.2.2
  have hphi := phi_lower hz
  dsimp [c] at *
  nlinarith [hconstants.2.2.2]

/-- The cap norm is enclosed on the whole secant-coefficient interval.
The squared majorant is concave after subtracting the force energy. -/
theorem cap_norm_upper {u : ℝ} (hu : u∈Icc 1 (327/250:ℝ)) :
    pairNorm u c frameCap<(171/100:ℝ)+(43/50)*u := by
  have hr := coefficient_range hu
  have hs := pairNorm_sq hr.1 (by norm_num [c] : 0<c)
    (t := frameCap) (by norm_num [frameCap])
  have ht := (transport_trig
    (by norm_num [frameCap] : frameCap∈Icc 0 frameCap)).2.2.2.1
  have hmul := mul_le_mul_of_nonneg_left ht.le hr.1.le
  have hinterval := mul_nonneg (sub_nonneg.mpr hu.1) (sub_nonneg.mpr hu.2)
  have hmajorant : u^2+c^2+2*u*c*Real.sin frameCap<
      ((171/100:ℝ)+(43/50)*u)^2 := by
    dsimp [c]
    nlinarith only [hmul,hinterval,hu.1,hu.2]
  dsimp [pairEnergy,pairProduct] at hs
  have hq : (pairNorm u c frameCap)^2<((171/100:ℝ)+(43/50)*u)^2 := by
    rw [hs]; linarith [hmajorant]
  exact lt_of_pow_lt_pow_left₀ 2 (by linarith [hu.1]) hq

theorem fullPositive_cap {u : ℝ} (hu : u∈Icc 1 (327/250:ℝ)) :
    baseline u+19/100<fullPositive u frameCap := by
  have hn := cap_norm_upper hu
  have hnp : 0<(171/100:ℝ)+(43/50)*u := by linarith [hu.1]
  have hnorm := radius_norm_upper hnp hn
  have hphi := phi_cap_lower
  have hdiag := mul_le_mul_of_nonneg_left diagonal_bounds.1.le
    (show 0≤u+c by dsimp [c]; linarith [hu.1])
  dsimp [fullPositive,baseline,PositiveAngularEnvelope.phi,c,L,frameCap] at *
  nlinarith [hu.2]

theorem positive_lower {u z : ℝ} (hu : u∈Icc 1 (327/250:ℝ))
    (hz : z∈Icc 0 frameCap) : baseline u≤ stress u z := by
  by_cases hdiag : forceF u z≤forceG z
  · have he : stress u z=diagonalPositive u z := by
      rw [diagonalPositive_eq hz]
      simp [stress,clippedSupport,hdiag]
    rw [he]
    exact diagonalPositive_lower hz
  · let e : ℝ→ℝ := fun t => forceF u t-forceG t
    have hec : Continuous e := by dsimp [e,forceF,forceG]; fun_prop
    have he0 : e 0≤0 := by
      dsimp [e,forceF,forceG,c]
      norm_num
      linarith [hu.2]
    have hez : 0≤e z := by dsimp [e]; linarith
    obtain ⟨t,ht,hte⟩ := intermediate_value_Icc hz.1 hec.continuousOn
      (show (0:ℝ)∈Icc (e 0) (e z) from ⟨he0,hez⟩)
    have hti : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hz.2⟩
    have hleft : baseline u≤fullPositive u t := by
      rw [← positive_match hu hti hte]
      exact diagonalPositive_lower hti
    have hright : baseline u≤fullPositive u frameCap := by
      linarith [fullPositive_cap hu]
    have hmin := (fullPositive_concave hu).min_le_of_mem_Icc hti
      (by norm_num [frameCap] : frameCap∈Icc 0 frameCap) ⟨ht.2,hz.2⟩
    have he : stress u z=fullPositive u z := by
      rw [fullPositive_eq hz]
      simp [stress,clippedSupport,hdiag]
    rw [he]
    exact (le_min hleft hright).trans hmin

theorem diagonalNegative_hasDerivAt (u w : ℝ) :
    HasDerivAt (diagonalNegative u)
      (c*((GlobalGA.Secondary.diagonal+1/2)*Real.cos w+(GlobalGA.Secondary.diagonal-1/2)*Real.sin w)-L) w := by
  have h := ((((((((Real.hasDerivAt_cos w).const_add 1).fun_add
    (Real.hasDerivAt_sin w)).const_mul c).div_const 2).add_const u).fun_sub
      (((((Real.hasDerivAt_sin w).const_mul c).const_sub u).fun_add
        ((Real.hasDerivAt_cos w).const_mul c)).const_mul GlobalGA.Secondary.diagonal)).fun_sub
          ((hasDerivAt_id' w).const_mul L))
  exact h.congr_deriv (by ring)

theorem diagonalNegative_monotone (u : ℝ) :
    MonotoneOn (diagonalNegative u) (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun w _ => (diagonalNegative_hasDerivAt u w).continuousAt.continuousWithinAt)
    (fun w _ => diagonalNegative_hasDerivAt u w)
  intro w hw
  have ht := transport_trig (Ioo_subset_Icc_self hw)
  have hm := mul_le_mul (show (1399/1000:ℝ)≤GlobalGA.Secondary.diagonal+1/2 by linarith [diagonal_bounds.1])
    ht.1.le (by norm_num : (0:ℝ)≤7648/10000) (by linarith [diagonal_bounds.1])
  have hp := mul_nonneg (show 0≤GlobalGA.Secondary.diagonal-1/2 by linarith [diagonal_bounds.1]) ht.2.2.1
  dsimp [c,L]
  nlinarith

theorem negative_lower {u w : ℝ} (hu : u∈Icc 1 (327/250:ℝ))
    (hw : w∈Icc 0 frameCap) : baseline u≤ stress u (-w) := by
  have hphi := phi_lower hw
  have hdiag : forceF u (-w)≤forceG (-w) := by
    dsimp [forceF,forceG,PositiveAngularEnvelope.phi,c] at *
    simp only [Real.cos_neg,Real.sin_neg]
    linarith [hu.2]
  have he : stress u (-w)=diagonalNegative u w := by
    simp only [stress,clippedSupport,ite_eq_left hdiag]
    rw [edgeWidth_negative_formula hw]
    dsimp [diagonalNegative,diagonalSupport,forceF,forceG]
    simp only [Real.cos_neg,Real.sin_neg]
    ring
  have hm := diagonalNegative_monotone u
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) hw hw.1
  have h0 : diagonalNegative u 0=baseline u := by
    simp [diagonalNegative,baseline]
    ring
  rw [he]
  rwa [h0] at hm

theorem stress_lower {u z : ℝ} (hu : u∈Icc 1 (327/250:ℝ))
    (hz : |z|≤frameCap) : baseline u≤ stress u z := by
  by_cases hpos : 0≤z
  · exact positive_lower hu ⟨hpos,by simpa [abs_of_nonneg hpos] using hz⟩
  · have hneg : -z∈Icc 0 frameCap :=
      ⟨by linarith,by simpa [abs_of_neg (lt_of_not_ge hpos)] using hz⟩
    simpa only [neg_neg] using negative_lower hu hneg

/-- This is the D inequality used by the actual source stress. -/
theorem actual_lower {q u z : ℝ} {D : SignedPoint}
    (hs : D.Sorted) (hy : 0≤D.y) (hc : D.Contained q) (hq : q≤qCap)
    (hu : u∈Icc 1 (327/250:ℝ)) (hz : |z|≤frameCap) :
    baseline u≤c*edgeWidth z+u-
      ((u+c*Real.sin z)*D.a+c*Real.cos z*D.y)+L*z := by
  have hsup := actual_clipped_support hs hy hc hq (force_positive hu hz).1.le
  have hlow := stress_lower hu hz
  dsimp [stress,forceF,forceG] at *
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDESecant
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeELowA
open Candidate Secondary NegativePrimary PairedE

abbrev k : ℝ := PositiveATD0.lowK
abbrev l : ℝ := PositiveATD0.lowL
abbrev c : ℝ := PositiveATD0.lowC
abbrev L : ℝ := PositiveATD0.charge

def owners (hg ga ab td de eh : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,
    2,if td then 2 else 0,if de then 3 else 2,if eh then 1 else 0]

def weights (C : SignedCycle) (td de eh : Bool) : Vertex→ℝ :=
  ![k,l,l,c,if td then c/Real.cos (delta C.theta T) else c,
    if de then 1/Real.cos (delta C.theta D) else 1,
    if eh then 1/Real.cos (delta C.theta E) else 1]

def stress (C : SignedCycle) (hg ga ab td de eh : Bool) : ℝ :=
  ∑i,weights C td de eh i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab td de eh i))

def hSecantIncrement (u v : ℝ) (H : SignedPoint) : ℝ :=
  k*(edgeWidth v-1)-((u+k*Real.sin v)*H.a+k*Real.cos v*H.y)+fullSupport u k+L*v

def dSecantIncrement (u z : ℝ) (D : SignedPoint) : ℝ :=
  c*edgeWidth z+u-((u+c*Real.sin z)*D.a+c*Real.cos z*D.y)+L*z-
    (u+c)*(1-GlobalGA.Secondary.diagonal)

def hIncrement (C : SignedCycle) (hg eh : Bool) : ℝ :=
  if eh then hSecantIncrement (1/Real.cos (delta C.theta E))
    (erase (!hg) (delta C.theta H)) (C.point H)
  else PositiveATD0.pairIncrement k 1 (erase (!hg) (delta C.theta H))
    (delta C.theta E) (C.point H)

def dIncrement (C : SignedCycle) (td de : Bool) : ℝ :=
  if de then dSecantIncrement (1/Real.cos (delta C.theta D))
    (erase td (delta C.theta T)) (C.point D).reflect
  else PositiveATD0.Source.dIncrement (erase td (delta C.theta T))
    (delta C.theta D) (C.point D).reflect

def reference (C : SignedCycle) (hg ga ab td de eh : Bool) : ℝ :=
  PositiveATD0.lowBaseline+hIncrement C hg eh+
    PositiveATD0.pairIncrement k l (erase hg (delta C.theta H))
      (erase ga (delta C.theta G)) (C.point G).reflect+
    PositiveATD0.pairIncrement l c (erase ab (delta C.theta A))
      (delta C.theta B) (C.point B).reflect+dIncrement C td de

/-- The width form makes the collection independent of a sign rewrite. Signs enter only in the
scalar lower bounds. -/
def rawE (d : ℝ) : ℝ :=
  (edgeWidth d-1-(7/12)*Real.sin d)/Real.cos d

def deGain (C : SignedCycle) (de : Bool) : ℝ :=
  if de then rawE (delta C.theta D)+(1/Real.cos (delta C.theta D)-1)*(1-GlobalGA.Secondary.diagonal) else 0

def ehGain (C : SignedCycle) (eh : Bool) : ℝ :=
  if eh then rawE (delta C.theta E)+(1/Real.cos (delta C.theta E)-1)-
    (fullSupport (1/Real.cos (delta C.theta E)) k-fullSupport 1 k) else 0

def tGain (C : SignedCycle) (td : Bool) : ℝ :=
  if td then c*(edgeWidth (delta C.theta T)-Real.cos (delta C.theta T)-
    (C.point T).a*Real.sin (delta C.theta T)-
    (1-Real.cos (delta C.theta T))*(-(C.point D).y))/Real.cos (delta C.theta T) else 0

def magnitude (C : SignedCycle) (i : Vertex) (b : Bool) : ℝ :=
  -selected b (delta C.theta i)

private theorem r79_eH (C : SignedCycle) (j : Fin 4) :
    C.edge H j=zeroProjection (C.point H) (C.point G) (delta C.theta H) j := by
  simp only [SignedCycle.edge,word,H,G,next]; rfl
private theorem r79_eG (C : SignedCycle) (j : Fin 4) :
    C.edge G j=quarterProjection (C.point G) (C.point A) (delta C.theta G) j := by
  simp only [SignedCycle.edge,word,G,A,next]; rfl
private theorem r79_eA (C : SignedCycle) (j : Fin 4) :
    C.edge A j=zeroProjection (C.point A) (C.point B) (delta C.theta A) j := by
  simp only [SignedCycle.edge,word,A,B,next]; rfl
private theorem r79_eB (C : SignedCycle) (j : Fin 4) :
    C.edge B j=quarterProjection (C.point B) (C.point T) (delta C.theta B) j := by
  simp only [SignedCycle.edge,word,B,T,next]; rfl
private theorem r79_eT (C : SignedCycle) (j : Fin 4) :
    C.edge T j=zeroProjection (C.point T) (C.point D) (delta C.theta T) j := by
  simp only [SignedCycle.edge,word,T,D,next]; rfl
private theorem r79_eD (C : SignedCycle) (j : Fin 4) :
    C.edge D j=quarterProjection (C.point D) (C.point E) (delta C.theta D) j := by
  simp only [SignedCycle.edge,word,D,E,next]; rfl
private theorem r79_eE (C : SignedCycle) (j : Fin 4) :
    C.edge E j=quarterProjection (C.point E) (C.point H) (delta C.theta E) j := by
  simp only [SignedCycle.edge,word,E,H,next]; rfl

private theorem r79_delta_sum (C : SignedCycle) :
    delta C.theta H+delta C.theta G+delta C.theta A+delta C.theta B+
      delta C.theta T+delta C.theta D+delta C.theta E=0 := by
  simp only [delta,next,H,G,A,B,T,D,E]
  norm_num

theorem decomposition (C : SignedCycle) (hg ga ab td de eh : Bool)
    (hflat : (C.point E).a=7/12)
    (hT : Real.cos (delta C.theta T)≠0)
    (hD : Real.cos (delta C.theta D)≠0)
    (hE : Real.cos (delta C.theta E)≠0) :
    stress C hg ga ab td de eh=reference C hg ga ab td de eh+
      L*(LowA.aTotal C ga ab-magnitude C D de-magnitude C E eh-magnitude C T td)+
      l*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
      deGain C de+ehGain C eh+tGain C td := by
  have hsum := r79_delta_sum C
  have h1 : stress C hg ga ab td de eh=
      k*(edgeWidth (delta C.theta H)-C.edge H (if hg then 2 else 0))+
      l*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))+
      l*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))+
      c*(edgeWidth (delta C.theta B)-C.edge B 2)+
      (if td then c/Real.cos (delta C.theta T) else c)*
        (edgeWidth (delta C.theta T)-C.edge T (if td then 2 else 0))+
      (if de then 1/Real.cos (delta C.theta D) else 1)*
        (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))+
      (if eh then 1/Real.cos (delta C.theta E) else 1)*
        (edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0)) := by
    simp only [stress,Fin.sum_univ_seven,weights,owners,Matrix.cons_val,H,G,A,B,T,D,E]
  -- separability of the coupled reference blocks
  have hHsep : hIncrement C hg eh=hIncrement C hg false+hIncrement C false eh-
      hIncrement C false false := by
    cases eh
    · simp only [hIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.pairIncrement,
        pairF,pairG,erase,Bool.not_false]
      ring
    · simp only [hIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.pairIncrement,
        hSecantIncrement,pairF,pairG,erase,Bool.not_false]
      ring
  have hGsep : PositiveATD0.pairIncrement k l (erase hg (delta C.theta H))
        (erase ga (delta C.theta G)) (C.point G).reflect=
      PositiveATD0.pairIncrement k l (erase hg (delta C.theta H))
        (erase false (delta C.theta G)) (C.point G).reflect+
      PositiveATD0.pairIncrement k l (erase false (delta C.theta H))
        (erase ga (delta C.theta G)) (C.point G).reflect-
      PositiveATD0.pairIncrement k l (erase false (delta C.theta H))
        (erase false (delta C.theta G)) (C.point G).reflect := by
    simp only [PositiveATD0.pairIncrement,pairF,pairG]
    ring
  have hDsep : dIncrement C td de=dIncrement C td false+dIncrement C false de-
      dIncrement C false false := by
    cases de
    · simp only [dIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.Source.dIncrement,
        PositiveATD0.dF,PositiveATD0.dG,erase]
      ring
    · simp only [dIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.Source.dIncrement,
        dSecantIncrement,PositiveATD0.dF,PositiveATD0.dG,erase]
      ring
  -- one flag at a time
  have hH : k*(edgeWidth (delta C.theta H)-C.edge H (if hg then 2 else 0))=
      k*(edgeWidth (delta C.theta H)-C.edge H 0)+
      (hIncrement C hg false-hIncrement C false false)+
      (PositiveATD0.pairIncrement k l (erase hg (delta C.theta H))
        (erase false (delta C.theta G)) (C.point G).reflect-
       PositiveATD0.pairIncrement k l (erase false (delta C.theta H))
        (erase false (delta C.theta G)) (C.point G).reflect) := by
    cases hg
    · simp
    · simp only [hIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.pairIncrement,pairF,pairG,
        erase,Bool.not_false,Bool.not_true,r79_eH,zeroProjection,Matrix.cons_val,
        SignedPoint.reflect,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  have hG : l*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))=
      l*(edgeWidth (delta C.theta G)-C.edge G 2)+
      (PositiveATD0.pairIncrement k l (erase false (delta C.theta H))
        (erase ga (delta C.theta G)) (C.point G).reflect-
       PositiveATD0.pairIncrement k l (erase false (delta C.theta H))
        (erase false (delta C.theta G)) (C.point G).reflect)+
      L*selected ga (delta C.theta G)+
      l*(if ga then edgeWidth (delta C.theta G)-1-((C.point A).a*Real.sin (delta C.theta G)+
        (C.point A).y*(1-Real.cos (delta C.theta G))) else 0) := by
    cases ga
    · simp [selected]
    · simp only [PositiveATD0.pairIncrement,pairF,pairG,erase,selected,↓reduceIte,
        Bool.false_eq_true,r79_eG,quarterProjection,Matrix.cons_val,
        SignedPoint.reflect,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  have hA : l*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))=
      l*(edgeWidth (delta C.theta A)-C.edge A 0)+
      (PositiveATD0.pairIncrement l c (erase ab (delta C.theta A))
        (delta C.theta B) (C.point B).reflect-
       PositiveATD0.pairIncrement l c (erase false (delta C.theta A))
        (delta C.theta B) (C.point B).reflect)+
      L*selected ab (delta C.theta A)+
      l*(if ab then edgeWidth (delta C.theta A)-1-((C.point A).a*Real.sin (delta C.theta A)+
        (C.point A).y*(Real.cos (delta C.theta A)-1)) else 0) := by
    cases ab
    · simp [selected]
    · simp only [PositiveATD0.pairIncrement,pairF,pairG,erase,selected,↓reduceIte,
        Bool.false_eq_true,r79_eA,zeroProjection,Matrix.cons_val,
        SignedPoint.reflect,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  have hT' : (if td then c/Real.cos (delta C.theta T) else c)*
        (edgeWidth (delta C.theta T)-C.edge T (if td then 2 else 0))=
      c*(edgeWidth (delta C.theta T)-C.edge T 0)+
      (dIncrement C td false-dIncrement C false false)-
      L*magnitude C T td+tGain C td := by
    cases td
    · simp [magnitude,selected,tGain]
    · simp only [dIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.Source.dIncrement,
        PositiveATD0.dF,PositiveATD0.dG,erase,magnitude,selected,tGain,r79_eT,
        zeroProjection,Matrix.cons_val,SignedPoint.reflect,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero]
      field_simp
      ring
  have hD : (if de then 1/Real.cos (delta C.theta D) else 1)*
        (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))=
      (edgeWidth (delta C.theta D)-C.edge D 2)+
      (dIncrement C false de-dIncrement C false false)-
      L*magnitude C D de+deGain C de := by
    cases de
    · simp [magnitude,selected,deGain]
    · simp only [dIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.Source.dIncrement,
        dSecantIncrement,PositiveATD0.dF,PositiveATD0.dG,erase,magnitude,selected,deGain,rawE,
        r79_eD,quarterProjection,Matrix.cons_val,SignedPoint.reflect,hflat]
      field_simp
      ring
  have hE' : (if eh then 1/Real.cos (delta C.theta E) else 1)*
        (edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0))=
      (edgeWidth (delta C.theta E)-C.edge E 0)+
      (hIncrement C false eh-hIncrement C false false)-
      L*magnitude C E eh+ehGain C eh := by
    cases eh
    · simp [magnitude,selected,ehGain]
    · simp only [hIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.pairIncrement,
        hSecantIncrement,pairF,pairG,erase,Bool.not_false,magnitude,selected,ehGain,rawE,
        r79_eE,quarterProjection,Matrix.cons_val,hflat,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero]
      field_simp
      ring
  have hbase : k*(edgeWidth (delta C.theta H)-C.edge H 0)+
      l*(edgeWidth (delta C.theta G)-C.edge G 2)+
      l*(edgeWidth (delta C.theta A)-C.edge A 0)+
      c*(edgeWidth (delta C.theta B)-C.edge B 2)+
      c*(edgeWidth (delta C.theta T)-C.edge T 0)+
      (edgeWidth (delta C.theta D)-C.edge D 2)+
      (edgeWidth (delta C.theta E)-C.edge E 0)=
      PositiveATD0.lowBaseline+hIncrement C false false+
      PositiveATD0.pairIncrement k l (erase false (delta C.theta H))
        (erase false (delta C.theta G)) (C.point G).reflect+
      PositiveATD0.pairIncrement l c (erase false (delta C.theta A))
        (delta C.theta B) (C.point B).reflect+
      dIncrement C false false := by
    simp only [hIncrement,dIncrement,Bool.false_eq_true,↓reduceIte,Bool.not_false,
      PositiveATD0.pairIncrement,PositiveATD0.Source.dIncrement,PositiveATD0.dF,PositiveATD0.dG,
      pairF,pairG,erase,PositiveATD0.lowBaseline,r79_eH,r79_eG,r79_eA,r79_eB,r79_eT,r79_eD,
      r79_eE,zeroProjection,quarterProjection,Matrix.cons_val,SignedPoint.reflect,
      Real.sin_zero,Real.cos_zero,edgeWidth_zero]
    linear_combination (-PositiveATD0.charge)*hsum
  rw [h1]
  simp only [reference,LowA.aTotal,total,primaryGain]
  linear_combination hH+hG+hA+hT'+hD+hE'+hbase-hHsep-hGsep-hDsep

theorem hIncrement_nonneg {q : ℝ} {C : SignedCycle} (hg eh : Bool)
    (hc : (C.point H).Contained q) (hq : q≤qCap) (hHy : 0≤(C.point H).y)
    (hvar : positiveVariation C.theta≤frameCap)
    (heh : eh=true→-delta C.theta E∈Icc 0 (1/4:ℝ)) :
    0≤hIncrement C hg eh := by
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  cases he : eh
  · have hb := erased_pair_budgets (i := H) (j := E) hvar hn (by norm_num [H,E]) (!hg) false
    simp only [erase_false] at hb
    have hh := PositiveATD0.actual_fixed_pair_nonneg 1 hHy hc hq hb.1 hb.2
    simpa [hIncrement,PositiveATD0.coefficientP,PositiveATD0.coefficientQ,k] using hh
  · have hsec := NegativeESecant.eh_secant_range (heh he)
    simp only [Real.cos_neg] at hsec
    have hh := NegativeEHSecant.actual_lower hHy hc hq hsec
      (erase_abs_bound (!hg) (original_error_bound hvar hn H))
    dsimp [NegativeEHSecant.k,NegativeEHSecant.L] at hh
    dsimp [hIncrement,hSecantIncrement,k,L,PositiveATD0.lowK,PositiveATD0.charge]
    linarith

theorem dIncrement_nonneg {q : ℝ} {C : SignedCycle} (td de : Bool)
    (hs : (C.point D).Sorted) (hc : (C.point D).Contained q)
    (hq : q≤qCap) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hde : de=true→delta C.theta D≤0) : 0≤dIncrement C td de := by
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  cases hd : de
  · have hb := erased_pair_budgets (i := T) (j := D) hvar hn (by norm_num [T,D]) td false
    simp only [erase_false] at hb
    have he := pair_error_bounds hb.1 hb.2
    have hh := PositiveATD0.actual_D_lower (P := (C.point D).reflect)
      (by simpa using hs) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc) hq he.1 he.2.1 he.2.2
    simpa [dIncrement,PositiveATD0.Source.dIncrement,sub_nonneg] using hh
  · have hsD : -delta C.theta D∈Icc 0 frameCap :=
      ⟨neg_nonneg.mpr (hde hd),(neg_le_abs _).trans (original_error_bound hvar hn D)⟩
    have hsec := NegativeESecant.de_secant_range hsD
    simp only [Real.cos_neg] at hsec
    have hh := NegativeDESecant.actual_lower (D := (C.point D).reflect)
      (by simpa using hs) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc) hq hsec (erase_abs_bound td (original_error_bound hvar hn T))
    dsimp [NegativeDESecant.baseline,NegativeDESecant.c,NegativeDESecant.L] at hh
    dsimp [dIncrement,dSecantIncrement,c,L,PositiveATD0.lowC,PositiveATD0.charge]
    linarith

theorem reference_lower {q : ℝ} {C : SignedCycle} (hg ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 (1/4:ℝ)) :
    PositiveATD0.lowBaseline≤reference C hg ga ab td de eh := by
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hgb := erased_pair_budgets (i := H) (j := G) hvar hn (by norm_num [H,G]) hg ga
  have hbb := erased_pair_budgets (i := A) (j := B) hvar hn (by norm_num [A,B]) ab false
  simp only [erase_false] at hbb
  have hG := PositiveATD0.actual_fixed_pair_nonneg 0 (P := (C.point G).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
    (by simpa using hc G) hq hgb.1 hgb.2
  have hB := PositiveATD0.actual_fixed_pair_nonneg 2 (P := (C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  have hH := hIncrement_nonneg hg eh (hc H) hq hHy hvar heh
  have hD := dIncrement_nonneg td de (hs D) (hc D) hq hDy hvar hde
  simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,Matrix.cons_val] at hG hB
  dsimp [reference,k,l,c]
  linarith

theorem raw_DE_identity {s : ℝ} (hs : s∈Icc 0 frameCap) :
    rawE (-s)+(1/Real.cos (-s)-1)*(1-GlobalGA.Secondary.diagonal)=
      NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2) s := by
  rw [rawE,edgeWidth_negative_formula hs]
  simp only [Real.cos_neg,Real.sin_neg]
  dsimp [NegativeESecant.gain,NegativeESecant.K]
  field_simp [(NegativeESecant.cos_pos hs).ne']
  ring

theorem raw_EH_identity {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    rawE (-s)+(1/Real.cos (-s)-1)-
      (fullSupport (1/Real.cos (-s)) k-fullSupport 1 k)=
      secantGain qCap k s := by
  have hsi := NegativeESecant.eh_short_subset hs
  have he := secantGain_eq_secant_expression qCap k (NegativeESecant.cos_pos hsi)
  rw [he,rawE,edgeWidth_negative_formula hsi]
  simp only [Real.cos_neg,Real.sin_neg,Real.tan_eq_sin_div_cos]
  dsimp [fullSupport]
  norm_num
  field_simp [(NegativeESecant.cos_pos hsi).ne']
  ring

theorem e_gain_lower {C : SignedCycle} (de eh : Bool)
    (hsmall : ∀i,|delta C.theta i|≤frameCap)
    (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 (1/4:ℝ)) :
    L*(magnitude C D de+magnitude C E eh)≤deGain C de+ehGain C eh := by
  have hD : L*magnitude C D de≤deGain C de := by
    cases hd : de
    · simp [magnitude,selected,deGain]
    · have hs : -delta C.theta D∈Icc 0 frameCap :=
        ⟨neg_nonneg.mpr (hde hd),(neg_le_abs _).trans (hsmall D)⟩
      have hgain := NegativeESecant.de_gain_lower
        (show GlobalGA.Secondary.diagonal-1/2≤2/5 by linarith [diagonal_bounds.2]) hs
      have hid := raw_DE_identity hs
      simp only [neg_neg] at hid
      dsimp [deGain,magnitude,selected,L,PositiveATD0.charge]
      rw [hid]
      nlinarith [hs.1]
  have hH : L*magnitude C E eh≤ehGain C eh := by
    cases he : eh
    · simp [magnitude,selected,ehGain]
    · have hs := heh he
      have hgain := NegativeESecant.eh_gain_lower hs
      have hid := raw_EH_identity hs
      simp only [neg_neg] at hid
      dsimp [ehGain,magnitude,selected,L,PositiveATD0.charge]
      rw [hid]
      change ((103/100:ℝ)+1/625)*(-delta C.theta E) ≤ secantGain qCap k (-delta C.theta E) at hgain
      nlinarith [hs.1]
  linarith

theorem t_gain_lower {q : ℝ} {C : SignedCycle} (td : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcore : (C.point T).AvoidsCore) (hq : q≤qCap) (hDy : (C.point D).y≤0)
    (hsmall : |delta C.theta T|≤frameCap) (htd : td=true→delta C.theta T≤0) :
    (9/10)*c*magnitude C T td≤tGain C td := by
  cases ht : td
  · simp [magnitude,selected,tGain]
  · have hz : -delta C.theta T∈Icc 0 frameCap :=
      ⟨neg_nonneg.mpr (htd ht),(neg_le_abs _).trans hsmall⟩
    have hgain := PositiveANegativeTD.actual_gain_lower (hs T) hcore (hc T)
      (hs D) hDy (hc D) hq (show 0≤c by norm_num [c,PositiveATD0.lowC]) hz
    have hwidth := edgeWidth_negative_formula hz
    simp only [neg_neg,Real.cos_neg,Real.sin_neg] at hwidth
    have hid : tGain C true=PositiveANegativeTD.gain c (-delta C.theta T)
        (C.point T).a (-(C.point D).y) := by
      dsimp [tGain,PositiveANegativeTD.gain]
      simp only [Real.cos_neg,Real.sin_neg]
      rw [hwidth]
      ring
    simpa [hid,magnitude,selected] using hgain

/-- Every weight is nonnegative and multiplies a weak separator of the cycle. The contradiction
uses the scalar reserves. -/
theorem actual_false {q : ℝ} {C : SignedCycle} (ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hflat : (C.point E).a=7/12) (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T (if td then 2 else 0))
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : LowA.aTotal C ga ab∈Icc 0 (1/6:ℝ))
    (htd : td=true→delta C.theta T≤0)
    (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 (1/4:ℝ)) : False := by
  obtain ⟨hg,hHG⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hcos (i : Vertex) := NegativePrimary.cos_pos (hsmall i)
  have hTpos := hcos T
  have hDpos := hcos D
  have hEpos := hcos E
  have hweights (i : Vertex) : 0≤weights C td de eh i := by
    cases td <;> cases de <;> cases eh <;> fin_cases i <;>
      simp [weights,k,l,c,PositiveATD0.lowK,PositiveATD0.lowL,PositiveATD0.lowC]
    all_goals positivity
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab td de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  have hu : stress C hg ga ab td de eh≤0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hh := hf i
    change 0≤C.edge i (owners hg ga ab td de eh i)-edgeWidth (delta C.theta i) at hh
    exact mul_nonpos_of_nonneg_of_nonpos (hweights i) (by linarith)
  have hreference := reference_lower hg ga ab td de eh hs hc hq hHy hGy hBy hDy hvar hde heh
  have hAmem : LowA.aTotal C ga ab∈Icc 0 frameCap :=
    ⟨ha.1,ha.2.trans (by norm_num [frameCap])⟩
  have hA := selected_charge ga ab (hs A) (hc A) hq (hsmall G) (hsmall A) hAmem
  have hAweighted := mul_le_mul_of_nonneg_left hA (show 0≤l by norm_num [l,PositiveATD0.lowL])
  have hscalar := PositiveATD0.low_scalar_positive ha
  have hE := e_gain_lower de eh hsmall hde heh
  have hT := t_gain_lower td hs hc hcoreT hq hDy (hsmall T) htd
  have ht0 : 0 ≤ magnitude C T td := by
    cases ht : td
    · simp [magnitude,selected]
    · simpa [magnitude,selected] using neg_nonneg.mpr (htd ht)
  rw [decomposition C hg ga ab td de eh hflat (hcos T).ne' (hcos D).ne' (hcos E).ne'] at hu
  change l*TwoPositive.ASupport.charge (LowA.aTotal C ga ab)≤_ at hAweighted
  dsimp only [L,c,l,PositiveATD0.charge,PositiveATD0.lowC,PositiveATD0.lowL] at hu hE hT hscalar hAweighted
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeELowA
end
end
end

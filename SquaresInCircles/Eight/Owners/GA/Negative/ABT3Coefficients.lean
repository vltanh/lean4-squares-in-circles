module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Data

/-!
# Eight squares: whole-interval domains for the reference BT3 weights

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

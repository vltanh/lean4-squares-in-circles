module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Stationary.CriticalHessian
public import SquaresInCircles.Eight.Owners.Critical.EPolynomials

/-!
# Eight squares: transfer of the sextic enclosures to the actual circle roots

Each step uses the same original q and u. Squaring
and monotonicity transfer the polynomial residuals successively through
r, U, V, Y, v and w. No independent root choices or altered radii enter
the chain, and no comparison-position premise is hidden in the result.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalERadicals
open Polynomial WholeIntervalPolynomial CriticalEPolynomials
open Stationary.FiveCornerGeometry

def ev (t : ℝ) (P : ℚ[X]) : ℝ := aeval (t-1/10) P

@[simp] theorem ev_add (t : ℝ) (P Q : ℚ[X]) : ev t (P+Q)=ev t P+ev t Q := by simp [ev]
@[simp] theorem ev_sub (t : ℝ) (P Q : ℚ[X]) : ev t (P-Q)=ev t P-ev t Q := by simp [ev]
@[simp] theorem ev_mul (t : ℝ) (P Q : ℚ[X]) : ev t (P*Q)=ev t P*ev t Q := by simp [ev]
@[simp] theorem ev_pow (t : ℝ) (P : ℚ[X]) (n : ℕ) : ev t (P^n)=ev t P^n := by simp [ev]
@[simp] theorem ev_C (t : ℝ) (r : ℚ) : ev t (C r)=(r:ℝ) := by simp [ev]
@[simp] theorem ev_nat (t : ℝ) (n : ℕ) : ev t (n:ℚ[X])=n := by simp [ev]
@[simp] theorem ev_parameter (t : ℝ) : ev t parameter=t := by simp [ev,parameter]
@[simp] theorem ev_minus (t : ℝ) : ev t uMinus=499/500-(127/200)*t := by simp [uMinus]
@[simp] theorem ev_plus (t : ℝ) : ev t uPlus=501/500-(16/25)*t := by simp [uPlus]

private theorem ev_two (t : ℝ) : ev t (2 : ℚ[X])=2 := by
  rw [ev]
  exact map_ofNat _ 2

private theorem ev_three (t : ℝ) : ev t (3 : ℚ[X])=3 := by
  rw [ev]
  exact map_ofNat _ 3

theorem local_parameter {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) :
    t-1/10∈Icc 0 (length:ℝ) := by
  norm_num [length]
  constructor <;> linarith [ht.1,ht.2]

theorem endpoints {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) (s : Chain) :
    (89/100:ℝ)<ev t (a s) ∧ ev t (a s)≤ev t (b s) ∧ ev t (b s)<19/20 := by
  cases s <;> simp only [a,b,ev_minus,ev_plus] <;>
    exact ⟨by linarith [ht.1,ht.2],by linarith [ht.1,ht.2],by linarith [ht.1,ht.2]⟩

theorem root_squares (s : Chain) (i : Fin 8) {t : ℝ}
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    0<ev t (rootLower (rootArgument s i)) ∧
    ev t (rootLower (rootArgument s i))^2<ev t (rootArgument s i) ∧
    ev t (rootArgument s i)<ev t (rootUpper (rootArgument s i))^2 ∧
    0<ev t (rootUpper (rootArgument s i)) := by
  have hz : t-1/10∈Icc ((0:ℚ):ℝ) (length:ℝ) := by
    rw [Rat.cast_zero]; exact local_parameter ht
  have h0 := positive_on_interval (by norm_num [length])
    (root_identities s i).1 (root_reserves s i).1 hz
  have h1 := positive_on_interval (by norm_num [length])
    (root_identities s i).2.1 (root_reserves s i).2.1 hz
  have h2 := positive_on_interval (by norm_num [length])
    (root_identities s i).2.2 (root_reserves s i).2.2 hz
  have h0' : (2879/2000:ℝ)<ev t (rootLower (rootArgument s i)) :=
    (by norm_num : (2879/2000:ℝ)=((2879/2000:ℚ):ℝ)).trans_lt h0
  have h1' : (23/80000000:ℝ)<ev t (rootArgument s i-rootLower (rootArgument s i)^2) :=
    (by norm_num : (23/80000000:ℝ)=((23/80000000:ℚ):ℝ)).trans_lt h1
  have h2' : (9/31250000:ℝ)<ev t (rootUpper (rootArgument s i)^2-rootArgument s i) :=
    (by norm_num : (9/31250000:ℝ)=((9/31250000:ℚ):ℝ)).trans_lt h2
  simp only [ev_sub,ev_pow] at h1' h2'
  have hdiff : ev t (rootUpper (rootArgument s i))-ev t (rootLower (rootArgument s i))=
      2/10000000 := by
    simp only [rootUpper,rootLower,ev_add,ev_sub,ev_C,epsilon]
    push_cast
    ring
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem root_between (s : Chain) (i j : Fin 8) {t z : ℝ}
    (ht : t∈Icc (1/10:ℝ) (4/25))
    (hz : z∈Icc (ev t (rootArgument s i)) (ev t (rootArgument s j))) :
    ev t (rootLower (rootArgument s i))<Real.sqrt z ∧
    Real.sqrt z<ev t (rootUpper (rootArgument s j)) := by
  have hi := root_squares s i ht
  have hj := root_squares s j ht
  have hz0 : 0≤z := by nlinarith [hi.2.1,hz.1,sq_nonneg (ev t (rootLower (rootArgument s i)))]
  have hs0 := Real.sqrt_nonneg z
  have hs2 := Real.sq_sqrt hz0
  constructor <;> nlinarith [hi.1,hi.2.1,hj.2.2.1,hj.2.2.2,hz.1,hz.2]

theorem polynomial_coordinates (s : Chain) (i : Fin 6) {t : ℝ}
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    1/2<ev t (coordinateLower s i) ∧ ev t (coordinateUpper s i)<2 := by
  have hz : t-1/10∈Icc ((0:ℚ):ℝ) (length:ℝ) := by
    rw [Rat.cast_zero]; exact local_parameter ht
  have hh := positive_on_interval (by norm_num [length])
    (coordinate_identities s i).1 (coordinate_reserves s i).1 hz
  have hu := (interval_bounds (by norm_num [length])
    (coordinate_identities s i).2 hz).2
  have hc : (upperOn 6 0 length (coordinateUpper s i):ℝ)<2 := by
    exact_mod_cast (coordinate_reserves s i).2
  have hh' : (1/2:ℝ)<ev t (coordinateLower s i) :=
    (by norm_num : (1/2:ℝ)=((1/2:ℚ):ℝ)).trans_lt hh
  exact ⟨hh',hu.trans_lt hc⟩

structure RadicalBounds (s : Chain) (q t u : ℝ) : Prop where
  r : lowerRight q u∈Icc (ev t (rLo s)) (ev t (rHi s))
  U : topRight q u∈Icc (ev t (ULo s)) (ev t (UHi s))
  V : topLeft q u∈Icc (ev t (VLo s)) (ev t (VHi s))
  Y : topHeight q u∈Icc (ev t (YLo s)) (ev t (YHi s))
  v : lowerHeight q u∈Icc (ev t (vLo s)) (ev t (vHi s))
  w : lowerLeft q u∈Icc (ev t (wLo s)) (ev t (wHi s))

theorem actual_radicals (s : Chain) {q t u : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25))
    (hu : u∈Icc (ev t (a s)) (ev t (b s))) : RadicalBounds s q t u := by
  have hab := endpoints ht s
  have ha : 0≤ev t (a s) := by linarith [hab.1]
  have hu0 : 0≤u := ha.trans hu.1
  have hrarg : q-u^2∈Icc (ev t (rootArgument s 0)) (ev t (rootArgument s 1)) := by
    have hl := square_mono_nonneg ha hu.1
    have hh := square_mono_nonneg hu0 hu.2
    simp only [rootArgument,Matrix.cons_val_zero,Matrix.cons_val_one,rArgLo,rArgHi,
      ev_sub,ev_C,ev_pow]
    constructor <;> linarith [hq.1,hq.2]
  obtain ⟨hrlo,hrhi⟩ := root_between s 0 1 ht hrarg
  have hr : lowerRight q u∈Icc (ev t (rLo s)) (ev t (rHi s)) := ⟨hrlo.le,hrhi.le⟩
  have hUarg : q-(2-u)^2∈Icc (ev t (rootArgument s 2)) (ev t (rootArgument s 3)) := by
    have hb : 0≤2-ev t (b s) := by linarith [hab.2.2]
    have hlow := square_mono_nonneg hb (show 2-ev t (b s)≤2-u by linarith [hu.2])
    have hhigh := square_mono_nonneg (show 0≤2-u by linarith [hu.2,hab.2.2])
      (show 2-u≤2-ev t (a s) by linarith [hu.1])
    have e2 : ev t (rootArgument s 2)=qLower-(2-ev t (a s))^2 := by
      simp [rootArgument,UArgLo,ev_two]
    have e3 : ev t (rootArgument s 3)=qUpper-(2-ev t (b s))^2 := by
      simp [rootArgument,UArgHi,ev_two]
    rw [e2,e3]
    constructor <;> linarith [hq.1,hq.2]
  obtain ⟨hUlo,hUhi⟩ := root_between s 2 3 ht hUarg
  have hU : topRight q u∈Icc (ev t (ULo s)) (ev t (UHi s)) := ⟨hUlo.le,hUhi.le⟩
  have hV : topLeft q u∈Icc (ev t (VLo s)) (ev t (VHi s)) := by
    simp only [topLeft,VLo,VHi,ev_sub,ev_three]
    exact ⟨by linarith [hU.2],by linarith [hU.1]⟩
  have hV0 : 0≤ev t (VLo s) := by
    have h2 : 1/2<ev t (VLo s) := (polynomial_coordinates s 2 ht).1
    linarith
  have hYarg : q-topLeft q u^2∈Icc (ev t (rootArgument s 4)) (ev t (rootArgument s 5)) := by
    have hlo := square_mono_nonneg hV0 hV.1
    have hhi := square_mono_nonneg (hV0.trans hV.1) hV.2
    have e4 : ev t (rootArgument s 4)=qLower-(ev t (VHi s))^2 := by
      simp [rootArgument,YArgLo]
    have e5 : ev t (rootArgument s 5)=qUpper-(ev t (VLo s))^2 := by
      simp [rootArgument,YArgHi]
    rw [e4,e5]
    constructor <;> linarith [hq.1,hq.2]
  obtain ⟨hYlo,hYhi⟩ := root_between s 4 5 ht hYarg
  have hY : topHeight q u∈Icc (ev t (YLo s)) (ev t (YHi s)) := ⟨hYlo.le,hYhi.le⟩
  have hv : lowerHeight q u∈Icc (ev t (vLo s)) (ev t (vHi s)) := by
    simp only [lowerHeight,vLo,vHi,ev_sub,ev_two]
    exact ⟨by linarith [hY.2],by linarith [hY.1]⟩
  have hv0 : 0≤ev t (vLo s) := by
    have h4 : 1/2<ev t (vLo s) := (polynomial_coordinates s 4 ht).1
    linarith
  have hwarg : q-lowerHeight q u^2∈Icc (ev t (rootArgument s 6)) (ev t (rootArgument s 7)) := by
    have hlo := square_mono_nonneg hv0 hv.1
    have hhi := square_mono_nonneg (hv0.trans hv.1) hv.2
    have e6 : ev t (rootArgument s 6)=qLower-(ev t (vHi s))^2 := by
      simp [rootArgument,wArgLo]
    have e7 : ev t (rootArgument s 7)=qUpper-(ev t (vLo s))^2 := by
      simp [rootArgument,wArgHi]
    rw [e6,e7]
    constructor <;> linarith [hq.1,hq.2]
  obtain ⟨hwlo,hwhi⟩ := root_between s 6 7 ht hwarg
  exact ⟨hr,hU,hV,hY,hv,hwlo.le,hwhi.le⟩

theorem RadicalBounds.smoothDomain {s : Chain} {q t u : ℝ}
    (h : RadicalBounds s q t u) (ht : t∈Icc (1/10:ℝ) (4/25))
    (hu : 0≤u) (hq : q<4) : SmoothDomain q u := by
  have h0 : 1/2<ev t (rLo s) := (polynomial_coordinates s 0 ht).1
  have h1 : 1/2<ev t (ULo s) := (polynomial_coordinates s 1 ht).1
  have h3 : 1/2<ev t (YLo s) := (polynomial_coordinates s 3 ht).1
  have h5 : 1/2<ev t (wLo s) := (polynomial_coordinates s 5 ht).1
  have hr : 0<lowerRight q u := by linarith [h.r.1]
  have hU : 0<topRight q u := by linarith [h.U.1]
  have hY : 0<topHeight q u := by linarith [h.Y.1]
  have hw : 0<lowerLeft q u := by linarith [h.w.1]
  exact ⟨⟨hu,by linarith [Real.sqrt_pos.mp hr],by linarith [Real.sqrt_pos.mp hU],
    by linarith [Real.sqrt_pos.mp hY],by linarith [Real.sqrt_pos.mp hw]⟩,hq,hr,hU,hY,hw⟩

end SquaresInCircles.Eight.CriticalERadicals

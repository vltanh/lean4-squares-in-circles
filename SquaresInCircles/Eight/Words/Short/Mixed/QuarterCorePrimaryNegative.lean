module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Stationary.Envelope
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroAlignedL
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroPositiveJ
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroCycle
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterCoreSecondaryNegative
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterCoreSecondaryPositive
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterSecondary
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterPrimaryReduction
public import SquaresInCircles.Eight.Words.Short.WordZero
public import SquaresInCircles.Eight.Owners.Stationary.PrimitiveForces
public import SquaresInCircles.Eight.Arithmetic.WholeIntervalPolynomial

/-!
# Eight squares: core-source primary contacts with negative outer target

The multiplier q/sin(phi) cancels the original target transverse term.
The lower-half derivative has the printed completed-square reserve;
the upper continuation loses at most the one concave tangent/secant
function on the whole physical interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.CorePrimaryNegative
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives Reference

def targetMaximum (r : Row) : ℝ := if 0≤coP r then coP r*outerAxial else coP r*outerDiagonal
def N (r : Row) (x : ℝ) : ℝ := Real.sqrt (coG r^2+(coQ r/Real.cos x)^2)
def Nd (r : Row) (x : ℝ) : ℝ := coQ r^2*Real.sin x/((Real.cos x)^3*N r x)
def constant (r : Row) : ℝ := coC r-coG r/2-targetMaximum r+coQ r/2
def F (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  angle upper x+constant r+
    coQ r*(if upper then -(outerAxial-1/2) else outerDiagonal+1/2)*
      (Real.sin x/Real.cos x)-N r x/12
def lowerD (r : Row) (x : ℝ) : ℝ :=
  -1+coQ r*(outerDiagonal+1/2)/(Real.cos x)^2-Nd r x/12
def tangentLoss (x : ℝ) : ℝ :=
  x-(567/500)*(183/200)*(Real.sin x/Real.cos x)-(189/2000)*(1/Real.cos x-1)
def tangentLossD (x : ℝ) : ℝ :=
  1-(567/500)*(183/200)/(Real.cos x)^2-(189/2000)*Real.sin x/(Real.cos x)^2
def tangentLossDD (x : ℝ) : ℝ :=
  -2*(567/500)*(183/200)*Real.sin x/(Real.cos x)^3-
    (189/2000)*(1+(Real.sin x)^2)/(Real.cos x)^3

theorem row_bounds (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=false) :
    coQ r≤567/500 ∧ 0< -1+(1399/1000)*coQ r-coQ r^2/576 := by
  revert hσ hτ
  fin_cases r <;> norm_num [sourcePositive,targetPositive,coQ]

theorem target_upper (r : Row) {A B : ℝ} (ht : OuterState A B) : coP r*A≤targetMaximum r := by
  have hb := outer_bounds ht
  by_cases hp : 0≤coP r
  · simpa [targetMaximum,hp] using mul_le_mul_of_nonneg_left hb.2.1 hp
  · simpa [targetMaximum,hp] using mul_le_mul_of_nonpos_left hb.1 (le_of_not_ge hp)

theorem N_positive (r : Row) (x : ℝ) : 0<N r x := by
  apply Real.sqrt_pos.mpr
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (coefficient_bounds r).1) (sq_nonneg _)
theorem N_square (r : Row) (x : ℝ) : N r x^2=coG r^2+(coQ r/Real.cos x)^2 :=
  Real.sq_sqrt (by positivity)
theorem N_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) : HasDerivAt (N r) (Nd r x) x := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  have hrad : coG r^2+(coQ r/Real.cos x)^2≠0 := by
    have hh := sq_pos_of_pos (coefficient_bounds r).1
    positivity
  have h := (((hasDerivAt_const x (coG r^2)).add
    (((hasDerivAt_const x (coQ r)).div (Real.hasDerivAt_cos x) hc).pow 2))).sqrt hrad
  convert h using 1
  · rfl
  · dsimp [Nd,N]
    field_simp [hc,(N_positive r x).ne']
    ring

theorem tangent_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (fun s => Real.sin s/Real.cos s) (1/(Real.cos x)^2) x := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  convert (Real.hasDerivAt_sin x).div (Real.hasDerivAt_cos x) hc using 1
  field_simp [hc]
  nlinarith [Real.sin_sq_add_cos_sq x]
theorem secant_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (fun s => 1/Real.cos s) (Real.sin x/(Real.cos x)^2) x := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  convert (hasDerivAt_const x (1:ℝ)).div (Real.hasDerivAt_cos x) hc using 1 <;> ring

theorem lower_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (F r false) (lowerD r x) x := by
  have h := ((((hasDerivAt_id' x).neg).const_add (Real.pi/2+constant r)).add
    ((tangent_hasDerivAt hx).const_mul (coQ r*(outerDiagonal+1/2)))).sub
      ((N_hasDerivAt r hx).div_const 12)
  have hF : F r false=fun y => Real.pi/2+constant r+-y+
      coQ r*(outerDiagonal+1/2)*(Real.sin y/Real.cos y)-N r y/12 := by
    funext y
    simp only [F,angle,direction,Bool.false_eq_true,↓reduceIte]
    ring
  rw [hF]
  convert h using 1
  simp only [lowerD]
  ring

theorem lower_derivative_positive (r : Row) (hσ : sourcePositive r=false)
    (hτ : targetPositive r=false) {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<lowerD r x := by
  have ht := positive_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  have hq := (coefficient_bounds r).2.2.1
  have hN := N_positive r x
  have hN2 := N_square r x
  have hrad : coQ r≤N r x*Real.cos x := by
    have hid : (N r x*Real.cos x)^2=(coG r*Real.cos x)^2+coQ r^2 := by
      rw [mul_pow,hN2]
      field_simp [hc.ne']
    nlinarith [mul_pos hN hc,sq_nonneg (coG r*Real.cos x)]
  have hratio : coQ r^2*Real.sin x/(N r x*Real.cos x)≤coQ r*Real.sin x := by
    apply (div_le_iff₀ (mul_pos hN hc)).2
    have hh := mul_le_mul_of_nonneg_left hrad (mul_nonneg hq.le ht.2.2.1)
    linarith
  have hid : lowerD r x*(Real.cos x)^2=
      -(Real.cos x)^2+coQ r*(outerDiagonal+1/2)-
        coQ r^2*Real.sin x/(12*(N r x*Real.cos x)) := by
    dsimp [lowerD,Nd]
    field_simp [hc.ne',hN.ne']
  have hdiag : (1399/1000:ℝ)<outerDiagonal+1/2 := by
    linarith [ShortMixedZero.fine_diagonal_bounds.1]
  have hd := mul_lt_mul_of_pos_left hdiag hq
  have hfloor := (row_bounds r hσ hτ).2
  have hsq := sq_nonneg (Real.sin x-coQ r/24)
  have hunit := Real.sin_sq_add_cos_sq x
  have h12 : coQ r^2*Real.sin x/(12*(N r x*Real.cos x))=
      (coQ r^2*Real.sin x/(N r x*Real.cos x))/12 := by ring
  have hprod : 0<lowerD r x*(Real.cos x)^2 := by
    nlinarith [hid,h12,hratio,hd,hfloor,hsq,hunit]
  exact (mul_pos_iff.mp hprod).resolve_right (by intro h; nlinarith [sq_nonneg (Real.cos x)]) |>.1

theorem lower_monotone (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=false) :
    MonotoneOn (F r false) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x hx => (lower_hasDerivAt r hx).continuousAt.continuousWithinAt)
    (fun x hx => lower_hasDerivAt r (Ioo_subset_Icc_self hx))
    (fun x hx => (lower_derivative_positive r hσ hτ (Ioo_subset_Icc_self hx)).le)

theorem norm_continuation (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    N r x-N r 0≤coQ r*(1/Real.cos x-1) := by
  have ht := positive_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  have hq := (coefficient_bounds r).2.2.1
  have h0 := N_positive r 0
  have hn := N_positive r x
  have he0 := N_square r 0
  have he := N_square r x
  simp only [Real.cos_zero,div_one] at he0
  have hbase : coQ r≤N r 0 := by nlinarith [sq_nonneg (coG r)]
  have hsec : 0≤1/Real.cos x-1 := by
    have h : 1≤1/Real.cos x := by
      rw [le_div_iff₀ hc,one_mul]
      exact Real.cos_le_one x
    linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hbase) (mul_nonneg hq.le hsec)
  have hid : (coQ r/Real.cos x)^2=
      coQ r^2+2*coQ r^2*(1/Real.cos x-1)+(coQ r*(1/Real.cos x-1))^2 := by ring
  nlinarith [mul_nonneg hq.le hsec]

theorem tangentLoss_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt tangentLoss (tangentLossD x) x := by
  convert ((hasDerivAt_id' x).sub ((tangent_hasDerivAt hx).const_mul ((567/500)*(183/200)))).sub
    (((secant_hasDerivAt hx).sub_const 1).const_mul (189/2000)) using 1
  · rfl
  · simp only [tangentLossD]
    ring
theorem tangentLossD_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt tangentLossD (tangentLossDD x) x := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  have h := (((hasDerivAt_const x (1:ℝ)).sub
    ((hasDerivAt_const x ((567/500:ℝ)*(183/200))).div ((Real.hasDerivAt_cos x).pow 2)
      (pow_ne_zero 2 hc))).sub
        (((Real.hasDerivAt_sin x).const_mul (189/2000)).div ((Real.hasDerivAt_cos x).pow 2)
          (pow_ne_zero 2 hc)))
  convert h using 1
  · rfl
  · dsimp [tangentLossDD]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq x]
theorem tangentLoss_concave : ConcaveOn ℝ (Icc 0 (7/10)) tangentLoss := by
  apply concave_of_deriv2 (fun x hx => tangentLoss_hasDerivAt hx)
    (fun x hx => tangentLossD_hasDerivAt hx)
  intro x hx
  have ht := positive_trig hx
  have hc : 0<(Real.cos x)^3 := pow_pos (by linarith [ht.1]) 3
  have h1 := div_nonpos_of_nonpos_of_nonneg
    (show -2*(567/500:ℝ)*(183/200)*Real.sin x≤0 by nlinarith [ht.2.2.1]) hc.le
  have h2 := div_nonneg (show 0≤(189/2000:ℝ)*(1+(Real.sin x)^2) by positivity) hc.le
  dsimp [tangentLossDD]
  linarith

theorem tangentLoss_cap : -(21/100:ℝ)<tangentLoss (7/10) := by
  let S := sine (by norm_num : (0:ℝ)≤7/10)
  let C := cosine (by norm_num : (0:ℝ)≤7/10)
  have hc : 0<C.lo := by dsimp [C]; mixed_fixed
  let B := ((Interval.point (7/10)).sub
    ((Interval.point ((567/500:ℝ)*(183/200))).mul (S.div C hc))).sub
      ((Interval.point (189/2000)).mul ((C.inv hc).sub (Interval.point 1)))
  have hlo : -(21/100:ℝ)<B.lo := by dsimp [B,S,C]; mixed_fixed
  exact hlo.trans_le B.mem.1
theorem tangentLoss_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) : -(21/100:ℝ)<tangentLoss x := by
  have h := tangentLoss_concave.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 (7/10) by norm_num) (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hx
  have h0 : tangentLoss 0=0 := by simp [tangentLoss]
  have hm : -(21/100:ℝ)< min (tangentLoss 0) (tangentLoss (7/10)) :=
    lt_min (by rw [h0]; norm_num) tangentLoss_cap
  exact hm.trans_le h

def targetBox (r : Row) : Interval (targetMaximum r) := by
  by_cases hp : 0≤coP r
  · simpa [targetMaximum,hp] using (Interval.point (coP r)).mul axial
  · simpa [targetMaximum,hp] using (Interval.point (coP r)).mul ShortWord.MixedQuarter.Reference.diagonal
def zeroNorm (r : Row) : Interval (N r 0) := by
  have h := rootSix (Interval.point (coG r^2+coQ r^2)) 2 (by norm_num)
    (by dsimp [Interval.point]; positivity)
  simpa [N] using h
def zeroValue (r : Row) : Interval (F r false 0) := by
  convert (((((halfPi.add (Interval.point (coC r))).sub (Interval.point (coG r/2))).sub
    (targetBox r)).add (Interval.point (coQ r/2))).sub
      ((zeroNorm r).div (Interval.point 12) (by norm_num [Interval.point]))) using 1 <;>
    simp [F,angle,constant] <;> ring

private lemma r82_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r82_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

private lemma r82_zeroValue_lo (r : Row) : (zeroValue r).lo =
    (((((halfPi.add (Interval.point (coC r))).sub (Interval.point (coG r/2))).sub
    (targetBox r)).add (Interval.point (coQ r/2))).sub
      ((zeroNorm r).div (Interval.point 12) (by norm_num [Interval.point]))).lo := by
  unfold zeroValue
  rw [r82_mpr_lo]
  simp [F,angle,constant]
  ring

private lemma r82_targetBox_hi (r : Row) : (targetBox r).hi =
    if 0≤coP r then ((Interval.point (coP r)).mul axial).hi
    else ((Interval.point (coP r)).mul ShortWord.MixedQuarter.Reference.diagonal).hi := by
  unfold targetBox
  split_ifs with hp
  · first
      | rfl
      | (rw [r82_mpr_hi]; simp [targetMaximum,hp])
  · first
      | rfl
      | (rw [r82_mpr_hi]; simp [targetMaximum,hp])

private lemma r82_zeroNorm_hi (r : Row) : (zeroNorm r).hi =
    (rootSix (Interval.point (coG r^2+coQ r^2)) 2 (by norm_num)
      (by dsimp [Interval.point]; positivity)).hi := by
  unfold zeroNorm
  first
    | rfl
    | (rw [r82_mpr_hi]; simp [N])

private lemma r82_zeroNorm_lo (r : Row) : (zeroNorm r).lo =
    (rootSix (Interval.point (coG r^2+coQ r^2)) 2 (by norm_num)
      (by dsimp [Interval.point]; positivity)).lo := by
  unfold zeroNorm
  first
    | rfl
    | (rw [r82_mpr_lo]; simp [N])

theorem aligned (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=false) :
    (32/25:ℝ)<F r false 0 := by
  have hlo : (32/25:ℝ)<(zeroValue r).lo := by
    revert hσ hτ
    fin_cases r <;> norm_num [sourcePositive,targetPositive] <;>
      norm_num [r82_zeroValue_lo,r82_targetBox_hi,r82_zeroNorm_hi,r82_zeroNorm_lo,
      Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
      piBox,halfPi,axial,ShortWord.MixedQuarter.Reference.diagonal,rootSix,
      SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
      SecondWord.OppositeThree.ReferenceAlgebra.rootStep,
      coC,coP,coQ,coG,Q0]
  exact hlo.trans_le (zeroValue r).mem.1

theorem upper_continuation (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=false)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : F r false 0+tangentLoss x≤F r true x := by
  have ht := positive_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  have hq := (coefficient_bounds r).2.2.1
  have hqu := (row_bounds r hσ hτ).1
  have htangent : 0≤Real.sin x/Real.cos x := div_nonneg ht.2.2.1 hc.le
  have hsec : 0≤1/Real.cos x-1 := by
    have h : 1≤1/Real.cos x := by
      rw [le_div_iff₀ hc,one_mul]
      exact Real.cos_le_one x
    linarith
  have hprod := mul_le_mul hqu (show outerAxial-1/2≤183/200 by linarith [outer_endpoint_bounds.2.1])
    (show 0≤outerAxial-1/2 by linarith [outer_endpoint_bounds.1]) (by norm_num : (0:ℝ)≤567/500)
  have htan := mul_le_mul_of_nonneg_right hprod htangent
  have hnorm := norm_continuation r hx
  have hsecQ := mul_le_mul_of_nonneg_right hqu hsec
  dsimp [F,angle,direction,tangentLoss]
  simp only [Real.sin_zero,Real.cos_zero,zero_div,mul_zero,add_zero]
  linarith

theorem scalar_lower (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=false)
    (upper : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) : (107/100:ℝ)<F r upper x := by
  cases upper
  · have hm := lower_monotone r hσ hτ (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hx hx.1
    linarith [aligned r hσ hτ]
  · linarith [aligned r hσ hτ,upper_continuation r hσ hτ hx,tangentLoss_lower hx]

theorem original_lower (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=false)
    (upper : Bool) {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle upper x)) :
    F r upper x≤coreOuterCost r a b A B (angle upper x) := by
  have htr := positive_trig hx
  have hc : 0<Real.cos x := by linarith [htr.1]
  have hq := (coefficient_bounds r).2.2.1
  have hg := (coefficient_bounds r).1
  let l := coQ r/Real.cos x
  have hl : 0≤l := div_nonneg hq.le hc.le
  have hid : l*Real.cos x=coQ r := div_mul_cancel₀ _ hc.ne'
  have hcore := core_circle_lower (X:= -l) (Y:= -coG r) hs (by linarith)
  have hroot : Real.sqrt ((-l)^2+(-coG r)^2)=N r x := by
    dsimp [N,l]
    congr 1
    ring
  rw [hroot] at hcore
  have htarget := target_upper r ht
  have hb := outer_bounds ht
  have htan := mul_nonneg hl htr.2.2.1
  have hAlo := mul_le_mul_of_nonneg_left hb.1 htan
  have hAhi := mul_le_mul_of_nonneg_left hb.2.1 htan
  dsimp [sourcePrimary] at hm
  have hmult := mul_le_mul_of_nonneg_left hm hl
  rw [angle_width upper hx,angle_sin,angle_cos,targetSign_negative hτ] at hmult
  have hsSign : sourceSign r= -1 := by simp [sourceSign,WordProblems.sign,hσ]
  dsimp [F,constant,coreOuterCost]
  rw [hsSign,targetSign_negative hτ]
  have htanEq : coQ r*(Real.sin x/Real.cos x)=l*Real.sin x := by dsimp [l]; ring
  cases upper <;> dsimp [direction] at * <;> nlinarith

theorem original (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=false)
    (upper : Bool) {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle upper x)) :
    (449/500:ℝ)<coreOuterCost r a b A B (angle upper x) := by
  have h := (scalar_lower r hσ hτ upper hx).trans_le (original_lower r hσ hτ upper hs ht hx hm)
  linarith

end SquaresInCircles.Eight.ShortWord.MixedQuarter.CorePrimaryNegative

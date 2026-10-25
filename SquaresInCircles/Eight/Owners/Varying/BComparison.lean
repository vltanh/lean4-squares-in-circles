module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcavity
public import SquaresInCircles.Eight.Owners.Varying.BCertificate
public import SquaresInCircles.Eight.Owners.Varying.BFunctions

/-!
# Eight squares: the full correlated comparison for the varying B coefficient

The actual endpoint inequality is proved in `VaryingBEndpoint`, the
whole-angle concavity and ratio monotonicity in `VaryingBFunctions`.
Consequently the final comparison has only the original coefficient and
angle hypotheses. It carries no polynomial-positivity or endpoint premise.
-/

section
/-!
## The derivative of the varying B at its endpoint

The polynomial inequality of degree `70` transfers to the trigonometric derivative
(`D_endpoint_pos`). Both comparisons of positive squares are written out, with the direction of
every Taylor bound and the sign of every denominator (`S11_nonneg`, `C12_le_one`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.VaryingBEndpoint
open PositiveStressCoefficients OrdinaryCurvatureBounds VaryingBFunctions

theorem S11_nonneg {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0≤HighOrderTaylor.S11 d := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have h6 := pow_le_pow_left₀ hd.1 hd.2 6
  have h10 := pow_le_pow_left₀ hd.1 hd.2 10
  have hfactor : 0≤1-d^2/6+d^4/120-d^6/5040+d^8/362880-d^10/39916800 := by
    dsimp [frameCap] at h2 h6 h10
    nlinarith [pow_nonneg hd.1 4,pow_nonneg hd.1 8]
  have he : HighOrderTaylor.S11 d=
      d*(1-d^2/6+d^4/120-d^6/5040+d^8/362880-d^10/39916800) := by
    dsimp [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7]
    ring
  rw [he]
  exact mul_nonneg hd.1 hfactor

theorem C12_le_one {d : ℝ} (hd : d∈Icc 0 frameCap) :
    HighOrderTaylor.C12 d≤1 := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have h6 := pow_le_pow_left₀ hd.1 hd.2 6
  have h10 := pow_le_pow_left₀ hd.1 hd.2 10
  have hfactor : 0≤1/2-d^2/24+d^4/720-d^6/40320+d^8/3628800-d^10/479001600 := by
    dsimp [frameCap] at h2 h6 h10
    nlinarith [pow_nonneg hd.1 4,pow_nonneg hd.1 8]
  have he : 1-HighOrderTaylor.C12 d=
      d^2*(1/2-d^2/24+d^4/720-d^6/40320+d^8/3628800-d^10/479001600) := by
    dsimp [HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8]
    ring
  have h := mul_nonneg (sq_nonneg d) hfactor
  rw [← he] at h
  linarith

/-- The algebraic core of `D_endpoint_pos`: the positive square comparison,
with the trigonometric values and Taylor bounds as plain variables. -/
private theorem r22_square_comparison {R q r u v A B S N slo sup clo cup bm bp H : ℝ}
    (hR : 0<R) (hR2 : R^2=q) (hq : q=9789/2500)
    (hr : r∈Icc (117/200) (1527/2000)) (hu : u∈Icc 0 frameCap)
    (hv0 : 0≤v) (hvsmall : v<147/625)
    (hAdef : A=1+r^2) (hBdef : B=A-2*r*u) (hB : 0<B)
    (hS : 0<S) (hS2 : S^2=A) (hN : 0<N) (hN2 : N^2=B)
    (hslo0 : 0 ≤ slo) (hslou : slo ≤ u) (husup : u ≤ sup)
    (hcup1 : cup≤1) (hvlv : 1-cup≤v) (hvvu : v≤1-clo)
    (hrsup : (19/200 : ℝ)<r-sup) (hfactor : (2511/5000 : ℝ)<2*r-A*sup)
    (hbmdef : bm=A-2*r*sup) (hbpdef : bp=A-2*r*slo)
    (hHdef : H=q*r^2*slo*(2*r-A*sup)+(1-cup)^2*A*bm)
    (hpoly : 0<H^2-4*q*(1-clo)^2*A*bp^2) :
    R*(1-r*u)*S<(R-v*S)*N := by
  have hu0 : 0≤u := hu.1
  have hu7 : u≤7/10 := hu.2
  have hr0 : 0<r := by linarith [hr.1]
  have hr2 : r^2≤(1527/2000 : ℝ)^2 := pow_le_pow_left₀ hr0.le hr.2 2
  have hRlo : 1<R :=
    lt_of_pow_lt_pow_left₀ 2 hR.le (by rw [hR2,hq]; norm_num)
  have hA : 0<A := by rw [hAdef]; positivity
  have hSupper : S≤2 := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) ?_
    rw [hS2,hAdef]
    linarith
  have hvlo : 0≤1-cup := by linarith
  have hvhi : 0≤1-clo := by linarith
  have hbm : 0<bm := by
    rw [hbmdef,hAdef]
    linarith [mul_pos hr0 (show 0<r-sup by linarith)]
  have hbmB : bm≤B := by
    rw [hbmdef,hBdef]
    linarith [mul_le_mul_of_nonneg_left husup hr0.le]
  have hBbp : B≤bp := by
    rw [hBdef,hbpdef]
    linarith [mul_le_mul_of_nonneg_left hslou hr0.le]
  have hbp : 0<bp := hB.trans_le hBbp
  have htruefactor : 2*r-A*sup≤2*r-A*u := by
    linarith [mul_le_mul_of_nonneg_left husup hA.le]
  have hH0 : 0≤H := by
    rw [hHdef,hq]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg r)) hslo0) (by linarith))
      (mul_nonneg (mul_nonneg (sq_nonneg _) hA.le) hbm.le)
  have hcrossUpper0 : 0≤2*R*(1-clo)*S*bp := by positivity
  have hcrossUpperSq : (2*R*(1-clo)*S*bp)^2=4*q*(1-clo)^2*A*bp^2 := by
    calc
      (2*R*(1-clo)*S*bp)^2=4*R^2*(1-clo)^2*S^2*bp^2 := by ring
      _=4*q*(1-clo)^2*A*bp^2 := by rw [hR2,hS2]
  have hHcross : 2*R*(1-clo)*S*bp<H :=
    lt_of_pow_lt_pow_left₀ 2 hH0 (by rw [hcrossUpperSq]; linarith)
  have hvcross : v*B≤(1-clo)*bp :=
    mul_le_mul hvvu hBbp hB.le hvhi
  have hcross : 2*R*v*S*B≤2*R*(1-clo)*S*bp := by
    have h := mul_le_mul_of_nonneg_left hvcross (show 0≤2*R*S by positivity)
    linarith
  have hfirst : slo*(2*r-A*sup)≤u*(2*r-A*u) :=
    mul_le_mul hslou htruefactor (by linarith) hu0
  have hfirst' := mul_le_mul_of_nonneg_left hfirst
    (show 0≤q*r^2 by rw [hq]; positivity)
  have hvSq : (1-cup)^2≤v^2 := pow_le_pow_left₀ hvlo hvlv 2
  have hsecond := mul_le_mul hvSq hbmB hbm.le (sq_nonneg v)
  have hsecond' := mul_le_mul_of_nonneg_left hsecond hA.le
  have hHactual : H≤q*r^2*u*(2*r-A*u)+v^2*A*B := by
    rw [hHdef]
    linarith
  have hpositiveSquare :
      0<q*r^2*u*(2*r-A*u)+v^2*A*B-2*R*v*S*B := by
    linarith
  have hleft : 0<R-v*S := by
    have hprod := mul_le_mul_of_nonneg_left hSupper hv0
    linarith
  have hright : 0<1-r*u := by
    have hmul := mul_le_mul hr.2 hu7 hu0 (by norm_num : (0:ℝ)≤1527/2000)
    linarith
  have hleftprod : 0<(R-v*S)*N := mul_pos hleft hN
  have hid : ((R-v*S)*N)^2-(R*(1-r*u)*S)^2=
      q*r^2*u*(2*r-A*u)+v^2*A*B-2*R*v*S*B := by
    rw [hBdef,hAdef] at hN2 ⊢
    rw [hAdef] at hS2
    linear_combination (R-v*S)^2*hN2+((1+r^2-2*r*u)-(1-r*u)^2*S^2)*hR2+
      (v^2*(1+r^2-2*r*u)-q*(1-r*u)^2)*hS2
  exact lt_of_pow_lt_pow_left₀ 2 hleftprod.le (by linarith)

/-- The derivative `D` is positive on `(0, frameCap]`: the inequality of degree `70` is a statement
about the derivative itself, not a hypothesis on the geometry. -/
theorem D_endpoint_pos {d : ℝ} (hd : d∈Ioc 0 frameCap) :
    0<D (Real.sqrt qCap) (ratio d) d := by
  have hd' : d∈Icc 0 frameCap := Ioc_subset_Icc_self hd
  have hd7 : d≤7/10 := hd'.2
  have hR : 0<Real.sqrt qCap := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hR2 : (Real.sqrt qCap)^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hr : ratio d∈Icc (117/200) (1527/2000) := by
    constructor <;> dsimp [ratio] <;> linarith [hd'.1]
  have hu : Real.sin d∈Icc 0 frameCap := sin_mem hd'
  have hv0 : 0≤1-Real.cos d := by linarith [Real.cos_le_one d]
  have hvsmall : 1-Real.cos d<147/625 := by linarith [(transport_trig hd').1]
  have hB : 0<1+(ratio d)^2-2*(ratio d)*Real.sin d := radicand_pos (ratio d) hu
  have hS := shape_pos (ratio d)
  have hS2 : (shape (ratio d))^2=1+(ratio d)^2 := shape_sq (ratio d)
  have hN := root_pos (ratio d) hu
  have hN2 := root_sq (ratio d) hu
  have hcup := HighOrderTaylor.cos_le_C12 hd'.1
  have hclo := Arithmetic.cos10_le_cos hd'.1
  have hsign := VaryingBCertificate.sign_bounds hd'
  have hrsup : (19/200 : ℝ)<ratio d-Arithmetic.sin9 d := by
    simpa only [map_sub,VaryingBCertificate.r_eval,VaryingBCertificate.S9_eval] using hsign.1
  have hfactor : (2511/5000 : ℝ)<2*ratio d-(1+(ratio d)^2)*Arithmetic.sin9 d := by
    simpa only [VaryingBCertificate.A,map_sub,map_mul,map_add,map_one,map_pow,
      map_ofNat,VaryingBCertificate.r_eval,VaryingBCertificate.S9_eval] using hsign.2
  have hpoly : 0<(qCap*(ratio d)^2*HighOrderTaylor.S11 d*
        (2*ratio d-(1+(ratio d)^2)*Arithmetic.sin9 d)+
        (1-HighOrderTaylor.C12 d)^2*(1+(ratio d)^2)*
          ((1+(ratio d)^2)-2*ratio d*Arithmetic.sin9 d))^2-
      4*qCap*(1-Arithmetic.cos10 d)^2*(1+(ratio d)^2)*
        ((1+(ratio d)^2)-2*ratio d*HighOrderTaylor.S11 d)^2 := by
    have h := VaryingBCertificate.numerator_positive hd
    simp only [VaryingBCertificate.numerator,VaryingBCertificate.H,
      VaryingBCertificate.A,VaryingBCertificate.Bminus,VaryingBCertificate.Bplus,
      map_sub,map_mul,map_add,map_one,map_pow,map_ofNat,Polynomial.aeval_C,eq_ratCast,
      VaryingBCertificate.r_eval,VaryingBCertificate.S9_eval,VaryingBCertificate.S11_eval,
      VaryingBCertificate.C10_eval,VaryingBCertificate.C12_eval] at h
    push_cast at h
    simpa only [qCap] using h
  have hcompare := r22_square_comparison hR hR2 rfl hr hu hv0 hvsmall rfl rfl hB hS hS2
    hN hN2 (S11_nonneg hd') (HighOrderTaylor.S11_le_sin hd'.1)
    (Arithmetic.sin_le_sin9 hd'.1) (C12_le_one hd') (by linarith) (by linarith)
    hrsup hfactor rfl rfl rfl hpoly
  have hclear : D (Real.sqrt qCap) (ratio d) d*(shape (ratio d)*root (ratio d) (Real.sin d))=
      (Real.sqrt qCap-(1-Real.cos d)*shape (ratio d))*root (ratio d) (Real.sin d)-
        Real.sqrt qCap*(1-ratio d*Real.sin d)*shape (ratio d) := by
    dsimp [D,gain]
    field_simp
    ring
  have hpositive : 0<D (Real.sqrt qCap) (ratio d) d*
      (shape (ratio d)*root (ratio d) (Real.sin d)) := by
    rw [hclear]
    linarith
  exact pos_of_mul_pos_left hpositive (mul_pos hS hN).le

end SquaresInCircles.Eight.VaryingBEndpoint
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.VaryingBComparison
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity PositiveStressCoefficients VaryingBFunctions

theorem D_correlated_nonneg {d t : ℝ} (hd : d∈Icc 0 frameCap)
    (ht : t∈Icc 0 d) : 0≤D (Real.sqrt qCap) (ratio d) t := by
  have hR0 : 0≤Real.sqrt qCap := Real.sqrt_nonneg qCap
  have hR2 : Real.sqrt qCap≤2 := by
    have h := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
    dsimp [qCap] at h
    nlinarith
  by_cases hz : d=0
  · have ht0 : t=0 := by rw [hz] at ht; linarith [ht.1,ht.2]
    simp [ht0]
  have hdp : 0<d := lt_of_le_of_ne hd.1 (Ne.symm hz)
  have hend := VaryingBEndpoint.D_endpoint_pos ⟨hdp,hd.2⟩
  have hconc := D_concave hR0 hR2 hd
  have h := hconc.min_le_of_mem_Icc ⟨le_rfl,hd.1⟩ ⟨hd.1,le_rfl⟩ ht
  simpa only [D_zero,min_eq_left hend.le] using h

theorem D_nonneg {r d t : ℝ} (hd : d∈Icc 0 frameCap)
    (ht : t∈Icc 0 d) (hr : ratio d≤r) (hr1 : r≤1) :
    0≤D (Real.sqrt qCap) r t := by
  have hr0 : 1/2≤ratio d := by dsimp [ratio]; linarith [hd.1]
  have hrd1 : ratio d≤1 := hr.trans hr1
  exact (D_correlated_nonneg hd ht).trans
    (D_monotone_ratio (Real.sqrt_nonneg qCap) ⟨ht.1,ht.2.trans hd.2⟩
      ⟨hr0,hrd1⟩ ⟨hr0.trans hr,hr1⟩ hr)

theorem negativeNorm_hasDerivAt_q {l q t : ℝ}
    (hl : 0<l) (hq : 0<q) (ht : t∈Icc 0 frameCap) :
    HasDerivAt (fun x => pairNorm l x (-t))
      ((q-l*Real.sin t)/pairNorm l q (-t)) q := by
  have harg : |-t|≤frameCap := by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2
  have hraw := (((hasDerivAt_const q (l^2)).add ((hasDerivAt_id q).pow 2)).add
    (((hasDerivAt_id q).const_mul (2*l)).mul_const (Real.sin (-t)))).sqrt
      (pair_radicand_pos hl hq harg).ne'
  convert hraw using 1
  · rfl
  · dsimp [pairNorm]
    rw [Real.sin_neg]
    ring

theorem negativeNorm_normalized {l q t : ℝ} (hq : 0<q) :
    pairNorm l q (-t)=q*root (l/q) (Real.sin t) := by
  unfold pairNorm root
  rw [Real.sin_neg]
  have he : l^2+q^2+2*l*q*(-Real.sin t)=
      q^2*(1+(l/q)^2-2*(l/q)*Real.sin t) := by
    field_simp
    ring
  rw [he,Real.sqrt_mul (sq_nonneg q),Real.sqrt_sq hq.le]

theorem V_hasDerivAt_q {R l q t : ℝ} (hl : 0<l) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (fun x => V R l x t) (D R (l/q) t) q := by
  have hN := negativeNorm_hasDerivAt_q hl hq ht
  have hZ := negativeNorm_hasDerivAt_q hl hq
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  simp only [neg_zero,Real.sin_zero,mul_zero,sub_zero] at hZ
  have hraw := ((hasDerivAt_id q).mul_const (Real.cos t-1)).sub
    ((hN.sub hZ).const_mul R)
  have hnorm := negativeNorm_normalized (l := l) (t := t) hq
  have hzero : pairNorm l q 0=q*shape (l/q) := by
    have h := negativeNorm_normalized (l := l) (t := 0) hq
    rw [neg_zero,Real.sin_zero,root_zero] at h
    exact h
  have hS := (shape_pos (l/q)).ne'
  have hNn := (root_pos (l/q) (sin_mem ht)).ne'
  convert hraw using 1
  · rfl
  · dsimp [D,gain]
    rw [hnorm,hzero]
    field_simp
    ring

/-- Increasing the larger coefficient preserves the required comparison
when its actual endpoint ratio has the correlated lower bound. -/
theorem V_larger_coefficient {l k q d t : ℝ}
    (hl : 0<l) (hlk : l≤k) (hkq : k≤q)
    (hratio : ratio d*q≤l) (hd : d∈Icc 0 frameCap) (ht : t∈Icc 0 d) :
    V (Real.sqrt qCap) l k t≤V (Real.sqrt qCap) l q t := by
  have hk : 0<k := hl.trans_le hlk
  have hr0 : 0≤ratio d := by dsimp [ratio]; linarith [hd.1]
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hd.2⟩
  have hcoeff (x : ℝ) (hx : x∈Icc k q) :
      0<x ∧ ratio d≤l/x ∧ l/x≤1 := by
    have hx0 : 0<x := hk.trans_le hx.1
    refine ⟨hx0,?_,?_⟩
    · exact (le_div_iff₀ hx0).2
        ((mul_le_mul_of_nonneg_left hx.2 hr0).trans hratio)
    · exact (div_le_one hx0).2 (hlk.trans hx.1)
  have hm : MonotoneOn (fun x => V (Real.sqrt qCap) l x t) (Icc k q) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (V_hasDerivAt_q hl (hcoeff x hx).1 ht').continuousAt.continuousWithinAt
    · intro x hx
      exact V_hasDerivAt_q hl (hcoeff x (Ioo_subset_Icc_self hx)).1 ht'
    · intro x hx
      have hc := hcoeff x (Ioo_subset_Icc_self hx)
      exact D_nonneg hd ht hc.2.1 hc.2.2
  exact hm ⟨le_rfl,hkq⟩ ⟨hkq,le_rfl⟩ hkq

end SquaresInCircles.Eight.VaryingBComparison
end
end
end

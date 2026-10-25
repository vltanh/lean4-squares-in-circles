module

public import SquaresInCircles.Eight.Words.Aligned.NegativeArc

/-!
# Eight squares: a uniform short-EH1 boundary reserve on the H/G arc

The short mixed angle is at most `11/50`. E's original circle gives the strict derivative bound
`highMixedDerivative < -1/2000` whenever the EH1 slack `highMixedSlack` is at most `1/1000`
(`Source.highMixedDerivative_negative`). This closed strip contains all first feasibility
boundaries and a small positive movement reserve. E need not satisfy a radial equality.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace AlignedNegative
open PrimaryCap

def highMixedSlack (qH P e : ℝ) (E : SignedPoint) (x : ℝ) : ℝ :=
  (movingAnchor qH P x).a+E.a*Real.sin (e+x)+E.y*Real.cos (e+x)-
    (1+Real.cos (e+x)+Real.sin (e+x))/2

def highMixedDerivative (qH P e : ℝ) (E : SignedPoint) (x : ℝ) : ℝ :=
  -primaryGain qH P x+(E.a-1/2)*Real.cos (e+x)+(1/2-E.y)*Real.sin (e+x)

theorem highMixedSlack_hasDerivAt {qH P e x : ℝ} (E : SignedPoint)
    (hc : Real.cos x≠0) (hrad : 0<qH-(2-value P x)^2) :
    HasDerivAt (highMixedSlack qH P e E) (highMixedDerivative qH P e E x) x := by
  obtain ⟨ha,hy⟩ := movingAnchor_derivatives hc hrad
  have he : HasDerivAt (fun z => e+z) 1 x := by
    simpa using (hasDerivAt_id x).const_add e
  have hcos : HasDerivAt (fun z => Real.cos (e+z)) (-Real.sin (e+x)*1) x :=
    (Real.hasDerivAt_cos (e+x)).comp x he
  have hsin : HasDerivAt (fun z => Real.sin (e+z)) (Real.cos (e+x)*1) x :=
    (Real.hasDerivAt_sin (e+x)).comp x he
  have h := ((ha.fun_add (hsin.const_mul E.a)).fun_add (hcos.const_mul E.y)).fun_sub
    ((((hasDerivAt_const x (1:ℝ)).fun_add hcos).fun_add hsin).div_const 2)
  convert h using 1
  · rfl
  · unfold highMixedDerivative
    ring

theorem highMixedSlack_actual {qH P e x : ℝ} (E : SignedPoint)
    (he : e+x∈Icc 0 (7/10 : ℝ)) :
    highMixedSlack qH P e E x=
      quarterProjection E (movingAnchor qH P x) (e+x) 1-edgeWidth (e+x) := by
  rw [edgeWidth_positive_formula he]
  simp [highMixedSlack,quarterProjection]

theorem Source.eh1_error_positive {q t ε : ℝ} {H G A E : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap)
    (hEs : E.Sorted) (hE : E.y≤0) (hε : |ε|≤7/10)
    (hf : quarterFeasible E H ε 1) : 0<ε := by
  have hHa := (I.cuts hq).2.2.2.2.1
  by_contra! hnonpos
  have hneg : -ε∈Icc 0 (7/10 : ℝ) := by
    constructor <;> linarith [(abs_le.mp hε).1]
  have hs := (transport_trig hneg).2.2.1
  rw [Real.sin_neg] at hs
  have hcos : 0<Real.cos ε := transport_cos_pos hε
  have hsin := mul_nonpos_of_nonneg_of_nonpos hEs.1.le
    (by linarith : Real.sin ε≤0)
  have htan := mul_nonpos_of_nonpos_of_nonneg hE hcos.le
  have hp : edgeWidth ε≤H.a+E.a*Real.sin ε+E.y*Real.cos ε := by
    simpa [quarterFeasible,quarterProjection] using hf
  linarith [edgeWidth_ge_one ε]

/-- The first-boundary comparison on the whole strip `L ≤ 1/1000`. The two rotated coordinates
keep E's exact shifted-circle norm. -/
theorem short_high_mixed_rate {ε aH L : ℝ} {E : SignedPoint}
    (hEc : E.Contained qCap) (hEy : E.y≤0)
    (hHa : 211/250<aH) (he : ε∈Icc 0 (11/50 : ℝ))
    (hL : L=aH+E.a*Real.sin ε+E.y*Real.cos ε-
      (1+Real.cos ε+Real.sin ε)/2) (hsmall : L≤1/1000) :
    (E.a-1/2)*Real.cos ε+(1/2-E.y)*Real.sin ε<1999/2000 := by
  let X := E.a+1/2
  let Y := 1/2-E.y
  let U := X*Real.cos ε+Y*Real.sin ε
  let V := Y*Real.cos ε-X*Real.sin ε
  have hcircle : X^2+Y^2≤qCap := by
    simpa [X,Y,SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hEy,
      sub_eq_add_neg,add_comm] using hEc
  have hrot : U^2+V^2=X^2+Y^2 := by
    calc
      U^2+V^2=(X^2+Y^2)*(Real.sin ε^2+Real.cos ε^2) := by
        dsimp [U,V]
        ring
      _=X^2+Y^2 := by rw [Real.sin_sq_add_cos_sq]; ring
  have hsin : Real.sin ε≤11/50 := by
    exact ((le_abs_self _).trans
      (Real.abs_sin_le_abs.trans_eq (abs_of_nonneg he.1))).trans he.2
  have hcos : (4879/5000 : ℝ)≤Real.cos ε := by
    have hh := Real.one_sub_sq_div_two_le_cos (x := ε)
    nlinarith [he.1,he.2]
  have hV : V=aH-1/2-Real.sin ε-L := by
    rw [hL]
    dsimp [V,X,Y]
    ring
  have hVlow : 123/1000<V := by linarith
  have hnorm : U^2+V^2≤qCap := hrot.trans_le hcircle
  by_contra! hbad
  have hU : (19753/10000 : ℝ)≤U := by
    have heq : U=(E.a-1/2)*Real.cos ε+(1/2-E.y)*Real.sin ε+Real.cos ε := by
      dsimp [U,X,Y]
      ring
    rw [heq]
    linarith
  dsimp [qCap] at hnorm
  nlinarith

theorem Source.highMixedDerivative_negative {q t e x : ℝ} {H G A E : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap)
    (hEc : E.Contained q) (hEy : E.y≤0)
    (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (A.a-1/2) x) A (-x) 0)
    (he : e+x∈Icc 0 (11/50 : ℝ))
    (hsmall : highMixedSlack H.circle (A.a-1/2) e E x≤1/1000) :
    highMixedDerivative H.circle (A.a-1/2) e E x< -(1/2000) := by
  let J := I.atAngle hq hx hnot
  have hj := J.cuts hq
  have hgeom := I.path_geometry hq ⟨hx.1.le,hx.2⟩
  have hD := I.path_cap hq ⟨hx.1.le,hx.2⟩
  have hR : intrinsic (value (A.a-1/2) x) x<qCap := by
    have hh := hj.2.2.2.2.2.2.1.trans_le hq
    simpa [point] using hh
  have hgain : 1<primaryGain H.circle (A.a-1/2) x :=
    circle_primary_gain ⟨hD.1,hD.2.1.le⟩
      ⟨hx.1.le,hx.2.trans I.tilt_cap⟩ hR (I.H_contained.trans hq)
      hgeom.2.2.2.2.2.2
  have hHa : 211/250<(movingAnchor H.circle (A.a-1/2) x).a := by
    have hsort := J.H_sorted.2
    rw [abs_of_nonneg J.H_nonneg] at hsort
    exact hj.2.2.2.1.trans_le hsort
  have hU := short_high_mixed_rate (hEc.trans hq) hEy hHa he rfl hsmall
  unfold highMixedDerivative
  linarith

end AlignedNegative
end SquaresInCircles.Eight

module

public import SquaresInCircles.Eight.Owners.E.ZeroCapped
public import SquaresInCircles.Eight.Owners.Positive.CancelingOuter

/-!
# Eight squares: deleting a negative outer error from the E-zero cap

For a large middle tangent, A keeps its circle and coordinates, and the negative core composite
is compared with the radical E-zero cap: its larger initial slope (`initial_demand_lower`) and the
strict curvature gap (`comparison_reserve`) delete the outer error from the angle of E
(`large_error_deletion`). The only cut is the crossing of that radical with the diagonal cap. A
small middle tangent absorbs the outer error into the quarter tilt (`small_error_absorption`), and
the two regimes give the same cap data (`side_cap`).
-/

section
/-!
## The core barrier for a negative noncanceling outer error

A continuous estimate on the whole interval `[0, 7/10]`. The bound on H gives a moving primary
threshold `D r = 1 - (2/5) sec r + (13/12) tan r`. Its energy `D² + D'²` is increasing and exceeds
`1501/1000 + 587/18000` (`energy_reserve`), while the rotated energy of A is below `1501/1000`
when the tangent of A is at most `1/2` (`middle_energy`). The reserve proves forward feasibility
(`feasible_primary`, `rate_on_feasible`) and the quantitative alignment of the pair.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NegativeNoncancelingBarrier
open PositiveCancelingOuter

def D (r : ℝ) : ℝ := 1-(2/5)/Real.cos r+(13/12)*Real.sin r/Real.cos r
def Dd (r : ℝ) : ℝ := ((13/12)-(2/5)*Real.sin r)/(Real.cos r)^2
def Ddd (r : ℝ) : ℝ :=
  (2*(13/12)*Real.sin r-(2/5)*(1+(Real.sin r)^2))/(Real.cos r)^3

theorem cos_pos {r : ℝ} (hr : r∈Icc 0 (7/10 : ℝ)) : 0<Real.cos r := by
  linarith [(transport_trig hr).1]

theorem D_hasDerivAt {r : ℝ} (hr : r∈Icc 0 (7/10 : ℝ)) :
    HasDerivAt D (Dd r) r := by
  have hc := (cos_pos hr).ne'
  have hh := (((hasDerivAt_const r (2/5)).div (Real.hasDerivAt_cos r) hc).const_sub 1).add
    (((Real.hasDerivAt_sin r).const_mul (13/12)).div (Real.hasDerivAt_cos r) hc)
  convert hh using 1
  · rfl
  · dsimp [Dd]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq r]

theorem Dd_hasDerivAt {r : ℝ} (hr : r∈Icc 0 (7/10 : ℝ)) :
    HasDerivAt Dd (Ddd r) r := by
  have hc := (cos_pos hr).ne'
  have hh := (((Real.hasDerivAt_sin r).const_mul (2/5)).const_sub (13/12)).div
    ((Real.hasDerivAt_cos r).pow 2) (pow_ne_zero 2 hc)
  convert hh using 1
  · rfl
  · dsimp [Ddd]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq r,
      congrArg (fun x : ℝ => Real.cos r*x) (Real.sin_sq_add_cos_sq r)]

theorem D_identity {r : ℝ} (hr : r∈Icc 0 (7/10 : ℝ)) :
    D r*Real.cos r=Real.cos r-2/5+(13/12)*Real.sin r := by
  dsimp [D]
  field_simp [(cos_pos hr).ne']

theorem Dd_identity {r : ℝ} (hr : r∈Icc 0 (7/10 : ℝ)) :
    Dd r*Real.cos r=(13/12)*Real.cos r+(D r-1)*Real.sin r := by
  dsimp [Dd,D]
  field_simp [(cos_pos hr).ne']
  nlinarith [Real.sin_sq_add_cos_sq r]

theorem D_lower {r : ℝ} (hr : r∈Icc 0 (7/10 : ℝ)) : (3/5 : ℝ)≤D r := by
  have hh := transport_trig hr
  have hw := edgeWidth_ge_one r
  rw [edgeWidth_positive_formula hr] at hw
  have hid := D_identity hr
  have hp := cos_pos hr
  apply le_of_mul_le_mul_right _ hp
  linarith [hh.2.2.1]

theorem Dd_bounds {r : ℝ} (hr : r∈Icc 0 (7/10 : ℝ)) : 0<Dd r ∧ Dd r<2 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hr
  have hp := cos_pos hr
  have hden : 0<(Real.cos r)^2 := sq_pos_of_pos hp
  have hlow : (9/16 : ℝ)≤(Real.cos r)^2 := by nlinarith
  dsimp [Dd]
  constructor
  · exact div_pos (by linarith) hden
  · apply (div_lt_iff₀ hden).2
    nlinarith

/-- `D + D''` is positive on `[0, 7/10]`: after the relation `cos² + sin² = 1` the identity has a
positive remainder. -/
theorem D_plus_Ddd_pos {r : ℝ} (hr : r∈Icc 0 (7/10 : ℝ)) : 0<D r+Ddd r := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hr
  have hp := cos_pos hr
  have hsq : (Real.sin r)^2≤(13/20 : ℝ)^2 :=
    pow_le_pow_left₀ hs0 (by linarith only [hs] : Real.sin r≤13/20) 2
  have hcoef : 0≤(13/12)*(3-(Real.sin r)^2)-(3/2)*Real.sin r := by linarith only [hsq,hs]
  have hprod := mul_nonneg hs0 hcoef
  have hrem := mul_nonneg (sq_nonneg (Real.cos r-1)) (show 0≤2*Real.cos r+1 by linarith only [hc])
  have hcube : 1-(3/2)*(Real.sin r)^2≤(Real.cos r)^3 := by
    linarith only [hrem,Real.sin_sq_add_cos_sq r]
  have hnum : 0<(Real.cos r)^3+(13/12)*Real.sin r*(3-(Real.sin r)^2)-4/5 := by
    linarith only [hcube,hprod]
  have hid : (D r+Ddd r)*(Real.cos r)^3=
      (Real.cos r)^3+(13/12)*Real.sin r*(3-(Real.sin r)^2)-4/5 := by
    have h1 := D_identity hr
    have h2 : Ddd r*(Real.cos r)^3=2*(13/12)*Real.sin r-(2/5)*(1+(Real.sin r)^2) :=
      div_mul_cancel₀ _ (pow_ne_zero 3 hp.ne')
    linear_combination (Real.cos r)^2*h1+h2+((13/12)*Real.sin r-2/5)*Real.sin_sq_add_cos_sq r
  have hprod' : 0<(D r+Ddd r)*(Real.cos r)^3 := by rwa [hid]
  by_contra! hbad
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hbad (pow_pos hp 3).le)) hprod'

theorem energy_hasDerivAt {r : ℝ} (hr : r∈Icc 0 (7/10 : ℝ)) :
    HasDerivAt (fun x => (D x)^2+(Dd x)^2) (2*Dd r*(D r+Ddd r)) r := by
  convert ((D_hasDerivAt hr).pow 2).add ((Dd_hasDerivAt hr).pow 2) using 1
  simp only [show (2:ℕ)-1=1 from rfl,pow_one,Nat.cast_ofNat]
  ring

theorem energy_reserve {r : ℝ} (hr : r∈Icc 0 (7/10 : ℝ)) :
    (1501/1000 : ℝ)+587/18000≤(D r)^2+(Dd r)^2 := by
  have hm : MonotoneOn (fun x => (D x)^2+(Dd x)^2) (Icc (0:ℝ) (7/10)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x hx => (energy_hasDerivAt hx).continuousAt.continuousWithinAt
    · exact fun x hx => energy_hasDerivAt (Ioo_subset_Icc_self hx)
    · intro x hx
      have hx' := Ioo_subset_Icc_self hx
      exact (mul_pos (by linarith [(Dd_bounds hx').1]) (D_plus_Ddd_pos hx')).le
  have hh := hm (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hr hr.1
  have h0 : (D 0)^2+(Dd 0)^2=5521/3600 := by norm_num [D,Dd]
  dsimp only at hh
  linarith

theorem V_hasDerivAt (A : SignedPoint) (x : ℝ) :
    HasDerivAt (V A) (-U A x) x := by
  convert ((Real.hasDerivAt_cos x).const_mul (A.a-1/2)).sub
    ((Real.hasDerivAt_sin x).const_mul (A.y+1/2)) using 1
  · rfl
  · dsimp [U]
    ring

theorem U_hasDerivAt (A : SignedPoint) (x : ℝ) :
    HasDerivAt (U A) (V A x) x := by
  convert ((Real.hasDerivAt_sin x).const_mul (A.a-1/2)).add
    ((Real.hasDerivAt_cos x).const_mul (A.y+1/2)) using 1
  · rfl
  · dsimp [V]
    ring

theorem rotation_energy (A : SignedPoint) (x : ℝ) :
    (V A x)^2+(U A x)^2=(A.a-1/2)^2+(A.y+1/2)^2 := by
  calc
    (V A x)^2+(U A x)^2=
        ((Real.sin x)^2+(Real.cos x)^2)*((A.a-1/2)^2+(A.y+1/2)^2) := by
      dsimp [V,U]
      ring
    _ = (A.a-1/2)^2+(A.y+1/2)^2 := by rw [Real.sin_sq_add_cos_sq,one_mul]

/-- A point A in the circle with tangent at most `1/2` has rotated energy below `1501/1000`,
strictly less than that of the moving core threshold. -/
theorem middle_energy {A : SignedPoint} (hAa : 1/2<A.a)
    (hAy : A.y∈Icc (0:ℝ) (1/2)) (hAc : A.Contained qCap) (x : ℝ) :
    (V A x)^2+(U A x)^2<(1501/1000 : ℝ) := by
  rw [rotation_energy]
  have hc := hAc
  rw [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hAy.1] at hc
  have hy2 : (A.y+1/2)^2≤1 := by
    simpa using pow_le_pow_left₀ (show 0≤A.y+1/2 by linarith [hAy.1])
      (show A.y+1/2≤1 by linarith [hAy.2]) 2
  by_cases hP : A.a-1/2≤7073/10000
  · have hP2 := pow_le_pow_left₀ (show 0≤A.a-1/2 by linarith) hP 2
    nlinarith
  · dsimp [qCap] at hc
    nlinarith [show 7073/10000<A.a-1/2 from lt_of_not_ge hP]

def F (H A : SignedPoint) (Θ z : ℝ) : ℝ :=
  H.y-1/2+(V A z-1)*Real.cos (Θ-z)-(13/12)*Real.sin (Θ-z)

def Fd (A : SignedPoint) (Θ z : ℝ) : ℝ :=
  ((13/12)-U A z)*Real.cos (Θ-z)+(V A z-1)*Real.sin (Θ-z)

theorem F_hasDerivAt (H A : SignedPoint) (Θ z : ℝ) :
    HasDerivAt (F H A Θ) (Fd A Θ z) z := by
  have hs := (Real.hasDerivAt_sin (Θ-z)).comp z
    ((hasDerivAt_const z Θ).sub (hasDerivAt_id z))
  have hc := (Real.hasDerivAt_cos (Θ-z)).comp z
    ((hasDerivAt_const z Θ).sub (hasDerivAt_id z))
  have hh := ((((V_hasDerivAt A z).sub_const 1).mul hc).const_add (H.y-1/2)).sub
    (hs.const_mul (13/12))
  convert hh using 1
  · rfl
  · dsimp [Fd]
    ring

theorem feasible_primary {H A : SignedPoint} {Θ z : ℝ}
    (hHy : H.y<9/10) (hr : Θ-z∈Icc 0 (7/10 : ℝ))
    (hf : 0≤F H A Θ z) : D (Θ-z)<V A z := by
  have hp := cos_pos hr
  have hid := D_identity hr
  apply lt_of_mul_lt_mul_right _ hp.le
  dsimp [F] at hf
  linarith

/-- Where the pair is feasible, `0 ≤ F H A Θ z`, its derivative exceeds `1/150`; forward
continuation then propagates the feasibility. -/
theorem rate_on_feasible {H A : SignedPoint} {Θ z : ℝ}
    (hHy : H.y<9/10) (hAa : 1/2<A.a)
    (hAy : A.y∈Icc (0:ℝ) (1/2)) (hAc : A.Contained qCap)
    (hz : z∈Icc 0 Θ) (hΘ : Θ≤7/10)
    (hf : 0≤F H A Θ z) : (1/150 : ℝ)<Fd A Θ z := by
  have hz' : z∈Icc 0 (7/10 : ℝ) := ⟨hz.1,hz.2.trans hΘ⟩
  have hr : Θ-z∈Icc 0 (7/10 : ℝ) := ⟨by linarith only [hz.2],by linarith only [hz.1,hΘ]⟩
  have htrig := transport_trig hr
  have hc := cos_pos hr
  have hV := feasible_primary hHy hr hf
  have hD := D_lower hr
  have hDd := Dd_bounds hr
  have henergy := energy_reserve hr
  have hAenergy := middle_energy hAa hAy hAc z
  have hV2 := pow_le_pow_left₀ (show 0≤D (Θ-z) by linarith only [hD]) hV.le 2
  have hU0 : 0≤U A z := by
    have htz := transport_trig hz'
    exact add_nonneg (mul_nonneg (by linarith only [hAa]) htz.2.2.1)
      (mul_nonneg (by linarith only [hAy.1]) (by linarith only [htz.1]))
  have hUu : U A z<5/4 := by
    by_contra! h
    have hh := mul_le_mul h h (by norm_num) hU0
    linarith only [hh,hAenergy,sq_nonneg (V A z)]
  have hsquare : (587/18000 : ℝ)<(Dd (Θ-z))^2-(U A z)^2 := by
    linarith only [henergy,hV2,hAenergy]
  have hdiff : 0<Dd (Θ-z)-U A z := by
    by_contra! h
    have hh := mul_le_mul (show Dd (Θ-z)≤U A z by linarith only [h])
      (show Dd (Θ-z)≤U A z by linarith only [h]) hDd.1.le hU0
    linarith only [hh,hsquare]
  have hden : Dd (Θ-z)+U A z<13/4 := by linarith only [hDd.2,hUu]
  have hmul := mul_lt_mul_of_pos_left hden hdiff
  have hgap : (587/58500 : ℝ)<Dd (Θ-z)-U A z := by linarith only [hmul,hsquare]
  have hid := Dd_identity hr
  have hVs := mul_le_mul_of_nonneg_right hV.le htrig.2.2.1
  have hrate : (Dd (Θ-z)-U A z)*Real.cos (Θ-z)≤Fd A Θ z := by
    dsimp [Fd]
    linarith only [hid,hVs]
  have hcmin : (3/4 : ℝ)≤Real.cos (Θ-z) := by linarith only [htrig.1]
  have hp1 := mul_le_mul_of_nonneg_left hcmin hdiff.le
  have hp2 := mul_lt_mul_of_pos_right hgap (show (0:ℝ)<3/4 by norm_num)
  linarith only [hrate,hp1,hp2]

end SquaresInCircles.Eight.NegativeNoncancelingBarrier
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NegativeOuterEZero
open PositiveCancelingOuter EZeroFunctions EZeroCapped

def demand (C r : ℝ) : ℝ := 1/2+C*Real.cos r+(13/12)*Real.sin r
def demandD (C r : ℝ) : ℝ := (13/12)*Real.cos r-C*Real.sin r

theorem demand_hasDerivAt (C r : ℝ) : HasDerivAt (demand C) (demandD C r) r := by
  convert (((Real.hasDerivAt_cos r).const_mul C).const_add (1/2)).add
    ((Real.hasDerivAt_sin r).const_mul (13/12)) using 1
  · rfl
  · dsimp [demandD]
    ring

theorem demandD_hasDerivAt (C r : ℝ) :
    HasDerivAt (demandD C) (-(demand C r-1/2)) r := by
  convert ((Real.hasDerivAt_cos r).const_mul (13/12)).sub
    ((Real.hasDerivAt_sin r).const_mul C) using 1
  · rfl
  · dsimp [demand]
    ring

theorem demandD_lower {C r : ℝ} (hC : C∈Ioo (0:ℝ) (8/15))
    (hr : r∈Icc 0 (7/10 : ℝ)) : (1/3 : ℝ)<demandD C r := by
  obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse hr
  have hprod := mul_le_mul hC.2.le hs.le hs0 (by norm_num : (0:ℝ)≤8/15)
  dsimp [demandD]
  linarith

theorem demand_growth {C x y : ℝ} (hC : C∈Ioo (0:ℝ) (8/15))
    (hx : x∈Icc 0 (7/10 : ℝ)) (hy : y∈Icc 0 (7/10 : ℝ)) (hxy : x≤y) :
    (y-x)/3≤demand C y-demand C x := by
  have hh := derivative_reserve
    (f := demand C) (df := demandD C) (l := 0) (u := (7/10 : ℝ)) (k := 1/3)
    (fun r _ => (demand_hasDerivAt C r).continuousAt.continuousWithinAt)
    (fun r _ => demand_hasDerivAt C r)
    (fun r hr => (demandD_lower hC (Ioo_subset_Icc_self hr)).le)
    hx hy hxy
  linarith

theorem demand_monotone {C : ℝ} (hC : C∈Ioo (0:ℝ) (8/15)) :
    MonotoneOn (demand C) (Icc 0 (7/10 : ℝ)) := by
  intro x hx y hy hxy
  have hh := demand_growth hC hx hy hxy
  linarith

theorem endpoint_strictMono : StrictMonoOn h (Icc 0 (7/10 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (7/10 : ℝ))
  · exact fun x hx => (h_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' := interior_subset hx
    rw [(h_hasDerivAt hx').deriv]
    exact hd_pos hx'

theorem endpoint_zero_upper : h 0<(791/1000 : ℝ) := by
  have hr := rho_sq (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  have hp := rho_pos (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  norm_num [u,qCap] at hr
  dsimp [h]
  nlinarith

/-- For A in the circle with tangent at least `1/2`, the initial H demand lies strictly above the E
cap at zero. -/
theorem initial_demand_lower {A : SignedPoint} {t : ℝ}
    (hAa : 1/2<A.a) (hAy : 1/2≤A.y) (hAc : A.Contained qCap)
    (ht : t∈Icc 0 (7/10 : ℝ)) :
    (73/250 : ℝ)<1-V A t ∧ h 0<1/2+(1-V A t) := by
  have hc := hAc
  rw [SignedPoint.Contained,SignedPoint.circle,
    abs_of_nonneg (show 0≤A.y by linarith)] at hc
  have hysq := pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num)
    (show 1≤A.y+1/2 by linarith) 2
  have hAu : A.a<151/125 := by
    dsimp [qCap] at hc
    nlinarith
  have hV := V_upper hAa (by linarith) ht
  have hzero := endpoint_zero_upper
  constructor <;> linarith

/-- The demand exceeds the shifted radical by at least `l/50`: the second derivative of the
difference is positive on the whole comparison interval, so the reserve of the initial slope
persists. -/
theorem comparison_reserve {C z l : ℝ} (hC : C∈Ioo (0:ℝ) (8/15))
    (hz : z∈Icc 0 (11/100 : ℝ)) (hl : l∈Icc 0 (7/10 : ℝ))
    (hzl : z+l≤11/100) (hinit : h z=1/2+C)
    (hupper : demand C l<9/10) :
    l/50≤demand C l-h (z+l) := by
  let f (r : ℝ) := demand C r-h (z+r)
  let df (r : ℝ) := demandD C r-hd (z+r)
  have hdom (r : ℝ) (hr : r∈Icc 0 l) : z+r∈Icc 0 (11/100 : ℝ) :=
    ⟨by linarith [hz.1,hr.1],by linarith [hr.2]⟩
  have hwide (r : ℝ) (hr : r∈Icc 0 l) : z+r∈Icc 0 (7/10 : ℝ) :=
    ⟨(hdom r hr).1,by linarith [(hdom r hr).2]⟩
  have hfd (r : ℝ) (hr : r∈Icc 0 l) : HasDerivAt f (df r) r := by
    have hh := (h_hasDerivAt (hwide r hr)).comp r ((hasDerivAt_id' r).const_add z)
    have h1 := (demand_hasDerivAt C r).sub hh
    rw [mul_one] at h1
    exact h1
  have hfdd (r : ℝ) (hr : r∈Icc 0 l) :
      HasDerivAt df (-(demand C r-1/2)-hdd (z+r)) r := by
    have hh := (hd_hasDerivAt (hwide r hr)).comp r ((hasDerivAt_id' r).const_add z)
    have h1 := (demandD_hasDerivAt C r).sub hh
    rw [mul_one] at h1
    exact h1
  have hdm : MonotoneOn df (Icc 0 l) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun r hr => (hfdd r hr).continuousAt.continuousWithinAt
    · exact fun r hr => hfdd r (Ioo_subset_Icc_self hr)
    · intro r hr
      have hr' := Ioo_subset_Icc_self hr
      have hrw : r∈Icc 0 (7/10 : ℝ) := ⟨hr'.1,hr'.2.trans hl.2⟩
      have hru := demand_monotone hC hrw hl hr'.2
      have hcurv := small_hdd (hdom r hr')
      linarith
  have hd0 : (1/50 : ℝ)<df 0 := by
    have hu := (small_hd hz).2
    simp only [df,demandD,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,add_zero]
    linarith
  have hf0 : f 0=0 := by simp [f,demand,hinit]
  have hh := derivative_reserve
    (f := f) (df := df) (l := 0) (u := l) (k := 1/50)
    (fun r hr => (hfd r hr).continuousAt.continuousWithinAt)
    (fun r hr => hfd r (Ioo_subset_Icc_self hr))
    (by
      intro r hr
      have hm := hdm (show (0:ℝ)∈Icc 0 l from ⟨le_rfl,hl.1⟩)
        (Ioo_subset_Icc_self hr) hr.1.le
      linarith)
    (show (0:ℝ)∈Icc 0 l from ⟨le_rfl,hl.1⟩)
    (show l∈Icc 0 l from ⟨hl.1,le_rfl⟩) hl.1
  rw [hf0] at hh
  dsimp [f] at hh
  linarith

/-- The deletion at the coordinates of A: the error `e` is at most `ε`, and A satisfies the cap
with `ε - e`, both strictly at positive error. -/
theorem large_error_deletion {A : SignedPoint} {t e ε : ℝ}
    (hAa : 1/2<A.a) (hAy : 1/2≤A.y) (hAc : A.Contained qCap)
    (ht : t∈Icc 0 (7/10 : ℝ)) (he : e∈Icc 0 (7/10 : ℝ))
    (hε : ε∈Icc 0 (7/10 : ℝ))
    (hsource : demand (1-V A t) e≤capped ε) :
    e≤ε ∧
      1+edgeWidth t≤capped (ε-e)+A.a*Real.cos t-A.y*Real.sin t ∧
      (0<e → e<ε ∧
        1+edgeWidth t<capped (ε-e)+A.a*Real.cos t-A.y*Real.sin t) := by
  let C := 1-V A t
  have hsource' : demand C e≤capped ε := hsource
  have hbase := initial_demand_lower hAa hAy hAc ht
  have hC0 : 0<C := by dsimp [C]; linarith [hbase.1]
  have hCtop : C<8/15 := by
    have hcap := capped_bounds hε
    obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse he
    have hp := mul_le_mul_of_nonneg_left hc.le hC0.le
    dsimp [demand] at hsource'
    nlinarith
  have hC : C∈Ioo (0:ℝ) (8/15) := ⟨hC0,hCtop⟩
  have hidentity : (1/2+C)+A.a*Real.cos t-A.y*Real.sin t=1+edgeWidth t := by
    rw [edgeWidth_positive_formula ht]
    dsimp [C,V]
    ring
  rcases eq_or_lt_of_le he.1 with he0 | hepos
  · have heq : e=0 := he0.symm
    subst e
    have hh : 1/2+C≤capped ε := by simpa [demand] using hsource'
    refine ⟨hε.1,?_,?_⟩
    · simpa only [sub_zero] using (show 1+edgeWidth t≤capped ε+A.a*Real.cos t-A.y*Real.sin t by linarith)
    · intro hh
      linarith
  have hreqgrow := demand_growth hC (show (0:ℝ)∈Icc 0 (7/10) by norm_num) he he.1
  have hdemand0 : demand C 0=1/2+C := by simp [demand]
  rw [hdemand0] at hreqgrow
  have hH0cap : 1/2+C<diagonalCoordinate qCap := by
    have hcap := min_le_left (diagonalCoordinate qCap) (h ε)
    change capped ε≤diagonalCoordinate qCap at hcap
    linarith
  obtain ⟨c,hc,hcross⟩ := crossing
  have hcc : c∈Icc 0 (7/10 : ℝ) := ⟨hc.1.le,by linarith [hc.2]⟩
  have hcont : ContinuousOn h (Icc 0 c) := fun z hz =>
    (h_hasDerivAt ⟨hz.1,hz.2.trans hcc.2⟩).continuousAt.continuousWithinAt
  have hbase' : h 0<1/2+C := hbase.2
  obtain ⟨z,hz,hinit⟩ := intermediate_value_Icc hc.1.le hcont
    (show 1/2+C∈Icc (h 0) (h c) by rw [hcross]; exact ⟨hbase'.le,hH0cap.le⟩)
  have hzpos : 0<z := by
    by_contra! hn
    have heq : z=0 := le_antisymm hn hz.1
    rw [heq] at hinit
    linarith
  have hzc : z<c := by
    by_contra! hn
    have heq : z=c := le_antisymm hz.2 hn
    rw [heq,hcross] at hinit
    linarith
  have hzsmall : z∈Icc 0 (11/100 : ℝ) := ⟨hz.1,hz.2.trans hc.2.le⟩
  have hreqcap : demand C e≤diagonalCoordinate qCap :=
    hsource'.trans (min_le_left _ _)
  have hreqtop : demand C e<9/10 := hreqcap.trans_lt diagonal_bounds.2
  have hecross : e<c-z := by
    by_contra! hn
    have hr : c-z∈Icc 0 (7/10 : ℝ) := ⟨by linarith,by linarith [hc.2]⟩
    have hreq := demand_monotone hC hr he hn
    have hgap := comparison_reserve hC hzsmall hr (by linarith [hc.2]) hinit
      (hreq.trans_lt hreqtop)
    rw [show z+(c-z)=c by ring,hcross] at hgap
    linarith
  have hgap := comparison_reserve hC hzsmall he (by linarith [hc.2]) hinit hreqtop
  have hεlower : z+e<ε := by
    by_contra! hn
    have hze : z+e∈Icc 0 (7/10 : ℝ) :=
      ⟨by linarith,by linarith [hc.2]⟩
    have hm := h_monotone hε hze hn
    have hcap : capped ε≤h ε := min_le_right _ _
    linarith
  have hdeleted : ε-e∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith,by linarith [hε.2]⟩
  have hstrict := endpoint_strictMono
    (show z∈Icc 0 (7/10 : ℝ) from ⟨hz.1,by linarith [hzsmall.2]⟩)
    hdeleted (by linarith : z<ε-e)
  have hcapstrict : 1/2+C<capped (ε-e) := by
    apply lt_min hH0cap
    rw [←hinit]
    exact hstrict
  refine ⟨by linarith,by linarith,?_⟩
  intro _
  exact ⟨by linarith,by linarith⟩

/-- A small middle tangent absorbs its outer error into the quarter tilt, at the same coordinates
of H and A, with the reserve `e/150`. -/
theorem small_error_absorption {H A : SignedPoint} {t e : ℝ}
    (hHy : H.y<9/10) (hAa : 1/2<A.a) (hAy : A.y∈Icc (0:ℝ) (1/2))
    (hAc : A.Contained qCap) (ht : 0≤t) (he : 0≤e) (hsum : t+e≤7/10)
    (hsource : demand (1-V A t) e≤H.y) :
    1+edgeWidth (t+e)+e/150≤
      H.y+A.a*Real.cos (t+e)-A.y*Real.sin (t+e) := by
  have hΘ : t+e∈Icc 0 (7/10 : ℝ) := ⟨add_nonneg ht he,hsum⟩
  have hf : 0≤NegativeNoncancelingBarrier.F H A (t+e) t := by
    dsimp [NegativeNoncancelingBarrier.F]
    rw [show t+e-t=e by ring]
    dsimp [demand] at hsource
    linarith
  have hh := HardCancelingOuter.feasible_right_reserve
    (f := NegativeNoncancelingBarrier.F H A (t+e))
    (df := NegativeNoncancelingBarrier.Fd A (t+e))
    (l := t) (u := t+e) (b := 0) (k := 1/150) (by linarith) (by norm_num)
    (fun z _ => NegativeNoncancelingBarrier.F_hasDerivAt H A (t+e) z)
    (by
      intro z hz hfeas
      exact (NegativeNoncancelingBarrier.rate_on_feasible hHy hAa hAy hAc
        ⟨ht.trans hz.1,hz.2⟩ hsum hfeas).le)
    hf (t+e) ⟨by linarith,le_rfl⟩
  have hreserve : e/150≤NegativeNoncancelingBarrier.F H A (t+e) (t+e) := by
    linarith [hh.2]
  simp only [NegativeNoncancelingBarrier.F,sub_self,Real.cos_zero,Real.sin_zero,
    mul_one,mul_zero,sub_zero] at hreserve
  rw [edgeWidth_positive_formula hΘ]
  dsimp [V] at hreserve
  linarith

/-- Both tangent regimes give cap data `τ`, `ε'` with `τ - ε' = t + e - ε`: the conserved difference
records which part of the outer error is absorbed into the quarter tilt and which part is deleted
from E. Both use the coordinates of A. -/
theorem side_cap {H A : SignedPoint} {t e ε : ℝ}
    (hHy : H.y<9/10) (hAa : 1/2<A.a) (hAy : 0≤A.y) (hAc : A.Contained qCap)
    (ht : 0≤t) (he : 0≤e) (hsum : t+e≤7/10) (hε : ε∈Icc 0 (7/10 : ℝ))
    (hsource : demand (1-V A t) e≤H.y) (hcap : H.y≤capped ε) :
    ∃τ ε', 0≤τ ∧ 0≤ε' ∧ τ≤t+e ∧ ε'≤ε ∧
      τ-ε'=t+e-ε ∧
      1+edgeWidth τ≤capped ε'+A.a*Real.cos τ-A.y*Real.sin τ := by
  by_cases hsmall : A.y≤1/2
  · have hh := small_error_absorption hHy hAa ⟨hAy,hsmall⟩ hAc ht he hsum hsource
    exact ⟨t+e,ε,add_nonneg ht he,hε.1,le_rfl,le_rfl,rfl,by linarith⟩
  · have hh := large_error_deletion hAa (le_of_not_ge hsmall) hAc
      ⟨ht,by linarith⟩ ⟨he,by linarith⟩ hε (hsource.trans hcap)
    exact ⟨t,ε-e,ht,by linarith [hh.1],by linarith,by linarith,
      by ring,hh.2.1⟩

end SquaresInCircles.Eight.NegativeOuterEZero
end
end
end

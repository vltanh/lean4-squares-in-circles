module

public import SquaresInCircles.Eight.TableFree.PositiveCancelingOuter

/-!
# The true-core barrier for a negative noncanceling outer error

Uncompiled draft.  This is a continuous estimate on the full interval
[0,.7].  The source H bound gives a moving primary threshold D.  Its
energy D²+D'² is increasing, with an explicit positive reserve over the
actual A energy when A's tangent is at most one half.  The reserve proves
forward feasibility and quantitative alignment of the original pair.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.NegativeNoncancelingBarrier
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

/-- The identity has a direct positive remainder after the unit-circle
relation is used.  No angular partition or sampled bound is involved. -/
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

/-- The actual A circle with tangent at most one half has a strictly
smaller rotated energy than the moving core threshold. -/
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

/-- The derivative lower bound is conditional only on genuine current
feasibility, which the forward continuation theorem then propagates. -/
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

end SquaresInCircles.Eight.TableFree.NegativeNoncancelingBarrier

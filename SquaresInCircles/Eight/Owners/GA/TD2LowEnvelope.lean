module

public import SquaresInCircles.Eight.Frames.Ordinary.PositiveEnvelope
public import SquaresInCircles.Eight.Owners.GA.DMinorant
public import SquaresInCircles.Eight.Owners.GA.Positive.TDConcentration

/-!
# Eight squares: four scalar expressions cover every low-angle TD2 alternative

The coefficient comparisons and the ordinary
whole-angle envelopes cover all four blocks and both intrinsic
concentration alternatives.  The D positive part remains its actual
linear clipped-circle bound.
-/

section
/-!
## Coordinate comparisons for the original TD2 negative charges

Both coefficient directions are covered on the
whole low-angle interval.  The larger-coordinate derivative has a
positive reserve obtained by integrating its exact norm derivative;
no angle subdivision or selected coefficient sample is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveTD
open Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope OrdinaryNegativeSlope
open VaryingBFunctions VaryingBComparison

theorem short_integrand_lower {r u : ℝ} (hr : (1/2:ℝ)≤r)
    (hu : u∈Icc 0 (1/6:ℝ)) : (1/18:ℝ)≤ integrand r u := by
  have hu' : u∈Icc 0 frameCap := ⟨hu.1,by dsimp [frameCap]; linarith [hu.2]⟩
  have hr0 : 0<r := by linarith
  have hn := root_pos r hu'
  have hn2 := root_sq r hu'
  have hru : (2/3)*r≤r-u := by linarith [hu.2]
  have hroot : root r u≤(9/4)*r := by
    have hmul := mul_nonneg hr0.le hu.1
    have hr2 : (1/2:ℝ)^2≤r^2 := pow_le_pow_left₀ (by norm_num) hr 2
    apply le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (by positivity)
    rw [hn2]
    linarith
  have hcube := pow_le_pow_left₀ hn.le hroot 3
  have hnum := mul_le_mul_of_nonneg_left hru (sq_nonneg r)
  have hr3 := pow_nonneg hr0.le 3
  unfold integrand
  rw [le_div_iff₀ (pow_pos hn 3)]
  linarith

theorem short_gain_lower {r u : ℝ} (hr : (1/2:ℝ)≤r)
    (hu : u∈Icc 0 (1/6:ℝ)) : u/18≤gain r u := by
  have hc (x : ℝ) (hx : x∈Icc 0 (1/6:ℝ)) : x∈Icc 0 frameCap :=
    ⟨hx.1,by dsimp [frameCap]; linarith [hx.2]⟩
  have hh := derivative_reserve
    (fun x hx => (gain_hasDerivAt_u r (hc x hx)).continuousAt.continuousWithinAt)
    (fun x hx => gain_hasDerivAt_u r (hc x (Ioo_subset_Icc_self hx)))
    (fun x hx => short_integrand_lower hr (Ioo_subset_Icc_self hx))
    (show (0:ℝ)∈Icc 0 (1/6:ℝ) by norm_num) hu hu.1
  simp only [gain_zero,sub_zero] at hh
  linarith

theorem short_cosine_lower {z : ℝ} (hz : 0≤z) : 1-z^2/2≤Real.cos z := by
  have hh := nonneg_of_deriv_nonneg (fun x => Real.cos x-1+x^2/2)
    (by fun_prop) (by norm_num)
    (fun x hx => by simp (disch := fun_prop); linarith [Real.sin_le hx]) hz
  linarith

/-- The second coefficient can cross the first: only its actual upper
ratio bound is needed on this short angle interval. -/
theorem short_D_lower {r z : ℝ} (hr : (1/2:ℝ)≤r)
    (hz : z∈Icc 0 (1/6:ℝ)) : z/40≤VaryingBFunctions.D R r z := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hs0 := (transport_trig hz').2.2.1
  have hsU := Real.sin_le hz.1
  have hs : Real.sin z∈Icc 0 (1/6:ℝ) := ⟨hs0,hsU.trans hz.2⟩
  have hgain := short_gain_lower hr hs
  have hsq : z^2≤1/36 := by
    have hh := pow_le_pow_left₀ hz.1 hz.2 2
    norm_num at hh
    exact hh
  have hcub := mul_le_mul_of_nonneg_right hsq hz.1
  have hsL : (215/216)*z≤Real.sin z := by
    have hh := Real.sin_ge_sub_cube hz.1
    linarith
  have hc := short_cosine_lower hz.1
  have hquadratic := mul_le_mul_of_nonneg_right hz.2 hz.1
  have hR : (197/100:ℝ)≤R := by linarith [radius_bounds.1]
  have hprod : R*(Real.sin z/18)≤R*gain r (Real.sin z) :=
    mul_le_mul_of_nonneg_left hgain (Real.sqrt_nonneg qCap)
  have hprodR := mul_le_mul_of_nonneg_right hR (div_nonneg hs0 (by norm_num : (0:ℝ)≤18))
  have hprodS := mul_le_mul_of_nonneg_left hsL (by norm_num : (0:ℝ)≤197/1800)
  dsimp only [VaryingBFunctions.D]
  linarith

theorem V_short_second_coefficient {p q₀ q₁ z : ℝ}
    (hp : 0<p) (hq₀ : 0<q₀) (hqq : q₀≤q₁) (hq₁ : q₁≤2*p)
    (hz : z∈Icc 0 (1/6:ℝ)) : V R p q₀ z≤V R p q₁ z := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hq (q : ℝ) (hq : q∈Icc q₀ q₁) : 0<q := hq₀.trans_le hq.1
  have hm : MonotoneOn (fun q => V R p q z) (Icc q₀ q₁) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro q hqq'
      exact (V_hasDerivAt_q hp (hq q hqq') hz').continuousAt.continuousWithinAt
    · intro q hqq'
      exact V_hasDerivAt_q hp (hq q (Ioo_subset_Icc_self hqq')) hz'
    · intro q hqq'
      have hq0 := hq q (Ioo_subset_Icc_self hqq')
      have hr : (1/2:ℝ)≤p/q := (le_div_iff₀ hq0).2 (by linarith [hqq'.2])
      have hh := short_D_lower hr hz
      linarith [hz.1]
  exact hm ⟨le_rfl,hqq⟩ ⟨hqq,le_rfl⟩ hqq

theorem extended_smallerD_nonneg {R r z : ℝ} (hR : 0≤R)
    (hr : r∈Icc (1/2:ℝ) 2) (hz : z∈Icc 0 frameCap) :
    0≤ smallerD R r z := by
  let u : ℝ := Real.sin z
  have hu : u∈Icc 0 frameCap := sin_mem hz
  have huSmall : u<129/200 := by dsimp [u]; linarith [(transport_trig hz).2.2.2.1]
  have hr0 : 0≤r := by linarith [hr.1]
  have hratio : (4/5)*(1+r^2)≤2*r := by
    have hh := mul_nonneg (show 0≤r-1/2 by linarith [hr.1])
      (show 0≤2-r by linarith [hr.2])
    nlinarith
  have hfactor : 0≤2*r-(1+r^2)*u := by
    have hh := mul_le_mul_of_nonneg_left huSmall.le (show 0≤1+r^2 by positivity)
    nlinarith [sq_nonneg r]
  have hS := shape_pos r
  have hN := root_pos r hu
  have hS2 := shape_sq r
  have hN2 := root_sq r hu
  have hfrac : (r-u)/root r u≤r/shape r := by
    apply (div_le_div_iff₀ hN hS).2
    by_cases hru : r-u≤0
    · exact (mul_nonpos_of_nonpos_of_nonneg hru hS.le).trans (mul_nonneg hr0 hN.le)
    · have hsquare : ((r-u)*shape r)^2≤(r*root r u)^2 := by
        have he : (r*root r u)^2-((r-u)*shape r)^2=u*(2*r-(1+r^2)*u) := by
          calc
            (r*root r u)^2-((r-u)*shape r)^2=
                r^2*(root r u)^2-(r-u)^2*(shape r)^2 := by ring
            _=u*(2*r-(1+r^2)*u) := by rw [hN2,hS2]; ring
        have hh := mul_nonneg hu.1 hfactor
        rw [← he] at hh
        linarith
      nlinarith [mul_nonneg hr0 hN.le,mul_nonneg (lt_of_not_ge hru).le hS.le]
  dsimp [smallerD]
  exact mul_nonneg hR (sub_nonneg.mpr hfrac)

theorem V_first_coefficient {p₀ p₁ q z : ℝ} (hq : 0<q)
    (hp₀ : q/2≤p₀) (hpp : p₀≤p₁) (hp₁ : p₁≤2*q)
    (hz : z∈Icc 0 frameCap) : V R p₀ q z≤V R p₁ q z := by
  have hp (p : ℝ) (hp : p∈Icc (q/2) (2*q)) : 0<p := by linarith [hp.1]
  have hm : MonotoneOn (fun p => V R p q z) (Icc (q/2) (2*q)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro p hpp'
      exact (V_hasDerivAt_p (hp p hpp') hq hz).continuousAt.continuousWithinAt
    · intro p hpp'
      exact V_hasDerivAt_p (hp p (Ioo_subset_Icc_self hpp')) hq hz
    · intro p hpp'
      have hr : p/q∈Icc (1/2:ℝ) 2 :=
        ⟨(le_div_iff₀ hq).2 (by linarith [hpp'.1]),
          (div_le_iff₀ hq).2 (by linarith [hpp'.2])⟩
      exact extended_smallerD_nonneg (Real.sqrt_nonneg qCap) hr hz
  exact hm ⟨hp₀,hpp.trans hp₁⟩ ⟨hp₀.trans hpp,hp₁⟩ hpp

theorem H_negative_endpoint_upper {k : ℝ} (hk : k∈Icc (1/2:ℝ) (17/20)) :
    V R k 1 frameCap<4/5 := by
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hmono := V_monotone_smaller (Real.sqrt_nonneg qCap) (by norm_num : (0:ℝ)<1) hh
    (show k∈Icc ((1:ℝ)/2) 1 by constructor <;> linarith [hk.1,hk.2])
    (show (17/20:ℝ)∈Icc ((1:ℝ)/2) 1 by norm_num) hk.2
  have hZ := pairNorm_pos (p:=17/20) (q:=1) (t:=0)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hZ2 := pairNorm_sq (p:=17/20) (q:=1) (t:=0)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hN := pairNorm_pos (p:=17/20) (q:=1) (t:= -frameCap)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hN2 := pairNorm_sq (p:=17/20) (q:=1) (t:= -frameCap)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_zero,Real.sin_neg] at hZ2 hN2
  have hZhi : pairNorm (17/20) 1 0<21/16 := by nlinarith
  have hNlo : (7919/10000:ℝ)<pairNorm (17/20) 1 (-frameCap) := by
    have hs := cap_trig.2.1
    norm_num [Arithmetic.sin9,Arithmetic.sin7,frameCap] at hs
    nlinarith
  have hcos : Real.cos frameCap<7649/10000 := by
    have hc := cap_trig.2.2.2
    norm_num [Arithmetic.cos8,frameCap] at hc
    linarith
  have hgap : pairNorm (17/20) 1 0-pairNorm (17/20) 1 (-frameCap)<2603/5000 := by
    linarith
  have hR0 : 0<R := by linarith [radius_bounds.1]
  have hprod := mul_lt_mul_of_pos_left hgap hR0
  have hRprod := mul_lt_mul_of_pos_right
    (show R<(4947/2500:ℝ) by linarith [radius_bounds.2])
    (by norm_num : (0:ℝ)<2603/5000)
  have hend : V R (17/20) 1 frameCap<4/5 := by
    dsimp [V]
    nlinarith
  exact hmono.trans_lt hend

end SquaresInCircles.Eight.GlobalGA.PositiveTD
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveTD
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open OrdinaryNegativeEnvelope OrdinaryPositiveEnvelope

def lowEnvelope (k l c z : ℝ) : ℝ :=
  min (V R k 1 z)
    (min (V R k 1 z+k*(PositiveAngularEnvelope.phi (frameCap-z)-1)+l*(Real.cos frameCap-Real.cos z))
      (min (-(109/200)*tilted c z*(frameCap-z)+V R k 1 frameCap)
        (-(109/200)*tilted c z*(frameCap-z)+V R k l frameCap)))

theorem low_envelope_bounds (k l c z : ℝ) :
    lowEnvelope k l c z≤V R k 1 z ∧
    lowEnvelope k l c z≤V R k 1 z+k*(PositiveAngularEnvelope.phi (frameCap-z)-1)+
      l*(Real.cos frameCap-Real.cos z) ∧
    lowEnvelope k l c z≤-(109/200)*tilted c z*(frameCap-z)+V R k 1 frameCap ∧
    lowEnvelope k l c z≤-(109/200)*tilted c z*(frameCap-z)+V R k l frameCap := by
  unfold lowEnvelope
  exact ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem low_coefficient_data {k l c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : tilted c z∈Icc l ((3/2)*l)) (i : Fin 4) :
    0<pWeights k l (tilted c z) i ∧
      pWeights k l (tilted c z) i≤qWeights k l (tilted c z) i ∧
      qWeights k l (tilted c z) i≤2*pWeights k l (tilted c z) i ∧
      qWeights k l (tilted c z) i≤tilted c z := by
  have hk0 : 0<k := by linarith [hk.1]
  have hl0 : 0<l := by linarith [hl.1]
  fin_cases i
  · change 0<k ∧ k≤1 ∧ 1≤2*k ∧ 1≤tilted c z
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1],hl.1.trans hm.1⟩
  · change 0<k ∧ k≤l ∧ l≤2*k ∧ l≤tilted c z
    exact ⟨hk0,by linarith [hk.2,hl.1],hl.2,hm.1⟩
  · change 0< min l (tilted c z) ∧ min l (tilted c z)≤ max l (tilted c z) ∧
      max l (tilted c z)≤2*min l (tilted c z) ∧ max l (tilted c z)≤tilted c z
    rw [min_eq_left hm.1,max_eq_right hm.1]
    exact ⟨hl0,hm.1,by linarith [hm.2],le_rfl⟩
  · change 0<k ∧ k≤1 ∧ 1≤2*k ∧ 1≤tilted c z
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1],hl.1.trans hm.1⟩

theorem low_pure_lower {k l c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : tilted c z∈Icc l ((3/2)*l)) (hz : z∈Icc 0 (1/6:ℝ)) (j : Fin 4) :
    V R k 1 z≤V R (pWeights k l (tilted c z) j)
      (qWeights k l (tilted c z) j) z := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hk0 : 0<k := by linarith [hk.1]
  have hl0 : 0<l := by linarith [hl.1]
  fin_cases j
  · exact le_rfl
  · change V R k 1 z≤V R k l z
    exact V_short_second_coefficient hk0 (by norm_num) hl.1 hl.2 hz
  · change V R k 1 z≤V R (min l (tilted c z)) (max l (tilted c z)) z
    rw [min_eq_left hm.1,max_eq_right hm.1]
    have hfirst : V R k 1 z≤V R l 1 z := V_first_coefficient (by norm_num)
      (by linarith [hk.1]) (by linarith [hk.2,hl.1])
      (by linarith [hl.2,hk.2]) hz'
    exact hfirst.trans (V_short_second_coefficient hl0 (by norm_num)
      (hl.1.trans hm.1) (by linarith [hm.2]) hz)
  · exact le_rfl

theorem low_positive_lower {k l c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : tilted c z∈Icc l ((3/2)*l)) (hz : z∈Icc 0 frameCap) (i : Fin 4) :
    -(109/200)*tilted c z*(frameCap-z)≤
      Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2) (pWeights k l (tilted c z))
        (qWeights k l (tilted c z)) 3 i (frameCap-z) := by
  have ha : frameCap-z∈Icc 0 frameCap := ⟨by linarith [hz.2],by linarith [hz.1]⟩
  by_cases hi : i=3
  · subst i
    simp only [Hybrid.positive,↓reduceIte]
    have hcoef : GlobalGA.Secondary.diagonal-1/2≤(109/200)*tilted c z := by
      linarith [diagonal_bounds.2,hl.1,hm.1]
    have hh := mul_le_mul_of_nonneg_right hcoef ha.1
    linarith
  · simp only [Hybrid.positive,hi,↓reduceIte]
    have hd := low_coefficient_data hk hl hm i
    have hU : -(109/200)*qWeights k l (tilted c z) i*(frameCap-z)≤
        U R (pWeights k l (tilted c z) i) (qWeights k l (tilted c z) i) (frameCap-z) :=
      U_lower (Real.sqrt_nonneg qCap) radius_sq.le hd.1 hd.2.1 hd.2.2.1 ha
    have hcoef := mul_le_mul_of_nonneg_right hd.2.2.2 ha.1
    generalize U R (pWeights k l (tilted c z) i) (qWeights k l (tilted c z) i) (frameCap-z)=u at hU ⊢
    generalize frameCap-z=w at hU hcoef ⊢
    linarith

theorem low_negative_endpoint_lower {k l c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : tilted c z∈Icc l ((3/2)*l)) (j : Fin 4) :
    min (V R k 1 frameCap) (V R k l frameCap)≤
      V R (pWeights k l (tilted c z) j) (qWeights k l (tilted c z) j) frameCap := by
  fin_cases j
  · exact min_le_left _ _
  · exact min_le_right _ _
  · change min (V R k 1 frameCap) (V R k l frameCap)≤
      V R (min l (tilted c z)) (max l (tilted c z)) frameCap
    rw [min_eq_left hm.1,max_eq_right hm.1]
    have hB : (87/100)*l<V R l (tilted c z) frameCap :=
      V_endpoint_lower sqrt_cap_lower (show 0<l by linarith [hl.1])
        hm.1 (show tilted c z≤2*l by linarith [hm.2,hl.1])
    have hH := H_negative_endpoint_upper (show k∈Icc (1/2:ℝ) (17/20) from
      ⟨by linarith [hk.1],hk.2⟩)
    exact (min_le_left _ _).trans (by linarith [hl.1])
  · exact min_le_left _ _

theorem M_correction (p q z : ℝ) :
    M R p q z=V R p q z+p*(PositiveAngularEnvelope.phi (frameCap-z)-1)+q*(Real.cos frameCap-Real.cos z) := by
  dsimp [M,V]
  ring

theorem low_saturated_lower {k l c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : tilted c z∈Icc l ((3/2)*l)) (hz : z∈Icc 0 (1/6:ℝ)) (i : Fin 4) :
    lowEnvelope k l c z≤Hybrid.saturated R (GlobalGA.Secondary.diagonal-1/2)
      (pWeights k l (tilted c z)) (qWeights k l (tilted c z)) 3 i z := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hb := low_envelope_bounds k l c z
  have hp := low_pure_lower hk hl hm hz i
  fin_cases i
  · change lowEnvelope k l c z≤M R k 1 z
    exact hb.1.trans (M_ge_V (by linarith [hk.1]) (by norm_num)
      (by linarith [hk.1]) hz')
  · change lowEnvelope k l c z≤M R k l z
    rw [M_correction]
    change V R k 1 z≤V R k l z at hp
    linarith [hb.2.1]
  · change lowEnvelope k l c z≤M R (min l (tilted c z)) (max l (tilted c z)) z
    rw [min_eq_left hm.1,max_eq_right hm.1]
    change V R k 1 z≤V R (min l (tilted c z)) (max l (tilted c z)) z at hp
    rw [min_eq_left hm.1,max_eq_right hm.1] at hp
    exact (hb.1.trans hp).trans (M_ge_V (by linarith [hl.1])
      (by linarith [hl.1,hm.1]) hm.2 hz')
  · change lowEnvelope k l c z≤-(GlobalGA.Secondary.diagonal-1/2)*(frameCap-z)+V R k 1 frameCap
    have hD := low_positive_lower hk hl hm hz' (3:Fin 4)
    change -(109/200)*tilted c z*(frameCap-z)≤-(GlobalGA.Secondary.diagonal-1/2)*(frameCap-z) at hD
    linarith [hb.2.2.1]

/-- Every intrinsic alternative lies above the same four explicit
expressions.  No original angle or witness is changed here. -/
theorem low_endpoint_lower {k l c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : tilted c z∈Icc l ((3/2)*l)) (hz : z∈Icc 0 (1/6:ℝ)) (i j : Fin 4) :
    lowEnvelope k l c z≤endpoint k l c z i j := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hb := low_envelope_bounds k l c z
  unfold endpoint
  apply le_min
  · exact hb.1.trans (low_pure_lower hk hl hm hz j)
  · by_cases hij : i=j
    · subst j
      simp only []
      exact low_saturated_lower hk hl hm hz i
    · simp only [ite_eq_right hij]
      have hp := low_positive_lower hk hl hm hz' i
      have hn := low_negative_endpoint_lower hk hl hm j
      have hbase : lowEnvelope k l c z+(109/200)*tilted c z*(frameCap-z)≤
          min (V R k 1 frameCap) (V R k l frameCap) := by
        apply le_min <;> linarith [hb.2.2.1,hb.2.2.2]
      linarith

theorem low_scalars_positive {k l c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : tilted c z∈Icc l ((3/2)*l)) (hz : z∈Icc 0 (1/6:ℝ))
    (hH : 0<baseline k l c z+V R k 1 z)
    (hM : 0<baseline k l c z+V R k 1 z+k*(PositiveAngularEnvelope.phi (frameCap-z)-1)+
      l*(Real.cos frameCap-Real.cos z))
    (hSH : 0<baseline k l c z-(109/200)*tilted c z*(frameCap-z)+V R k 1 frameCap)
    (hSG : 0<baseline k l c z-(109/200)*tilted c z*(frameCap-z)+V R k l frameCap)
    (i j : Fin 4) : 0<baseline k l c z+endpoint k l c z i j := by
  have hlow : 0<baseline k l c z+lowEnvelope k l c z := by
    unfold lowEnvelope
    rw [add_min,add_min,add_min]
    exact lt_min hH (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  linarith [low_endpoint_lower hk hl hm hz i j]

end SquaresInCircles.Eight.GlobalGA.PositiveTD
end
end
end

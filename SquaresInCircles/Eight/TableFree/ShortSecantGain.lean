module

public import SquaresInCircles.Eight.TableFree.GlobalGASecantGain
public import SquaresInCircles.Eight.TableFree.PositiveStressCoefficients

/-!
# The short negative-BT secant gain at every original radius

Uncompiled source. The derivative estimate is uniform for coefficient at
least one half and angle at most 9/100. Integrating the affine derivative
bound gives the strict 131/125 slope needed by the negative-T stress.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortSecantGain
open GlobalGA PositiveStressCoefficients

theorem radius_ratio {q a t : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : 1/2≤a) (ht : t∈Icc 0 (9/100 : ℝ)) :
    Real.sqrt q/Real.sqrt (gainRadicand a t)<89/50 := by
  have hsin : 0≤Real.sin t := (transport_trig ⟨ht.1,by linarith [ht.2]⟩).2.2.1
  have hs : Real.sin t≤9/100 := (Real.sin_le ht.1).trans ht.2
  have hs2 := pow_le_pow_left₀ hsin hs 2
  have ha2 := pow_le_pow_left₀ (show (0:ℝ)≤1/2 by norm_num) ha 2
  have hc2 : 1-(9/100 : ℝ)^2≤(Real.cos t)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hprod := mul_le_mul ha2 hc2 (by norm_num) (sq_nonneg a)
  have hrad : 1+(1/4 : ℝ)*(1-(9/100)^2)≤gainRadicand a t := by
    dsimp [gainRadicand]
    nlinarith
  have hreserve : qCap<(89/50 : ℝ)^2*(1+(1/4)*(1-(9/100)^2)) := by norm_num [qCap]
  have hh := mul_le_mul_of_nonneg_left hrad (sq_nonneg (89/50 : ℝ))
  have hz := Real.sqrt_pos.mpr (gainRadicand_pos a t)
  have hlt : q<(89/50 : ℝ)^2*gainRadicand a t := hQ.trans_lt (hreserve.trans_le hh)
  have hroot := Real.sqrt_lt_sqrt hq hlt
  rw [Real.sqrt_mul (by norm_num),Real.sqrt_sq (by norm_num)] at hroot
  exact (div_lt_iff₀ hz).2 hroot

theorem derivative_affine_lower {q a t : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : 1/2≤a) (ht : t∈Icc 0 (9/100 : ℝ)) :
    13/12-(39/50)*t≤ secantGainDeriv q a t := by
  have hr := radius_ratio hq hQ ha ht
  obtain ⟨hc,hcu,hs0,hs,hsc⟩ := transport_trig ⟨ht.1,by linarith [ht.2]⟩
  have hst := Real.sin_le ht.1
  have hm := mul_le_mul_of_nonneg_right hr.le hs0
  have hlow : 0≤(13/12 : ℝ)-(39/50)*t := by linarith [ht.2]
  have hc2 : (Real.cos t)^2≤1 := by nlinarith
  have hcpos : 0<Real.cos t := by linarith
  have hp := mul_nonneg hlow (sub_nonneg.mpr hc2)
  unfold secantGainDeriv
  apply (le_div_iff₀ (sq_pos_of_pos hcpos)).2
  have he : Real.sqrt q*Real.sin t/Real.sqrt (gainRadicand a t)=
      (Real.sqrt q/Real.sqrt (gainRadicand a t))*Real.sin t := by ring
  rw [he]
  nlinarith

theorem quadratic_lower {q a t : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : 1/2≤a) (ht : t∈Icc 0 (9/100 : ℝ)) :
    (13/12)*t-(39/100)*t^2≤ secantGain q a t := by
  let f : ℝ → ℝ := fun x => secantGain q a x-(13/12)*x+(39/100)*x^2
  have hd : ∀ x∈Icc 0 (9/100 : ℝ), HasDerivAt f
      (secantGainDeriv q a x-13/12+(39/50)*x) x := by
    intro x hx
    have hc := transport_cos_pos (by rw [abs_of_nonneg hx.1]; linarith [hx.2])
    convert ((secantGain_hasDerivAt q a hc.ne').sub
      ((hasDerivAt_id x).const_mul (13/12 : ℝ))).add
        (((hasDerivAt_id x).pow 2).const_mul (39/100 : ℝ)) using 1
    · rfl
    · simp only [id]
      ring
  have hm : MonotoneOn f (Icc 0 (9/100 : ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => hd x (Ioo_subset_Icc_self hx)
    · intro x hx
      have hh := derivative_affine_lower hq hQ ha (Ioo_subset_Icc_self hx)
      linarith
  have hh := hm (show (0:ℝ)∈Icc 0 (9/100) by constructor <;> norm_num) ht ht.1
  dsimp [f] at hh
  rw [secantGain_zero] at hh
  nlinarith

theorem strict_gain {q a t : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : 1/2≤a) (ht : t∈Ioc 0 (9/100 : ℝ)) :
    (131/125)*t<secantGain q a t := by
  have hh := quadratic_lower hq hQ ha (Ioc_subset_Icc_self ht)
  have hm := mul_le_mul_of_nonneg_left ht.2 ht.1.le
  have ht0 := ht.1
  nlinarith

theorem negative_family_slopes {d : ℝ} (hd : d∈Icc 0 frameCap) :
    lambdaN d≤103/100 ∧ lambdaN d<(103/100)*cN d ∧
      lambdaN d<(131/125)*cN d ∧ k<1/cN d ∧
      1/2≤lN d/cN d := by
  have hb := coefficient_bounds hd
  have hc0 : 0<cN d := by dsimp [cN,frameCap] at *; nlinarith [hd.1,hd.2]
  have hchord := mul_nonneg hd.1 (sub_nonneg.mpr hd.2)
  have hcup : cN d≤2069/2000 := by
    dsimp [cN,frameCap] at *
    nlinarith
  refine ⟨?_,?_,?_,?_,?_⟩
  · dsimp [lambdaN,frameCap] at *; linarith [hd.2]
  · dsimp [lambdaN,cN,frameCap] at *; nlinarith
  · dsimp [lambdaN,cN,frameCap] at *; nlinarith
  · apply (lt_div_iff₀ hc0).2
    dsimp [k]
    linarith
  · apply (le_div_iff₀ hc0).2
    dsimp [lN,cN,frameCap] at *
    nlinarith

theorem negative_BT_gain {q d t : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (hd : d∈Icc 0 frameCap) (ht : t∈Ioc 0 (9/100 : ℝ)) :
    lambdaN d*t<cN d*secantGain q (lN d/cN d) t := by
  have hb := negative_family_slopes hd
  have hc0 : 0<cN d := by
    have := coefficient_bounds hd
    dsimp [cN,frameCap] at *
    nlinarith [hd.1,hd.2]
  have hgain := mul_lt_mul_of_pos_left (strict_gain hq hQ hb.2.2.2.2 ht) hc0
  have hcoeff := mul_lt_mul_of_pos_right hb.2.2.1 ht.1
  nlinarith

end SquaresInCircles.Eight.TableFree.ShortSecantGain

module

public import SquaresInCircles.Eight.TableFree.CriticalPositiveTCoefficients
public import SquaresInCircles.Eight.TableFree.HalfRatioNormGain

/-!
# The critical coefficient-loss estimates

Uncompiled transcription of the positive-squaring argument (24). The
factored cubic proves the uniform .4 bound for the normalized gain
integrand at every actual sine argument. Integration in the angle and
then in the coefficient gives the BT-to-TD comparison on the full
coefficient segment. The short A estimate is its stated .5 consequence.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalPositiveTNormGain
open SoleNormGain PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeEnvelope
open VaryingBFunctions VaryingBComparison

theorem integrand_upper {r s : ℝ} (hr : r∈Icc (61/100:ℝ) (71/100))
    (hs : s∈Icc 0 frameCap) : integrand r s≤1/5 := by
  have hN := root_pos r hs
  have hN2 := root_sq r hs
  have hr0 : 0≤r := by linarith [hr.1]
  by_cases hsr : r ≤ s
  · have hnum : r^2*(r-s)≤0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) (by linarith)
    have hdiv : integrand r s≤0 := div_nonpos_of_nonpos_of_nonneg hnum (pow_pos hN 3).le
    linarith
  · have hx : 0≤r-s := by linarith [lt_of_not_ge hsr]
    have hr2 : r^2≤(71/100:ℝ)^2 := pow_le_pow_left₀ hr0 hr.2 2
    have ha : 0≤1-r^2 := by nlinarith
    have hfactor : 0≤(1-r^2-r*(r-s))^2*(1-r^2+8*r*(r-s)) :=
      mul_nonneg (sq_nonneg _) (by nlinarith [mul_nonneg hr0 hx])
    have hremain : 0≤r^2*(r-s)^2*(27*(1-r^2)-25*r^2) := by
      exact mul_nonneg (mul_nonneg (sq_nonneg r) (sq_nonneg (r-s))) (by nlinarith)
    have hid : (1+r^2-2*r*s)^3-(5*r^2*(r-s))^2=
        (1-r^2-r*(r-s))^2*(1-r^2+8*r*(r-s))+
        r^2*(r-s)^2*(27*(1-r^2)-25*r^2) := by ring
    have hsquare : (5*r^2*(r-s))^2≤((root r s)^3)^2 := by
      have he : ((root r s)^3)^2=((root r s)^2)^3 := by ring
      rw [he,hN2]
      nlinarith only [hid,hfactor,hremain]
    have hcross : 5*r^2*(r-s)≤(root r s)^3 := by
      nlinarith [mul_nonneg (by positivity : 0≤5*r^2) hx,pow_nonneg hN.le 3]
    dsimp [integrand]
    apply (div_le_iff₀ (pow_pos hN 3)).2
    linarith

theorem scaled_integrand_upper {R r s : ℝ} (hR : R∈Icc 0 2)
    (hr : r∈Icc (61/100:ℝ) (71/100)) (hs : s∈Icc 0 frameCap) :
    R*integrand r s≤2/5 := by
  have hh := mul_le_mul_of_nonneg_left (integrand_upper hr hs) hR.1
  nlinarith [hR.2]

theorem scaled_gain {R r s : ℝ} (hR : R∈Icc 0 2)
    (hr : r∈Icc (61/100:ℝ) (71/100)) (hs : s∈Icc 0 frameCap) :
    R*gain r (Real.sin s)≤(2/5)*s := by
  have hsin := sin_mem hs
  have hh := derivative_reserve
    (f:=fun v => -R*gain r v) (df:=fun v => -R*integrand r v) (k:= -(2/5:ℝ))
    (fun v hv => ((gain_hasDerivAt_u r hv).const_mul (-R)).continuousAt.continuousWithinAt)
    (fun v hv => (gain_hasDerivAt_u r (Ioo_subset_Icc_self hv)).const_mul (-R))
    (fun v hv => by linarith [scaled_integrand_upper hR hr (Ioo_subset_Icc_self hv)])
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hsin hsin.1
  have hz : gain r 0=0 := by simp [gain,root,OrdinaryCurvatureBounds.shape]
  rw [hz] at hh
  nlinarith [Real.sin_le hs.1]

theorem coefficient_loss {R p a b s : ℝ} (hR : R∈Icc 0 2)
    (ha : 0<a) (hab : a≤b) (hplo : (61/100)*b≤p) (hphi : p≤(71/100)*a)
    (hs : s∈Icc 0 frameCap) :
    normGain R p b s-normGain R p a s≤(2/5)*s*(b-a) := by
  have hp : 0<p := by nlinarith
  have hx (x : ℝ) (hxx : x∈Icc a b) : 0<x ∧ p/x∈Icc (61/100:ℝ) (71/100) := by
    have hxp : 0<x := ha.trans_le hxx.1
    refine ⟨hxp,⟨(le_div_iff₀ hxp).2 ?_,(div_le_iff₀ hxp).2 ?_⟩⟩ <;>
      nlinarith [hxx.1,hxx.2]
  have hh := derivative_reserve
    (f:=fun x => -normGain R p x s)
    (df:=fun x => -(R*gain (p/x) (Real.sin s))) (k:= -(2/5)*s)
    (fun x hxx => (normGain_hasDerivAt_large hp (hx x hxx).1 hs).neg.continuousAt.continuousWithinAt)
    (fun x hxx => (normGain_hasDerivAt_large hp (hx x (Ioo_subset_Icc_self hxx)).1 hs).neg)
    (fun x hxx => by linarith [scaled_gain hR (hx x (Ioo_subset_Icc_self hxx)).2 hs])
    (show a∈Icc a b from ⟨le_rfl,hab⟩) (show b∈Icc a b from ⟨hab,le_rfl⟩) hab
  linarith

theorem coefficient_short {R p a b s : ℝ} (hR : R∈Icc 0 2)
    (ha : 0<a) (hab : a≤b) (hplo : (61/100)*b≤p) (hphi : p≤(27/40)*a)
    (hs : s∈Icc 0 (4/25:ℝ)) :
    normGain R p b s-normGain R p a s≤(1/2)*s*(b-a) := by
  have hh := coefficient_loss hR ha hab hplo (show p≤(71/100)*a by nlinarith)
    (show s∈Icc 0 frameCap from ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩)
  have hprod := mul_nonneg hs.1 (sub_nonneg.mpr hab)
  nlinarith

end SquaresInCircles.Eight.TableFree.CriticalPositiveTNormGain

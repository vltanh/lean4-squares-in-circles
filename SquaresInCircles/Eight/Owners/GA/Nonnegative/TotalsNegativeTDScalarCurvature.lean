module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNegativeTDData
public import SquaresInCircles.Eight.Owners.GA.Positive.ANegativeTDASupport
public import SquaresInCircles.Eight.Frames.Ordinary.NegativeSlope
public import SquaresInCircles.Eight.Owners.SplitConcavityTools

/-!
# Eight squares: the exact one-variable reduction of the three negative endpoints

At fixed E total all
coefficients are fixed, and the A charge has argument delta-e. Its
actual C1 join is at delta=e+alpha. The proof covers that join and the
case in which it lies beyond the interval, without inserting a new
partition into the two-dimensional polynomial domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.NegativeTD
open Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeSlope TwoPositive.ASupport

theorem negative_curvature {p q t : ℝ} (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (ht : t∈Icc 0 frameCap) : curvature R p q (-t)-q*Real.cos t< -(81/1250)*q := by
  have hq := hp.trans_le hpq
  have hc := curvature_constant_bounds (Real.sqrt_nonneg qCap) radius_sq.le hp hpq hqp
  have hn := curvature_negative_upper (Real.sqrt_nonneg qCap) hp hq
    (show -t∈Icc (-frameCap) 0 from ⟨by linarith [ht.2],by linarith [ht.1]⟩)
  have hcos := mul_lt_mul_of_pos_left (transport_trig ht).1 hq
  linarith [hc.2.2.1]

theorem shifted_charge_concave {w E : ℝ} {f df ddf : ℝ→ℝ}
    (hw : 0≤w) (hE : E∈Icc 0 frameCap)
    (hf : ∀t∈Icc E frameCap,HasDerivAt f (df t) t)
    (hdf : ∀t∈Icc E frameCap,HasDerivAt df (ddf t) t)
    (hcurv : ∀t∈Icc E frameCap,ddf t≤-w/50) :
    ConcaveOn ℝ (Icc E frameCap) (fun t => w*charge (t-E)+f t) := by
  let left : ℝ→ℝ := fun t => w*axialCharge (t-E)+f t
  let right : ℝ→ℝ := fun t => w*circleCharge (t-E)+f t
  have harg {t : ℝ} (ht : t∈Icc E frameCap) : t-E∈Icc 0 frameCap :=
    ⟨by linarith [ht.1],by linarith [ht.2,hE.1]⟩
  have leftD {t : ℝ} (ht : t∈Icc E frameCap) :
      HasDerivAt left (w*axialD (t-E)+df t) t :=
    (((axial_derivative (t-E)).comp_sub_const t E).const_mul w).fun_add (hf t ht)
  have rightD {t : ℝ} (ht : t∈Icc E frameCap) :
      HasDerivAt right (w*circleD (t-E)+df t) t :=
    (((circle_derivative (t-E)).comp_sub_const t E).const_mul w).fun_add (hf t ht)
  have leftDD {t : ℝ} (ht : t∈Icc E frameCap) :
      HasDerivAt (fun t => w*axialD (t-E)+df t) (w*axialDD (t-E)+ddf t) t :=
    (((axial_second (t-E)).comp_sub_const t E).const_mul w).fun_add (hdf t ht)
  have rightDD {t : ℝ} (ht : t∈Icc E frameCap) :
      HasDerivAt (fun t => w*circleD (t-E)+df t) (w*circleDD (t-E)+ddf t) t :=
    (((circle_second (t-E)).comp_sub_const t E).const_mul w).fun_add (hdf t ht)
  have leftConcave {U : ℝ} (hU : U∈Icc E frameCap) (hcut : U-E≤TwoPositive.ASupport.alpha) :
      ConcaveOn ℝ (Icc E U) left := by
    apply concave_of_deriv2
      (fun t ht => leftD ⟨ht.1,ht.2.trans hU.2⟩)
      (fun t ht => leftDD ⟨ht.1,ht.2.trans hU.2⟩)
    intro t ht
    have ht' : t∈Icc E frameCap := ⟨ht.1,ht.2.trans hU.2⟩
    have haxis := PositiveANegativeTD.ABounds.axial_second_upper
      (show t-E∈Icc 0 TwoPositive.ASupport.alpha from ⟨by linarith [ht.1],by linarith [ht.2]⟩)
    have hp := mul_le_mul_of_nonneg_left haxis.le hw
    linarith [hcurv t ht']
  by_cases hcut : frameCap≤E+TwoPositive.ASupport.alpha
  · have hl := leftConcave ⟨hE.2,le_rfl⟩ (by linarith)
    refine hl.congr fun t ht => ?_
    have hh : t-E≤TwoPositive.ASupport.alpha := by linarith [ht.2]
    simp only [left,TwoPositive.ASupport.charge,hh,↓reduceIte]
  · have hjoin : E+TwoPositive.ASupport.alpha∈Icc E frameCap :=
      ⟨by linarith [alpha_bounds.1],(lt_of_not_ge hcut).le⟩
    have hl := leftConcave hjoin (by rw [add_sub_cancel_left])
    have hr : ConcaveOn ℝ (Icc (E+TwoPositive.ASupport.alpha) frameCap) right := by
      apply concave_of_deriv2
        (fun t ht => rightD ⟨hjoin.1.trans ht.1,ht.2⟩)
        (fun t ht => rightDD ⟨hjoin.1.trans ht.1,ht.2⟩)
      intro t ht
      have ht' : t∈Icc E frameCap := ⟨hjoin.1.trans ht.1,ht.2⟩
      have hc := mul_nonpos_of_nonneg_of_nonpos hw (circle_curvature (harg ht'))
      linarith [hcurv t ht']
    have he : left (E+TwoPositive.ASupport.alpha)=right (E+TwoPositive.ASupport.alpha) := by
      simp only [left,right,add_sub_cancel_left,transition_value]
    have hdL := leftD hjoin
    have hdR := rightD hjoin
    simp only [add_sub_cancel_left] at hdL hdR
    rw [←transition_derivative] at hdR
    have hj := SplitConcavityTools.join hjoin hl hr he hdL hdR
    refine hj.congr fun t ht => ?_
    by_cases hh : t≤E+TwoPositive.ASupport.alpha
    · have ha : t-E≤TwoPositive.ASupport.alpha := by linarith
      simp only [left,TwoPositive.ASupport.charge,hh,ha,↓reduceIte]
    · have ha : ¬t-E≤TwoPositive.ASupport.alpha := by intro h; exact hh (by linarith)
      simp only [right,TwoPositive.ASupport.charge,hh,ha,↓reduceIte]

theorem negativeScalar_concave (i : Fin 3) {E : ℝ} (hE : E∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc E frameCap) (fun t => negativeScalar i t E) := by
  have hc := coefficients hE i.castSucc
  have hq := hc.1.trans_le hc.2.1
  have hl := ranges hE
  have ht {t : ℝ} (ht : t∈Icc E frameCap) : t∈Icc 0 frameCap := ⟨hE.1.trans ht.1,ht.2⟩
  have hh := shifted_charge_concave (w:=l E) (by linarith [hl.2.2.1]) hE
    (f:=fun t => base E+TwoPositive.ASupport.charge E+V R (p E i.castSucc) (q E i.castSucc) t)
    (df:=Vd R (p E i.castSucc) (q E i.castSucc))
    (ddf:=fun t => curvature R (p E i.castSucc) (q E i.castSucc) (-t)-q E i.castSucc*Real.cos t)
    (fun t ht' => (V_hasDerivAt hc.1 hq (ht ht')).const_add
      (base E+TwoPositive.ASupport.charge E))
    (fun t ht' => Vd_hasDerivAt hc.1 hq (ht ht'))
    (fun t ht' => by
      have hn := negative_curvature hc.1 hc.2.1 (by linarith [hc.2.2.1]) (ht ht')
      linarith [hl.2.2.2.1,hc.2.2.2.1])
  convert hh using 1
  funext t
  dsimp [negativeScalar,primaryCost]
  ring

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.NegativeTD

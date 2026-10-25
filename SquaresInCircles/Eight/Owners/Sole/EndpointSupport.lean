module

public import SquaresInCircles.Eight.Owners.Sole.SplitModel

/-!
# Eight squares: the actual-radius E supports at the two intrinsic split endpoints

The high endpoint uses the complete circle support
in the positive folded direction. For sole-DE this support dominates
the work at the actual axis point of the same circle. No original
point is moved to that axis point, and no radius is enlarged.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleEndpointSupport
open Candidate SignedStress SoleECoefficients SoleResiduals SoleSplitModel

def highWork (R t : ℝ) : ℝ :=
  2*R*Real.sin (t/2)-(Real.sin t+1-Real.cos t)/2

def endpointWork (b : Band) (de : Bool) (R M t : ℝ) : ℝ :=
  if b=.high then highWork R t
  else if de then M*Real.sin t else sigma R (eta b t)*Real.sin t

theorem high_circle_support (R : ℝ) {t : ℝ} (ht : t∈Icc 0 frameCap) :
    circleSupport R (Real.sin t,1-Real.cos t)=highWork R t := by
  have hs := (transport_trig ht).2.2.1
  have hc : 0≤1-Real.cos t := sub_nonneg.mpr (Real.cos_le_one t)
  have hh : t/2∈Icc 0 frameCap := by
    have h1 := ht.1
    have h2 := ht.2
    simp only [frameCap] at h2 ⊢
    constructor <;> linarith
  have hsh := (transport_trig hh).2.2.1
  have hdouble := Real.cos_two_mul (t/2)
  rw [show 2*(t/2)=t by ring] at hdouble
  have hcos : Real.cos t=1-2*(Real.sin (t/2))^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (t/2)]
  have hnorm : (Real.sin t)^2+(1-Real.cos t)^2=(2*Real.sin (t/2))^2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  simp only [circleSupport,hnorm,Real.sqrt_sq_eq_abs,abs_of_nonneg hs,
    abs_of_nonneg hc,abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hsh),highWork]
  ring

theorem actual_axis {q : ℝ} (hq : qLow≤q) :
    0<axisCoordinate q ∧ (⟨axisCoordinate q,0⟩ : SignedPoint).Contained q := by
  have hq' : 0≤q-1/4 := by dsimp [qLow] at hq; linarith
  have hs := Real.sqrt_nonneg (q-1/4)
  have hsq := Real.sq_sqrt hq'
  constructor
  · dsimp [axisCoordinate]
    dsimp [qLow] at hq
    nlinarith
  · change (axisCoordinate q+1/2)^2+(|0|+1/2)^2≤q
    simp only [axisCoordinate,abs_zero]
    nlinarith

theorem primary_le_axis {q : ℝ} {p : SignedPoint}
    (hq : qLow≤q) (hs : p.Sorted) (hc : p.Contained q) : p.a≤axisCoordinate q := by
  have hq' : 0≤q-1/4 := by dsimp [qLow] at hq; linarith
  have hroot := Real.sqrt_nonneg (q-1/4)
  have hsq := Real.sq_sqrt hq'
  have hcircle : (p.a+1/2)^2+(|p.y|+1/2)^2≤q := hc
  have hsmall : (p.a+1/2)^2≤q-1/4 := by
    nlinarith [abs_nonneg p.y,sq_nonneg |p.y|]
  dsimp [axisCoordinate]
  nlinarith [hs.1]

theorem axis_work_le {q t : ℝ} (hq : qLow≤q) (ht : t∈Icc 0 frameCap) :
    axisCoordinate q*Real.sin t≤highWork (Real.sqrt q) t := by
  obtain ⟨ha,hc⟩ := actual_axis hq
  have hq0 : 0≤q := by dsimp [qLow] at hq; linarith
  have hs : (⟨axisCoordinate q,0⟩ : SignedPoint).Sorted := by
    exact ⟨ha,by simpa using ha.le⟩
  have hc' : (⟨axisCoordinate q,0⟩ : SignedPoint).Contained ((Real.sqrt q)^2) := by
    simpa only [Real.sq_sqrt hq0] using hc
  have hw := work_le_circleSupport (Real.sqrt_nonneg q) hs hc'
    (Real.sin t,1-Real.cos t)
  rw [high_circle_support (Real.sqrt q) ht] at hw
  simpa [work,mul_comm] using hw

theorem folded_work_le {p : SignedPoint} {R t : ℝ} (hR : 0≤R)
    (hs : p.Sorted) (hc : p.Contained (R^2)) (ht : t∈Icc 0 frameCap) :
    p.a*Real.sin t+|p.y| *(1-Real.cos t)≤highWork R t := by
  let pf : SignedPoint := ⟨p.a,|p.y|⟩
  have hsf : pf.Sorted := ⟨hs.1,by simpa [pf] using hs.2⟩
  have hcf : pf.Contained (R^2) := by simpa [pf,SignedPoint.Contained,SignedPoint.circle] using hc
  have hh := work_le_circleSupport hR hsf hcf (Real.sin t,1-Real.cos t)
  rw [high_circle_support R ht] at hh
  simpa [work,pf,mul_comm] using hh

theorem at_G (C : SignedCycle) (b : Band) (de : Bool) (R M t : ℝ) :
    eBound C b de R M t 0=0 := by
  cases b <;> cases de <;> simp [eBound]

theorem at_E {C : SignedCycle} {b : Band} (de : Bool) {q t : ℝ}
    (hq : qLow≤q) (ht : t∈domain b)
    (hs : (C.point E).Sorted) (hc : (C.point E).Contained q) :
    eBound C b de (Real.sqrt q) (axisCoordinate q) t t≤
      endpointWork b de (Real.sqrt q) (axisCoordinate q) t := by
  have hq0 : 0≤q := by dsimp [qLow] at hq; linarith
  by_cases hb : b=.high
  · subst b
    cases de
    · have hh := folded_work_le (Real.sqrt_nonneg q) hs
        (by simpa only [Real.sq_sqrt hq0] using hc) (angle ht)
      simpa [eBound,endpointWork] using hh
    · simpa [eBound,endpointWork] using axis_work_le hq (angle ht)
  · simp [eBound,endpointWork,hb]

end SquaresInCircles.Eight.SoleEndpointSupport

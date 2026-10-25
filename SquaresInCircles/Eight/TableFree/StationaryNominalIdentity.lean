module

public import SquaresInCircles.Eight.TableFree.StationaryCanonicalCorrection

/-!
# The nominal stress is the actual position envelope

Uncompiled reconstruction.  The four successive circle points and the
closing point are kept as explicit own-frame points.  Position
stationarity balances the E force; all other force balances are the
definitions of the five masses.  Consequently the nominal defect is
exactly the closing mass times the actual five-corner defect.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.StationaryTerminal
open ExactFamily.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

/-- Original-anchor order A,B,D,E,H.  The final point need not lie on the
circle: its actual radial excess is the five-corner defect. -/
def nominalPoints (q u h : ℝ) : Fin 5 → SignedPoint := ![
  ⟨lowerRight q u-1/2,u-1/2⟩,
  ⟨topRight q u-1/2,(2-u)-1/2⟩,
  ⟨topHeight q u-1/2,topLeft q u-1/2⟩,
  ⟨lowerLeft q u-1/2,lowerHeight q u-1/2⟩,
  ⟨secondComponent q (cosine h) (sine h) u-1/2,
    firstComponent q (cosine h) (sine h) u-1/2⟩]

theorem nominal_y_nonneg {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) (i : Fin 5) :
    0≤(nominalPoints q u h i).y := by
  have hr := radical_bounds hq hu
  have hf := force_bounds hq hu hh
  fin_cases i <;> simp only [nominalPoints,Matrix.cons_val,Fin.reduceFinMk] <;>
    linarith [hu.1,hu.2,hr.V_lower,hr.v_lower,hf.k1_lower]

theorem nominal_circles {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) (i : Fin 5) :
    (nominalPoints q u h i).circle=
      (![q,q,q,q,q+ExactFamily.FiveCornerGeometry.defect q (cosine h) (sine h) u] i) := by
  have hd := (radical_bounds hq hu).smoothDomain (by linarith [hq.2])
    (by linarith [hu.1])
  have hA : lowerRight q u^2+u^2=q := upper_circle hd.toDomain.first_radicand
  have hB : topRight q u^2+(2-u)^2=q := upper_circle hd.toDomain.second_radicand
  have hD : topHeight q u^2+topLeft q u^2=q := upper_circle hd.toDomain.third_radicand
  have hE : lowerLeft q u^2+lowerHeight q u^2=q := upper_circle hd.toDomain.fourth_radicand
  rw [SignedPoint.circle,abs_of_nonneg (nominal_y_nonneg hq hu hh i)]
  fin_cases i <;> simp only [nominalPoints,Matrix.cons_val,Fin.reduceFinMk,
    ExactFamily.FiveCornerGeometry.defect,sub_add_cancel]
  · exact hA
  · exact hB
  · exact hD
  · exact hE
  · ring

/-- The E tangential force balance is precisely the actual position
stationarity equation. -/
theorem delta_cancellation {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (hz : positionHalf q (cosine h) (sine h) u=0) :
    (weights q u h).delta-(weights q u h).epsilon*cosine h=
      (weights q u h).epsilon*sine h*lowerHeight q u/lowerLeft q u := by
  have hr := radical_bounds hq hu
  have hV : topLeft q u≠0 := ne_of_gt (by linarith [hr.V_lower])
  have hY : topHeight q u≠0 := ne_of_gt (by linarith [hr.Y_lower])
  have hw : lowerLeft q u≠0 := ne_of_gt (by linarith [hr.w_lower])
  dsimp only [weights]
  rw [rawBeta_cancellation hq hu hh hz,sine_eq]
  field_simp [hV,hY,hw]
  ring

theorem nominal_force_balance {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (hz : positionHalf q (cosine h) (sine h) u=0) (i : Fin 5) :
    forces (weights q u h) (Real.arctan h) 0 (Real.arctan h) 0 i=
      (2*(weights q u h).mu i*((nominalPoints q u h i).a+1/2),
       2*(weights q u h).mu i*((nominalPoints q u h i).y+1/2)) := by
  have hr := radical_bounds hq hu
  have hf := force_bounds hq hu hh
  have hrn : lowerRight q u≠0 := ne_of_gt (by linarith [hr.r_lower])
  have hln : 2-u≠0 := ne_of_gt (by linarith [hu.2])
  have hVn : topLeft q u≠0 := ne_of_gt (by linarith [hr.V_lower])
  have hwn : lowerLeft q u≠0 := ne_of_gt (by linarith [hr.w_lower])
  have hKn : firstComponent q (cosine h) (sine h) u≠0 :=
    ne_of_gt (by linarith [hf.k1_lower])
  have hc : Real.cos (Real.arctan h)=cosine h := rfl
  have hs : Real.sin (Real.arctan h)=sine h := rfl
  have hdc := delta_cancellation hq hu hh hz
  fin_cases i <;> apply Prod.ext <;>
    simp only [forces,nominalPoints,Matrix.cons_val,Fin.reduceFinMk,Real.cos_zero,Real.sin_zero,
      hc,hs,mul_one,mul_zero,div_one,sub_zero,sub_add_cancel]
  all_goals try (rw [hdc])
  all_goals simp only [weights,rawMass,rawAlpha,rawBeta,rawEpsilon,positionA,Matrix.cons_val]
  all_goals field_simp
  all_goals ring

theorem nominal_center_loss {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (hz : positionHalf q (cosine h) (sine h) u=0) :
    centerLoss (weights q u h) (Real.arctan h) 0 (Real.arctan h) 0
      (nominalPoints q u h)=0 := by
  have hm := (positive hq hu hh).2.2.2.2.2
  unfold centerLoss
  apply Finset.sum_eq_zero
  intro i _
  rw [centerSquare,nominal_force_balance hq hu hh hz i]
  have hmi := (hm i).ne'
  have e1 : 2*(weights q u h).mu i*((nominalPoints q u h i).a+1/2)/(2*(weights q u h).mu i)=
      (nominalPoints q u h i).a+1/2 := by field_simp
  have e2 : 2*(weights q u h).mu i*((nominalPoints q u h i).y+1/2)/(2*(weights q u h).mu i)=
      (nominalPoints q u h i).y+1/2 := by field_simp
  dsimp only
  rw [e1,e2]
  ring

theorem nominal_circle_loss {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    circleLoss q (weights q u h) (nominalPoints q u h)=
      -(weights q u h).mu 4*ExactFamily.FiveCornerGeometry.defect q (cosine h) (sine h) u := by
  simp only [circleLoss,nominal_circles hq hu hh,Fin.sum_univ_five,Matrix.cons_val]
  ring

/-- All five nominal contacts are equalities before any stationary or
zero-defect equation is imposed. -/
theorem nominal_contact_identity (q u h : ℝ) (w : CanonicalNegativeStress.Parameters) :
    demand w (Real.arctan h) 0 (Real.arctan h) 0-
      ∑i : Fin 5,work (forces w (Real.arctan h) 0 (Real.arctan h) 0 i)
        (nominalPoints q u h i)=0 := by
  simp only [demand,forces,work,nominalPoints,Fin.sum_univ_five,Matrix.cons_val,
    W,NegativeCaptureStress.W,NegativeLargeDEStress.W,Real.cos_zero,Real.sin_zero,Real.tan_zero]
  dsimp only [firstComponent,secondComponent,topLeft,lowerHeight,cosine,sine]
  ring

/-- Exact radial completion at the actual position root; no zero-defect
or tilt-stationarity premise is used. -/
theorem nominal_defect_identity {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (hz : positionHalf q (cosine h) (sine h) u=0) :
    CanonicalNegativeStress.defect q (weights q u h)
      (Real.arctan h) 0 (Real.arctan h) 0=
      (weights q u h).mu 4*ExactFamily.FiveCornerGeometry.defect q (cosine h) (sine h) u := by
  have hm : ∀i,(weights q u h).mu i≠0 := fun i => ((positive hq hu hh).2.2.2.2.2 i).ne'
  have hid := exact_identity hm (nominal_y_nonneg hq hu hh)
    q (Real.arctan h) 0 (Real.arctan h) 0
  rw [nominal_center_loss hq hu hh hz,nominal_circle_loss hq hu hh,
    nominal_contact_identity] at hid
  linarith

theorem minimizing_nominal_defect {q t : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    CanonicalNegativeStress.defect q (minimizingWeights q t) t 0 t 0=
      (minimizingWeights q t).mu 4*positionEnvelope q t := by
  obtain ⟨hh,hat⟩ := terminal_tangent ht
  obtain ⟨huL,_,_,huU⟩ := minimizingPosition_terminal hq ht
  have hid := nominal_defect_identity hq ⟨huL.le,huU.le⟩ hh
    (minimizingPosition_chart_root hq ht)
  rw [hat] at hid
  rw [positionEnvelope_eq]
  change CanonicalNegativeStress.defect q (weights q (minimizingPosition q t) (Real.tan t))
    t 0 t 0=(weights q (minimizingPosition q t) (Real.tan t)).mu 4*
      ExactFamily.FiveCornerGeometry.defect q (Real.cos t) (Real.sin t) (minimizingPosition q t)
  simpa only [cosine,sine,hat] using hid

end SquaresInCircles.Eight.TableFree.StationaryTerminal

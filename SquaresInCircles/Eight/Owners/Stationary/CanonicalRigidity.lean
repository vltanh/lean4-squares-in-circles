module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Owners.Canonical.NominalFlux
public import SquaresInCircles.Eight.Owners.Stationary.FluxBounds
public import SquaresInCircles.Eight.Owners.Stationary.PositionBounds

/-!
# Eight squares: equality identifies the five anchors

When the radial and center losses vanish (`circle_loss_zero`, `center_loss_zero`), every anchor is
its nominal point (`nominal_points_of_center_loss`); the envelope of positions then identifies the
tilt and the whole stationary chain (`stationary_rigidity`). The circle equalities come from the
anchors themselves, not from a moved intermediate point.
-/

section
/-!
## The two-error correction at the actual varying position minimum

This module discharges every coefficient,
flux, and primitive estimate in the quantitative correction theorem by
the actual nested-circle minimizer.  The only remaining error hypotheses
are the canonical nonnegative angles and their proved geometric sum.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.StationaryTerminal
open Stationary.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

def minimizingWeights (q t : ℝ) : CanonicalNegativeStress.Parameters :=
  weights q (minimizingPosition q t) (Real.tan t)

theorem minimizingPosition_chart_root {q t : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    positionHalf q (cosine (Real.tan t)) (sine (Real.tan t)) (minimizingPosition q t)=0 := by
  obtain ⟨hh,hat⟩ := terminal_tangent ht
  have hz := minimizingPosition_root (by nlinarith [hq.1] : (79/40:ℝ)^2≤q) hq.2
    (arctan_mem_tiltInterval hh)
  rw [hat] at hz
  dsimp [jointPosition] at hz
  rw [cosine,sine,hat]
  linarith

theorem minimizingWeights_positive {q t : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (ht : t∈Icc (1/10:ℝ) (4/25)) : (minimizingWeights q t).Positive := by
  have hu := minimizingPosition_terminal hq ht
  exact positive hq ⟨hu.1.le,hu.2.2.2.le⟩ (terminal_tangent ht).1

theorem minimizingWeights_mass {q t : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (ht : t∈Icc (1/10:ℝ) (4/25)) : massSum (minimizingWeights q t)=1 := by
  have hu := minimizingPosition_terminal hq ht
  exact mass_one hq ⟨hu.1.le,hu.2.2.2.le⟩ (terminal_tangent ht).1

theorem actual_correction_lower {q α t e : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hα : α∈Icc (1/10:ℝ) (4/25))
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) (hu : t+e≤α) :
    (t+e)/5000≤correction (minimizingWeights q α) α t e := by
  obtain ⟨hh,hat⟩ := terminal_tangent hα
  obtain ⟨huL,haL,haU,huU⟩ := minimizingPosition_terminal hq hα
  have hpos : minimizingPosition q α∈Icc (179/200:ℝ) (47/50) := ⟨huL.le,huU.le⟩
  have hz := minimizingPosition_chart_root hq hα
  obtain ⟨homega,hKA,hbeta,hKB,hgamma⟩ := correction_coefficients hq hpos hh hz
  have hflux := flux_pos hq hpos hh
  have hsmall := small_reserve hq hpos hh
  have hsecant := secant_reserve hq hpos hh ⟨haL,haU⟩ hz
  rw [hat] at hflux hsmall hsecant
  exact CanonicalNegativeCorrection.correction_lower hα ht he hr hu
    homega hKA hbeta hKB hgamma hflux.le hsmall.le hsecant.le

end SquaresInCircles.Eight.StationaryTerminal
end
end
end

section
/-!
## The nominal stress is the actual position envelope

The four successive circle points and the
closing point are kept as explicit own-frame points.  Position
stationarity balances the E force; all other force balances are the
definitions of the five masses.  Consequently the nominal defect is
exactly the closing mass times the actual five-corner defect.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.StationaryTerminal
open Stationary.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

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
      (![q,q,q,q,q+Stationary.FiveCornerGeometry.defect q (cosine h) (sine h) u] i) := by
  have hd := (radical_bounds hq hu).smoothDomain (by linarith [hq.2])
    (by linarith [hu.1])
  have hA : lowerRight q u^2+u^2=q := upper_circle hd.toDomain.first_radicand
  have hB : topRight q u^2+(2-u)^2=q := upper_circle hd.toDomain.second_radicand
  have hD : topHeight q u^2+topLeft q u^2=q := upper_circle hd.toDomain.third_radicand
  have hE : lowerLeft q u^2+lowerHeight q u^2=q := upper_circle hd.toDomain.fourth_radicand
  rw [SignedPoint.circle,abs_of_nonneg (nominal_y_nonneg hq hu hh i)]
  fin_cases i <;> simp only [nominalPoints,Matrix.cons_val,Fin.reduceFinMk,
    Stationary.FiveCornerGeometry.defect,sub_add_cancel]
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
      -(weights q u h).mu 4*Stationary.FiveCornerGeometry.defect q (cosine h) (sine h) u := by
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
      (weights q u h).mu 4*Stationary.FiveCornerGeometry.defect q (cosine h) (sine h) u := by
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
      Stationary.FiveCornerGeometry.defect q (Real.cos t) (Real.sin t) (minimizingPosition q t)
  simpa only [cosine,sine,hat] using hid

end SquaresInCircles.Eight.StationaryTerminal
end
end
end

section
/-!
## The canonical terminal bound with all original radial losses

The source radius may differ from the
reference radius used for the actual position minimizer.  Normalization
of the five masses makes their difference exact.  The quantitative
conclusion retains both center-completion squares and every original
anchor's radial slack.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.StationaryTerminal
open Stationary.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

theorem terminal_tilt_mem {α : ℝ} (hα : α∈Icc (1/10:ℝ) (4/25)) :
    α∈tiltInterval := by
  obtain ⟨hh,hat⟩ := terminal_tangent hα
  rw [← hat]
  exact arctan_mem_tiltInterval hh

/-- Exact reference-radius transfer plus the proved two-error reserve.
The five weak contacts are the original geometric inequalities. -/
theorem original_quantitative_bound {H A B D E : SignedPoint} {q₀ q α t e : ℝ}
    (hq₀ : q₀∈Icc (19577/5000:ℝ) (9789/2500))
    (hα : α∈Icc (1/10:ℝ) (4/25))
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) (hu : t+e≤α)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hHA : 1+W (α-t-e)≤H.y+A.a*Real.cos (α-t-e)-A.y*Real.sin (α-t-e))
    (hAB : 1≤A.y+B.y)
    (hBD : W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      D.y/Real.cos e+B.a*Real.cos t-B.y*Real.sin t)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) :
    q₀+(minimizingWeights q₀ α).mu 4*positionEnvelope q₀ α+(t+e)/5000+
      centerLoss (minimizingWeights q₀ α) α t (α-t-e) e ![A,B,D,E,H]+
      circleLoss q (minimizingWeights q₀ α) ![A,B,D,E,H]≤q := by
  have hw := minimizingWeights_positive hq₀ hα
  have hm : ∀i,(minimizingWeights q₀ α).mu i≠0 := fun i => (hw.2.2.2.2.2 i).ne'
  have hcontact := original_circle_inequality (q:=q) hw
    hyH hyA hyB hyD hyE hHA hAB hBD hDE hEH
  have hid : CanonicalNegativeStress.defect q (minimizingWeights q₀ α) α t (α-t-e) e=
      (minimizingWeights q₀ α).mu 4*positionEnvelope q₀ α+
        correction (minimizingWeights q₀ α) α t e-(q-q₀) := by
    rw [defect_radius (minimizingWeights q₀ α) q q₀,
      defect_difference hm,minimizing_nominal_defect hq₀ hα,
      minimizingWeights_mass hq₀ hα]
    ring
  rw [hid] at hcontact
  linarith [actual_correction_lower hq₀ hα ht he hr hu]

/-- A zero of the actual envelope at an interior angle is the unique
stationary angle.  Local minimality follows from the proved global
nonnegativity of the original envelope. -/
theorem stationary_zero_angle {d : Stationary.Coordinates}
    (hd : d.IsStationary) {α : ℝ} (hα : α∈tiltInterval)
    (hzero : positionEnvelope d.q α=0) : α=coordinateAngle d := by
  have hmin : IsMinOn (positionEnvelope d.q) (Icc 0 (Real.arctan (1/5))) α := by
    intro x hx
    rw [hzero]
    exact stationary_envelope_nonneg hd hx
  have hloc := hmin.isLocalMin (Icc_mem_nhds hα.1 hα.2)
  have hder := positionEnvelope_hasDerivAt hd.q_lower hd.q_upper hα
  have hderzero := hloc.hasDerivAt_eq_zero hder
  have hz : deriv (positionEnvelope d.q) α=0 := hder.deriv.trans hderzero
  exact positionEnvelope_critical_unique hd.q_lower hd.q_upper hα
    (stationary_angle_mem hd) hz (stationary_envelope_critical hd)

end SquaresInCircles.Eight.StationaryTerminal
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.StationaryTerminal
open Stationary.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

theorem circle_loss_zero {w : CanonicalNegativeStress.Parameters} (hw : w.Positive)
    {p : Fin 5 → SignedPoint} {q : ℝ}
    (hc : ∀i,(p i).Contained q) (hz : circleLoss q w p=0) :
    ∀i,(p i).circle=q := by
  intro i
  have hterm : w.mu i*(q-(p i).circle)≤circleLoss q w p :=
    Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 5))) =>
      mul_nonneg (hw.2.2.2.2.2 j).le (sub_nonneg.mpr (hc j))) (Finset.mem_univ i)
  rw [hz] at hterm
  have hm := hw.2.2.2.2.2 i
  have hi := hc i
  change (p i).circle≤q at hi
  nlinarith

theorem center_loss_zero {w : CanonicalNegativeStress.Parameters} (hw : w.Positive)
    {p : Fin 5 → SignedPoint} {α t u e : ℝ}
    (hz : centerLoss w α t u e p=0) :
    ∀i,(p i).a+1/2=(forces w α t u e i).1/(2*w.mu i) ∧
      (p i).y+1/2=(forces w α t u e i).2/(2*w.mu i) := by
  intro i
  have hnonneg : ∀j : Fin 5,0≤centerSquare (w.mu j) (forces w α t u e j) (p j) := by
    intro j
    exact mul_nonneg (hw.2.2.2.2.2 j).le (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hterm : centerSquare (w.mu i) (forces w α t u e i) (p i)≤
      centerLoss w α t u e p :=
    Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  have hzero : centerSquare (w.mu i) (forces w α t u e i) (p i)=0 := by
    rw [hz] at hterm
    exact le_antisymm hterm (hnonneg i)
  have hsum : ((p i).a+1/2-(forces w α t u e i).1/(2*w.mu i))^2+
      ((p i).y+1/2-(forces w α t u e i).2/(2*w.mu i))^2=0 :=
    (mul_eq_zero.mp hzero).resolve_left (hw.2.2.2.2.2 i).ne'
  have hx : ((p i).a+1/2-(forces w α t u e i).1/(2*w.mu i))^2=0 := by
    nlinarith [sq_nonneg ((p i).y+1/2-(forces w α t u e i).2/(2*w.mu i))]
  have hy : ((p i).y+1/2-(forces w α t u e i).2/(2*w.mu i))^2=0 := by
    nlinarith [sq_nonneg ((p i).a+1/2-(forces w α t u e i).1/(2*w.mu i))]
  exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hx),sub_eq_zero.mp (sq_eq_zero_iff.mp hy)⟩

theorem nominal_points_of_center_loss {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (hroot : positionHalf q (cosine h) (sine h) u=0)
    {p : Fin 5 → SignedPoint}
    (hz : centerLoss (weights q u h) (Real.arctan h) 0 (Real.arctan h) 0 p=0) :
    p=nominalPoints q u h := by
  have hw := positive hq hu hh
  funext i
  have hcoord := center_loss_zero hw hz i
  rw [nominal_force_balance hq hu hh hroot i] at hcoord
  dsimp only at hcoord
  have hm : (weights q u h).mu i≠0 := (hw.2.2.2.2.2 i).ne'
  have hx : (2*(weights q u h).mu i*((nominalPoints q u h i).a+1/2))/
      (2*(weights q u h).mu i)=(nominalPoints q u h i).a+1/2 := by
    field_simp [hm]
  have hy : (2*(weights q u h).mu i*((nominalPoints q u h i).y+1/2))/
      (2*(weights q u h).mu i)=(nominalPoints q u h i).y+1/2 := by
    field_simp [hm]
  rw [hx,hy] at hcoord
  apply SignedPoint.ext <;> linarith [hcoord.1,hcoord.2]

/-- In the canonical two-error branch at a radius `q ≤ d.q`, equality identifies everything:
`q = d.q`, both angular errors vanish, the tilt is `coordinateAngle d`, and the five anchors lie on
the circle at the nominal points of `d`. The stationary datum is the geometric predicate
`IsStationary`. -/
theorem stationary_rigidity {d : Stationary.Coordinates}
    (hd : d.IsStationary) (hq₀ : d.q∈Icc (19577/5000:ℝ) (9789/2500))
    {H A B D E : SignedPoint} {q α t e : ℝ}
    (hqq : q≤d.q) (hα : α∈Icc (1/10:ℝ) (4/25))
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) (hu : t+e≤α)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hc : ∀i : Fin 5,(![A,B,D,E,H] i).Contained q)
    (hHA : 1+W (α-t-e)≤H.y+A.a*Real.cos (α-t-e)-A.y*Real.sin (α-t-e))
    (hAB : 1≤A.y+B.y)
    (hBD : W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      D.y/Real.cos e+B.a*Real.cos t-B.y*Real.sin t)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) :
    q=d.q ∧ t=0 ∧ e=0 ∧ α=coordinateAngle d ∧
      (∀i : Fin 5,(![A,B,D,E,H] i).circle=d.q) ∧
      ![A,B,D,E,H]=nominalPoints d.q (-d.y) (Real.tan (coordinateAngle d)) := by
  have hw := minimizingWeights_positive hq₀ hα
  have hb := original_quantitative_bound (q:=q) hq₀ hα ht he hr hu
    hyH hyA hyB hyD hyE hHA hAB hBD hDE hEH
  have htilt := terminal_tilt_mem hα
  have henv := stationary_envelope_nonneg hd ⟨htilt.1.le,htilt.2.le⟩
  have hmass := hw.2.2.2.2.2 4
  have henvterm := mul_nonneg hmass.le henv
  have hcenter := centerLoss_nonneg hw ![A,B,D,E,H] α t (α-t-e) e
  have hcircle := circleLoss_nonneg hw hc
  have hqeq : q=d.q := le_antisymm hqq (by linarith)
  have htzero : t=0 := by linarith
  have hezero : e=0 := by linarith
  have henvzero : positionEnvelope d.q α=0 := by nlinarith
  have hcenterzero : centerLoss (minimizingWeights d.q α) α t (α-t-e) e
      ![A,B,D,E,H]=0 := by linarith
  have hcirclezero : circleLoss q (minimizingWeights d.q α) ![A,B,D,E,H]=0 := by linarith
  have halpha := stationary_zero_angle hd htilt henvzero
  have hcircles := circle_loss_zero hw hc hcirclezero
  rw [htzero,hezero] at hcenterzero
  simp only [sub_zero] at hcenterzero
  obtain ⟨hh,hat⟩ := terminal_tangent hα
  obtain ⟨huL,_,_,huU⟩ := minimizingPosition_terminal hq₀ hα
  have hz : centerLoss (weights d.q (minimizingPosition d.q α) (Real.tan α))
      (Real.arctan (Real.tan α)) 0 (Real.arctan (Real.tan α)) 0 ![A,B,D,E,H]=0 := by
    simpa only [hat,minimizingWeights] using hcenterzero
  have hpoints := nominal_points_of_center_loss hq₀ ⟨huL.le,huU.le⟩ hh
    (minimizingPosition_chart_root hq₀ hα) hz
  rw [halpha,stationary_minimizingPosition hd] at hpoints
  refine ⟨hqeq,htzero,hezero,halpha,?_,hpoints⟩
  intro i
  exact (hcircles i).trans hqeq

end SquaresInCircles.Eight.StationaryTerminal
end
end
end

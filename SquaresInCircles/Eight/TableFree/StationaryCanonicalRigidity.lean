module

public import SquaresInCircles.Eight.TableFree.StationaryCanonicalTerminal

/-!
# Equality retains the five original anchors

Uncompiled reconstruction.  Vanishing of the exact radial and center
losses identifies every original point.  The position envelope then
identifies the tilt and the entire stationary chain.  No replaced
intermediate point supplies a circle equality.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.StationaryTerminal
open ExactFamily.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

theorem circle_loss_zero {w : Parameters} (hw : w.Positive)
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

theorem center_loss_zero {w : Parameters} (hw : w.Positive)
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
  simp only [Prod.fst_mk,Prod.snd_mk] at hcoord
  have hm : (weights q u h).mu i≠0 := (hw.2.2.2.2.2 i).ne'
  have hx : (2*(weights q u h).mu i*((nominalPoints q u h i).a+1/2))/
      (2*(weights q u h).mu i)=(nominalPoints q u h i).a+1/2 := by
    field_simp [hm]
  have hy : (2*(weights q u h).mu i*((nominalPoints q u h i).y+1/2))/
      (2*(weights q u h).mu i)=(nominalPoints q u h i).y+1/2 := by
    field_simp [hm]
  rw [hx,hy] at hcoord
  cases hpi : p i with
  | mk a y =>
    cases hni : nominalPoints q u h i with
    | mk b z =>
      simp only [hpi,hni] at hcoord
      congr 1 <;> linarith [hcoord.1,hcoord.2]

/-- Equality in the canonical two-error branch identifies all five
source points and both angular errors.  The stationary datum is the
broad geometric predicate; no local root box is used. -/
theorem stationary_rigidity {d : ExactFamily.Coordinates}
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

end SquaresInCircles.Eight.TableFree.StationaryTerminal

module

public import SquaresInCircles.Eight.TableFree.GeometricExistenceBoundaries

/-!
# Stationary existence from compact minima and two radii

Uncompiled reconstruction of
HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md.  The actual continuous
circle defect is minimized over a fixed position window and a fixed
tilt interval.  Opposite signs at two radii give a zero minimum.  The
boundary stress makes its tilt interior, and Fermat's rule supplies
the two actual stationary equations.  Geometric uniqueness then gives
the same radius bounds for every broad stationary datum.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GeometricExistence
open ExactFamily ExactFamily.FiveCornerGeometry Eight.FiveCorner

theorem closedTilts_nonempty : closedTilts.Nonempty :=
  ⟨0,le_rfl,(Real.arctan_pos.mpr (by norm_num : (0:ℝ)<1/5)).le⟩

theorem positionEnvelope_joint_continuous :
    Continuous (fun p : ℝ×ℝ => positionEnvelope p.1 p.2) := by
  change Continuous (fun p : ℝ×ℝ =>
    sInf ((fun u => defect p.1 (Real.cos p.2) (Real.sin p.2) u) '' positionWindow))
  apply (isCompact_Icc : IsCompact positionWindow).continuous_sInf
  dsimp [defect,firstComponent,secondComponent,lowerRight,lowerLeft,
    lowerHeight,topHeight,topLeft,topRight,upper]
  fun_prop

def radiusEnvelope (q : ℝ) : ℝ := sInf ((positionEnvelope q) '' closedTilts)

theorem radiusEnvelope_continuous : Continuous radiusEnvelope := by
  unfold radiusEnvelope
  apply (isCompact_Icc : IsCompact closedTilts).continuous_sInf
  exact positionEnvelope_joint_continuous

theorem radius_minimum (q : ℝ) :
    ∃t∈closedTilts, radiusEnvelope q=positionEnvelope q t ∧
      ∀s∈closedTilts,positionEnvelope q t≤positionEnvelope q s := by
  exact (isCompact_Icc : IsCompact closedTilts).exists_sInf_image_eq_and_le
    closedTilts_nonempty (positionEnvelope_continuous q).continuousOn

theorem lower_radius_minimum_positive : 0<radiusEnvelope lowerRadius := by
  obtain ⟨t,ht,he,_⟩ := radius_minimum lowerRadius
  rw [he]
  exact lower_radius_positionEnvelope_positive ht

theorem upper_radius_minimum_negative : radiusEnvelope upperRadius<0 := by
  obtain ⟨t,ht,he,hm⟩ := radius_minimum upperRadius
  have htrial : RationalTrial.angle∈closedTilts :=
    ⟨RationalTrial.angle_mem.1.le,RationalTrial.angle_mem.2.le⟩
  rw [he]
  exact lt_of_le_of_lt (hm _ htrial) upper_radius_positionEnvelope_negative

theorem radius_zero_exists :
    ∃q∈Ioo lowerRadius upperRadius,radiusEnvelope q=0 := by
  have hcont : ContinuousOn (fun q : ℝ => -radiusEnvelope q)
      (Icc lowerRadius upperRadius) := radiusEnvelope_continuous.neg.continuousOn
  obtain ⟨q,hq,hzero⟩ := intermediate_value_Icc radius_order.2.1.le hcont
    (show (0:ℝ)∈Icc (-radiusEnvelope lowerRadius) (-radiusEnvelope upperRadius) from
      ⟨by linarith [lower_radius_minimum_positive],by linarith [upper_radius_minimum_negative]⟩)
  have hz : radiusEnvelope q=0 := by linarith
  have hql : lowerRadius<q := by
    by_contra! hbad
    have he : q=lowerRadius := le_antisymm hbad hq.1
    rw [he] at hz
    linarith [lower_radius_minimum_positive]
  have hqu : q<upperRadius := by
    by_contra! hbad
    have he : q=upperRadius := le_antisymm hq.2 hbad
    rw [he] at hz
    linarith [upper_radius_minimum_negative]
  exact ⟨q,⟨hql,hqu⟩,hz⟩

/-- The existence witness is obtained from the actual compact minimum.
The stationary predicate keeps its original equations and branch signs. -/
theorem stationary_exists :
    ∃d : Coordinates,d.IsStationary ∧ lowerRadius<d.q ∧ d.q<upperRadius := by
  obtain ⟨q,hq,hzero⟩ := radius_zero_exists
  obtain ⟨t,ht,he,hm⟩ := radius_minimum q
  have hM : positionEnvelope q t=0 := by linarith
  have hqclosed : q∈Icc lowerRadius upperRadius := ⟨hq.1.le,hq.2.le⟩
  have hend := endpoint_positionEnvelope_positive hqclosed
  have htl : 0<t := by
    by_contra! hbad
    have htzero : t=0 := le_antisymm hbad ht.1
    rw [htzero] at hM
    linarith [hend.1]
  have htu : t<Real.arctan (1/5) := by
    by_contra! hbad
    have htlast : t=Real.arctan (1/5) := le_antisymm ht.2 hbad
    rw [htlast] at hM
    linarith [hend.2]
  have htilt : t∈tiltInterval := ⟨htl,htu⟩
  have hql : (79/40:ℝ)^2≤q := radius_order.1.le.trans hq.1.le
  have hqu : q≤9789/2500 := hq.2.le.trans radius_order.2.2.le
  let u := minimizingPosition q t
  have hu : u∈positionWindow := windowMinimizer_mem q (Real.cos t) (Real.sin t)
  have hF : defect q (Real.cos t) (Real.sin t) u=0 := by
    rw [positionEnvelope_eq] at hM
    exact hM
  have hP : positionHalf q (Real.cos t) (Real.sin t) u=0 := by
    have hp := minimizingPosition_root hql hqu htilt
    change 2*positionHalf q (Real.cos t) (Real.sin t) u=0 at hp
    linarith
  have hmin : IsMinOn (positionEnvelope q) closedTilts t := by
    intro s hs
    exact hm s hs
  have hT : tiltFirst q (Real.cos t) (Real.sin t) u=0 :=
    (hmin.isLocalMin (Icc_mem_nhds htl htu)).hasDerivAt_eq_zero
      (positionEnvelope_hasDerivAt hql hqu htilt)
  exact ⟨data q u t,data_stationary hql hqu hu htilt hF hP hT,hq.1,hq.2⟩

/-- A selected stationary datum whose existence proof contains no local
stationary enclosure or generated formula certificate. -/
def stationaryDatum : Coordinates := Classical.choose stationary_exists

theorem stationaryDatum_stationary : stationaryDatum.IsStationary :=
  (Classical.choose_spec stationary_exists).1

theorem stationaryDatum_radius : lowerRadius<stationaryDatum.q ∧
    stationaryDatum.q<upperRadius := (Classical.choose_spec stationary_exists).2

theorem stationaryDatum_unique {d : Coordinates} (hd : d.IsStationary) :
    d=stationaryDatum := stationary_chain_unique hd stationaryDatum_stationary

/-- The broad stationary equations themselves now imply the required
radius bracket, with existence and uniqueness both supplied geometrically. -/
theorem stationary_radius_bounds {d : Coordinates} (hd : d.IsStationary) :
    lowerRadius<d.q ∧ d.q<upperRadius := by
  rw [stationaryDatum_unique hd]
  exact stationaryDatum_radius

theorem stationary_radius_strip {d : Coordinates} (hd : d.IsStationary) :
    d.q∈Icc (19577/5000:ℝ) (9789/2500) := by
  have hq := stationary_radius_bounds hd
  exact ⟨hq.1.le,hq.2.le.trans radius_order.2.2.le⟩

theorem stationary_radius_ceiling {d : Coordinates} (hd : d.IsStationary) :
    d.q<Nominal.ceiling := (stationary_radius_bounds hd).2

end SquaresInCircles.Eight.TableFree.GeometricExistence

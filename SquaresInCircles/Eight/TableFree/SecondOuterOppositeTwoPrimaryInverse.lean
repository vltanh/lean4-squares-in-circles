module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoTargetRatio

/-!
# The explicit inverse rotation for an arbitrary physical primary height

The fixed-primary shift ranges up to .915.  The actual circle keeps
its radical strictly positive throughout this whole range.  The
source derivative of the inverse angle increases with the primary
shift, so the diagonal ratio already pays every physical primary
contact.  Original weak separators give a finite comparison to this
curve.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.PrimaryInverse

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

abbrev radius := NegativeTwo.ContactInverse.radius
abbrev speed := NegativeTwo.ContactInverse.speed
abbrev baseAngle := NegativeTwo.ContactInverse.baseAngle
abbrev inverseAngle := NegativeTwo.ContactInverse.angle
def shifts : Set ℝ := Icc 0 (183/200)
def X (z b : ℝ) : ℝ := Real.pi/2-inverseAngle z b
def F (z b : ℝ) : ℝ := Inverse.factor (U b)+z*ratio b/(Inverse.q (U b)*speed z b)
def targetCost (z b : ℝ) : ℝ := X z b-V b

lemma data {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    1<radius b ∧ (radius b)^2=Inverse.q (U b) ∧
      0<speed z b ∧ z^2+(speed z b)^2=Inverse.q (U b) := by
  have hzero := NegativeTwo.ContactInverse.data hb
    (show (0:ℝ)∈Icc (-(1/2)) (2/5) by norm_num)
  have hq := (Inverse.range_data
    (show U b∈Inverse.interval from ⟨(UW_bounds hb).1.le,(UW_bounds hb).2.1.le⟩)).2
  have hz2 : z^2≤(183/200:ℝ)^2 := by nlinarith [hz.1,hz.2]
  have hrad : 0<Inverse.q (U b)-z^2 := by linarith
  have hv := Real.sqrt_pos.mpr hrad
  have hv2 := Real.sq_sqrt hrad.le
  refine ⟨hzero.2.2.1,hzero.2.2.2.1,hv,?_⟩
  change z^2+(Real.sqrt (Inverse.q (U b)-z^2))^2=Inverse.q (U b)
  linarith

lemma inverse_root {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    Real.sqrt (1-(z/radius b)^2)=speed z b/radius b := by
  have hd := data hb hz
  have hn : 0<radius b := by linarith [hd.1]
  have he : 1-(z/radius b)^2=(speed z b/radius b)^2 := by
    field_simp [hn.ne']
    nlinarith [hd.2.1,hd.2.2.2]
  rw [he,Real.sqrt_sq (div_nonneg hd.2.2.1.le hn.le)]

lemma argument_bounds {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    -1<z/radius b ∧ z/radius b<1 := by
  have hd := data hb hz
  have hn : 0<radius b := by linarith [hd.1]
  constructor
  · apply (lt_div_iff₀ hn).2
    linarith [hz.1,hd.1]
  · apply (div_lt_iff₀ hn).2
    linarith [hz.2,hd.1]

lemma angle_source_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (inverseAngle z) (-F z b) b := by
  have hd := data hb hz
  have hn : 0<radius b := by linarith [hd.1]
  have hv := hd.2.2.1
  have ha := argument_bounds hb hz
  have hratio : HasDerivAt (fun y => z/radius y) (-z*ratio b/(radius b)^3) b := by
    convert (hasDerivAt_const b z).div
      (NegativeTwo.ContactInverse.radius_hasDerivAt hb) hn.ne' using 1
    field_simp [hn.ne']
    ring
  have hbeta : HasDerivAt (fun y => Real.arcsin (z/radius y))
      (-z*ratio b/(Inverse.q (U b)*speed z b)) b := by
    have hh := (Real.hasDerivAt_arcsin (by linarith : z/radius b≠-1)
      (by linarith : z/radius b≠1)).comp b hratio
    convert hh using 1
    rw [inverse_root hb hz,←hd.2.1]
    field_simp [hn.ne',hv.ne']
    ring
  convert (NegativeTwo.ContactInverse.base_hasDerivAt hb).add hbeta using 1 <;>
    dsimp [inverseAngle,NegativeTwo.ContactInverse.angle,F] <;> ring

lemma X_source_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (X z) (F z b) b := by
  convert (angle_source_hasDerivAt hb hz).const_sub (Real.pi/2) using 1 <;>
    dsimp [X] <;> ring

lemma X_shift_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (fun t => X t b) (-(1/speed z b)) z := by
  have hd := data hb hz
  have hn : 0<radius b := by linarith [hd.1]
  have ha := argument_bounds hb hz
  have hbeta := (Real.hasDerivAt_arcsin (by linarith : z/radius b≠-1)
    (by linarith : z/radius b≠1)).comp z ((hasDerivAt_id z).div_const (radius b))
  have hangle := hbeta.const_add (baseAngle b)
  convert hangle.const_sub (Real.pi/2) using 1
  · funext t
    dsimp [X,inverseAngle,NegativeTwo.ContactInverse.angle]
    ring
  · rw [inverse_root hb hz]
    field_simp [hn.ne',hd.2.2.1.ne']
    ring

lemma F_paid {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z∈shifts)
    (hdiag : TargetRatio.z≤z) : VLabel.d1 b<F z b := by
  have hd := data hb hz
  have hd0 := NegativeTwo.ContactInverse.data hb TargetRatio.z_mem
  have hq : 0<Inverse.q (U b) := by linarith [(Inverse.range_data
    (show U b∈Inverse.interval from ⟨(UW_bounds hb).1.le,(UW_bounds hb).2.1.le⟩)).2]
  have hsmall : speed z b≤TargetRatio.speed b := by
    apply Real.sqrt_le_sqrt
    nlinarith [hz.1,TargetRatio.z_bounds.1]
  have hz0 : 0≤TargetRatio.z := by linarith [TargetRatio.z_bounds.1]
  have hprod := mul_le_mul hdiag hsmall hd.2.2.1.le hz.1
  have hquot : TargetRatio.z/TargetRatio.speed b≤z/speed z b := by
    apply (div_le_div_iff₀ hd0.2.2.2.2.1 hd.2.2.1).2
    exact hprod
  have hr : 0≤ratio b/Inverse.q (U b) :=
    div_nonneg (by linarith [(outer_ratio_bounds hb).1]) hq.le
  have hm := mul_le_mul_of_nonneg_left hquot hr
  have he0 : TargetRatio.F b=Inverse.factor (U b)+
      (ratio b/Inverse.q (U b))*(TargetRatio.z/TargetRatio.speed b) := by
    rw [TargetRatio.F_formula]
    ring
  have he : F z b=Inverse.factor (U b)+
      (ratio b/Inverse.q (U b))*(z/speed z b) := by dsimp [F]; ring
  rw [he]
  have hp := TargetRatio.paid hb
  rw [he0] at hp
  linarith

lemma targetCost_monotone {z : ℝ} (hz : z∈shifts) (hdiag : TargetRatio.z≤z) :
    MonotoneOn (targetCost z) (Icc 0 outerDiagonal) := by
  have hd {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
      HasDerivAt (targetCost z) (F z b-VLabel.d1 b) b := by
    convert (X_source_hasDerivAt hb hz).sub (VLabel.outer_hasDerivAt (outer_domain hb))
      using 1 <;> dsimp [targetCost,V] <;> ring
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (hd hb).continuousAt.continuousWithinAt
  · exact fun b hb => hd (Ioo_subset_Icc_self hb)
  · intro b hb
    linarith [F_paid (Ioo_subset_Icc_self hb) hz hdiag]

lemma aligned {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z=W b) : X z b=0 := by
  have ha := NegativeTwo.ContactInverse.base_bounds hb
  have ht := NegativeTwo.ContactInverse.base_trig hb
  have hrange : -(Real.pi/2)≤Real.pi/2-baseAngle b ∧
      Real.pi/2-baseAngle b≤Real.pi/2 := by
    constructor <;> linarith [Real.pi_pos]
  have hs : z/radius b=Real.sin (Real.pi/2-baseAngle b) := by
    rw [Real.sin_pi_div_two_sub,ht.1,hz]
  dsimp [X,inverseAngle,NegativeTwo.ContactInverse.angle]
  rw [hs,Real.arcsin_sin hrange.1 hrange.2]
  ring

/-- A weak physical upper-primary inequality lies after its explicit
inverse contact angle, even when that angle is negative. -/
lemma weak_angle {a b z x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10)) (hz : z∈shifts)
    (hcut : upperPrimary a b x≤z+1/2) : X z b≤x := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2⟩
  have hd := data hb hz
  have hn : 0<radius b := by linarith [hd.1]
  have ha := NegativeTwo.ContactInverse.base_bounds hb
  have ht := NegativeTwo.ContactInverse.base_trig hb
  let y : ℝ := Real.pi/2-x-baseAngle b
  have hy : -(Real.pi/2)≤y ∧ y≤Real.pi/2 := by
    dsimp [y]
    constructor <;> linarith [hx.1,hx.2,ha.1,ha.2,pi_hand_enclosure.1]
  have hsine : Real.sin y=
      (W b*Real.cos x-(U b-1)*Real.sin x)/radius b := by
    rw [show y=Real.pi/2-(x+baseAngle b) by dsimp [y]; ring,
      Real.sin_pi_div_two_sub,Real.cos_add,ht.1,ht.2]
    field_simp [hn.ne']
    ring
  have hnum : W b*Real.cos x-(U b-1)*Real.sin x≤z := by
    dsimp [upperPrimary] at hcut
    rw [←(ShortOuterOne.SameContact.actual_arc hs).1] at hcut
    dsimp [U,W]
    linarith
  have hsin : Real.sin y≤z/radius b := by
    rw [hsine]
    exact div_le_div_of_nonneg_right hnum hn.le
  have hh := Real.arcsin_le_arcsin hsin
  rw [Real.arcsin_sin hy.1 hy.2] at hh
  dsimp [X,inverseAngle,NegativeTwo.ContactInverse.angle,y] at *
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.PrimaryInverse

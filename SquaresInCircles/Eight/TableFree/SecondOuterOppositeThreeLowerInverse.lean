module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeUpperInverse

/-!
# The exact inverse for both lower-secondary contacts

The free coordinate is the shifted secondary coordinate `z`; the other
coordinate supplies the unchanged outer-circle radical.  The phase is
the negative contact angle.  Its source and free-coordinate derivatives
are proved on the full radical domain needed by both original owners.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerInverse
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

abbrev q := NegativeTwo.Inverse.q
abbrev factor := NegativeTwo.Inverse.factor
abbrev factorD := NegativeTwo.Inverse.factorD
abbrev radius := UpperInverse.radius
abbrev speed := UpperInverse.speed
abbrev shifts := UpperInverse.shifts
abbrev base := NegativeTwo.ContactInverse.baseAngle
def phase (z y : ℝ) : ℝ := -base y+Real.arcsin (z/radius y)
def first (z y : ℝ) : ℝ := factor (U y)-z*ratio y/(q (U y)*speed z y)
def second (z y : ℝ) : ℝ :=
  -ratio y*factorD (U y)-z/(q (U y)*speed z y)*
    NegativeTwo.Inverse.brace (U y) (ratio y) (speed z y)

lemma speed_source_hasDerivAt {y z : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (speed z) (ratio y/speed z y) y := by
  have hh := OppositeTwo.PrimaryInverse.data hy hz
  have hrad : q (U y)-z^2≠0 := by nlinarith [hh.2.2.1,hh.2.2.2]
  have hu := (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hy)).add_const (1/2)
  have hd := (((NegativeTwo.Inverse.q_hasDerivAt (U y)).comp y hu).sub_const (z^2)).sqrt hrad
  convert hd using 1
  · rfl
  · dsimp [speed,UpperInverse.speed,OppositeTwo.PrimaryInverse.speed,NegativeTwo.ContactInverse.speed]
    field_simp [show Real.sqrt (q (U y)-z^2)≠0 from hh.2.2.1.ne']
    ring

lemma speed_shift_hasDerivAt {y z : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (fun t => speed t y) (-z/speed z y) z := by
  have hh := OppositeTwo.PrimaryInverse.data hy hz
  have hrad : q (U y)-z^2≠0 := by nlinarith [hh.2.2.1,hh.2.2.2]
  have hd := (((hasDerivAt_id z).pow 2).const_sub (q (U y))).sqrt hrad
  convert hd using 1
  · rfl
  · dsimp [speed,UpperInverse.speed,OppositeTwo.PrimaryInverse.speed,NegativeTwo.ContactInverse.speed]
    field_simp [show Real.sqrt (q (U y)-z^2)≠0 from hh.2.2.1.ne']
    ring

lemma phase_source_hasDerivAt {y z : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (phase z) (first z y) y := by
  have hh := OppositeTwo.PrimaryInverse.data hy hz
  have hr : 0<radius y := by linarith [hh.1]
  have ha := OppositeTwo.PrimaryInverse.argument_bounds hy hz
  have hd := (hasDerivAt_const y z).div
    (NegativeTwo.ContactInverse.radius_hasDerivAt hy) hr.ne'
  have hasin := (Real.hasDerivAt_arcsin (by linarith : z/radius y≠-1)
    (by linarith : z/radius y≠1)).comp y hd
  have hder : HasDerivAt (fun t => Real.arcsin (z/radius t))
      (-z*ratio y/(q (U y)*speed z y)) y := by
    convert hasin using 1
    rw [OppositeTwo.PrimaryInverse.inverse_root hy hz,←hh.2.1]
    field_simp [hr.ne',hh.2.2.1.ne']
    ring
  convert (NegativeTwo.ContactInverse.base_hasDerivAt hy).neg.add hder using 1 <;>
    dsimp [phase,first] <;> ring

lemma phase_shift_hasDerivAt {y z : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (fun t => phase t y) (1/speed z y) z := by
  have hh := OppositeTwo.PrimaryInverse.data hy hz
  have hr : 0<radius y := by linarith [hh.1]
  have ha := OppositeTwo.PrimaryInverse.argument_bounds hy hz
  have hd := (Real.hasDerivAt_arcsin (by linarith : z/radius y≠-1)
    (by linarith : z/radius y≠1)).comp z ((hasDerivAt_id z).div_const (radius y))
  convert hd.const_add (-base y) using 1
  · rfl
  · rw [OppositeTwo.PrimaryInverse.inverse_root hy hz]
    field_simp [hr.ne',hh.2.2.1.ne']
    ring

lemma first_source_hasDerivAt {y z : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (first z) (second z y) y := by
  have hh := OppositeTwo.PrimaryInverse.data hy hz
  have hu := U_positive (outer_domain hy)
  have hq : q (U y)≠0 := by linarith [NegativeTwo.Inverse.actual_q_positive hy]
  have hU := (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hy)).add_const (1/2)
  have hf := (NegativeTwo.Inverse.factor_hasDerivAt hu.ne' hq).comp y hU
  have hden := ((NegativeTwo.Inverse.q_hasDerivAt (U y)).comp y hU).mul
    (speed_source_hasDerivAt hy hz)
  have hnum := (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hy)).const_mul z
  convert hf.sub (hnum.div hden (mul_ne_zero hq hh.2.2.1.ne')) using 1
  · rfl
  · dsimp [second,NegativeTwo.Inverse.brace,ratioD]
    change -ratio y*factorD (U y)-z/(q (U y)*speed z y)*
      (Q0/(U y)^3-2*(ratio y)^2/q (U y)-(ratio y)^2/(speed z y)^2)=_
    field_simp [hu.ne',hq,hh.2.2.1.ne']
    ring

lemma shift_second_hasDerivAt {y z : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (fun t => 1/speed t y) (z/(speed z y)^3) z := by
  have hv := (OppositeTwo.PrimaryInverse.data hy hz).2.2.1
  convert (hasDerivAt_const z (1:ℝ)).div (speed_shift_hasDerivAt hy hz) hv.ne' using 1
  field_simp [hv.ne']
  ring

lemma shift_source_hasDerivAt {y z : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (fun t => 1/speed z t) (-ratio y/(speed z y)^3) y := by
  have hv := (OppositeTwo.PrimaryInverse.data hy hz).2.2.1
  convert (hasDerivAt_const y (1:ℝ)).div (speed_source_hasDerivAt hy hz) hv.ne' using 1
  field_simp [hv.ne']
  ring

lemma first_shift_hasDerivAt {y z : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (fun t => first t y) (-ratio y/(speed z y)^3) z := by
  have hh := OppositeTwo.PrimaryInverse.data hy hz
  have hq : q (U y)≠0 := by linarith [NegativeTwo.Inverse.actual_q_positive hy]
  have hden := (speed_shift_hasDerivAt hy hz).const_mul (q (U y))
  have hnum := (hasDerivAt_id z).mul_const (ratio y)
  have hd := (hnum.div hden (mul_ne_zero hq hh.2.2.1.ne')).const_sub (factor (U y))
  convert hd using 1
  · rfl
  · field_simp [hq,hh.2.2.1.ne']
    nlinarith [hh.2.2.2]

lemma aligned {y z : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z=U y-1) : phase z y=0 := by
  have hb := NegativeTwo.ContactInverse.base_bounds hy
  have ht := NegativeTwo.ContactInverse.base_trig hy
  have hs : z/radius y=Real.sin (base y) := by rw [ht.2,hz]
  dsimp [phase]
  rw [hs,Real.arcsin_sin (by linarith [hb.1,Real.pi_pos]) hb.2.le]
  ring

lemma weak_phase {y z x : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts)
    (hx : x∈Icc 0 (7/10))
    (hcut : z≤(arc y-1/2)*Real.cos x-(y+1/2)*Real.sin x) : phase z y≤ -x := by
  have hd := OppositeTwo.PrimaryInverse.data hy hz
  have hr : 0<radius y := by linarith [hd.1]
  have hb := NegativeTwo.ContactInverse.base_bounds hy
  have ht := NegativeTwo.ContactInverse.base_trig hy
  have hangle : -(Real.pi/2)≤base y-x ∧ base y-x≤Real.pi/2 := by
    constructor <;> linarith [hb.1,hb.2,hx.1,hx.2,pi_hand_enclosure.1]
  have hs : Real.sin (base y-x)=
      ((arc y-1/2)*Real.cos x-(y+1/2)*Real.sin x)/radius y := by
    rw [Real.sin_sub,ht.1,ht.2]
    dsimp [U,W]
    field_simp [hr.ne']
    ring
  have hsin : z/radius y≤Real.sin (base y-x) := by
    rw [hs]
    exact div_le_div_of_nonneg_right hcut hr.le
  have ha := Real.arcsin_le_arcsin hsin
  rw [Real.arcsin_sin hangle.1 hangle.2] at ha
  dsimp [phase]
  linarith

lemma phase_lower {y z x : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts)
    (hx : x∈Icc 0 (7/10))
    (hcut : (arc y-1/2)*Real.cos x-(y+1/2)*Real.sin x≤z) : -x≤phase z y := by
  have hd := OppositeTwo.PrimaryInverse.data hy hz
  have hr : 0<radius y := by linarith [hd.1]
  have hb := NegativeTwo.ContactInverse.base_bounds hy
  have ht := NegativeTwo.ContactInverse.base_trig hy
  have hangle : -(Real.pi/2)≤base y-x ∧ base y-x≤Real.pi/2 := by
    constructor <;> linarith [hb.1,hb.2,hx.1,hx.2,pi_hand_enclosure.1]
  have hs : Real.sin (base y-x)=
      ((arc y-1/2)*Real.cos x-(y+1/2)*Real.sin x)/radius y := by
    rw [Real.sin_sub,ht.1,ht.2]
    dsimp [U,W]
    field_simp [hr.ne']
    ring
  have hsin : Real.sin (base y-x)≤z/radius y := by
    rw [hs]
    exact div_le_div_of_nonneg_right hcut hr.le
  have ha := Real.arcsin_le_arcsin hsin
  rw [Real.arcsin_sin hangle.1 hangle.2] at ha
  dsimp [phase]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerInverse

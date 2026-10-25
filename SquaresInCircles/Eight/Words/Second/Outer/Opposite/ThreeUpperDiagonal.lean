module

public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeUpperDiagonalData

/-!
# Eight squares: the entire original target-diagonal boundary

One tangent parabola controls the whole initial source interval; the
analytic source motion controls its entire complement.  The result is
strictly above the opposite edge-three entry on every source state.
-/

section
/-!
## The exact inverse for both lower-secondary contacts

The free coordinate is the shifted secondary coordinate `z`; the other
coordinate supplies the unchanged outer-circle radical.  The phase is
the negative contact angle.  Its source and free-coordinate derivatives
are proved on the full radical domain needed by both original owners.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerInverse
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
  have hv : 0<Real.sqrt (q (U y)-z^2) := hh.2.2.1
  have hrad : q (U y)-z^2≠0 := by
    intro h
    rw [h,Real.sqrt_zero] at hv
    exact lt_irrefl _ hv
  have hU : HasDerivAt U (-ratio y) y :=
    (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hy)).add_const (1/2)
  have hd := (((NegativeTwo.Inverse.q_hasDerivAt (U y)).comp y hU).sub_const (z^2)).sqrt hrad
  refine hd.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [show speed z y=Real.sqrt (q (U y)-z^2) from rfl,
    div_eq_div_iff (mul_pos two_pos hv).ne' hv.ne']
  ring

lemma speed_shift_hasDerivAt {y z : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (fun t => speed t y) (-z/speed z y) z := by
  have hh := OppositeTwo.PrimaryInverse.data hy hz
  have hv : 0<Real.sqrt (q (U y)-z^2) := hh.2.2.1
  have hrad : q (U y)-z^2≠0 := by
    intro h
    rw [h,Real.sqrt_zero] at hv
    exact lt_irrefl _ hv
  have hd := (((hasDerivAt_id' (x := z)).fun_pow 2).const_sub (q (U y))).sqrt hrad
  refine hd.congr_deriv ?_
  rw [show speed z y=Real.sqrt (q (U y)-z^2) from rfl,
    div_eq_div_iff (mul_pos two_pos hv).ne' hv.ne']
  push_cast
  ring

lemma phase_source_hasDerivAt {y z : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (phase z) (first z y) y := by
  have hh := OppositeTwo.PrimaryInverse.data hy hz
  have hr : 0<radius y := by linarith [hh.1]
  have hv : 0<speed z y := hh.2.2.1
  have hr2 : (radius y)^2=q (U y) := hh.2.1
  have ha := OppositeTwo.PrimaryInverse.argument_bounds hy hz
  have hratio : HasDerivAt (fun t => z/radius t) (-z*ratio y/(radius y)^3) y := by
    have hd := (hasDerivAt_const y z).fun_div
      (NegativeTwo.ContactInverse.radius_hasDerivAt hy) hr.ne'
    refine hd.congr_deriv ?_
    have hr' := hr.ne'
    field_simp
    ring
  have hder : HasDerivAt (fun t => Real.arcsin (z/radius t))
      (-z*ratio y/(q (U y)*speed z y)) y := by
    have hd := (Real.hasDerivAt_arcsin (by linarith : z/radius y≠-1)
      (by linarith : z/radius y≠1)).comp y hratio
    refine hd.congr_deriv ?_
    rw [OppositeTwo.PrimaryInverse.inverse_root hy hz,←hr2]
    have hr' := hr.ne'
    have hv' := hv.ne'
    field_simp
  exact ((NegativeTwo.ContactInverse.base_hasDerivAt hy).neg.fun_add hder).congr_deriv
    (by simp only [first]; ring)

lemma phase_shift_hasDerivAt {y z : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (fun t => phase t y) (1/speed z y) z := by
  have hh := OppositeTwo.PrimaryInverse.data hy hz
  have hr : 0<radius y := by linarith [hh.1]
  have hv : 0<speed z y := hh.2.2.1
  have ha := OppositeTwo.PrimaryInverse.argument_bounds hy hz
  have hd := (Real.hasDerivAt_arcsin (by linarith : z/radius y≠-1)
    (by linarith : z/radius y≠1)).comp z ((hasDerivAt_id' (x := z)).div_const (radius y))
  refine (hd.const_add (-base y)).congr_deriv ?_
  rw [OppositeTwo.PrimaryInverse.inverse_root hy hz]
  have hr' := hr.ne'
  have hv' := hv.ne'
  field_simp

lemma first_source_hasDerivAt {y z : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (first z) (second z y) y := by
  have hh := OppositeTwo.PrimaryInverse.data hy hz
  have hu := U_positive (outer_domain hy)
  have hq : q (U y)≠0 := by linarith [NegativeTwo.Inverse.actual_q_positive hy]
  have hv : 0<speed z y := hh.2.2.1
  have hU : HasDerivAt U (-ratio y) y :=
    (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hy)).add_const (1/2)
  have hf := (NegativeTwo.Inverse.factor_hasDerivAt hu.ne' hq).comp y hU
  have hden := ((NegativeTwo.Inverse.q_hasDerivAt (U y)).comp y hU).fun_mul
    (speed_source_hasDerivAt hy hz)
  have hnum := (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hy)).const_mul z
  have hd := hf.fun_sub (hnum.fun_div hden (mul_ne_zero hq hv.ne'))
  refine hd.congr_deriv ?_
  have hrD : ratioD y=Q0/(U y)^3 := rfl
  simp only [second,NegativeTwo.Inverse.brace,Function.comp_apply,hrD]
  have hu' := hu.ne'
  have hv' := hv.ne'
  field_simp
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
  have hv : 0<speed z y := hh.2.2.1
  have hc : z^2+(speed z y)^2=q (U y) := hh.2.2.2
  have hden := (speed_shift_hasDerivAt hy hz).const_mul (q (U y))
  have hnum := (hasDerivAt_id' (x := z)).mul_const (ratio y)
  have hd := (hnum.fun_div hden (mul_ne_zero hq hv.ne')).const_sub (factor (U y))
  refine hd.congr_deriv ?_
  have hv' := hv.ne'
  rw [← hc] at hq ⊢
  field_simp
  ring

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

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerInverse
end
end
end

section
/-!
## Exact third derivatives of the lower inverse rotation

The source second derivative is a cubic in the positive speed quotient.
Differentiating that identity gives the five-term expression used on
each complete analytic minimum regime.  No estimate enters these
differential identities.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerInverse
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def factorDD (u : ℝ) : ℝ :=
  2*Q0/((Q0+1)*u^3)+8*(Q0-1)/((Q0+1)*(q u)^3)
def X (y : ℝ) : ℝ := -ratioD y*factorD (U y)+(ratio y)^2*factorDD (U y)
def A1 (y : ℝ) : ℝ :=
  9*ratio y*ratioD y/(q (U y))^2-15*(ratio y)^3/(q (U y))^3-ratioDD y/q (U y)
def A3 (y : ℝ) : ℝ :=
  3*ratio y*ratioD y/(q (U y))^2-10*(ratio y)^3/(q (U y))^3
def quotient (z y : ℝ) : ℝ := z/speed z y
def third (z y : ℝ) : ℝ := X y+A1 y*quotient z y+A3 y*(quotient z y)^3-
  3*(ratio y)^3/(q (U y))^3*(quotient z y)^5

lemma factorD_hasDerivAt {u : ℝ} (hu : u≠0) (hq : q u≠0) :
    HasDerivAt factorD (factorDD u) u := by
  have hnum : HasDerivAt NegativeTwo.Inverse.N (4*Q0-4*u) u := by
    have h := (((hasDerivAt_id' (x := u)).const_mul (4*Q0)).fun_sub
      (((hasDerivAt_id' (x := u)).fun_pow 2).const_mul 2)).sub_const (Q0*(Q0+1))
    refine h.congr_deriv ?_
    push_cast
    ring
  have hqd := NegativeTwo.Inverse.q_hasDerivAt u
  have hq' : NegativeTwo.Inverse.q u≠0 := hq
  have hden := ((hasDerivAt_id' (x := u)).fun_pow 2).fun_mul (hqd.fun_pow 2)
  have hd := hnum.fun_div hden (mul_ne_zero (pow_ne_zero 2 hu) (pow_ne_zero 2 hq'))
  refine hd.congr_deriv ?_
  simp only [factorDD,q,NegativeTwo.Inverse.q,NegativeTwo.Inverse.N] at hq' ⊢
  have hQ1 : Q0+1≠0 := by norm_num [Q0]
  rw [div_add_div _ _ (mul_ne_zero hQ1 (pow_ne_zero 3 hu)) (mul_ne_zero hQ1 (pow_ne_zero 3 hq')),
    div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero (pow_ne_zero 2 hu) (pow_ne_zero 2 hq')))
      (mul_ne_zero (mul_ne_zero hQ1 (pow_ne_zero 3 hu)) (mul_ne_zero hQ1 (pow_ne_zero 3 hq')))]
  simp only [Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,pow_one,mul_one]
  ring

lemma factorDD_positive {u : ℝ} (hu : 0<u) (hq : 0<q u) : 0<factorDD u := by
  have hQ : (0:ℝ)<Q0 ∧ 0<Q0-1 ∧ 0<Q0+1 := by norm_num [Q0]
  have h1 : 0<2*Q0/((Q0+1)*u^3) := div_pos (by linarith [hQ.1]) (mul_pos hQ.2.2 (pow_pos hu 3))
  have h2 : 0<8*(Q0-1)/((Q0+1)*(q u)^3) :=
    div_pos (by linarith [hQ.2.1]) (mul_pos hQ.2.2 (pow_pos hq 3))
  simp only [factorDD]
  linarith

lemma second_cubic {z y : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    second z y= -ratio y*factorD (U y)+(ratio y)^2/(q (U y))^2*(quotient z y)^3+
      (3*(ratio y)^2/(q (U y))^2-ratioD y/q (U y))*quotient z y := by
  have hh := OppositeTwo.PrimaryInverse.data hy hz
  have hu := U_positive (outer_domain hy)
  have hq : q (U y)≠0 := by linarith [NegativeTwo.Inverse.actual_q_positive hy]
  have hn : q (U y)=z^2+(speed z y)^2 := hh.2.2.2.symm
  dsimp [second,quotient,NegativeTwo.Inverse.brace]
  change -ratio y*factorD (U y)-z/(q (U y)*speed z y)*
    (ratioD y-2*(ratio y)^2/q (U y)-(ratio y)^2/(speed z y)^2)=_
  field_simp [hq,hh.2.2.1.ne']
  rw [hn]
  ring

lemma second_source_hasDerivAt {z y : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (second z) (third z y) y := by
  have hh := OppositeTwo.PrimaryInverse.data hy hz
  have hu := U_positive (outer_domain hy)
  have hq : q (U y)≠0 := by linarith [NegativeTwo.Inverse.actual_q_positive hy]
  have hv : 0<speed z y := hh.2.2.1
  have hn : q (U y)=z^2+(speed z y)^2 := hh.2.2.2.symm
  have hU : HasDerivAt U (-ratio y) y :=
    (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hy)).add_const (1/2)
  have hqD : HasDerivAt (fun t => q (U t)) (2*ratio y) y :=
    ((NegativeTwo.Inverse.q_hasDerivAt (U y)).comp y hU).congr_deriv (by ring)
  have hrD := ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hy)
  have hrDD := ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hy)
  have hvD := speed_source_hasDerivAt hy hz
  have hfD : HasDerivAt (fun t => factorD (U t)) (-(factorDD (U y)*ratio y)) y :=
    ((factorD_hasDerivAt hu.ne' hq).comp y hU).congr_deriv (by ring)
  have hr2 : HasDerivAt (fun t => ratio t^2) (2*ratio y*ratioD y) y :=
    (hrD.fun_pow 2).congr_deriv (by push_cast; ring)
  have hv2 : HasDerivAt (fun t => speed z t^2) (2*ratio y) y :=
    (hvD.fun_pow 2).congr_deriv (by have hv' := hv.ne'; field_simp; ring)
  have hbr := (hrDD.fun_sub ((hr2.const_mul 2).fun_div hqD hq)).fun_sub
    (hr2.fun_div hv2 (pow_ne_zero 2 hv.ne'))
  have hweight := (hasDerivAt_const y z).fun_div (hqD.fun_mul hvD) (mul_ne_zero hq hv.ne')
  have hd := (hrD.fun_mul hfD).neg.fun_sub (hweight.fun_mul hbr)
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · simp only [third,X,A1,A3,quotient]
    rw [hn] at hq ⊢
    have hv' := hv.ne'
    field_simp
    ring
  · simp only [second,NegativeTwo.Inverse.brace,Pi.neg_apply]
    rw [show ratioD t=Q0/(U t)^3 from rfl]
    ring

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerInverse
end
end
end

section
/-!
## One rational source reference on the target diagonal

The inverse angle is bounded from below by a direct trigonometric
contact comparison.  All radical and derivative bounds concern this
single rational source coordinate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.UpperDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

def reference : ℝ := 542853/100000000
def referenceAngle : ℝ := 4521/40000

lemma reference_mem : reference∈Icc 0 (1/10) := by norm_num [reference]

lemma reference_U : (7652599/4000000:ℝ)<U reference ∧
    U reference<23914372/12500000 := by
  exact shifted_chart_reference (outer_domain (early_domain reference_mem))
    (by norm_num) (by norm_num) (by norm_num [reference,W,Q0])
    (by norm_num [reference,W,Q0])

lemma reference_q : (3404064/3125000:ℝ)<NegativeTwo.Inverse.q (U reference) ∧
    NegativeTwo.Inverse.q (U reference)<2178601/2000000 := by
  dsimp [NegativeTwo.Inverse.q]
  norm_num [Q0]
  constructor <;> linarith [reference_U.1,reference_U.2]

lemma reference_z : (19960703/50000000:ℝ)<z ∧ z<39921407/100000000 := by
  dsimp [z,OppositeTwo.TargetRatio.z]
  constructor <;> linarith [diagonal_fine.1,diagonal_fine.2]

lemma reference_speed : (19286561/20000000:ℝ)<speed reference ∧
    speed reference<12054101/12500000 := by
  have hd := OppositeTwo.PrimaryInverse.data (early_domain reference_mem) z_mem
  have hvp : 0<speed reference := hd.2.2.1
  have hvn : z^2+(speed reference)^2=NegativeTwo.Inverse.q (U reference) := hd.2.2.2
  constructor <;> nlinarith [reference_q.1,reference_q.2,reference_z.1,reference_z.2,hvp,hvn]

lemma reference_ratio : (26418659/100000000:ℝ)<ratio reference ∧
    ratio reference<26418661/100000000 := by
  have hu := U_positive (outer_domain (early_domain reference_mem))
  have hU := reference_U
  have hr0 : reference=542853/100000000 := rfl
  change (26418659/100000000:ℝ)<(reference+1/2)/U reference ∧
    (reference+1/2)/U reference<26418661/100000000
  constructor
  · rw [lt_div_iff₀ hu]
    linarith only [hU.2,hr0]
  · rw [div_lt_iff₀ hu]
    linarith only [hU.1,hr0]

lemma reference_factor : (12010885/12500000:ℝ)<NegativeTwo.Inverse.factor (U reference) ∧
    NegativeTwo.Inverse.factor (U reference)<9608711/10000000 := by
  have hu := U_positive (outer_domain (early_domain reference_mem))
  have hU := reference_U
  have hQ := reference_q
  have hq : 0<NegativeTwo.Inverse.q (U reference) := by linarith only [hQ.1]
  have hlo := mul_lt_mul hU.1 hQ.1.le (by norm_num) hu.le
  have hhi := mul_lt_mul hU.2 hQ.2.le hq (by norm_num)
  have hQ0 : Q0=9789/2500 := rfl
  simp only [NegativeTwo.Inverse.factor]
  constructor
  · rw [lt_div_iff₀ (mul_pos hu hq)]
    linarith only [hhi,hU.2,hQ0]
  · rw [div_lt_iff₀ (mul_pos hu hq)]
    linarith only [hlo,hU.1,hQ0]

lemma reference_correction :
    (502011/5000000:ℝ)<z*ratio reference/(NegativeTwo.Inverse.q (U reference)*speed reference) ∧
    z*ratio reference/(NegativeTwo.Inverse.q (U reference)*speed reference)<502013/5000000 := by
  have hq : 0<NegativeTwo.Inverse.q (U reference) := by linarith only [reference_q.1]
  have hv : 0<speed reference := by linarith only [reference_speed.1]
  have hz := reference_z
  have hr := reference_ratio
  have hQ := reference_q
  have hV := reference_speed
  have hnlo := mul_lt_mul hz.1 hr.1.le (by norm_num) (by linarith only [hz.1] : 0≤z)
  have hnhi := mul_lt_mul hz.2 hr.2.le (by linarith only [hr.1] : 0<ratio reference) (by norm_num)
  have hdlo := mul_lt_mul hQ.1 hV.1.le (by norm_num) hq.le
  have hdhi := mul_lt_mul hQ.2 hV.2.le hv (by norm_num)
  constructor
  · rw [lt_div_iff₀ (mul_pos hq hv)]
    linarith only [hnlo,hdhi]
  · rw [div_lt_iff₀ (mul_pos hq hv)]
    linarith only [hnhi,hdlo]

lemma reference_T : T reference<(22481/1000000:ℝ) ∧
    (13265915/12500000:ℝ)<TLabel.d1 reference ∧
      TLabel.d1 reference<1326592/1250000 := by
  have hh := FixedReference.target (early_domain reference_mem)
    (show reference∈Icc reference reference from ⟨le_rfl,le_rfl⟩)
    ⟨reference_U.1.le,reference_U.2.le⟩
    (by norm_num [reference]) (by norm_num)
  have h1 : FixedReference.valueHi reference reference (7652599/4000000) (23914372/12500000)<
      22481/1000000 := by
    norm_num [FixedReference.valueHi,reference]
  have h2 : (13265915/12500000:ℝ)<
      FixedReference.firstLo reference reference (7652599/4000000) (23914372/12500000) := by
    norm_num [FixedReference.firstLo,reference]
  have h3 : FixedReference.firstHi reference reference (7652599/4000000) (23914372/12500000)<
      1326592/1250000 := by
    norm_num [FixedReference.firstHi,reference]
  exact ⟨hh.2.1.trans_lt h1,h2.trans_le hh.2.2.1,hh.2.2.2.1.trans_lt h3⟩

lemma reference_first : |first reference|<(1/1000000:ℝ) := by
  have hF := reference_factor
  have hc := reference_correction
  have hT := reference_T
  rw [abs_lt]
  dsimp [first]
  rw [OppositeTwo.TargetRatio.F_formula]
  constructor <;> linarith

lemma reference_contact_before : outerDiagonal<upperPrimary reference referenceAngle := by
  have hx : referenceAngle∈Icc 0 (7/10) := by norm_num [referenceAngle]
  have hs := sin_le_sin9 hx.1
  have hc := cos10_le_cos hx.1
  have ht := positive_trig hx
  have hu : arc reference-1/2<(11414372/12500000:ℝ) := by
    have hh := reference_U.2
    dsimp [U] at hh
    linarith only [hh]
  have hproduct := mul_le_mul hu.le hs ht.2.2.1 (by norm_num)
  have hx0 : referenceAngle=4521/40000 := rfl
  have hr0 : reference=542853/100000000 := rfl
  rw [hx0] at hc hproduct
  norm_num [sin9,sin7,cos10,cos8] at hc hproduct
  have hd := diagonal_fine.2
  simp only [upperPrimary]
  rw [hx0,hr0]
  rw [hr0] at hproduct
  linarith only [hd,hc,hproduct]

lemma reference_angle : referenceAngle<UpperInverse.X z reference := by
  have hzero : 0≤UpperInverse.X z reference :=
    UpperInverse.X_nonnegative (early_domain reference_mem) (by
      dsimp [z,OppositeTwo.TargetRatio.z,W,reference]
      linarith [outer_endpoint_bounds.2.2.2])
  by_contra hbad
  have hle : UpperInverse.X z reference≤referenceAngle := le_of_not_gt hbad
  have hx : referenceAngle∈Icc 0 (7/10) := by norm_num [referenceAngle]
  have hX : UpperInverse.X z reference∈Icc 0 (7/10) := ⟨hzero,hle.trans hx.2⟩
  have hmono := upperPrimary_antitone (early_domain reference_mem) hX hx hle
  rw [UpperInverse.X_contact (early_domain reference_mem) z_mem] at hmono
  have he : z+1/2=outerDiagonal := by dsimp [z,OppositeTwo.TargetRatio.z]; ring
  rw [he] at hmono
  linarith [reference_contact_before]

lemma reference_value : (224443/250000:ℝ)<value reference := by
  have hx := reference_angle
  have ht := reference_T.1
  have hl := L_diagonal_upper
  dsimp [value,referenceAngle] at *
  linarith [pi_hand_enclosure.1]

end SquaresInCircles.Eight.SecondWord.OppositeThree.UpperDiagonal
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.UpperDiagonal
open CommonQuarter CorePairGeometry Arithmetic

theorem early_lower {b : ℝ} (hb : b∈Icc 0 (1/10)) :
    (89777/100000:ℝ)<value b := by
  have ht := curvature_tangent (κ := (9/10:ℝ)) hb reference_mem
    (fun t ht => value_hasDerivAt (early_domain ht))
    (fun t ht => first_hasDerivAt (early_domain ht))
    (fun t ht => (early_curvature ht).le)
  have hs := abs_lt.mp reference_first
  have hsq : (first reference)^2<(1/1000000:ℝ)^2 := by nlinarith
  nlinarith [reference_value,sq_nonneg ((9/10)*(b-reference)+first reference)]

theorem lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (89777/100000:ℝ)<value b := by
  by_cases hearly : b≤1/10
  · exact early_lower ⟨hb.1,hearly⟩
  · have hh := late_monotone
      ⟨le_rfl,UpperTarget.tenth_mem.2⟩ ⟨by linarith,hb.2⟩ (by linarith)
    exact (early_lower (show (1/10:ℝ)∈Icc 0 (1/10) by norm_num)).trans_le hh

end SquaresInCircles.Eight.SecondWord.OppositeThree.UpperDiagonal
end
end
end

module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSameSecondaryTargetRatio

/-!
# The actual late source-diagonal secondary arc and its speed

Uncompiled transcription of Section 4.2 of
`HAND_SHORT_WORD_SAME_SIGN_SECONDARY_COMPLETE_WITHOUT_TABLES.md`.
The two coordinates are those of the already constructed exact circle
rotation, exchanged after the simultaneous-diagonal event. The speed
and its second derivative retain the factor and its exact derivatives.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Negative.SourceDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)
open Diagonal (Z Y horizontal vertical height factor factorD)

abbrev offset := SecondWord.NegativeTwo.PrimaryDiagonal.offset
def numerator (x : ℝ) : ℝ :=
  (1-Q0+offset^2)*Real.cos x+offset*(1+(Real.cos x)^2)
def numeratorD (x : ℝ) : ℝ :=
  (Q0-1-offset^2-2*offset*Real.cos x)*Real.sin x
def factorDD (x : ℝ) : ℝ :=
  numeratorD x/(Y x)^3-3*numerator x*Z x*Real.sin x/(Y x)^5
def speed (x : ℝ) : ℝ := vertical x*factor x
def speedD (x : ℝ) : ℝ := horizontal x*(factor x)^2+vertical x*factorD x
def speedDD (x : ℝ) : ℝ :=
  -vertical x*(factor x)^3+3*horizontal x*factor x*factorD x+vertical x*factorDD x
def cost (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2-x+c r+(t r-P r)*outerDiagonal+p r*(vertical x-1/2)-q r*(horizontal x-1/2)
def first (r : Row) (x : ℝ) : ℝ :=
  -1+q r*speed x+p r*horizontal x*factor x

lemma numerator_identity {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    factorD x*(Y x)^3=numerator x :=
  SecondWord.NegativeTwo.PrimaryDiagonal.factorD_numerator hx

lemma numerator_hasDerivAt (x : ℝ) : HasDerivAt numerator (numeratorD x) x := by
  convert ((Real.hasDerivAt_cos x).const_mul (1-Q0+offset^2)).add
    ((((Real.hasDerivAt_cos x).pow 2).const_add 1).const_mul offset) using 1
  · funext y; simp only [numerator,Pi.add_apply,Pi.pow_apply]
  · simp only [numeratorD]; ring

lemma factorD_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt factorD (factorDD x) x := by
  have hy : 0<Y x := by linarith [(SecondWord.NegativeTwo.PrimaryDiagonal.radical_data hx).2.2.1]
  have hlocal : factorD=ᶠ[𝓝 x] (fun y => numerator y/(Y y)^3) := by
    have hY : Continuous Y := by
      show Continuous (fun y => Real.sqrt (Q0-(Real.cos y+offset)^2))
      fun_prop
    have hO : IsOpen {y : ℝ | 0<Y y} := isOpen_lt continuous_const hY
    filter_upwards [hO.mem_nhds hy] with y hy'
    dsimp [factorD,SecondWord.NegativeTwo.PrimaryDiagonal.factorD,numerator,
      Y,SecondWord.NegativeTwo.PrimaryDiagonal.Y,Z,SecondWord.NegativeTwo.PrimaryDiagonal.Z]
    have hrad : 0≤Q0-(Real.cos y+offset)^2 := by
      have hh : 0<Real.sqrt (Q0-(Real.cos y+offset)^2) := hy'
      exact (Real.sqrt_pos.mp hh).le
    have hs := Real.sq_sqrt hrad
    congr 1
    linear_combination (Real.cos y+offset)*(Real.sin_sq_add_cos_sq y)-Real.cos y*hs
  have hd := (numerator_hasDerivAt x).div
    ((SecondWord.NegativeTwo.PrimaryDiagonal.Y_hasDerivAt hx).pow 3) (pow_ne_zero _ hy.ne')
  have he : HasDerivAt (fun y => numerator y/(Y y)^3) (factorDD x) x := by
    convert hd using 1
    simp only [factorDD,Pi.pow_apply]
    field_simp
    ring
  exact he.congr_of_eventuallyEq hlocal

lemma factorDD_nonnegative {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0≤factorDD x := by
  have ht := positive_trig hx
  have hdata := SecondWord.NegativeTwo.PrimaryDiagonal.radical_data hx
  have ho := SecondWord.NegativeTwo.PrimaryDiagonal.offset_bounds
  have hy : 0<Y x := by linarith [hdata.2.2.1]
  have hN : numerator x<0 := by
    rw [←numerator_identity hx]
    exact mul_neg_of_neg_of_pos
      (SecondWord.NegativeTwo.PrimaryDiagonal.factorD_negative hx) (pow_pos hy 3)
  have hcoef : 0≤Q0-1-offset^2-2*offset*Real.cos x := by
    have hp := mul_nonpos_of_nonpos_of_nonneg (show offset≤0 by linarith [ho.2])
      (show 0≤Real.cos x by linarith [ht.1])
    norm_num [Q0]
    nlinarith
  have hN' : 0≤numeratorD x := mul_nonneg hcoef ht.2.2.1
  have hfirst := div_nonneg hN' (pow_nonneg hy.le 3)
  have hsecond := div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hN] : 3*numerator x≤0) hdata.1.le)
      ht.2.2.1) (pow_nonneg hy.le 5)
  dsimp [factorDD]
  linarith

lemma factorD_monotone : MonotoneOn factorD (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
  (fun x hx => (factorD_hasDerivAt hx).continuousAt.continuousWithinAt)
  (fun x hx => factorD_hasDerivAt (Ioo_subset_Icc_self hx))
  (fun x hx => factorDD_nonnegative (Ioo_subset_Icc_self hx))

lemma speed_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) : HasDerivAt speed (speedD x) x := by
  convert (SecondWord.NegativeTwo.PrimaryDiagonal.vertical_hasDerivAt hx).mul
    (SecondWord.NegativeTwo.PrimaryDiagonal.factor_hasDerivAt hx) using 1
  · funext y; simp only [speed,vertical,factor,Pi.mul_apply]
  · simp only [speedD,horizontal,vertical,factor,factorD,
      SecondWord.NegativeTwo.PrimaryDiagonal.speed]
    ring

lemma speedD_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) : HasDerivAt speedD (speedDD x) x := by
  convert ((SecondWord.NegativeTwo.PrimaryDiagonal.horizontal_hasDerivAt hx).mul
    ((SecondWord.NegativeTwo.PrimaryDiagonal.factor_hasDerivAt hx).pow 2)).add
      ((SecondWord.NegativeTwo.PrimaryDiagonal.vertical_hasDerivAt hx).mul
        (factorD_hasDerivAt hx)) using 1
  · funext y
    simp only [speedD,horizontal,vertical,factor,factorD,Pi.add_apply,Pi.mul_apply,Pi.pow_apply]
  · simp only [speedDD,horizontal,vertical,factor,factorD,Pi.pow_apply,
      SecondWord.NegativeTwo.PrimaryDiagonal.speed]
    ring

lemma event_coordinates {e : ℝ} (he : Diagonal.IsEvent e) :
    horizontal e=outerDiagonal+1/2 ∧ vertical e=outerDiagonal+1/2 := by
  have hB := Diagonal.event_height he
  have hc := SecondWord.NegativeTwo.PrimaryDiagonal.circle (Diagonal.event_angle he)
  have hp := SecondWord.NegativeTwo.PrimaryDiagonal.coordinates_positive (Diagonal.event_angle he)
  change vertical e-1/2=outerDiagonal at hB
  exact ⟨by nlinarith [diagonal_circle,outer_endpoint_bounds.2.2.1],by linarith⟩

lemma late_state {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc e (7/10)) :
    OuterState (vertical x-1/2) (horizontal x-1/2) := by
  have hx' : x∈Icc 0 (7/10) := ⟨(Diagonal.event_angle he).1.trans hx.1,hx.2⟩
  have hc := SecondWord.NegativeTwo.PrimaryDiagonal.circle hx'
  have hp := SecondWord.NegativeTwo.PrimaryDiagonal.coordinates_positive hx'
  have hm := SecondWord.NegativeTwo.PrimaryDiagonal.height_monotone
    (Diagonal.event_angle he) hx' hx.1
  have hE : SecondWord.NegativeTwo.PrimaryDiagonal.height e=outerDiagonal :=
    Diagonal.event_height he
  rw [hE] at hm
  have hV : outerDiagonal+1/2≤vertical x := by
    change outerDiagonal≤vertical x-1/2 at hm
    linarith
  have hv2 := pow_le_pow_left₀
    (show 0≤outerDiagonal+1/2 by linarith [outer_endpoint_bounds.2.2.1]) hV 2
  have horder : horizontal x≤vertical x := by nlinarith [diagonal_circle]
  exact ⟨by linarith [hp.1],by linarith,by nlinarith only [hc]⟩

lemma cost_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (cost r) (first r x) x := by
  convert (((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+c r+(t r-P r)*outerDiagonal)).add
      (((SecondWord.NegativeTwo.PrimaryDiagonal.vertical_hasDerivAt hx).sub_const
        (1/2)).const_mul (p r))).sub
          (((SecondWord.NegativeTwo.PrimaryDiagonal.horizontal_hasDerivAt hx).sub_const
            (1/2)).const_mul (q r))) using 1
  · funext y
    simp only [cost,horizontal,vertical,Pi.add_apply,Pi.sub_apply,Pi.neg_apply,id_eq]
    ring
  · simp only [first,speed,horizontal,vertical,factor,
      SecondWord.NegativeTwo.PrimaryDiagonal.speed]
    ring

lemma original_coordinates {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (he : 1/2+(1/2-A)*Real.cos x+(1/2+B)*Real.sin x=outerDiagonal) :
    vertical x=A+1/2 ∧ horizontal x=B+1/2 := by
  let T : ℝ := (A+1/2)*Real.sin x+(B+1/2)*Real.cos x
  have htr := positive_trig hx
  have hT : 0<T := by
    have hs := mul_nonneg (show 0≤A+1/2 by linarith [ht.1,ht.2.1]) htr.2.2.1
    have hc := mul_pos (show 0<B+1/2 by linarith [ht.1])
      (show 0<Real.cos x by linarith [htr.1])
    dsimp [T]
    linarith
  have hZ : Z x=(A+1/2)*Real.cos x-(B+1/2)*Real.sin x := by
    dsimp [Z,SecondWord.NegativeTwo.PrimaryDiagonal.Z,offset,
      SecondWord.NegativeTwo.PrimaryDiagonal.offset]
    linarith
  have hcircle : T^2+(Z x)^2=Q0 := by
    rw [hZ]
    dsimp [T]
    linear_combination ht.2.2+((A+1/2)^2+(B+1/2)^2)*(Real.sin_sq_add_cos_sq x)
  have hY : Y x=T := by
    have hd := SecondWord.NegativeTwo.PrimaryDiagonal.radical_data hx
    nlinarith [hd.2.2.1,hd.2.2.2.2]
  constructor
  · show Y x*Real.sin x+Z x*Real.cos x=A+1/2
    rw [hY,hZ]
    dsimp [T]
    linear_combination (A+1/2)*(Real.sin_sq_add_cos_sq x)
  · show Y x*Real.cos x-Z x*Real.sin x=B+1/2
    rw [hY,hZ]
    dsimp [T]
    linear_combination (B+1/2)*(Real.sin_sq_add_cos_sq x)

lemma original_after_event {A B e x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (he : Diagonal.IsEvent e)
    (hc : 1/2+(1/2-A)*Real.cos x+(1/2+B)*Real.sin x=outerDiagonal) : e≤x := by
  have hh := original_coordinates ht hx hc
  have hA := (outer_bounds ht).1
  by_contra! hbad
  have hm := SecondWord.NegativeTwo.PrimaryDiagonal.height_half_monotone hx
    (Diagonal.event_angle he) hbad.le
  have hE : SecondWord.NegativeTwo.PrimaryDiagonal.height e=outerDiagonal :=
    Diagonal.event_height he
  simp only at hm
  rw [hE] at hm
  change vertical x-1/2-x/2≤outerDiagonal-e/2 at hm
  rw [hh.1] at hm
  linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Negative.SourceDiagonal

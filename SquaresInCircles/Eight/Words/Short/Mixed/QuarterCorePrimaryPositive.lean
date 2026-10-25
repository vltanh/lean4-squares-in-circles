module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Arithmetic.WholeIntervalPolynomial
public import SquaresInCircles.Eight.Owners.Stationary.TerminalWeights
public import SquaresInCircles.Eight.Stationary.System
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroLReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroAsymmetric
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroCycle
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterPrimaryReduction
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterReferences
public import SquaresInCircles.Eight.Words.Short.WordZero

/-!
# Eight squares: core-source primary contacts with positive outer target

The original primary separator excludes the lower angle half
and forces x > .4 on the upper half. The stated multiplier 1.6 gives
the exact outer axial support and the core-circle support. The resulting
single scalar decreases on the entire remaining interval.
-/

section
/-!
## Every negative outer target on a mixed source-secondary quarter edge

The multiplier is exactly the original core coefficient. Its remainder
vanishes, and the target support is axial. The three fixed coefficient
ranges supply derivative reserves on an entire half, never angle cells.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.CoreSecondaryNegative
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives Reference

def F (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  angle upper x+coC r-coP r*outerAxial+coG r/2+
    coG r/2*Real.sin x-coG r*(outerAxial-1/2)*Real.cos x
def Fd (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  direction upper+coG r/2*Real.cos x+coG r*(outerAxial-1/2)*Real.sin x
def loss (r : Row) : ℝ := if coG r≤477/500 then 0 else if coG r≤1 then 43/1000 else 19/100
def endpointFloor (r : Row) : ℝ :=
  if coG r≤477/500 then 921/1000 else if coG r≤1 then 47/50 else 519/500

theorem F_hasDerivAt (r : Row) (upper : Bool) (x : ℝ) :
    HasDerivAt (F r upper) (Fd r upper x) x := by
  have h := ((((hasDerivAt_id' x).const_mul (direction upper)).const_add
    (Real.pi/2+coC r-coP r*outerAxial+coG r/2)).add
      ((Real.hasDerivAt_sin x).const_mul (coG r/2))).sub
        ((Real.hasDerivAt_cos x).const_mul (coG r*(outerAxial-1/2)))
  have hF : F r upper=fun y => Real.pi/2+coC r-coP r*outerAxial+coG r/2+direction upper*y+
      coG r/2*Real.sin y-coG r*(outerAxial-1/2)*Real.cos y := by
    funext y
    simp only [F,angle]
    ring
  rw [hF]
  convert h using 1
  simp only [Fd]
  ring

theorem original_lower (r : Row) (hr : targetPositive r=false) (upper : Bool)
    {a b A B x : ℝ} (_hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourceSecondary r a b A B (angle upper x)) :
    F r upper x≤coreOuterCost r a b A B (angle upper x) := by
  have hb := coefficient_bounds r
  have htr := positive_trig hx
  have hsin : 0<coP r+coG r*Real.cos x := by
    have hp := mul_lt_mul_of_pos_left htr.1 hb.1
    linarith [hb.2.2.2.2.2.2.2.2.2.1]
  have hy : 0≤coQ r+direction upper*coG r*Real.sin x := by
    have hp := mul_lt_mul_of_pos_left htr.2.2.2.1 hb.1
    cases upper <;> dsimp [direction] <;> nlinarith [hb.2.2.2.2.2.2.2.2.1]
  have hsup := MixedQuarter.outer_axial_lower ht (show -(coP r+coG r*Real.cos x)≤0 by linarith) hy
  dsimp [sourceSecondary] at hm
  have hmult := mul_le_mul_of_nonneg_left hm hb.1.le
  rw [angle_width upper hx,angle_sin,angle_cos,targetSign_negative hr] at hmult
  dsimp [F,coreOuterCost]
  rw [targetSign_negative hr]
  nlinarith

theorem derivative_lower_half (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    Fd r false x≤loss r := by
  have hg := (coefficient_bounds r).1
  have hgu := (coefficient_bounds r).2.1
  have hA := outer_endpoint_bounds
  have htr := positive_trig hx
  let v := Real.cos x/2+(outerAxial-1/2)*Real.sin x
  have hv : 0≤v := by
    exact add_nonneg (div_nonneg (by linarith [htr.1]) (by norm_num))
      (mul_nonneg (by linarith [hA.1]) htr.2.2.1)
  have hs : v^2≤1/4+(outerAxial-1/2)^2 := by
    have hid : v^2+(Real.sin x/2-(outerAxial-1/2)*Real.cos x)^2=
        1/4+(outerAxial-1/2)^2 := by
      dsimp [v]
      linear_combination (1/4+(outerAxial-1/2)^2)*(Real.sin_sq_add_cos_sq x)
    nlinarith [sq_nonneg (Real.sin x/2-(outerAxial-1/2)*Real.cos x)]
  have hvs : v^2<(43489/40000:ℝ) := by nlinarith [hA.1,hA.2.1]
  have hvu : v<(1043/1000:ℝ) := by nlinarith
  have hgv : 0≤coG r*v := mul_nonneg hg.le hv
  by_cases hsmall : coG r≤477/500
  · have hgs : coG r^2≤(477/500:ℝ)^2 := pow_le_pow_left₀ hg.le hsmall 2
    have hp := mul_lt_mul_of_pos_right hvs (sq_pos_of_pos hg)
    have hq := mul_le_mul_of_nonneg_right hgs (by norm_num : (0:ℝ)≤43489/40000)
    have hbound : coG r*v<1 := by nlinarith
    dsimp [Fd,direction,loss]
    rw [ite_eq_left hsmall]
    dsimp [v] at hbound
    linarith
  · by_cases hmid : coG r≤1
    · have hp := mul_le_mul_of_nonneg_right hmid hv
      dsimp [Fd,direction,loss]
      rw [ite_eq_right hsmall,ite_eq_left hmid]
      dsimp [v] at hp hvu
      linarith
    · have hp := mul_lt_mul_of_pos_left hvu hg
      have hq : (1043/1000:ℝ)*coG r<(1043/1000)*(1139/1000) := by nlinarith
      dsimp [Fd,direction,loss]
      rw [ite_eq_right hsmall,ite_eq_right hmid]
      dsimp [v] at hp
      nlinarith

def endpointBox (r : Row) : Interval (F r false (7/10)) := by
  let s := sine (by norm_num : (0:ℝ)≤7/10)
  let k := cosine (by norm_num : (0:ℝ)≤7/10)
  convert ((((((halfPi.sub (Interval.point (7/10))).add (Interval.point (coC r))).sub
    ((Interval.point (coP r)).mul axial)).add (Interval.point (coG r/2))).add
      ((Interval.point (coG r/2)).mul s)).sub
        (((Interval.point (coG r)).mul (axial.sub (Interval.point (1/2)))).mul k))
    using 1
  dsimp [F,angle,direction]
  ring

private lemma r82_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl

private lemma r82_endpointBox_lo (r : Row) : (endpointBox r).lo =
    ((((((halfPi.sub (Interval.point (7/10))).add (Interval.point (coC r))).sub
    ((Interval.point (coP r)).mul axial)).add (Interval.point (coG r/2))).add
      ((Interval.point (coG r/2)).mul (sine (by norm_num : (0:ℝ)≤7/10)))).sub
        (((Interval.point (coG r)).mul (axial.sub (Interval.point (1/2)))).mul
          (cosine (by norm_num : (0:ℝ)≤7/10)))).lo := by
  unfold endpointBox
  dsimp only
  rw [r82_mpr_lo]
  dsimp [F,angle,direction]
  ring

theorem endpoint (r : Row) (hr : targetPositive r=false) : endpointFloor r<F r false (7/10) := by
  have hlo : endpointFloor r<(endpointBox r).lo := by
    rw [r82_endpointBox_lo]
    revert hr
    fin_cases r <;> norm_num [targetPositive] <;> simp only [endpointFloor] <;> mixed_fixed
  exact hlo.trans_le (endpointBox r).mem.1

theorem floor_reserve (r : Row) : (449/500:ℝ)<endpointFloor r-loss r*(7/10) ∧ 0≤loss r := by
  fin_cases r <;> norm_num [endpointFloor,loss,coG]

theorem lower_half (r : Row) (hr : targetPositive r=false) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : (449/500:ℝ)<F r false x := by
  have h := derivative_reserve (f:=fun z => -F r false z) (df:=fun z => -Fd r false z)
    (k:= -loss r) (fun z _ => (F_hasDerivAt r false z).neg.continuousAt.continuousWithinAt)
    (fun z _ => (F_hasDerivAt r false z).neg)
    (fun z hz => by linarith [derivative_lower_half r (Ioo_subset_Icc_self hz)])
    hx (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hx.2
  have hL := mul_nonneg (floor_reserve r).2 hx.1
  linarith [endpoint r hr,(floor_reserve r).1]

theorem upper_increases (r : Row) : MonotoneOn (F r true) (Icc 0 (7/10)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun x _ => (F_hasDerivAt r true x).continuousAt.continuousWithinAt)
    (fun x _ => F_hasDerivAt r true x)
  intro x hx
  have ht := positive_trig (Ioo_subset_Icc_self hx)
  have hg := (coefficient_bounds r).1
  have hA : 0≤outerAxial-1/2 := by linarith [outer_endpoint_bounds.1]
  dsimp [Fd,direction]
  have h1 := mul_nonneg hg.le (show 0≤Real.cos x by linarith [ht.1])
  have h2 := mul_nonneg (mul_nonneg hg.le hA) ht.2.2.1
  nlinarith

theorem all_angles (r : Row) (hr : targetPositive r=false) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : (449/500:ℝ)<F r upper x := by
  cases upper
  · exact lower_half r hr hx
  · have h0 := lower_half r hr (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
    have hm := upper_increases r (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hx hx.1
    have he : F r true 0=F r false 0 := by simp [F,angle]
    linarith

theorem original (r : Row) (hr : targetPositive r=false) (upper : Bool)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourceSecondary r a b A B (angle upper x)) :
    (449/500:ℝ)<coreOuterCost r a b A B (angle upper x) :=
  (all_angles r hr upper hx).trans_le (original_lower r hr upper hs ht hx hm)

end SquaresInCircles.Eight.ShortWord.MixedQuarter.CoreSecondaryNegative
end
end
end

section
/-!
## All original outer-to-core secondary quarter contacts

The original outer transverse term cancels with its exact multiplier.
The negative core target has axial support; the positive target uses
the core-circle support on both closed pieces. The norm speed is bounded
by each vector length on each entire angle half.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterSecondary
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives Reference
open SecondWord.OppositeThree.ReferenceAlgebra (rootThree)

def sourceMinimum (r : Row) : ℝ := if 0≤ocP r then ocP r*outerDiagonal else ocP r*outerAxial
def negative (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  angle upper x+ocC r+sourceMinimum r+ocQ r/2+ocQ r/2*Real.sin x-ocQ r/12*Real.cos x
def negativeD (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  direction upper+ocQ r/2*Real.cos x+ocQ r/12*Real.sin x
def mass (r : Row) : ℝ := ocQ r^2+ocG r^2
def wave (r : Row) (upper : Bool) : ℝ := 2*direction upper*ocQ r*ocG r
def N (r : Row) (upper : Bool) (x : ℝ) : ℝ := CircularNorm.norm (mass r) 0 (wave r upper) x
def Nd (r : Row) (upper : Bool) (x : ℝ) : ℝ := CircularNorm.d1 (mass r) 0 (wave r upper) x
def positive (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  angle upper x+ocC r+sourceMinimum r+(ocQ r-ocG r)/2+
    (if upper then 0 else ocQ r*Real.sin x)-N r upper x/12
def positiveD (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  direction upper+(if upper then 0 else ocQ r*Real.cos x)-Nd r upper x/12
def loss (r : Row) : ℝ := if ocQ r≤19/20 then 3/100 else 3/10
def endpointFloor (r : Row) : ℝ := if ocQ r≤19/20 then 1103/1000 else 178/125

theorem source_lower (r : Row) {a b : ℝ} (hs : OuterState a b) : sourceMinimum r≤ocP r*a := by
  have h := outer_bounds hs
  by_cases hp : 0≤ocP r
  · simpa [sourceMinimum,hp] using mul_le_mul_of_nonneg_left h.1 hp
  · simpa [sourceMinimum,hp] using mul_le_mul_of_nonpos_left h.2.1 (le_of_not_ge hp)

theorem energy_identity (r : Row) (upper : Bool) (x : ℝ) :
    CircularNorm.energy (mass r) 0 (wave r upper) x=
      (-ocQ r*Real.cos x)^2+(-direction upper*ocQ r*Real.sin x-ocG r)^2 := by
  cases upper <;> dsimp [CircularNorm.energy,mass,wave,direction] <;>
    linear_combination -(ocQ r)^2*(Real.sin_sq_add_cos_sq x)

theorem energy_positive (r : Row) (upper : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<CircularNorm.energy (mass r) 0 (wave r upper) x := by
  have hq := (coefficient_bounds r).2.2.2.2.2.2.1
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  rw [energy_identity]
  exact add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero (mul_ne_zero (neg_ne_zero.mpr hq.ne') hc.ne')) (sq_nonneg _)

theorem N_positive (r : Row) (upper : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<N r upper x :=
  CircularNorm.norm_pos (energy_positive r upper hx)
theorem N_square (r : Row) (upper : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    N r upper x^2=mass r+wave r upper*Real.sin x := by
  simpa [N,CircularNorm.energy] using CircularNorm.norm_sq (energy_positive r upper hx).le

theorem speed_bound (r : Row) (upper : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    |Nd r upper x|≤ min (ocQ r) (ocG r) := by
  have hN := N_positive r upper hx
  have hN2 := N_square r upper hx
  have hq := (coefficient_bounds r).2.2.2.2.2.2.1
  have hg := (coefficient_bounds r).2.2.2.2.1
  have hform : Nd r upper x=direction upper*ocQ r*ocG r*Real.cos x/N r upper x := by
    dsimp [Nd,CircularNorm.d1,CircularNorm.slope,wave,N]
    ring
  have hqSq : (direction upper*ocQ r*ocG r*Real.cos x)^2≤ocQ r^2*N r upper x^2 := by
    have he : ocQ r^2*N r upper x^2-(direction upper*ocQ r*ocG r*Real.cos x)^2=
        ocQ r^2*(ocQ r+direction upper*ocG r*Real.sin x)^2 := by
      rw [hN2]
      cases upper <;> dsimp [mass,wave,direction] <;>
        linear_combination -(ocQ r*ocG r)^2*(Real.sin_sq_add_cos_sq x)
    nlinarith [sq_nonneg (ocQ r+direction upper*ocG r*Real.sin x),sq_nonneg (ocQ r)]
  have hgSq : (direction upper*ocQ r*ocG r*Real.cos x)^2≤ocG r^2*N r upper x^2 := by
    have he : ocG r^2*N r upper x^2-(direction upper*ocQ r*ocG r*Real.cos x)^2=
        ocG r^2*(ocG r+direction upper*ocQ r*Real.sin x)^2 := by
      rw [hN2]
      cases upper <;> dsimp [mass,wave,direction] <;>
        linear_combination -(ocQ r*ocG r)^2*(Real.sin_sq_add_cos_sq x)
    nlinarith [sq_nonneg (ocG r+direction upper*ocQ r*Real.sin x),sq_nonneg (ocG r)]
  rw [hform,abs_div,abs_of_pos hN]
  apply le_min
  · apply (div_le_iff₀ hN).2
    nlinarith [abs_nonneg (direction upper*ocQ r*ocG r*Real.cos x),
      sq_abs (direction upper*ocQ r*ocG r*Real.cos x),mul_pos hq hN]
  · apply (div_le_iff₀ hN).2
    nlinarith [abs_nonneg (direction upper*ocQ r*ocG r*Real.cos x),
      sq_abs (direction upper*ocQ r*ocG r*Real.cos x),mul_pos hg hN]

theorem negative_hasDerivAt (r : Row) (upper : Bool) (x : ℝ) :
    HasDerivAt (negative r upper) (negativeD r upper x) x := by
  have h1 : HasDerivAt (fun y => angle upper y+ocC r+sourceMinimum r+ocQ r/2)
      (direction upper*1) x :=
    ((((hasDerivAt_id' x).const_mul (direction upper)).const_add (Real.pi/2)).add_const
      (ocC r)).add_const (sourceMinimum r) |>.add_const (ocQ r/2)
  have h2 := (h1.fun_add ((Real.hasDerivAt_sin x).const_mul (ocQ r/2))).fun_sub
    ((Real.hasDerivAt_cos x).const_mul (ocQ r/12))
  have h3 : HasDerivAt (negative r upper)
      (direction upper*1+ocQ r/2*Real.cos x-ocQ r/12*(-Real.sin x)) x := h2
  exact h3.congr_deriv (by simp only [negativeD]; ring)

theorem positive_hasDerivAt (r : Row) (upper : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (positive r upper) (positiveD r upper x) x := by
  have hn := CircularNorm.norm_hasDerivAt (energy_positive r upper hx)
  have h1 : HasDerivAt (fun y => angle upper y+ocC r+sourceMinimum r+(ocQ r-ocG r)/2)
      (direction upper*1) x :=
    ((((hasDerivAt_id' x).const_mul (direction upper)).const_add (Real.pi/2)).add_const
      (ocC r)).add_const (sourceMinimum r) |>.add_const ((ocQ r-ocG r)/2)
  cases upper
  · have h2 := (h1.fun_add ((Real.hasDerivAt_sin x).const_mul (ocQ r))).fun_sub (hn.div_const 12)
    have h3 : HasDerivAt (positive r false)
        (direction false*1+ocQ r*Real.cos x-CircularNorm.d1 (mass r) 0 (wave r false) x/12) x :=
      h2
    exact h3.congr_deriv (by simp only [positiveD,Nd,Bool.false_eq_true,↓reduceIte]; ring)
  · have h2 := (h1.fun_add (hasDerivAt_const x (0:ℝ))).fun_sub (hn.div_const 12)
    have h3 : HasDerivAt (positive r true)
        (direction true*1+0-CircularNorm.d1 (mass r) 0 (wave r true) x/12) x := h2
    exact h3.congr_deriv (by simp only [positiveD,Nd,↓reduceIte]; ring)

theorem negative_original_lower (r : Row) (hr : targetPositive r=false) (upper : Bool)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourceSecondary r a b A B (angle upper x)) :
    negative r upper x≤outerCoreCost r a b A B (angle upper x) := by
  obtain ⟨_,_,_,_,hg,hgu,hq,hqu,_,_,hgap⟩ := coefficient_bounds r
  have htr := positive_trig hx
  have hv : 0≤ocG r+direction upper*ocQ r*Real.sin x := by
    have hh := mul_lt_mul_of_pos_left htr.2.2.2.1 hq
    cases upper <;> dsimp [direction] <;> nlinarith
  have hu : -ocQ r*Real.cos x≤0 := by nlinarith [htr.1]
  have hcore := core_axial_lower ht hu hv
  have hsmin := source_lower r hs
  dsimp [sourceSecondary] at hm
  have hmult := mul_le_mul_of_nonneg_left hm hq.le
  rw [angle_width upper hx,angle_sin,angle_cos,targetSign_negative hr] at hmult
  dsimp [negative,outerCoreCost]
  rw [targetSign_negative hr]
  nlinarith

theorem positive_original_lower (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourceSecondary r a b A B (angle upper x)) :
    positive r upper x≤outerCoreCost r a b A B (angle upper x) := by
  obtain ⟨_,_,_,_,hg,hgu,hq,hqu,_,_,hgap⟩ := coefficient_bounds r
  have htr := positive_trig hx
  have hv : -direction upper*ocQ r*Real.sin x-ocG r≤0 := by
    have hh := mul_lt_mul_of_pos_left htr.2.2.2.1 hq
    cases upper <;> dsimp [direction] <;> nlinarith
  have hcore := core_circle_lower (X:= -ocQ r*Real.cos x) ht hv
  have he : Real.sqrt ((-ocQ r*Real.cos x)^2+
      (-direction upper*ocQ r*Real.sin x-ocG r)^2)=N r upper x := by
    rw [N,CircularNorm.norm,energy_identity]
  rw [he] at hcore
  have hsmin := source_lower r hs
  dsimp [sourceSecondary] at hm
  have hmult := mul_le_mul_of_nonneg_left hm hq.le
  rw [angle_width upper hx,angle_sin,angle_cos,targetSign_positive hr] at hmult
  dsimp [positive,outerCoreCost]
  rw [targetSign_positive hr]
  cases upper <;> dsimp [direction] at * <;> nlinarith

def sourceBox (r : Row) : Interval (sourceMinimum r) := by
  by_cases hp : 0≤ocP r
  · simpa [sourceMinimum,hp] using (Interval.point (ocP r)).mul ShortWord.MixedQuarter.Reference.diagonal
  · simpa [sourceMinimum,hp] using (Interval.point (ocP r)).mul axial
def negativeEndpoint (r : Row) : Interval (negative r false (7/10)) := by
  let s := sine (by norm_num : (0:ℝ)≤7/10)
  let k := cosine (by norm_num : (0:ℝ)≤7/10)
  convert ((((((halfPi.sub (Interval.point (7/10))).add (Interval.point (ocC r))).add
    (sourceBox r)).add (Interval.point (ocQ r/2))).add
      ((Interval.point (ocQ r/2)).mul s)).sub ((Interval.point (ocQ r/12)).mul k))
    using 1
  dsimp [negative,angle,direction]
  ring
def energyEndpoint (r : Row) : Interval (mass r+wave r false*Real.sin (7/10)) :=
  (Interval.point (mass r)).add ((Interval.point (wave r false)).mul
    (sine (by norm_num : (0:ℝ)≤7/10)))
theorem energyEndpoint_nonnegative (r : Row) : 0≤(energyEndpoint r).lo := by
  fin_cases r <;> dsimp [energyEndpoint,mass,wave,direction] <;> mixed_fixed

private theorem r84_negative_endpoint_of (r : Row) {S : ℝ} (B : Interval S)
    (hS : sourceMinimum r=S)
    (h : (1381/1000:ℝ)<((((((halfPi.sub (Interval.point (7/10))).add
      (Interval.point (ocC r))).add B).add (Interval.point (ocQ r/2))).add
        ((Interval.point (ocQ r/2)).mul
          (MixedQuarter.Reference.sine (by norm_num : (0:ℝ)≤7/10)))).sub
            ((Interval.point (ocQ r/12)).mul
              (MixedQuarter.Reference.cosine (by norm_num : (0:ℝ)≤7/10)))).lo) :
    (1381/1000:ℝ)<negative r false (7/10) := by
  have h2 := h.trans_le ((((((halfPi.sub (Interval.point (7/10))).add
      (Interval.point (ocC r))).add B).add (Interval.point (ocQ r/2))).add
        ((Interval.point (ocQ r/2)).mul
          (MixedQuarter.Reference.sine (by norm_num : (0:ℝ)≤7/10)))).sub
            ((Interval.point (ocQ r/12)).mul
              (MixedQuarter.Reference.cosine (by norm_num : (0:ℝ)≤7/10)))).mem.1
  have e : negative r false (7/10)=Real.pi/2-7/10+ocC r+S+ocQ r/2+
      ocQ r/2*Real.sin (7/10)-ocQ r/12*Real.cos (7/10) := by
    simp only [negative,angle,direction,hS,Bool.false_eq_true,↓reduceIte]
    ring
  rw [e]
  exact h2

theorem negative_endpoint (r : Row) (hr : targetPositive r=false) :
    (1381/1000:ℝ)<negative r false (7/10) := by
  by_cases hp : 0≤ocP r
  · apply r84_negative_endpoint_of r
      ((Interval.point (ocP r)).mul ShortWord.MixedQuarter.Reference.diagonal)
      (by simp [sourceMinimum,hp])
    fin_cases r <;> norm_num [targetPositive] at hr <;> norm_num [ocP] at hp <;> mixed_fixed
  · apply r84_negative_endpoint_of r ((Interval.point (ocP r)).mul axial)
      (by simp [sourceMinimum,hp])
    fin_cases r <;> norm_num [targetPositive] at hr <;> norm_num [ocP] at hp <;> mixed_fixed
/-- A four-digit square root of each endpoint energy: one Newton step from it. -/
private def r84_guess : Row→ℝ :=
  ![1,9584/10000,8271/10000,9875/10000,1,8120/10000,7695/10000,8204/10000,1,1,7626/10000,1,1,7547/10000,7606/10000,7615/10000,1,1,7724/10000,1,8394/10000,8190/10000,8430/10000,1]
private theorem r84_guess_pos (r : Row) : 0<r84_guess r := by
  fin_cases r <;> norm_num [r84_guess]

private theorem r84_positive_endpoint_of (r : Row) {S : ℝ} (B : Interval S)
    (hS : sourceMinimum r=S)
    (h : endpointFloor r<((((((halfPi.sub (Interval.point (7/10))).add
      (Interval.point (ocC r))).add B).add (Interval.point ((ocQ r-ocG r)/2))).add
        ((Interval.point (ocQ r)).mul
          (MixedQuarter.Reference.sine (by norm_num : (0:ℝ)≤7/10)))).sub
            ((SecondWord.OppositeThree.ReferenceAlgebra.rootStep (energyEndpoint r) (r84_guess r)
              (r84_guess_pos r) (energyEndpoint_nonnegative r)).div
              (Interval.point 12) (by norm_num [Interval.point]))).lo) :
    endpointFloor r<positive r false (7/10) := by
  have h2 := h.trans_le ((((((halfPi.sub (Interval.point (7/10))).add
      (Interval.point (ocC r))).add B).add (Interval.point ((ocQ r-ocG r)/2))).add
        ((Interval.point (ocQ r)).mul
          (MixedQuarter.Reference.sine (by norm_num : (0:ℝ)≤7/10)))).sub
            ((SecondWord.OppositeThree.ReferenceAlgebra.rootStep (energyEndpoint r) (r84_guess r)
              (r84_guess_pos r) (energyEndpoint_nonnegative r)).div
              (Interval.point 12) (by norm_num [Interval.point]))).mem.1
  have e : positive r false (7/10)=Real.pi/2-7/10+ocC r+S+(ocQ r-ocG r)/2+
      ocQ r*Real.sin (7/10)-Real.sqrt (mass r+wave r false*Real.sin (7/10))/12 := by
    simp only [positive,angle,direction,hS,N,CircularNorm.norm,CircularNorm.energy,
      Bool.false_eq_true,↓reduceIte,zero_mul,add_zero]
    ring
  rw [e]
  exact h2

theorem positive_endpoint (r : Row) (hr : targetPositive r=true) :
    endpointFloor r<positive r false (7/10) := by
  by_cases hp : 0≤ocP r
  · apply r84_positive_endpoint_of r
      ((Interval.point (ocP r)).mul ShortWord.MixedQuarter.Reference.diagonal)
      (by simp [sourceMinimum,hp])
    fin_cases r <;> norm_num [targetPositive] at hr <;> norm_num [ocP] at hp <;>
      dsimp [energyEndpoint,endpointFloor,mass,wave,direction,r84_guess] <;> mixed_fixed
  · apply r84_positive_endpoint_of r ((Interval.point (ocP r)).mul axial)
      (by simp [sourceMinimum,hp])
    fin_cases r <;> norm_num [targetPositive] at hr <;> norm_num [ocP] at hp <;>
      dsimp [energyEndpoint,endpointFloor,mass,wave,direction,r84_guess] <;> mixed_fixed

theorem negative_all (r : Row) (hr : targetPositive r=false) (upper : Bool)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : (449/500:ℝ)<negative r upper x := by
  have hq := (coefficient_bounds r).2.2.2.2.2.2.1
  have hqu := (coefficient_bounds r).2.2.2.2.2.2.2.1
  have hlow : AntitoneOn (negative r false) (Icc 0 (7/10)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun s _ => (negative_hasDerivAt r false s).continuousAt.continuousWithinAt)
      (fun s _ => negative_hasDerivAt r false s)
    intro s hs
    have htr := positive_trig (Ioo_subset_Icc_self hs)
    have h1 := mul_le_mul_of_nonneg_left (Real.cos_le_one s) hq.le
    have h2 := mul_le_mul_of_nonneg_left htr.2.2.2.1.le hq.le
    dsimp [negativeD,direction]
    nlinarith
  have hhigh : MonotoneOn (negative r true) (Icc 0 (7/10)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun s _ => (negative_hasDerivAt r true s).continuousAt.continuousWithinAt)
      (fun s _ => negative_hasDerivAt r true s)
    intro s hs
    have htr := positive_trig (Ioo_subset_Icc_self hs)
    dsimp [negativeD,direction]
    have h1 := mul_nonneg hq.le (show 0≤Real.cos s by linarith [htr.1])
    have h2 := mul_nonneg hq.le htr.2.2.1
    nlinarith
  have hcap : (7/10:ℝ)∈Icc 0 (7/10) := by norm_num
  have hz : (0:ℝ)∈Icc 0 (7/10) := by norm_num
  cases upper
  · linarith [hlow hx hcap hx.2,negative_endpoint r hr]
  · have he : negative r true 0=negative r false 0 := by simp [negative,angle]
    linarith [hlow hz hcap (by norm_num),hhigh hz hx hx.1,negative_endpoint r hr]

theorem positive_lower_derivative (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    positiveD r false x≤loss r := by
  have hq := (coefficient_bounds r).2.2.2.2.2.2.1
  have hqu := (coefficient_bounds r).2.2.2.2.2.2.2.1
  have hs := (abs_le.mp ((speed_bound r false hx).trans (min_le_left _ _))).1
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hq.le
  by_cases hh : ocQ r≤19/20 <;> simp [positiveD,direction,loss,hh] <;> linarith

theorem positive_all (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : (449/500:ℝ)<positive r upper x := by
  have hq := (coefficient_bounds r).2.2.2.2.2.2.1
  have hqu := (coefficient_bounds r).2.2.2.2.2.2.2.1
  have hlow (s : ℝ) (hs : s∈Icc 0 (7/10)) : (449/500:ℝ)<positive r false s := by
    have h := derivative_reserve (f:=fun z => -positive r false z)
      (df:=fun z => -positiveD r false z) (k:= -loss r)
      (fun z hz => (positive_hasDerivAt r false hz).neg.continuousAt.continuousWithinAt)
      (fun z hz => (positive_hasDerivAt r false (Ioo_subset_Icc_self hz)).neg)
      (fun z hz => by linarith [positive_lower_derivative r (Ioo_subset_Icc_self hz)])
      hs (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hs.2
    have hl : (449/500:ℝ)<endpointFloor r-loss r*(7/10) ∧ 0≤loss r := by
      fin_cases r <;> norm_num [endpointFloor,loss,ocQ]
    have hprod := mul_nonneg hl.2 hs.1
    linarith [positive_endpoint r hr,hl.1]
  cases upper
  · exact hlow x hx
  · have hm : MonotoneOn (positive r true) (Icc 0 (7/10)) := by
      apply monoOn_of_hasDeriv_nonneg
        (fun z hz => (positive_hasDerivAt r true hz).continuousAt.continuousWithinAt)
        (fun z hz => positive_hasDerivAt r true (Ioo_subset_Icc_self hz))
      intro z hz
      have hs := (abs_le.mp ((speed_bound r true (Ioo_subset_Icc_self hz)).trans (min_le_left _ _))).2
      dsimp [positiveD,direction]
      linarith
    have he : positive r true 0=positive r false 0 := by
      simp [positive,angle,N,CircularNorm.norm,CircularNorm.energy]
    have hz : (0:ℝ)∈Icc 0 (7/10) := by norm_num
    linarith [hlow 0 hz,hm hz hx hx.1]

theorem original (r : Row) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourceSecondary r a b A B (angle upper x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle upper x) := by
  cases hr : targetPositive r
  · exact (negative_all r hr upper hx).trans_le (negative_original_lower r hr upper hs ht hx hm)
  · exact (positive_all r hr upper hx).trans_le (positive_original_lower r hr upper hs ht hx hm)

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterSecondary
end
end
end

section
/-!
## Named endpoints of the positive-target secondary supports

Concavity has already been proved on both whole
halves. The only substitutions are alignment, the physical cap, and
the original negative-source feasibility cap phi=1.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.CoreSecondaryPositive
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives Reference

def energyBox (r : Row) (upper : Bool) {x : ℝ}
    (S : Interval (Real.sin x)) (C : Interval (Real.cos x)) :
    Interval (CircularNorm.energy (mass r) (cosineWeight r) (sineWeight r upper) x) :=
  ((Interval.point (mass r)).add ((Interval.point (cosineWeight r)).mul C)).add
    ((Interval.point (sineWeight r upper)).mul S)
def normBox (r : Row) (upper : Bool) {x : ℝ}
    (S : Interval (Real.sin x)) (C : Interval (Real.cos x))
    (hn : 0≤(energyBox r upper S C).lo) : Interval (N r upper x) :=
  rootSix (energyBox r upper S C) 2 (by norm_num) hn
def valueBox (r : Row) (upper : Bool) {x : ℝ} (X : Interval x)
    (S : Interval (Real.sin x)) (C : Interval (Real.cos x))
    (hn : 0≤(energyBox r upper S C).lo) : Interval (F r upper x) := by
  let T : Interval (if upper then Real.sin x else 0) := by
    cases upper
    · exact Interval.point 0
    · exact S
  convert (((((halfPi.add ((Interval.point (direction upper)).mul X)).add
    (Interval.point (coC r))).add (Interval.point ((lambda r+coP r+coQ r)/2))).add
      ((Interval.point (lambda r)).mul (C.add T))).sub (circleRadius.mul (normBox r upper S C hn)))
    using 1
  cases upper <;> dsimp [F,angle,T,direction]

def zeroS : Interval (Real.sin (0:ℝ)) := by simpa using Interval.point (0:ℝ)
def zeroC : Interval (Real.cos (0:ℝ)) := by simpa using Interval.point (1:ℝ)
private lemma r83_mpr_lo {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).lo=S.lo := by subst e; rfl
private lemma r83_mpr_hi {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).hi=S.hi := by subst e; rfl
private lemma r83_zeroS_lo : zeroS.lo=0 := r83_mpr_lo Real.sin_zero _ _
private lemma r83_zeroS_hi : zeroS.hi=0 := r83_mpr_hi Real.sin_zero _ _
private lemma r83_zeroC_lo : zeroC.lo=1 := r83_mpr_lo Real.cos_zero _ _
private lemma r83_zeroC_hi : zeroC.hi=1 := r83_mpr_hi Real.cos_zero _ _
private lemma r83_valueBox_false_lo (r : Row) {x : ℝ} (X : Interval x)
    (S : Interval (Real.sin x)) (C : Interval (Real.cos x)) (hn : 0≤(energyBox r false S C).lo) :
    (valueBox r false X S C hn).lo=(((((halfPi.add ((Interval.point (direction false)).mul X)).add
      (Interval.point (coC r))).add (Interval.point ((lambda r+coP r+coQ r)/2))).add
        ((Interval.point (lambda r)).mul (C.add (Interval.point 0)))).sub
          (circleRadius.mul (normBox r false S C hn))).lo := by
  unfold valueBox
  exact r83_mpr_lo (by simp only [F,angle]) _ _
private lemma r83_valueBox_true_lo (r : Row) {x : ℝ} (X : Interval x)
    (S : Interval (Real.sin x)) (C : Interval (Real.cos x)) (hn : 0≤(energyBox r true S C).lo) :
    (valueBox r true X S C hn).lo=(((((halfPi.add ((Interval.point (direction true)).mul X)).add
      (Interval.point (coC r))).add (Interval.point ((lambda r+coP r+coQ r)/2))).add
        ((Interval.point (lambda r)).mul (C.add S))).sub
          (circleRadius.mul (normBox r true S C hn))).lo := by
  unfold valueBox
  exact r83_mpr_lo (by simp only [F,angle]) _ _
private lemma r83_rows (r : Row) (hr : targetPositive r=true) :
    r=1 ∨ r=2 ∨ r=3 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=10 ∨ r=13 ∨ r=14 ∨ r=15 ∨ r=18 ∨ r=20 ∨ r=21 ∨ r=22 := by
  fin_cases r <;> simp_all [targetPositive]

local macro "r83_fixed" : tactic => `(tactic|
  norm_num [r83_zeroS_lo,r83_zeroS_hi,r83_zeroC_lo,r83_zeroC_hi,
    energyBox,normBox,mass,cosineWeight,sineWeight,direction,lambda,
    Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    piBox,halfPi,axial,circleRadius,Reference.sine,Reference.cosine,
    rootSix,SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
    SecondWord.OppositeThree.ReferenceAlgebra.rootStep,HighOrderTaylor.S15,HighOrderTaylor.S13,
    HighOrderTaylor.S11,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8,
    coC,coP,coQ,coG,Q0])
theorem zero_energy (r : Row) (hr : targetPositive r=true) :
    0≤(energyBox r false zeroS zeroC).lo := by
  rcases r83_rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> r83_fixed
theorem aligned (r : Row) (hr : targetPositive r=true) : (89809/100000:ℝ)<F r false 0 := by
  have hlo : (89809/100000:ℝ)<
      (valueBox r false (Interval.point 0) zeroS zeroC (zero_energy r hr)).lo := by
    rw [r83_valueBox_false_lo]
    rcases r83_rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> r83_fixed
  exact hlo.trans_le (valueBox r false _ zeroS zeroC (zero_energy r hr)).mem.1

theorem cap_energy (r : Row) (hr : targetPositive r=true) (upper : Bool) :
    0≤(energyBox r upper (sine (by norm_num : (0:ℝ)≤7/10))
      (cosine (by norm_num : (0:ℝ)≤7/10))).lo := by
  fin_cases r <;> cases upper <;> norm_num [targetPositive] at hr <;>
    dsimp [energyBox,mass,cosineWeight,sineWeight,direction,lambda] <;> mixed_fixed
theorem lower_cap (r : Row) (hr : targetPositive r=true) (hs : sourcePositive r=true) :
    (1813/2000:ℝ)<F r false (7/10) := by
  have hlo : (1813/2000:ℝ)<(valueBox r false (Interval.point (7/10))
      (sine (by norm_num : (0:ℝ)≤7/10)) (cosine (by norm_num : (0:ℝ)≤7/10))
        (cap_energy r hr false)).lo := by
    rw [r83_valueBox_false_lo]
    have hrows : r=1 ∨ r=5 ∨ r=10 ∨ r=13 ∨ r=18 ∨ r=22 := by
      rcases r83_rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp_all [sourcePositive]
    rcases hrows with rfl|rfl|rfl|rfl|rfl|rfl <;> r83_fixed
  exact hlo.trans_le (valueBox r false _ _ _ (cap_energy r hr false)).mem.1
private lemma r83_upper_cap_first (r : Row) (hr : targetPositive r=true)
    (hrows : r=1 ∨ r=2 ∨ r=3 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=10) :
    (119/100:ℝ)<(valueBox r true (Interval.point (7/10))
      (sine (by norm_num : (0:ℝ)≤7/10)) (cosine (by norm_num : (0:ℝ)≤7/10))
        (cap_energy r hr true)).lo := by
  rw [r83_valueBox_true_lo]
  rcases hrows with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> r83_fixed
private lemma r83_upper_cap_second (r : Row) (hr : targetPositive r=true)
    (hrows : r=13 ∨ r=14 ∨ r=15 ∨ r=18 ∨ r=20 ∨ r=21 ∨ r=22) :
    (119/100:ℝ)<(valueBox r true (Interval.point (7/10))
      (sine (by norm_num : (0:ℝ)≤7/10)) (cosine (by norm_num : (0:ℝ)≤7/10))
        (cap_energy r hr true)).lo := by
  rw [r83_valueBox_true_lo]
  rcases hrows with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> r83_fixed
theorem upper_cap (r : Row) (hr : targetPositive r=true) : (119/100:ℝ)<F r true (7/10) := by
  have hlo : (119/100:ℝ)<(valueBox r true (Interval.point (7/10))
      (sine (by norm_num : (0:ℝ)≤7/10)) (cosine (by norm_num : (0:ℝ)≤7/10))
        (cap_energy r hr true)).lo := by
    have hsplit : (r=1 ∨ r=2 ∨ r=3 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=10) ∨
        (r=13 ∨ r=14 ∨ r=15 ∨ r=18 ∨ r=20 ∨ r=21 ∨ r=22) := by
      rcases r83_rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    rcases hsplit with h|h
    · exact r83_upper_cap_first r hr h
    · exact r83_upper_cap_second r hr h
  exact hlo.trans_le (valueBox r true _ _ _ (cap_energy r hr true)).mem.1

def cut : ℝ := Real.pi/2-1
theorem cut_mem : cut∈Icc 0 (7/10) := by
  dsimp [cut]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]
def cutS : Interval (Real.sin cut) := by
  simpa [cut,Real.sin_sub] using cosine (by norm_num : (0:ℝ)≤1)
def cutC : Interval (Real.cos cut) := by
  simpa [cut,Real.cos_sub] using sine (by norm_num : (0:ℝ)≤1)
def cutX : Interval cut := halfPi.sub (Interval.point 1)
private lemma r83_cutS_lo : cutS.lo=(cosine (by norm_num : (0:ℝ)≤1)).lo := by
  unfold cutS
  exact r83_mpr_lo (by rw [cut,Real.sin_pi_div_two_sub]) _ _
private lemma r83_cutS_hi : cutS.hi=(cosine (by norm_num : (0:ℝ)≤1)).hi := by
  unfold cutS
  exact r83_mpr_hi (by rw [cut,Real.sin_pi_div_two_sub]) _ _
private lemma r83_cutC_lo : cutC.lo=(sine (by norm_num : (0:ℝ)≤1)).lo := by
  unfold cutC
  exact r83_mpr_lo (by rw [cut,Real.cos_pi_div_two_sub]) _ _
private lemma r83_cutC_hi : cutC.hi=(sine (by norm_num : (0:ℝ)≤1)).hi := by
  unfold cutC
  exact r83_mpr_hi (by rw [cut,Real.cos_pi_div_two_sub]) _ _

theorem cut_energy (r : Row) (hr : targetPositive r=true) :
    0≤(energyBox r false cutS cutC).lo := by
  rcases r83_rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [r83_cutS_lo,r83_cutS_hi,r83_cutC_lo,r83_cutC_hi,cutX,
      energyBox,normBox,mass,cosineWeight,sineWeight,direction,lambda,
      Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
      piBox,halfPi,axial,circleRadius,Reference.sine,Reference.cosine,
      rootSix,SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
      SecondWord.OppositeThree.ReferenceAlgebra.rootStep,HighOrderTaylor.S15,HighOrderTaylor.S13,
      HighOrderTaylor.S11,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8,
      coC,coP,coQ,coG,Q0]
theorem lower_cut (r : Row) (hr : targetPositive r=true) (hs : sourcePositive r=false) :
    (1813/2000:ℝ)<F r false cut := by
  have hlo : (1813/2000:ℝ)<(valueBox r false cutX cutS cutC (cut_energy r hr)).lo := by
    rw [r83_valueBox_false_lo]
    have hrows : r=2 ∨ r=3 ∨ r=6 ∨ r=7 ∨ r=14 ∨ r=15 ∨ r=20 ∨ r=21 := by
      rcases r83_rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp_all [sourcePositive]
    rcases hrows with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [r83_cutS_lo,r83_cutS_hi,r83_cutC_lo,r83_cutC_hi,cutX,
        energyBox,normBox,mass,cosineWeight,sineWeight,direction,lambda,
        Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
        Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
        piBox,halfPi,axial,circleRadius,Reference.sine,Reference.cosine,
        rootSix,SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
        SecondWord.OppositeThree.ReferenceAlgebra.rootStep,HighOrderTaylor.S15,HighOrderTaylor.S13,
        HighOrderTaylor.S11,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
        Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8,
        coC,coP,coQ,coG,Q0]
  exact hlo.trans_le (valueBox r false cutX cutS cutC (cut_energy r hr)).mem.1

def cap (x : ℝ) : ℝ := (outerAxial-1/2)*Real.cos x-Real.sin x/2-1/2
theorem cap_antitone : AntitoneOn cap (Icc 0 (7/10)) := by
  have hd : ∀ x, HasDerivAt cap (-(outerAxial-1/2)*Real.sin x-Real.cos x/2) x := by
    intro x
    have h := (((Real.hasDerivAt_cos x).const_mul (outerAxial-1/2)).fun_sub
      ((Real.hasDerivAt_sin x).div_const 2)).sub_const (1/2)
    exact h.congr_deriv (by ring)
  apply antiOn_of_hasDeriv_nonpos (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => hd x)
  intro x hx
  have ht := positive_trig (Ioo_subset_Icc_self hx)
  have hh := mul_nonneg (show 0≤outerAxial-1/2 by linarith [outer_endpoint_bounds.1]) ht.2.2.1
  linarith [ht.1]
theorem cap_cut_negative : cap cut<0 := by
  let B := (((axial.sub (Interval.point (1/2))).mul cutC).sub
    (cutS.div (Interval.point 2) (by norm_num [Interval.point]))).sub (Interval.point (1/2))
  have hhi : B.hi<0 := by
    simp only [B]
    norm_num [r83_cutS_lo,r83_cutS_hi,r83_cutC_lo,r83_cutC_hi,cutX,
      energyBox,normBox,mass,cosineWeight,sineWeight,direction,lambda,
      Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
      piBox,halfPi,axial,circleRadius,Reference.sine,Reference.cosine,
      rootSix,SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
      SecondWord.OppositeThree.ReferenceAlgebra.rootStep,HighOrderTaylor.S15,HighOrderTaylor.S13,
      HighOrderTaylor.S11,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8,
      coC,coP,coQ,coG,Q0]
  exact B.mem.2.trans_lt hhi

theorem original_lower_cut (r : Row) (hr : targetPositive r=true) (hσ : sourcePositive r=false)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourceSecondary r a b A B (angle false x)) : x<cut := by
  have hcore := CoreAngleEndpoint.state_bounds hs
  have houter := outer_bounds ht
  have htr := positive_trig hx
  have hA := mul_le_mul_of_nonneg_right houter.2.1 (show 0≤Real.cos x by linarith [htr.1])
  have hB := mul_nonneg ht.1 htr.2.2.1
  dsimp [sourceSecondary] at hm
  rw [angle_width false hx,angle_sin,angle_cos] at hm
  simp [sourceSign,targetSign,WordProblems.sign,hσ,hr,direction] at hm
  have hcap : 0≤cap x := by dsimp [cap]; nlinarith
  by_contra! hbad
  have h := cap_antitone cut_mem hx hbad
  linarith [cap_cut_negative]

end SquaresInCircles.Eight.ShortWord.MixedQuarter.CoreSecondaryPositive
end
end
end

section
/-!
## Every positive outer target on a mixed source-secondary quarter edge

The original weak separator supplies the source sign's precise lower
angle domain. Whole-half concavity and its proved geometric endpoints
then give the corrected original role-label inequality.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.CoreSecondaryPositive
open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourceSecondary r a b A B (angle upper x)) :
    F r upper x≤coreOuterCost r a b A B (angle upper x) := by
  have hh := fixed_coefficients r hr
  have hb := CoreAngleEndpoint.state_bounds hs
  have hrem := mul_nonneg hh.2.1 hb.2.2.1
  have hsup := outer_circle_lower (X:= -coP r-lambda r*Real.cos x)
    (Y:= -direction upper*lambda r*Real.sin x-coQ r) ht
  have he : Real.sqrt ((-coP r-lambda r*Real.cos x)^2+
      (-direction upper*lambda r*Real.sin x-coQ r)^2)=N r upper x := by
    rw [N,CircularNorm.norm,energy_identity]
    congr 1
    ring
  rw [he] at hsup
  dsimp [sourceSecondary] at hm
  have hmult := mul_le_mul_of_nonneg_left hm hh.1.le
  rw [angle_width upper hx,angle_sin,angle_cos,targetSign_positive hr] at hmult
  dsimp [F,coreOuterCost]
  rw [targetSign_positive hr]
  cases upper <;> dsimp [direction] at * <;> nlinarith

theorem scalar_lower (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {x : ℝ} (hx : x∈Icc 0 (7/10))
    (hcut : upper=false → sourcePositive r=false → x≤cut) : (449/500:ℝ)<F r upper x := by
  have hzero : (0:ℝ)∈Icc 0 (7/10) := by norm_num
  have hcap : (7/10:ℝ)∈Icc 0 (7/10) := by norm_num
  cases upper
  · cases hs : sourcePositive r
    · have hx' : x∈Icc 0 cut := ⟨hx.1,hcut rfl hs⟩
      have h := (concave r hr false).min_le_of_mem_Icc hzero cut_mem hx'
      have hm : (449/500:ℝ)< min (F r false 0) (F r false cut) :=
        lt_min (by linarith [aligned r hr]) (by linarith [lower_cut r hr hs])
      exact hm.trans_le h
    · have h := (concave r hr false).min_le_of_mem_Icc hzero hcap hx
      have hm : (449/500:ℝ)< min (F r false 0) (F r false (7/10)) :=
        lt_min (by linarith [aligned r hr]) (by linarith [lower_cap r hr hs])
      exact hm.trans_le h
  · have he : F r true 0=F r false 0 := by
      simp [F,angle,N,CircularNorm.norm,CircularNorm.energy]
    have h := (concave r hr true).min_le_of_mem_Icc hzero hcap hx
    have hm : (449/500:ℝ)< min (F r true 0) (F r true (7/10)) :=
      lt_min (by linarith [aligned r hr]) (by linarith [upper_cap r hr])
    exact hm.trans_le h

theorem original (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourceSecondary r a b A B (angle upper x)) :
    (449/500:ℝ)<coreOuterCost r a b A B (angle upper x) := by
  have hcut : upper=false → sourcePositive r=false → x≤cut := by
    rintro rfl hσ
    exact (original_lower_cut r hr hσ hs ht hx hm).le
  exact (scalar_lower r hr upper hx hcut).trans_le (original_lower r hr upper hs ht hx hm)

end SquaresInCircles.Eight.ShortWord.MixedQuarter.CoreSecondaryPositive
end
end
end

section
/-!
## Core-source primary contacts with negative outer target

The multiplier q/sin(phi) cancels the original target transverse term.
The lower-half derivative has the printed completed-square reserve;
the upper continuation loses at most the one concave tangent/secant
function on the whole physical interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.CorePrimaryNegative
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives Reference

def targetMaximum (r : Row) : ℝ := if 0≤coP r then coP r*outerAxial else coP r*outerDiagonal
def N (r : Row) (x : ℝ) : ℝ := Real.sqrt (coG r^2+(coQ r/Real.cos x)^2)
def Nd (r : Row) (x : ℝ) : ℝ := coQ r^2*Real.sin x/((Real.cos x)^3*N r x)
def constant (r : Row) : ℝ := coC r-coG r/2-targetMaximum r+coQ r/2
def F (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  angle upper x+constant r+
    coQ r*(if upper then -(outerAxial-1/2) else outerDiagonal+1/2)*
      (Real.sin x/Real.cos x)-N r x/12
def lowerD (r : Row) (x : ℝ) : ℝ :=
  -1+coQ r*(outerDiagonal+1/2)/(Real.cos x)^2-Nd r x/12
def tangentLoss (x : ℝ) : ℝ :=
  x-(567/500)*(183/200)*(Real.sin x/Real.cos x)-(189/2000)*(1/Real.cos x-1)
def tangentLossD (x : ℝ) : ℝ :=
  1-(567/500)*(183/200)/(Real.cos x)^2-(189/2000)*Real.sin x/(Real.cos x)^2
def tangentLossDD (x : ℝ) : ℝ :=
  -2*(567/500)*(183/200)*Real.sin x/(Real.cos x)^3-
    (189/2000)*(1+(Real.sin x)^2)/(Real.cos x)^3

theorem row_bounds (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=false) :
    coQ r≤567/500 ∧ 0< -1+(1399/1000)*coQ r-coQ r^2/576 := by
  revert hσ hτ
  fin_cases r <;> norm_num [sourcePositive,targetPositive,coQ]

theorem target_upper (r : Row) {A B : ℝ} (ht : OuterState A B) : coP r*A≤targetMaximum r := by
  have hb := outer_bounds ht
  by_cases hp : 0≤coP r
  · simpa [targetMaximum,hp] using mul_le_mul_of_nonneg_left hb.2.1 hp
  · simpa [targetMaximum,hp] using mul_le_mul_of_nonpos_left hb.1 (le_of_not_ge hp)

theorem N_positive (r : Row) (x : ℝ) : 0<N r x := by
  apply Real.sqrt_pos.mpr
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (coefficient_bounds r).1) (sq_nonneg _)
theorem N_square (r : Row) (x : ℝ) : N r x^2=coG r^2+(coQ r/Real.cos x)^2 :=
  Real.sq_sqrt (by positivity)
theorem N_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) : HasDerivAt (N r) (Nd r x) x := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  have hrad : coG r^2+(coQ r/Real.cos x)^2≠0 := by
    have hh := sq_pos_of_pos (coefficient_bounds r).1
    positivity
  have h := (((hasDerivAt_const x (coG r^2)).add
    (((hasDerivAt_const x (coQ r)).div (Real.hasDerivAt_cos x) hc).pow 2))).sqrt hrad
  convert h using 1
  · rfl
  · dsimp [Nd,N]
    field_simp [hc,(N_positive r x).ne']
    ring

theorem tangent_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (fun s => Real.sin s/Real.cos s) (1/(Real.cos x)^2) x := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  convert (Real.hasDerivAt_sin x).div (Real.hasDerivAt_cos x) hc using 1
  field_simp [hc]
  nlinarith [Real.sin_sq_add_cos_sq x]
theorem secant_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (fun s => 1/Real.cos s) (Real.sin x/(Real.cos x)^2) x := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  convert (hasDerivAt_const x (1:ℝ)).div (Real.hasDerivAt_cos x) hc using 1
  ring

theorem lower_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (F r false) (lowerD r x) x := by
  have h := ((((hasDerivAt_id' x).neg).const_add (Real.pi/2+constant r)).add
    ((tangent_hasDerivAt hx).const_mul (coQ r*(outerDiagonal+1/2)))).sub
      ((N_hasDerivAt r hx).div_const 12)
  have hF : F r false=fun y => Real.pi/2+constant r+-y+
      coQ r*(outerDiagonal+1/2)*(Real.sin y/Real.cos y)-N r y/12 := by
    funext y
    simp only [F,angle,direction,Bool.false_eq_true,↓reduceIte]
    ring
  rw [hF]
  convert h using 1
  simp only [lowerD]
  ring

theorem lower_derivative_positive (r : Row) (hσ : sourcePositive r=false)
    (hτ : targetPositive r=false) {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<lowerD r x := by
  have ht := positive_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  have hq := (coefficient_bounds r).2.2.1
  have hN := N_positive r x
  have hN2 := N_square r x
  have hrad : coQ r≤N r x*Real.cos x := by
    have hid : (N r x*Real.cos x)^2=(coG r*Real.cos x)^2+coQ r^2 := by
      rw [mul_pow,hN2]
      field_simp [hc.ne']
    nlinarith [mul_pos hN hc,sq_nonneg (coG r*Real.cos x)]
  have hratio : coQ r^2*Real.sin x/(N r x*Real.cos x)≤coQ r*Real.sin x := by
    apply (div_le_iff₀ (mul_pos hN hc)).2
    have hh := mul_le_mul_of_nonneg_left hrad (mul_nonneg hq.le ht.2.2.1)
    linarith
  have hid : lowerD r x*(Real.cos x)^2=
      -(Real.cos x)^2+coQ r*(outerDiagonal+1/2)-
        coQ r^2*Real.sin x/(12*(N r x*Real.cos x)) := by
    dsimp [lowerD,Nd]
    field_simp [hc.ne',hN.ne']
  have hdiag : (1399/1000:ℝ)<outerDiagonal+1/2 := by
    linarith [ShortMixedZero.fine_diagonal_bounds.1]
  have hd := mul_lt_mul_of_pos_left hdiag hq
  have hfloor := (row_bounds r hσ hτ).2
  have hsq := sq_nonneg (Real.sin x-coQ r/24)
  have hunit := Real.sin_sq_add_cos_sq x
  have h12 : coQ r^2*Real.sin x/(12*(N r x*Real.cos x))=
      (coQ r^2*Real.sin x/(N r x*Real.cos x))/12 := by ring
  have hprod : 0<lowerD r x*(Real.cos x)^2 := by
    nlinarith [hid,h12,hratio,hd,hfloor,hsq,hunit]
  exact (mul_pos_iff.mp hprod).resolve_right (by intro h; nlinarith [sq_nonneg (Real.cos x)]) |>.1

theorem lower_monotone (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=false) :
    MonotoneOn (F r false) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hx => (lower_hasDerivAt r hx).continuousAt.continuousWithinAt)
    (fun _ hx => lower_hasDerivAt r (Ioo_subset_Icc_self hx))
    (fun _ hx => (lower_derivative_positive r hσ hτ (Ioo_subset_Icc_self hx)).le)

theorem norm_continuation (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    N r x-N r 0≤coQ r*(1/Real.cos x-1) := by
  have ht := positive_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  have hq := (coefficient_bounds r).2.2.1
  have h0 := N_positive r 0
  have hn := N_positive r x
  have he0 := N_square r 0
  have he := N_square r x
  simp only [Real.cos_zero,div_one] at he0
  have hbase : coQ r≤N r 0 := by nlinarith [sq_nonneg (coG r)]
  have hsec : 0≤1/Real.cos x-1 := by
    have h : 1≤1/Real.cos x := by
      rw [le_div_iff₀ hc,one_mul]
      exact Real.cos_le_one x
    linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hbase) (mul_nonneg hq.le hsec)
  have hid : (coQ r/Real.cos x)^2=
      coQ r^2+2*coQ r^2*(1/Real.cos x-1)+(coQ r*(1/Real.cos x-1))^2 := by ring
  nlinarith [mul_nonneg hq.le hsec]

theorem tangentLoss_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt tangentLoss (tangentLossD x) x := by
  convert ((hasDerivAt_id' x).sub ((tangent_hasDerivAt hx).const_mul ((567/500)*(183/200)))).sub
    (((secant_hasDerivAt hx).sub_const 1).const_mul (189/2000)) using 1
  · rfl
  · simp only [tangentLossD]
    ring
theorem tangentLossD_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt tangentLossD (tangentLossDD x) x := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  have h := (((hasDerivAt_const x (1:ℝ)).sub
    ((hasDerivAt_const x ((567/500:ℝ)*(183/200))).div ((Real.hasDerivAt_cos x).pow 2)
      (pow_ne_zero 2 hc))).sub
        (((Real.hasDerivAt_sin x).const_mul (189/2000)).div ((Real.hasDerivAt_cos x).pow 2)
          (pow_ne_zero 2 hc)))
  convert h using 1
  · rfl
  · dsimp [tangentLossDD]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq x]
theorem tangentLoss_concave : ConcaveOn ℝ (Icc 0 (7/10)) tangentLoss := by
  apply concave_of_deriv2 (fun x hx => tangentLoss_hasDerivAt hx)
    (fun x hx => tangentLossD_hasDerivAt hx)
  intro x hx
  have ht := positive_trig hx
  have hc : 0<(Real.cos x)^3 := pow_pos (by linarith [ht.1]) 3
  have h1 := div_nonpos_of_nonpos_of_nonneg
    (show -2*(567/500:ℝ)*(183/200)*Real.sin x≤0 by nlinarith [ht.2.2.1]) hc.le
  have h2 := div_nonneg (show 0≤(189/2000:ℝ)*(1+(Real.sin x)^2) by positivity) hc.le
  dsimp [tangentLossDD]
  linarith

theorem tangentLoss_cap : -(21/100:ℝ)<tangentLoss (7/10) := by
  let S := sine (by norm_num : (0:ℝ)≤7/10)
  let C := cosine (by norm_num : (0:ℝ)≤7/10)
  have hc : 0<C.lo := by dsimp [C]; mixed_fixed
  let B := ((Interval.point (7/10)).sub
    ((Interval.point ((567/500:ℝ)*(183/200))).mul (S.div C hc))).sub
      ((Interval.point (189/2000)).mul ((C.inv hc).sub (Interval.point 1)))
  have hlo : -(21/100:ℝ)<B.lo := by dsimp [B,S,C]; mixed_fixed
  exact hlo.trans_le B.mem.1
theorem tangentLoss_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) : -(21/100:ℝ)<tangentLoss x := by
  have h := tangentLoss_concave.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 (7/10) by norm_num) (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hx
  have h0 : tangentLoss 0=0 := by simp [tangentLoss]
  have hm : -(21/100:ℝ)< min (tangentLoss 0) (tangentLoss (7/10)) :=
    lt_min (by rw [h0]; norm_num) tangentLoss_cap
  exact hm.trans_le h

def targetBox (r : Row) : Interval (targetMaximum r) := by
  by_cases hp : 0≤coP r
  · simpa [targetMaximum,hp] using (Interval.point (coP r)).mul axial
  · simpa [targetMaximum,hp] using (Interval.point (coP r)).mul ShortWord.MixedQuarter.Reference.diagonal
def zeroNorm (r : Row) : Interval (N r 0) := by
  have h := rootSix (Interval.point (coG r^2+coQ r^2)) 2 (by norm_num)
    (by dsimp [Interval.point]; positivity)
  simpa [N] using h
def zeroValue (r : Row) : Interval (F r false 0) := by
  convert (((((halfPi.add (Interval.point (coC r))).sub (Interval.point (coG r/2))).sub
    (targetBox r)).add (Interval.point (coQ r/2))).sub
      ((zeroNorm r).div (Interval.point 12) (by norm_num [Interval.point]))) using 1
  simp [F,angle,constant]
  ring

private lemma r82_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r82_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

private lemma r82_zeroValue_lo (r : Row) : (zeroValue r).lo =
    (((((halfPi.add (Interval.point (coC r))).sub (Interval.point (coG r/2))).sub
    (targetBox r)).add (Interval.point (coQ r/2))).sub
      ((zeroNorm r).div (Interval.point 12) (by norm_num [Interval.point]))).lo := by
  unfold zeroValue
  rw [r82_mpr_lo]
  simp [F,angle,constant]
  ring

private lemma r82_targetBox_hi (r : Row) : (targetBox r).hi =
    if 0≤coP r then ((Interval.point (coP r)).mul axial).hi
    else ((Interval.point (coP r)).mul ShortWord.MixedQuarter.Reference.diagonal).hi := by
  unfold targetBox
  split_ifs with hp
  · first
      | rfl
      | (rw [r82_mpr_hi]; simp [targetMaximum,hp])
  · first
      | rfl
      | (rw [r82_mpr_hi]; simp [targetMaximum,hp])

private lemma r82_zeroNorm_hi (r : Row) : (zeroNorm r).hi =
    (rootSix (Interval.point (coG r^2+coQ r^2)) 2 (by norm_num)
      (by dsimp [Interval.point]; positivity)).hi := by
  unfold zeroNorm
  first
    | rfl
    | (rw [r82_mpr_hi]; simp [N])

private lemma r82_zeroNorm_lo (r : Row) : (zeroNorm r).lo =
    (rootSix (Interval.point (coG r^2+coQ r^2)) 2 (by norm_num)
      (by dsimp [Interval.point]; positivity)).lo := by
  unfold zeroNorm
  first
    | rfl
    | (rw [r82_mpr_lo]; simp [N])

theorem aligned (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=false) :
    (32/25:ℝ)<F r false 0 := by
  have hlo : (32/25:ℝ)<(zeroValue r).lo := by
    revert hσ hτ
    fin_cases r <;> norm_num [sourcePositive,targetPositive] <;>
      norm_num [r82_zeroValue_lo,r82_targetBox_hi,r82_zeroNorm_hi,r82_zeroNorm_lo,
      Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
      piBox,halfPi,axial,ShortWord.MixedQuarter.Reference.diagonal,rootSix,
      SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
      SecondWord.OppositeThree.ReferenceAlgebra.rootStep,
      coC,coP,coQ,coG,Q0]
  exact hlo.trans_le (zeroValue r).mem.1

theorem upper_continuation (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=false)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : F r false 0+tangentLoss x≤F r true x := by
  have ht := positive_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  have hq := (coefficient_bounds r).2.2.1
  have hqu := (row_bounds r hσ hτ).1
  have htangent : 0≤Real.sin x/Real.cos x := div_nonneg ht.2.2.1 hc.le
  have hsec : 0≤1/Real.cos x-1 := by
    have h : 1≤1/Real.cos x := by
      rw [le_div_iff₀ hc,one_mul]
      exact Real.cos_le_one x
    linarith
  have hprod := mul_le_mul hqu (show outerAxial-1/2≤183/200 by linarith [outer_endpoint_bounds.2.1])
    (show 0≤outerAxial-1/2 by linarith [outer_endpoint_bounds.1]) (by norm_num : (0:ℝ)≤567/500)
  have htan := mul_le_mul_of_nonneg_right hprod htangent
  have hnorm := norm_continuation r hx
  have hsecQ := mul_le_mul_of_nonneg_right hqu hsec
  dsimp [F,angle,direction,tangentLoss]
  simp only [Real.sin_zero,Real.cos_zero,zero_div,mul_zero,add_zero]
  linarith

theorem scalar_lower (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=false)
    (upper : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) : (107/100:ℝ)<F r upper x := by
  cases upper
  · have hm := lower_monotone r hσ hτ (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hx hx.1
    linarith [aligned r hσ hτ]
  · linarith [aligned r hσ hτ,upper_continuation r hσ hτ hx,tangentLoss_lower hx]

theorem original_lower (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=false)
    (upper : Bool) {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle upper x)) :
    F r upper x≤coreOuterCost r a b A B (angle upper x) := by
  have htr := positive_trig hx
  have hc : 0<Real.cos x := by linarith [htr.1]
  have hq := (coefficient_bounds r).2.2.1
  have hg := (coefficient_bounds r).1
  let l := coQ r/Real.cos x
  have hl : 0≤l := div_nonneg hq.le hc.le
  have hid : l*Real.cos x=coQ r := div_mul_cancel₀ _ hc.ne'
  have hcore := core_circle_lower (X:= -l) (Y:= -coG r) hs (by linarith)
  have hroot : Real.sqrt ((-l)^2+(-coG r)^2)=N r x := by
    dsimp [N,l]
    congr 1
    ring
  rw [hroot] at hcore
  have htarget := target_upper r ht
  have hb := outer_bounds ht
  have htan := mul_nonneg hl htr.2.2.1
  have hAlo := mul_le_mul_of_nonneg_left hb.1 htan
  have hAhi := mul_le_mul_of_nonneg_left hb.2.1 htan
  dsimp [sourcePrimary] at hm
  have hmult := mul_le_mul_of_nonneg_left hm hl
  rw [angle_width upper hx,angle_sin,angle_cos,targetSign_negative hτ] at hmult
  have hsSign : sourceSign r= -1 := by simp [sourceSign,WordProblems.sign,hσ]
  dsimp [F,constant,coreOuterCost]
  rw [hsSign,targetSign_negative hτ]
  have htanEq : coQ r*(Real.sin x/Real.cos x)=l*Real.sin x := by dsimp [l]; ring
  cases upper <;> dsimp [direction] at * <;> nlinarith

theorem original (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=false)
    (upper : Bool) {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle upper x)) :
    (449/500:ℝ)<coreOuterCost r a b A B (angle upper x) := by
  have h := (scalar_lower r hσ hτ upper hx).trans_le (original_lower r hσ hτ upper hs ht hx hm)
  linarith

end SquaresInCircles.Eight.ShortWord.MixedQuarter.CorePrimaryNegative
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.CorePrimaryPositive
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives Reference

def multiplier : ℝ := 8/5
def cap (x : ℝ) : ℝ := 1/12+(outerAxial-1/2)*Real.sin x-Real.cos x/2
def N (r : Row) : ℝ := Real.sqrt (multiplier^2+coG r^2)
def F (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2+x+coC r-coG r/2-N r/12-coP r*outerAxial+
    (4/5)*Real.cos x-multiplier*(outerAxial-1/2)*Real.sin x
def Fd (_r : Row) (x : ℝ) : ℝ :=
  1-(4/5)*Real.sin x-multiplier*(outerAxial-1/2)*Real.cos x

theorem sourceSign_negative {r : Row} (hr : sourcePositive r=false) : sourceSign r= -1 := by
  simp [sourceSign,WordProblems.sign,hr]

theorem lower_impossible (r : Row) (hτ : targetPositive r=true)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) : ¬sourcePrimary r a b A B (angle false x) := by
  intro hm
  have hb := CoreAngleEndpoint.state_bounds hs
  have htr := positive_trig hx
  have hA : 0≤A := ht.1.trans ht.2.1
  have hAs := mul_nonneg hA htr.2.2.1
  have hBc := mul_nonneg ht.1 (show 0≤Real.cos x by linarith [htr.1])
  dsimp [sourcePrimary] at hm
  rw [angle_width false hx,angle_cos,angle_sin,targetSign_positive hτ] at hm
  dsimp [direction] at hm
  nlinarith

theorem necessary_cap (r : Row) (hτ : targetPositive r=true)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle true x)) : 0≤cap x := by
  have hb := CoreAngleEndpoint.state_bounds hs
  have htB := outer_bounds ht
  have htr := positive_trig hx
  have hAs := mul_le_mul_of_nonneg_right htB.2.1 htr.2.2.1
  have hBc := mul_nonneg ht.1 (show 0≤Real.cos x by linarith [htr.1])
  dsimp [sourcePrimary] at hm
  rw [angle_width true hx,angle_cos,angle_sin,targetSign_positive hτ] at hm
  dsimp [direction,cap] at *
  nlinarith

theorem cap_reference : cap (2/5)<0 := by
  let B := ((Interval.point (1/12)).add
    ((axial.sub (Interval.point (1/2))).mul (sine (by norm_num : (0:ℝ)≤2/5)))).sub
      ((cosine (by norm_num : (0:ℝ)≤2/5)).div (Interval.point 2) (by norm_num [Interval.point]))
  have hhi : B.hi<0 := by dsimp [B]; mixed_fixed
  exact B.mem.2.trans_lt hhi

theorem cap_monotone : MonotoneOn cap (Icc 0 (7/10)) := by
  intro x hx y hy hxy
  have hs := sin_mono hx hy hxy
  have hc := cos_anti hx hy hxy
  have ha : 0≤outerAxial-1/2 := by linarith [outer_endpoint_bounds.1]
  have hp := mul_le_mul_of_nonneg_left hs ha
  dsimp [cap]
  linarith

theorem original_angle_lower (r : Row) (hτ : targetPositive r=true)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle true x)) : 2/5<x := by
  have hcap := necessary_cap r hτ hs ht hx hm
  by_contra h
  have hmono := cap_monotone hx (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num) (le_of_not_gt h)
  linarith [cap_reference]

theorem sine_reference : (389/1000:ℝ)<Real.sin (2/5) := by
  have h := (sine (by norm_num : (0:ℝ)≤2/5)).mem.1
  have hb : (389/1000:ℝ)<(sine (by norm_num : (0:ℝ)≤2/5)).lo := by mixed_fixed
  exact hb.trans_le h

theorem support_coefficients (r : Row) (hσ : sourcePositive r=false)
    (hτ : targetPositive r=true) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    -multiplier*Real.sin x-coP r<0 ∧ 0< multiplier*Real.cos x-coQ r := by
  have hx0 : x∈Icc 0 (7/10) := ⟨by linarith [hx.1],hx.2⟩
  have ht := positive_trig hx0
  have hs := sin_mono (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num) hx0 hx.1
  have hp : -(19335/100000:ℝ)≤coP r := by
    revert hσ hτ
    fin_cases r <;> norm_num [sourcePositive,targetPositive,coP]
  have hq := (coefficient_bounds r).2.2.2.1
  dsimp [multiplier]
  constructor <;> linarith [sine_reference]

theorem hasDerivAt_F (r : Row) (x : ℝ) : HasDerivAt (F r) (Fd r x) x := by
  have h := ((((hasDerivAt_id' x).const_add (Real.pi/2+coC r-coG r/2-N r/12-coP r*outerAxial)).add
    ((Real.hasDerivAt_cos x).const_mul (4/5))).sub
      ((Real.hasDerivAt_sin x).const_mul (multiplier*(outerAxial-1/2))))
  have hF : F r=fun y => Real.pi/2+coC r-coG r/2-N r/12-coP r*outerAxial+y+
      4/5*Real.cos y-multiplier*(outerAxial-1/2)*Real.sin y := by
    funext y
    simp only [F]
    ring
  rw [hF]
  convert h using 1
  simp only [Fd]
  ring

theorem derivative_negative (r : Row) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) : Fd r x<0 := by
  have hx0 : x∈Icc 0 (7/10) := ⟨by linarith [hx.1],hx.2⟩
  have ht := positive_trig hx0
  have hs := sin_mono (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num) hx0 hx.1
  have ha : (1829/2000:ℝ)<outerAxial-1/2 := by
    linarith [ShortOuterZero.fine_axial_bounds.1]
  have hmul := mul_lt_mul_of_pos_right ha (show 0<Real.cos x by linarith [ht.1])
  dsimp [Fd,multiplier]
  nlinarith [sine_reference]

theorem antitone (r : Row) : AntitoneOn (F r) (Icc (2/5) (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x _ => (hasDerivAt_F r x).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_F r x)
    (fun _ hx => (derivative_negative r (Ioo_subset_Icc_self hx)).le)

def normBox (r : Row) : Interval (N r) :=
  rootSix (Interval.point (multiplier^2+coG r^2)) 2 (by norm_num)
    (by dsimp [Interval.point]; positivity)
def endpointBox (r : Row) : Interval (F r (7/10)) := by
  convert ((((((((halfPi.add (Interval.point (7/10))).add (Interval.point (coC r))).sub
    (Interval.point (coG r/2))).sub ((normBox r).div (Interval.point 12) (by norm_num [Interval.point]))).sub
      ((Interval.point (coP r)).mul axial)).add
        ((Interval.point (4/5)).mul (cosine (by norm_num : (0:ℝ)≤7/10)))).sub
          (((Interval.point multiplier).mul (axial.sub (Interval.point (1/2)))).mul
            (sine (by norm_num : (0:ℝ)≤7/10))))) using 1
  dsimp [F]

private lemma r82_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl

private lemma r82_endpointBox_lo (r : Row) : (endpointBox r).lo =
    ((((((((halfPi.add (Interval.point (7/10))).add (Interval.point (coC r))).sub
    (Interval.point (coG r/2))).sub ((normBox r).div (Interval.point 12) (by norm_num [Interval.point]))).sub
      ((Interval.point (coP r)).mul axial)).add
        ((Interval.point (4/5)).mul (cosine (by norm_num : (0:ℝ)≤7/10)))).sub
          (((Interval.point multiplier).mul (axial.sub (Interval.point (1/2)))).mul
            (sine (by norm_num : (0:ℝ)≤7/10))))).lo := by
  unfold endpointBox
  rw [r82_mpr_lo]
  dsimp [F]

theorem endpoint (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=true) :
    (152/125:ℝ)<F r (7/10) := by
  have hbound : (152/125:ℝ)<(endpointBox r).lo := by
    rw [r82_endpointBox_lo]
    revert hσ hτ
    fin_cases r <;> norm_num [sourcePositive,targetPositive] <;> simp only [normBox,multiplier] <;>
      mixed_fixed
  exact hbound.trans_le (endpointBox r).mem.1

theorem original_lower (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=true)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc (2/5) (7/10)) (hm : sourcePrimary r a b A B (angle true x)) :
    F r x≤coreOuterCost r a b A B (angle true x) := by
  have hx0 : x∈Icc 0 (7/10) := ⟨by linarith [hx.1],hx.2⟩
  have hg := (coefficient_bounds r).1
  have hcore := core_circle_lower (X:= -multiplier) (Y:= -coG r) hs (by linarith)
  have he : Real.sqrt ((-multiplier)^2+(-coG r)^2)=N r := by
    dsimp [N]
    congr 1
    ring
  rw [he] at hcore
  have hcoeff := support_coefficients r hσ hτ hx
  have houter := outer_axial_lower (X:= -multiplier*Real.sin x-coP r)
    (Y:=multiplier*Real.cos x-coQ r) ht hcoeff.1.le hcoeff.2.le
  dsimp [sourcePrimary] at hm
  rw [angle_width true hx0,angle_sin,angle_cos,targetSign_positive hτ] at hm
  have hmult := mul_le_mul_of_nonneg_left hm (show 0≤ multiplier by norm_num [multiplier])
  dsimp [F,coreOuterCost]
  rw [sourceSign_negative hσ,targetSign_positive hτ]
  dsimp [angle,direction,multiplier] at *
  nlinarith

theorem original (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=true)
    (upper : Bool) {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle upper x)) :
    (449/500:ℝ)<coreOuterCost r a b A B (angle upper x) := by
  cases upper
  · exact False.elim (lower_impossible r hτ hs ht hx hm)
  · have hxl := original_angle_lower r hτ hs ht hx hm
    have hxr : x∈Icc (2/5) (7/10) := ⟨hxl.le,hx.2⟩
    have hmono := antitone r hxr (show (7/10:ℝ)∈Icc (2/5) (7/10) by norm_num) hx.2
    have hsource := original_lower r hσ hτ hs ht hxr hm
    linarith [endpoint r hσ hτ]

end SquaresInCircles.Eight.ShortWord.MixedQuarter.CorePrimaryPositive
end
end
end

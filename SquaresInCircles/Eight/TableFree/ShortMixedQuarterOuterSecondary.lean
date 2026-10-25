module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterCoreSecondaryNegative
public import SquaresInCircles.Eight.TableFree.CircularNorm

/-!
# All original outer-to-core secondary quarter contacts

Uncompiled transcription of Section 4 of the parent hand proof.
The original outer transverse term cancels with its exact multiplier.
The negative core target has axial support; the positive target uses
the core-circle support on both closed pieces. The norm speed is bounded
by each vector length on each entire angle half.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterSecondary
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
    using 1 <;> dsimp [negative,angle,direction] <;> ring
def energyEndpoint (r : Row) : Interval (mass r+wave r false*Real.sin (7/10)) :=
  (Interval.point (mass r)).add ((Interval.point (wave r false)).mul
    (sine (by norm_num : (0:ℝ)≤7/10)))
theorem energyEndpoint_nonnegative (r : Row) : 0≤(energyEndpoint r).lo := by
  fin_cases r <;> dsimp [energyEndpoint,mass,wave,direction] <;> mixed_fixed
def normEndpoint (r : Row) : Interval (N r false (7/10)) := by
  have h := rootThree (energyEndpoint r) 1 (by norm_num) (energyEndpoint_nonnegative r)
  simpa [N,CircularNorm.norm,CircularNorm.energy] using h
def positiveEndpoint (r : Row) : Interval (positive r false (7/10)) := by
  convert ((((((halfPi.sub (Interval.point (7/10))).add (Interval.point (ocC r))).add
    (sourceBox r)).add (Interval.point ((ocQ r-ocG r)/2))).add
      ((Interval.point (ocQ r)).mul (sine (by norm_num : (0:ℝ)≤7/10)))).sub
        ((normEndpoint r).div (Interval.point 12) (by norm_num [Interval.point])))
    using 1 <;> dsimp [positive,angle,direction] <;> ring

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

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterSecondary

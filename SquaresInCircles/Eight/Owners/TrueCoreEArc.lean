module

public import SquaresInCircles.Eight.Owners.CircleGeometry

/-!
# Eight squares: E's entire true-core arc, including its curved-to-flat join

The primary coordinate is obtained from the actual core
equation. Decreasing E's nonnegative tangent magnitude preserves sorting
and the true core, and does not increase its corner circle. The derivative
at tangent magnitude one half is proved by joining the two one-sided
derivatives; no flat-core hypothesis is imposed on the original point.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight
namespace TrueCoreE

def primary (b : ℝ) : ℝ :=
  1/2+Real.sqrt ((1/12 : ℝ)^2-(max (b-1/2) 0)^2)

def slope (b : ℝ) : ℝ :=
  max (b-1/2) 0/Real.sqrt ((1/12 : ℝ)^2-(max (b-1/2) 0)^2)

def point (b : ℝ) : SignedPoint := ⟨primary b,-b⟩

theorem continuous_primary : Continuous primary := by
  unfold primary
  fun_prop

theorem primary_flat {b : ℝ} (hb : b≤1/2) : primary b=7/12 := by
  norm_num [primary,max_eq_right (by linarith : b-1/2≤0)]

theorem slope_flat {b : ℝ} (hb : b≤1/2) : slope b=0 := by
  rw [slope,max_eq_right (by linarith : b-1/2≤0),zero_div]

theorem primary_curved {b : ℝ} (hb : 1/2≤b) :
    primary b=1/2+Real.sqrt ((1/12 : ℝ)^2-(b-1/2)^2) := by
  rw [primary,max_eq_left (by linarith : 0≤b-1/2)]

private theorem curved_hasDerivAt {b : ℝ}
    (hr : 0<(1/12 : ℝ)^2-(b-1/2)^2) :
    HasDerivAt (fun x : ℝ => 1/2+Real.sqrt ((1/12 : ℝ)^2-(x-1/2)^2))
      (-(b-1/2)/Real.sqrt ((1/12 : ℝ)^2-(b-1/2)^2)) b := by
  have hs : Real.sqrt ((1/12 : ℝ)^2-(b-1/2)^2)≠0 :=
    (Real.sqrt_pos.mpr hr).ne'
  have hin : HasDerivAt (fun x : ℝ => (1/12 : ℝ)^2-(x-1/2)^2) (-(2*(b-1/2))) b := by
    have h := (((hasDerivAt_id' b).sub_const (1/2)).pow 2).const_sub ((1/12 : ℝ)^2)
    convert h using 1
    norm_num
  have hd := (hin.sqrt hr.ne').const_add (1/2)
  convert hd using 1
  rw [neg_div,neg_div,mul_div_mul_left _ _ (two_ne_zero)]

/-- The maximum in the true-core equation is smooth after squaring at
the join. Both one-sided derivatives are exactly zero there. -/
theorem primary_hasDerivAt {b : ℝ}
    (hr : 0<(1/12 : ℝ)^2-(max (b-1/2) 0)^2) :
    HasDerivAt primary (-slope b) b := by
  rcases lt_trichotomy b (1/2 : ℝ) with hlt | heq | hgt
  · have hevent : primary =ᶠ[𝓝 b] (fun _ : ℝ => 7/12) :=
      (eventually_lt_nhds hlt).mono fun x hx => primary_flat hx.le
    simpa only [slope_flat hlt.le,neg_zero] using
      (hasDerivAt_const b (7/12 : ℝ)).congr_of_eventuallyEq hevent
  · subst b
    have hleft : HasDerivWithinAt primary 0 (Iic (1/2 : ℝ)) (1/2) := by
      apply (hasDerivAt_const (1/2 : ℝ) (7/12 : ℝ)).hasDerivWithinAt.congr
      · intro x hx
        exact primary_flat hx
      · exact primary_flat le_rfl
    have hrightBase : HasDerivAt
        (fun x : ℝ => 1/2+Real.sqrt ((1/12 : ℝ)^2-(x-1/2)^2)) 0 (1/2) := by
      simpa using curved_hasDerivAt (b := (1/2 : ℝ)) (by norm_num)
    have hright : HasDerivWithinAt primary 0 (Ici (1/2 : ℝ)) (1/2) := by
      apply hrightBase.hasDerivWithinAt.congr
      · intro x hx
        exact primary_curved hx
      · exact primary_curved le_rfl
    have hu : Iic (1/2 : ℝ)∪Ici (1/2 : ℝ)=univ := by
      ext x
      simp only [mem_union,mem_Iic,mem_Ici,mem_univ,iff_true]
      exact le_total x (1/2)
    have hboth : HasDerivAt primary 0 (1/2) := by
      simpa only [hu,hasDerivWithinAt_univ] using hleft.union hright
    simpa only [slope_flat (b := (1/2 : ℝ)) le_rfl,neg_zero] using hboth
  · have hr' : 0<(1/12 : ℝ)^2-(b-1/2)^2 := by
      simpa only [max_eq_left (show 0≤b-1/2 by linarith)] using hr
    have hevent : primary =ᶠ[𝓝 b]
        (fun x : ℝ => 1/2+Real.sqrt ((1/12 : ℝ)^2-(x-1/2)^2)) :=
      (eventually_gt_nhds hgt).mono fun x hx => primary_curved hx.le
    have hd := (curved_hasDerivAt hr').congr_of_eventuallyEq hevent
    simpa only [slope,max_eq_left (show 0≤b-1/2 by linarith),neg_div] using hd

structure Source (E : SignedPoint) : Prop where
  sorted : E.Sorted
  nonpos : E.y≤0
  core : E.Core

theorem Source.initial {E : SignedPoint} (I : Source E) : point (-E.y)=E := by
  have ha := SignedPoint.primary_gt_half I.sorted I.core.ge
  have heq : (E.a-1/2)^2+(max (-E.y-1/2) 0)^2=(1/12 : ℝ)^2 := by
    simpa only [SignedPoint.Core,SignedPoint.coreDistance,abs_of_nonpos I.nonpos,
      max_eq_left (show 0≤E.a-1/2 by linarith)] using I.core
  have hr : (1/12 : ℝ)^2-(max (-E.y-1/2) 0)^2=(E.a-1/2)^2 := by
    linarith
  apply SignedPoint.ext
  · change 1/2+Real.sqrt ((1/12 : ℝ)^2-(max (-E.y-1/2) 0)^2)=E.a
    rw [hr,Real.sqrt_sq_eq_abs,abs_of_pos (sub_pos.mpr ha)]
    ring
  · simp [point]

/-- The source's exact core equation controls every smaller tangent.
In particular the square root stays strictly positive even at the sorted
core diagonal. -/
theorem Source.geometry {E : SignedPoint} {b : ℝ} (I : Source E)
    (hb : b∈Icc 0 (-E.y)) :
    (point b).Sorted ∧ (point b).Core ∧ E.a≤primary b ∧
      1/2<primary b ∧ primary b≤7/12 ∧
      0<(1/12 : ℝ)^2-(max (b-1/2) 0)^2 ∧
      0≤ slope b ∧ slope b≤1 := by
  let m := max (b-1/2) 0
  let m₀ := max (-E.y-1/2) 0
  let r := Real.sqrt ((1/12 : ℝ)^2-m^2)
  have hEa := SignedPoint.primary_gt_half I.sorted I.core.ge
  have hsort : -E.y≤E.a := by simpa [abs_of_nonpos I.nonpos] using I.sorted.2
  have hm : 0≤ m := le_max_right _ _
  have hm₀ : 0≤ m₀ := le_max_right _ _
  have hmm₀ : m≤ m₀ := max_le_max_right 0 (by linarith [hb.2])
  have hm₀a : m₀≤E.a-1/2 := max_le (by linarith) (by linarith)
  have heq : (E.a-1/2)^2+m₀^2=(1/12 : ℝ)^2 := by
    simpa only [SignedPoint.Core,SignedPoint.coreDistance,abs_of_nonpos I.nonpos,
      max_eq_left (show 0≤E.a-1/2 by linarith)] using I.core
  have hmsq := pow_le_pow_left₀ hm hmm₀ 2
  have hrpos : 0<(1/12 : ℝ)^2-m^2 := by
    have heapos : 0<(E.a-1/2)^2 := sq_pos_of_pos (sub_pos.mpr hEa)
    nlinarith
  have hr : 0<r := Real.sqrt_pos.mpr hrpos
  have hr2 : r^2=(1/12 : ℝ)^2-m^2 := Real.sq_sqrt hrpos.le
  have hrr : E.a-1/2≤r := by nlinarith
  have hru : r≤1/12 := by nlinarith [sq_nonneg m]
  have hmr : m≤r := hmm₀.trans (hm₀a.trans hrr)
  have ha : 1/2<primary b := by change 1/2<1/2+r; linarith
  have hinit : E.a≤primary b := by change E.a≤1/2+r; linarith
  have hbsort : b≤primary b := hb.2.trans (hsort.trans hinit)
  refine ⟨⟨by change 0<primary b; linarith,by
      simpa only [point,abs_neg,abs_of_nonneg hb.1] using hbsort⟩,?_,hinit,ha,?_,hrpos,?_,?_⟩
  · change (max (primary b-1/2) 0)^2+(max (|-b|-1/2) 0)^2=(1/12 : ℝ)^2
    rw [max_eq_left (by linarith),abs_neg,abs_of_nonneg hb.1]
    change (1/2+r-1/2)^2+m^2=(1/12 : ℝ)^2
    nlinarith
  · change 1/2+r≤7/12
    linarith
  · exact div_nonneg hm hr.le
  · exact (div_le_one hr).2 hmr

theorem Source.derivative {E : SignedPoint} {b : ℝ} (I : Source E)
    (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt primary (-slope b) b ∧ 0≤ slope b ∧ slope b≤1 := by
  have hg := I.geometry hb
  exact ⟨primary_hasDerivAt hg.2.2.2.2.2.1,hg.2.2.2.2.2.2⟩

theorem Source.radial_identity {E : SignedPoint} {b : ℝ} (I : Source E)
    (hb : b∈Icc 0 (-E.y)) :
    (slope b=0 ∧ b≤1/2) ∨ b-slope b*primary b=(1-slope b)/2 := by
  by_cases hflat : b≤1/2
  · exact Or.inl ⟨slope_flat hflat,hflat⟩
  · right
    have hgt : 1/2<b := lt_of_not_ge hflat
    have hm : max (b-1/2) 0=b-1/2 := max_eq_left (by linarith)
    have hr : Real.sqrt ((1/12 : ℝ)^2-(b-1/2)^2)≠0 := by
      have h := (I.geometry hb).2.2.2.2.2.1
      rw [hm] at h
      exact (Real.sqrt_pos.mpr h).ne'
    simp only [slope,primary,hm]
    generalize Real.sqrt ((1/12 : ℝ)^2-(b-1/2)^2)=S at hr ⊢
    field_simp
    ring

theorem Source.circle_nonincrease {E : SignedPoint} {b : ℝ} (I : Source E)
    (hb : b∈Icc 0 (-E.y)) : (point b).circle≤E.circle := by
  let f : ℝ → ℝ := fun x => (primary x+1/2)^2+(x+1/2)^2
  let df : ℝ → ℝ := fun x => 2*((x+1/2)-(primary x+1/2)*slope x)
  have hc : Continuous f :=
    ((continuous_primary.add continuous_const).pow 2).add ((continuous_id.add continuous_const).pow 2)
  have hd {x : ℝ} (hx : x∈Icc 0 (-E.y)) : HasDerivAt f (df x) x := by
    have ha := (I.derivative hx).1
    have h := ((ha.add_const (1/2)).pow 2).fun_add (((hasDerivAt_id' x).add_const (1/2)).pow 2)
    convert h using 1
    simp only [df]
    norm_num
    ring
  have hdf {x : ℝ} (hx : x∈Icc 0 (-E.y)) : 0≤df x := by
    have hv := (I.derivative hx).2
    rcases I.radial_identity hx with ⟨hvzero,hflat⟩ | hcurve
    · simp only [df,hvzero,mul_zero,sub_zero]
      linarith [hx.1]
    · dsimp [df]
      linarith [hv.2]
  have hmono : MonotoneOn f (Icc 0 (-E.y)) := by
    apply monoOn_of_hasDeriv_nonneg hc.continuousOn
    · intro x hx
      exact hd (Ioo_subset_Icc_self hx)
    · intro x hx
      exact hdf (Ioo_subset_Icc_self hx)
  have hval' : ∀ x : ℝ,0≤x → f x=(point x).circle := by
    intro x hx
    simp only [f,SignedPoint.circle,point,abs_neg,abs_of_nonneg hx]
  have hinit : f (-E.y)=E.circle := by
    rw [hval' _ (neg_nonneg.mpr I.nonpos),I.initial]
  rw [← hval' b hb.1,← hinit]
  exact hmono hb ⟨neg_nonneg.mpr I.nonpos,le_rfl⟩ hb.2

theorem Source.contained {q : ℝ} {E : SignedPoint} {b : ℝ} (I : Source E)
    (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) : (point b).Contained q := by
  have hg := I.geometry hb
  have ha := hg.2.2.2.2.1
  have hbs : b≤primary b := by simpa [point,abs_neg,abs_of_nonneg hb.1] using hg.1.2
  have ha0 : 0≤primary b+1/2 := by linarith [hg.2.2.2.1]
  have hb0 : 0≤b+1/2 := by linarith [hb.1]
  have hasq := pow_le_pow_left₀ ha0 (show primary b+1/2≤13/12 by linarith) 2
  have hbsq := pow_le_pow_left₀ hb0 (show b+1/2≤13/12 by linarith) 2
  dsimp [SignedPoint.Contained,SignedPoint.circle,point]
  rw [abs_neg,abs_of_nonneg hb.1]
  dsimp [qLow] at hq
  nlinarith

end TrueCoreE
end SquaresInCircles.Eight

module

public import SquaresInCircles.Eight.TableFree.DirectNegativeTEndpoint
public import SquaresInCircles.Eight.TableFree.FirstNegativeSlack

/-!
# Whole-domain positive DE continuation with the original E fixed

Uncompiled source. This is the positive-DE part of the complete one-negative
BT theorem. No H cut or H--D span is used. An actual outer DE3 contact has
error below .18; beyond .18 its actual margin has an explicit positive
reserve. Core E and DE2 have full-angle derivative bounds. The first actual
BT2 contact, or preceding DE alignment, therefore has strict original-DE
slack and can pay the already constructed D-circle contraction.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace DirectNegativeT
open AlignedNegative PrimaryCap

theorem outer_primary_plus_tangent {q : ℝ} {E : SignedPoint}
    (hqL : qLow≤q) (hEs : E.Sorted) (hEy : E.y≤0) (ho : E.Outer q) :
    axisCoordinate q≤E.a-E.y := by
  have hqroot : 0≤q-1/4 := by dsimp [qLow] at hqL; linarith
  have hroot := Real.sqrt_nonneg (q-1/4)
  have hroot2 := Real.sq_sqrt hqroot
  have hprod := mul_nonneg hEs.1.le (neg_nonneg.mpr hEy)
  have hcircle : (E.a+1/2)^2+(-E.y+1/2)^2=q := by
    simpa [SignedPoint.Outer,SignedPoint.circle,abs_of_nonpos hEy] using ho
  have hsum : 0≤E.a-E.y+1/2 := by linarith [hEs.1]
  unfold axisCoordinate
  by_contra! hbad
  nlinarith

private theorem outer_DE3_base {d : ℝ} (hd : d∈Icc (9/50 : ℝ) (7/10 : ℝ)) :
    (33/2500 : ℝ)<43/125+(9/10)*Real.sin d-(1/2)*Real.cos d := by
  let f : ℝ → ℝ := fun x => 43/125+(9/10)*Real.sin x-(1/2)*Real.cos x
  have hderiv (x : ℝ) : HasDerivAt f ((9/10)*Real.cos x+(1/2)*Real.sin x) x := by
    exact ((((Real.hasDerivAt_sin x).const_mul (9/10)).const_add (43/125)).sub
      ((Real.hasDerivAt_cos x).const_mul (1/2))).congr_deriv (by ring)
  have hmono : MonotoneOn f (Icc 0 (7/10 : ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg (by dsimp [f]; fun_prop) (fun x _ => hderiv x)
    intro x hx
    have ht := transport_trig (Ioo_subset_Icc_self hx)
    linarith [ht.1,ht.2.2.1]
  have hbase : (33/2500 : ℝ)<f (9/50) := by
    have hs := sin_lower_seven (show (0:ℝ)≤9/50 by norm_num)
    have hc := cos_upper_four (show (0:ℝ)≤9/50 by norm_num)
    dsimp [f]
    norm_num at hs hc
    linarith
  exact hbase.trans_le (hmono (by constructor <;> norm_num)
    ⟨by linarith [hd.1],hd.2⟩ hd.1)

/-- The actual outer-E margin, rather than a numerical contact search,
excludes the whole large-error interval. -/
theorem outer_DE3_margin {q d : ℝ} {D E : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hEs : E.Sorted) (hEy : E.y≤0) (ho : E.Outer q)
    (hDa : 211/250<D.a) (hd : d∈Icc (9/50 : ℝ) (7/10 : ℝ)) :
    33/2500<quarterProjection D E d 3-edgeWidth d := by
  have hd0 : d∈Icc 0 (7/10 : ℝ) := ⟨by linarith [hd.1],hd.2⟩
  have ht := transport_trig hd0
  have haxis : (7/5 : ℝ)<axisCoordinate q := by
    have hh := (uniform_circle_reserves hqL hqU).2.2.1
    dsimp [axisCoordinate]
    linarith
  have hsum := outer_primary_plus_tangent hqL hEs hEy ho
  have hmul := mul_le_mul_of_nonneg_right hsum ht.2.2.1
  have hdiag := mul_nonneg (neg_nonneg.mpr hEy)
    (sub_nonneg.mpr ht.2.2.2.2.le)
  have hbound : axisCoordinate q*Real.sin d≤E.a*Real.sin d-E.y*Real.cos d := by
    nlinarith
  have haxisprod := mul_le_mul_of_nonneg_right
    (show (7/5 : ℝ)≤axisCoordinate q by linarith) ht.2.2.1
  have hbase := outer_DE3_base hd
  rw [edgeWidth_positive_formula hd0]
  simp only [quarterProjection,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  linarith


theorem core_original_e_rate {E : SignedPoint} {d : ℝ}
    (hEs : E.Sorted) (hEc : E.Core) (hEy : E.y≤0)
    (hd : d∈Icc 0 (7/10 : ℝ)) :
    (E.a-1/2)*Real.cos d+(1/2+E.y)*Real.sin d<203/500 := by
  have ha := SignedPoint.core_primary_le hEs hEc
  have ht := transport_trig hd
  have hcos0 : 0≤Real.cos d := by linarith [ht.1]
  have hprim := mul_le_mul_of_nonneg_right
    (show E.a-1/2≤(1/12:ℝ) by linarith) hcos0
  have hprim1 := mul_le_mul_of_nonneg_left ht.2.1 (by norm_num : (0:ℝ)≤1/12)
  have htan := mul_le_mul_of_nonneg_right
    (show 1/2+E.y≤(1/2:ℝ) by linarith) ht.2.2.1
  nlinarith [ht.2.2.2.1]

/-- A uniform derivative reserve on the actual small-slack set, on the
whole positive DE interval. E may be core corner, flat core, or outer. -/
theorem Source.positive_de_small_slack_derivative {q t e x : ℝ}
    {D T B E : SignedPoint} (I : Source q t D T B)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore)
    (hEr : E.Boundary q) (hEy : E.y≤0)
    (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (B.a-1/2) x) B.reflect (-x) 0)
    (he : e+x∈Icc 0 (7/10 : ℝ)) (j : Fin 4) (hj : j=2 ∨ j=3)
    (hsmall : positiveDESlack D.circle (B.a-1/2) e E j x≤1/1000) :
    positiveDEDerivative D.circle (B.a-1/2) e E j x< -(1/1250) := by
  rcases hj with rfl | rfl
  · have hh := I.lowMixedDerivative_negative hqU hx hnot he
    rw [SignedPoint.reflect_circle] at hh
    have h2 : lowMixedDerivative D.circle (B.a-1/2) e x< -(1/1250) :=
      hh.trans (by norm_num : -(3/50 : ℝ)< -(1/1250))
    simpa [positiveDEDerivative] using h2
  · have hgain := I.primary_gain hqU hx hnot
    have hrate : (E.a-1/2)*Real.cos (e+x)+(1/2+E.y)*Real.sin (e+x)<1249/1250 := by
      rcases hEr with ho | hc
      · have hDa : 211/250<(Dpath D.circle (B.a-1/2) x).a := by
          let J := I.atAngle hqU hx hnot
          have hh := J.H_sorted.2
          rw [abs_of_nonneg J.H_nonneg] at hh
          have hlow := (J.cuts hqU).2.2.2.1.trans_le hh
          rw [SignedPoint.reflect_circle] at hlow
          exact hlow
        have hshort : e+x<9/50 := by
          by_contra! hlarge
          have hm := outer_DE3_margin hqL hqU hEs hEy ho hDa ⟨hlarge,he.2⟩
          rw [← positiveDESlack_actual E 3 (Or.inr rfl) he] at hm
          linarith
        have ha := (SignedPoint.coordinate_bounds hEs hEcore hEc hqU).2.1
        have hh := short_original_e_rate ha (neg_nonneg.mpr hEy)
          (show e+x∈Icc 0 (21/100 : ℝ) from ⟨he.1,by linarith⟩)
        simpa using hh
      · exact (core_original_e_rate hEs hc hEy he).trans (by norm_num)
    simp only [positiveDEDerivative,show (3:Fin 4)≠2 by decide,ite_false,
      highMixedDerivative,SignedPoint.reflect]
    linarith


/-- With E fixed, actual BT2 or actual DE alignment is reached with strict
original-DE slack. The proof takes the first geometric hard contact and
uses the small-slack barrier, without assuming a feasible motion path. -/
theorem Source.positive_de_stop_full {q t e : ℝ} {D T B E : SignedPoint}
    (I : Source q t D T B) (hqL : qLow≤q) (hqU : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore)
    (hEr : E.Boundary q) (hEy : E.y≤0)
    (he : e+t∈Ioc 0 (7/10 : ℝ)) (j : Fin 4) (hj : j=2 ∨ j=3)
    (hf : quarterFeasible D E (e+t) j) : Nonempty (PositiveDEStop I E e j) := by
  obtain ⟨O⟩ := I.first_hard hqU
  let P := B.a-1/2
  let r := max O.angle (-e)
  let L := positiveDESlack D.circle P e E j
  let F : ℝ → ℝ := fun x => L x-(t-x)/4000
  let dF : ℝ → ℝ := fun x => positiveDEDerivative D.circle P e E j x+1/4000
  have hrO : O.angle≤r := le_max_left _ _
  have hre : -e≤r := le_max_right _ _
  have hr0 : 0≤r := O.angle_mem.1.trans hrO
  have hrt : r<t := max_lt_iff.mpr ⟨O.angle_mem.2,by linarith [he.1]⟩
  have heR : e+r∈Icc 0 (7/10 : ℝ) := by constructor <;> linarith [he.2]
  have heX (x : ℝ) (hx : x∈Icc r t) : e+x∈Icc 0 (7/10 : ℝ) := by
    constructor <;> linarith [hx.1,hx.2,he.2]
  have hterminal : quarterFeasible (point P r) B.reflect (-r) 0 ∨ e+r=0 := by
    rcases le_total O.angle (-e) with hle | hle
    · right
      dsimp [r]
      rw [max_eq_right hle]
      ring
    · left
      have hr : r=O.angle := max_eq_left hle
      rw [hr]
      exact O.hard
  have hderiv (x : ℝ) (hx : x∈Icc r t) : HasDerivAt F (dF x) x := by
    have hx0 : 0≤x := hr0.trans hx.1
    have hc : Real.cos x≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hx0]; exact hx.2.trans I.tilt_cap)).ne'
    have hg := I.path_geometry hqU ⟨hx0,hx.2⟩
    have hL := positiveDESlack_hasDerivAt (qD := D.circle) (P := P) (e := e) E j hc
      (by have h6 := hg.2.2.2.2.2.2; rw [SignedPoint.reflect_circle] at h6; exact h6)
    exact (hL.sub (((hasDerivAt_id x).const_sub t).div_const 4000)).congr_deriv
      (by dsimp only [dF]; ring)
  have hcont : ContinuousOn F (Icc r t) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hFt : 0≤F t := by
    have hraw := (quarterFeasible_reflect D E (e+t) j).2 hf
    have hj' : reflectedOwner j=0 ∨ reflectedOwner j=1 := by
      rcases hj with rfl | rfl <;> norm_num [reflectedOwner]
    have hnormalized := (I.normalize hqU).retains_mixed hqU
      (by rw [abs_of_pos he.1]; exact he.2) hj' hraw
    rw [(I.normalize hqU).H_eq] at hnormalized
    have hback : quarterFeasible (Dpath D.circle P t) E (e+t) j := by
      apply (quarterFeasible_reflect (Dpath D.circle P t) E (e+t) j).1
      simp only [Dpath,SignedPoint.reflect_reflect]
      simp only [SignedPoint.reflect_circle] at hnormalized
      exact hnormalized
    have hLstart : 0≤L t := by
      dsimp [L]
      rw [positiveDESlack_actual E j hj ⟨he.1.le,he.2⟩]
      exact sub_nonneg.mpr hback
    simpa [F] using hLstart
  have hbarrier : 0≤F r := left_sublevel_barrier hrt hcont
    (fun x hx => hderiv x (Ioo_subset_Icc_self hx))
    (fun x hx hFx => by
      have hx0 : 0<x := hr0.trans_lt hx.1
      have hnot := O.later_unavailable ⟨hrO.trans_lt hx.1,hx.2.le⟩
      have hsmall : L x≤1/1000 := by
        dsimp [F] at hFx
        linarith [I.tilt_cap]
      have hh := I.positive_de_small_slack_derivative hqL hqU hEs hEc hEcore hEr hEy
        ⟨hx0,hx.2.le⟩ hnot (heX x (Ioo_subset_Icc_self hx)) j hj hsmall
      dsimp [dF,P]
      linarith) hFt
  have hstrict : 0<L r := by
    have hp : 0<(t-r)/4000 := div_pos (sub_pos.mpr hrt) (by norm_num)
    dsimp [F] at hbarrier
    linarith
  exact ⟨⟨r,⟨hr0,hrt⟩,heR,hstrict,hterminal⟩⟩


end DirectNegativeT
end SquaresInCircles.Eight.TableFree

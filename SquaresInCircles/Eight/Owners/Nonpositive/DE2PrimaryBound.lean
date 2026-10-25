module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.Nonpositive.EOutsideCycle

/-!
# Eight squares: a rotated DE2 witness below D gives E primary above one

The two mixed inequalities and the bound on the primary sum of the nonpositive chain suffice
(`original_primary_gt_one`). Concavity on the whole triangular frame domain proves the scalar gap
(`gap_concave`, `gap_positive`), whose three endpoint reserves use Taylor bounds; E needs no circle
or radial boundary hypothesis. On a hard input with E below D and a DE2 witness, the primary of E
exceeds `1` (`HardInput.nonpositive_below_DE2_primary`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NonpositiveDE2PrimaryBound

def gap (α x : ℝ) : ℝ :=
  2/625+(359/500)*Real.sin α+(603/500)*Real.sin x-
    (1/2)*Real.sin (α+x)-(3/2)*(1-Real.cos (α+x))

def gapD (α x : ℝ) : ℝ :=
  (603/500)*Real.cos x-(1/2)*Real.cos (α+x)-(3/2)*Real.sin (α+x)

def gapDD (α x : ℝ) : ℝ :=
  -(603/500)*Real.sin x+(1/2)*Real.sin (α+x)-(3/2)*Real.cos (α+x)

theorem gap_derivative (α x : ℝ) : HasDerivAt (gap α) (gapD α x) x := by
  have hd : HasDerivAt (fun z : ℝ => α+z) 1 x := by
    simpa using (hasDerivAt_id x).const_add α
  have h := (((hasDerivAt_const x (2/625+(359/500)*Real.sin α)).fun_add
    ((Real.hasDerivAt_sin x).const_mul (603/500))).fun_sub
      (hd.sin.const_mul (1/2))).fun_sub ((hd.cos.const_sub 1).const_mul (3/2))
  refine HasDerivAt.congr_deriv (show HasDerivAt (gap α) _ x from h) ?_
  simp only [gapD]
  ring

theorem gap_second_derivative (α x : ℝ) : HasDerivAt (gapD α) (gapDD α x) x := by
  have hd : HasDerivAt (fun z : ℝ => α+z) 1 x := by
    simpa using (hasDerivAt_id x).const_add α
  have h := (((Real.hasDerivAt_cos x).const_mul (603/500)).fun_sub
    (hd.cos.const_mul (1/2))).fun_sub (hd.sin.const_mul (3/2))
  refine HasDerivAt.congr_deriv (show HasDerivAt (gapD α) _ x from h) ?_
  simp only [gapDD]
  ring

theorem gap_concave {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    ConcaveOn ℝ (Icc 0 (7/10-α)) (gap α) := by
  apply concave_of_deriv2 (f' := gapD α) (f'' := gapDD α)
  · intro x hx; exact gap_derivative α x
  · intro x hx; exact gap_second_derivative α x
  · intro x hx
    have hxdom : x∈Icc 0 (7/10:ℝ) := ⟨hx.1,by linarith [hx.2,hα.1]⟩
    have hpdom : α+x∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.1,hx.1],by linarith [hx.2]⟩
    have hsx := (transport_trig hxdom).2.2.1
    have hcp := (transport_trig hpdom).1
    have hsp := (Real.sin_le hpdom.1).trans hpdom.2
    dsimp [gapDD]
    linarith

theorem near_endpoint {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) : 0<gap α 0 := by
  have hsq := pow_le_pow_left₀ hα.1 hα.2 2
  have hcube : α^3≤(27/100)^2*α := by
    calc α^3=α^2*α := by ring
      _≤(27/100)^2*α := mul_le_mul_of_nonneg_right hsq hα.1
  have hsin : (49/50)*α≤Real.sin α := by
    linarith [Real.sin_ge_sub_cube hα.1,hα.1]
  have hquad := mul_nonneg hα.1 (show 0≤27/100-α by linarith [hα.2])
  have hcos := Real.one_sub_sq_div_two_le_cos (x := α)
  simp only [gap,Real.sin_zero,mul_zero,add_zero]
  nlinarith

def far (α : ℝ) : ℝ :=
  2/625+(359/500)*Real.sin α+(603/500)*Real.sin (7/10-α)-
    (1/2)*Real.sin (7/10)-(3/2)*(1-Real.cos (7/10))

def farD (α : ℝ) : ℝ :=
  (359/500)*Real.cos α-(603/500)*Real.cos (7/10-α)

def farDD (α : ℝ) : ℝ :=
  -(359/500)*Real.sin α-(603/500)*Real.sin (7/10-α)

theorem far_derivative (α : ℝ) : HasDerivAt far (farD α) α := by
  have hd : HasDerivAt (fun z : ℝ => 7/10-z) (-1) α := by
    simpa using (hasDerivAt_id α).const_sub (7/10)
  have h := (((((Real.hasDerivAt_sin α).const_mul (359/500)).const_add (2/625)).fun_add
    (hd.sin.const_mul (603/500))).sub_const ((1/2)*Real.sin (7/10))).sub_const
      ((3/2)*(1-Real.cos (7/10)))
  refine HasDerivAt.congr_deriv (show HasDerivAt (far) _ α from h) ?_
  simp only [farD]
  ring

theorem far_second_derivative (α : ℝ) : HasDerivAt farD (farDD α) α := by
  have hd : HasDerivAt (fun z : ℝ => 7/10-z) (-1) α := by
    simpa using (hasDerivAt_id α).const_sub (7/10)
  have h := ((Real.hasDerivAt_cos α).const_mul (359/500)).fun_sub
    (hd.cos.const_mul (603/500))
  refine HasDerivAt.congr_deriv (show HasDerivAt (farD) _ α from h) ?_
  simp only [farDD]
  ring

theorem far_concave : ConcaveOn ℝ (Icc (0:ℝ) (27/100)) far := by
  apply concave_of_deriv2 (f' := farD) (f'' := farDD)
  · intro α hα; exact far_derivative α
  · intro α hα; exact far_second_derivative α
  · intro α hα
    have hαdom : α∈Icc 0 (7/10:ℝ) := ⟨hα.1,by linarith [hα.2]⟩
    have hβdom : 7/10-α∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.2],by linarith [hα.1]⟩
    dsimp [farDD]
    linarith [(transport_trig hαdom).2.2.1,(transport_trig hβdom).2.2.1]

theorem far_zero : 0<far 0 := by
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤7/10 by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (7/10:ℝ))
  simp only [far,Real.sin_zero,mul_zero,add_zero,sub_zero]
  norm_num at hs hc ⊢
  linarith

theorem far_last : 0<far (27/100) := by
  have hsα := Real.sin_ge_sub_cube (show (0:ℝ)≤27/100 by norm_num)
  have hsβ := Real.sin_ge_sub_cube (show (0:ℝ)≤43/100 by norm_num)
  have hsp := sin_upper_five (show (0:ℝ)≤7/10 by norm_num)
  have hcp := Real.one_sub_sq_div_two_le_cos (x := (7/10:ℝ))
  simp only [far]
  norm_num at hsα hsβ hsp hcp ⊢
  linarith

theorem far_positive {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) : 0<far α := by
  have hm := far_concave.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 (27/100) by norm_num)
    (show (27/100:ℝ)∈Icc 0 (27/100) by norm_num) hα
  exact (lt_min far_zero far_last).trans_le hm

theorem gap_positive {α x : ℝ} (hα : α∈Icc 0 (27/100:ℝ))
    (hx : 0≤x) (hsum : α+x≤7/10) : 0<gap α x := by
  have hright : 0<gap α (7/10-α) := by
    simpa [gap,far,show α+(7/10-α)=7/10 by ring] using far_positive hα
  have hu : 0≤7/10-α := by linarith [hα.2]
  have hm := (gap_concave hα).min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 (7/10-α) from ⟨le_rfl,hu⟩)
    (show 7/10-α∈Icc 0 (7/10-α) from ⟨hu,le_rfl⟩)
    (show x∈Icc 0 (7/10-α) from ⟨hx,by linarith⟩)
  exact (lt_min (near_endpoint hα) hright).trans_le hm

/-- The weak DE2 and EH1 witnesses with the bound on the primary sum give `1 < E.a`; the radius of
E is unrestricted. -/
theorem original_primary_gt_one {H D E : SignedPoint} {α x : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hDa : 1/2≤D.a) (hDy : 353/500< -D.y)
    (hα : α∈Icc 0 (27/100:ℝ)) (hx : 0≤x) (hsum : α+x≤7/10)
    (hprimary : H.a+D.a<1248/625-(359/500)*Real.sin α)
    (hDE : quarterFeasible D E (-x) 2) (hEH : quarterFeasible E H (α+x) 1) :
    1<E.a := by
  by_contra! hbad
  have hb : 0≤ -E.y := neg_nonneg.mpr hEy
  have hbu : -E.y≤1 := by
    have hs : -E.y≤E.a := by simpa [abs_of_nonpos hEy] using hEs.2
    exact hs.trans hbad
  have hxdom : x∈Icc 0 (7/10:ℝ) := ⟨hx,by linarith [hα.1]⟩
  have hpdom : α+x∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.1],hsum⟩
  have hsx := (transport_trig hxdom).2.2.1
  have hsp := (transport_trig hpdom).2.2.1
  have hLx : 0≤1-Real.cos x := sub_nonneg.mpr (Real.cos_le_one x)
  have hLp : 0≤1-Real.cos (α+x) := sub_nonneg.mpr (Real.cos_le_one (α+x))
  have hdeDa := mul_nonneg (sub_nonneg.mpr hDa) hLx
  have hdeDy := mul_nonneg (show 0≤ -D.y+1/2-603/500 by linarith) hsx
  have hEHmajor := mul_le_mul_of_nonneg_right (show E.a-1/2≤1/2 by linarith) hsp
  have hEHminor := mul_le_mul_of_nonneg_right (show -E.y+1/2≤3/2 by linarith) hLp
  have hDEbound : 1+(603/500)*Real.sin x≤D.a-E.y := by
    have h : edgeWidth (-x)≤D.a*Real.cos (-x)-D.y*Real.sin (-x)-E.y := hDE
    rw [edgeWidth_negative_formula hxdom,Real.cos_neg,Real.sin_neg] at h
    linarith
  have hEHbound : 1-(1/2)*Real.sin (α+x)-(3/2)*(1-Real.cos (α+x))≤H.a+E.y := by
    have h : edgeWidth (α+x)≤H.a+E.a*Real.sin (α+x)+E.y*Real.cos (α+x) := hEH
    rw [edgeWidth_positive_formula hpdom] at h
    linarith
  have hgap := gap_positive hα hx hsum
  dsimp [gap] at hgap
  linarith

end SquaresInCircles.Eight.NonpositiveDE2PrimaryBound

namespace SquaresInCircles.Eight.SignedCycle
open Candidate

theorem HardInput.nonpositive_below_DE2_primary {q : ℝ}
    (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hED : I.cycle.theta E<I.cycle.theta D) (hDE2 : I.cycle.Feasible D 2) :
    1<(I.cycle.point E).a := by
  have hb := I.nonpositive_composite_bounds hq hAB hAG hGH hDT hTB hHG hTD
  have hEHorder : I.cycle.theta E≤I.cycle.theta H :=
    hED.le.trans (sub_nonneg.mp hb.span_nonneg)
  have hEH1 := I.nonpositive_EH_primary_of_nonneg hq hAB hAG hGH hDT hTB hHG hTD hEHorder
  let α := I.cycle.theta H-I.cycle.theta D
  let x := I.cycle.theta D-I.cycle.theta E
  have hα : α∈Icc 0 (27/100:ℝ) := ⟨hb.span_nonneg,hb.span_lt.le⟩
  have hx : 0≤x := (sub_pos.mpr hED).le
  have hsum : α+x≤7/10 := by
    have hh := (le_abs_self _).trans (I.necessary.spread H E)
    dsimp [α,x,frameCap] at *
    linarith
  have hDE : quarterFeasible (I.cycle.point D) (I.cycle.point E) (-x) 2 := by
    have heq : -x=I.cycle.theta E-I.cycle.theta D := by dsimp [x]; ring
    simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg,heq] using hDE2
  have hEH : quarterFeasible (I.cycle.point E) (I.cycle.point H) (α+x) 1 := by
    have heq : α+x=I.cycle.theta H-I.cycle.theta E := by dsimp [α,x]; ring
    simpa [Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg,heq] using hEH1
  exact NonpositiveDE2PrimaryBound.original_primary_gt_one
    (I.necessary.sorted E) I.E_nonpos hb.D_primary.1.le hb.D_tangent.1
    hα hx hsum hb.primary_sum hDE hEH

end SquaresInCircles.Eight.SignedCycle

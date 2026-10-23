module

public import SquaresInCircles.Eight.TableFree.MiddleHardCap

/-!
# An actual A-up contraction for a positive AB0 error

Uncompiled draft.  Advance A by any positive amount not exceeding either
its positive GA angle or its positive AB error.  The exact AB demand has
growth below `21/20`; the same-original-circle hard cap has gain above
that rate.  Reconstructing the exact GA contact therefore strictly lowers
the original A circle, even if that circle was already below the ceiling.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.MiddleAAdvanceContraction
open HardSplitCap MiddlePositiveContraction

def demand (B : SignedPoint) (x : ℝ) : ℝ :=
  1+(B.y+1/2)*Real.cos x+(1/2-B.a)*Real.sin x

theorem actual_demand_iff (A B : SignedPoint) {x : ℝ}
    (hx : x ∈ Icc 0 (7/10 : ℝ)) :
    zeroFeasible A B x 0 ↔ demand B x ≤ A.y+1/2 := by
  simp only [zeroFeasible,zeroProjection,Matrix.cons_val_zero]
  rw [edgeWidth_positive_formula hx]
  dsimp [demand]
  constructor <;> intro h <;> nlinarith

theorem demand_deriv (B : SignedPoint) (x : ℝ) :
    HasDerivAt (demand B)
      (-((B.a-1/2)*Real.cos x+(B.y+1/2)*Real.sin x)) x := by
  convert (((Real.hasDerivAt_cos x).const_mul (B.y+1/2)).const_add 1).add
    ((Real.hasDerivAt_sin x).const_mul (1/2-B.a)) using 1
  · rfl
  · ring

/-- The actual source B point gives a whole-angle derivative bound. -/
theorem demand_opposing_rate {B : SignedPoint} {x : ℝ}
    (hBa : B.a ≤ 283/200) (hyB : B.y ≤ 0)
    (hx : x ∈ Icc 0 (7/10 : ℝ)) :
    (B.a-1/2)*Real.cos x+(B.y+1/2)*Real.sin x < 21/20 := by
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hx
  have hc0 : 0 ≤ Real.cos x := by linarith
  have hp := mul_le_mul_of_nonneg_right (show B.a-1/2 ≤ 183/200 by linarith) hc0
  have ht := mul_le_mul_of_nonneg_right (show B.y+1/2 ≤ 1/2 by linarith) hs
  let R := (183/200 : ℝ)*Real.cos x+(1/2)*Real.sin x
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hRsq : R^2 ≤ (183/200 : ℝ)^2+(1/2 : ℝ)^2 := by
    have hu := Real.sin_sq_add_cos_sq x
    have hz := sq_nonneg ((183/200 : ℝ)*Real.sin x-(1/2)*Real.cos x)
    dsimp [R]
    nlinarith
  have hRu : R < 21/20 := by nlinarith
  dsimp [R] at hRu
  linarith

theorem demand_gain {B : SignedPoint} {d e : ℝ}
    (hBa : B.a ≤ 283/200) (hyB : B.y ≤ 0)
    (hd : d ∈ Icc 0 (7/10 : ℝ)) (he : 0 ≤ e) (hed : e < d) :
    demand B e < demand B d+(21/20)*(d-e) := by
  have hf : StrictMonoOn (fun x => demand B x+(21/20)*x) (Icc 0 (7/10 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 (7/10 : ℝ))
    · intro x hx
      exact ((demand_deriv B x).add
        ((hasDerivAt_id x).const_mul (21/20))).continuousAt.continuousWithinAt
    · intro x hx
      have hxd := interior_subset hx
      have hdr := (demand_deriv B x).add ((hasDerivAt_id x).const_mul (21/20))
      rw [hdr.deriv]
      linarith [demand_opposing_rate hBa hyB hxd]
  have hh := hf (show e ∈ Icc 0 (7/10 : ℝ) from ⟨he,hed.le.trans hd.2⟩) hd hed
  linarith

structure AAdvance (G A B : SignedPoint) (t e : ℝ) where
  point : SignedPoint
  sorted : point.Sorted
  avoids : point.AvoidsCore
  normal : 0 ≤ point.y
  circle_lt : point.circle < A.circle
  transverse_nondecrease : A.y ≤ point.y
  GA_exact : quarterProjection G point (-t) 0=edgeWidth (-t)
  AB : zeroFeasible point B e 0

/-- Original weak GA0 and AB0 invoke the cap gain at A's actual circle.
The selected tangent is explicit, and the exact contact primary is
strictly inside that circle.  The only fixed ceiling is an upper bound. -/
theorem actual_A_advance {G A B : SignedPoint} {r d m : ℝ}
    (hqA : A.circle ≤ qCap) (hyA : 0 ≤ A.y)
    (hBa : B.a ≤ 283/200) (hyB : B.y ≤ 0) (hyG : G.y ≤ (1/10 : ℝ))
    (hr : r ∈ Icc 0 (7/10 : ℝ)) (hd : d ∈ Icc 0 (7/10 : ℝ))
    (hm : 0 < m) (hmr : m ≤ r) (hmd : m ≤ d)
    (hGA : quarterFeasible G A (-r) 0) (hAB : zeroFeasible A B d 0) :
    Nonempty (AAdvance G A B (r-m) (d-m)) := by
  let D := 1/2-G.y
  let X := A.a+1/2
  let Y := A.y+1/2
  let Y' := max Y (demand B (d-m))
  let X' := primaryCorner D Y' (r-m)
  have hD : 2/5 ≤ D := by dsimp [D]; linarith
  have hY : 1/2 ≤ Y := by dsimp [Y]; linarith
  have ht : r-m ∈ Icc 0 (7/10 : ℝ) := ⟨sub_nonneg.mpr hmr,by linarith [hr.2]⟩
  have he : d-m ∈ Icc 0 (7/10 : ℝ) := ⟨sub_nonneg.mpr hmd,by linarith [hd.2]⟩
  have hcontact : D ≤ (X-1)*Real.cos r-Y*Real.sin r := by
    have hh := hGA
    simp [quarterFeasible,quarterProjection] at hh
    rw [edgeWidth_positive_formula hr] at hh
    dsimp [D,X,Y]
    nlinarith
  have hsource : X^2+Y^2=A.circle := by
    simp [X,Y,SignedPoint.circle,abs_of_nonneg hyA]
  have hf : MiddleHardCap.Feasible A.circle D := MiddleHardCap.feasible_of_contact
    hqA hD hr hY hcontact hsource.le
  have hcap : Y ≤ cap A.circle D r := MiddleHardCap.cap_majorizes
    hf hr (show 0 ≤ Y by linarith) hcontact hsource.le
  have hgain := MiddleHardCap.cap_gain hf hr ht.1
    (show r-m < r by linarith) (hY.trans hcap)
  have hdemand := demand_gain hBa hyB hd he.1 (show d-m < d by linarith)
  have hABsource : demand B d ≤ Y := by
    simpa [Y] using (actual_demand_iff A B hd).1 hAB
  have hYtarget : 1/2 ≤ Y' := hY.trans (le_max_left _ _)
  have htargetcap : Y' < cap A.circle D (r-m) := by
    dsimp [Y']
    apply max_lt
    · linarith
    · linarith
  obtain ⟨hprimary,hnorm,hsorted⟩ := MiddleHardCap.strict_contact_norm
    hf ht hYtarget htargetcap
  change 7/5 ≤ X' at hprimary
  change X'^2+Y'^2 < A.circle at hnorm
  change Y' < X' at hsorted
  let A' : SignedPoint := ⟨X'-1/2,Y'-1/2⟩
  have hnormal : 0 ≤ A'.y := by dsimp [A']; linarith
  have hcircle : A'.circle=X'^2+Y'^2 := by
    dsimp [SignedPoint.circle]
    rw [abs_of_nonneg hnormal]
    dsimp [A']
    ring
  refine ⟨{
    point := A'
    sorted := ⟨by dsimp [A']; linarith,?_⟩
    avoids := ?_
    normal := hnormal
    circle_lt := by rw [hcircle]; exact hnorm
    transverse_nondecrease := by
      have hh : Y ≤ Y' := le_max_left _ _
      dsimp [A',Y] at *
      linarith
    GA_exact := ?_
    AB := ?_
  }⟩
  · rw [abs_of_nonneg hnormal]
    dsimp [A']
    linarith
  · have ha : (9/10 : ℝ) ≤ A'.a := by dsimp [A']; linarith
    dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
    rw [max_eq_left (by linarith : 0 ≤ A'.a-1/2)]
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2/5)
      (show 2/5 ≤ A'.a-1/2 by linarith) 2
    nlinarith [sq_nonneg (max (|A'.y|-1/2) 0)]
  · have hc0 : Real.cos (r-m) ≠ 0 := ne_of_gt (by
      linarith [(transport_trig_coarse ht).1] : 0 < Real.cos (r-m))
    have hh := primaryCorner_contact (D := D) (Y := Y') hc0
    change (X'-1)*Real.cos (r-m)-Y'*Real.sin (r-m)=D at hh
    change G.y+A'.a*Real.cos (-(r-m))+A'.y*Real.sin (-(r-m))=edgeWidth (-(r-m))
    rw [Real.cos_neg,Real.sin_neg,edgeWidth_neg,edgeWidth_positive_formula ht]
    dsimp [A',D] at *
    nlinarith
  · apply (actual_demand_iff A' B he).2
    have hh : demand B (d-m) ≤ Y' := le_max_right _ _
    dsimp [A']
    linarith

end SquaresInCircles.Eight.TableFree.MiddleAAdvanceContraction

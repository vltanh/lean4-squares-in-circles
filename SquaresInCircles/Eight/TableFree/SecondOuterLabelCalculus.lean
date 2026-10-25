module

public import SquaresInCircles.Eight.TableFree.SecondWordData
public import SquaresInCircles.Eight.TableFree.ShortOuterZeroPositivePrimary

/-!
# Exact circle references for the original second-word labels

The only enclosures here are proved from the one physical circle equation.
Multiplying a label derivative by its positive circle radical makes the
reference comparison affine in that radical.  Thus a rational square
bracket supplies a reference without an interval evaluation procedure.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma shifted_chart_reference {b l u : ℝ} (hb : b∈Icc 0 outerAxial)
    (hl : 0≤l) (hu : 0≤u)
    (hlo : l^2+(W b)^2<Q0) (hhi : Q0<u^2+(W b)^2) :
    l<U b ∧ U b<u := by
  have hc := UW_circle hb
  have hp := U_positive hb
  constructor <;> nlinarith

namespace Asymmetric

lemma rational_outer_mem {b : ℝ} (hb : b∈Icc 0 (899/1000)) :
    b∈Icc 0 outerDiagonal :=
  ⟨hb.1,by linarith [hb.2,fine_outer_endpoint_bounds.2]⟩

lemma shifted_reference {b l u : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hl : 0≤l) (hu : 0≤u)
    (hlo : l^2+(W b)^2<Q0) (hhi : Q0<u^2+(W b)^2) :
    l<U b ∧ U b<u := shifted_chart_reference (outer_domain hb) hl hu hlo hhi

end Asymmetric

lemma affine_min_le {c l u x : ℝ} (hx : x∈Icc l u) :
    min (c*l) (c*u)≤c*x := by
  by_cases hc : 0≤c
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hx.1 hc)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge hc))

lemma affine_le_max {c l u x : ℝ} (hx : x∈Icc l u) :
    c*x≤ max (c*l) (c*u) := by
  by_cases hc : 0≤c
  · exact (mul_le_mul_of_nonneg_left hx.2 hc).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge hc)).trans (le_max_left _ _)

lemma RoleLabel.first_numerator (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) :
    H.d1 b*U b=(H.q+2*H.r*b-H.s/2)*U b+
      H.s*(Q0-(W b)^2)-(H.p+H.s*b)*W b := by
  have hp := U_positive hb
  have hc := UW_circle hb
  have hr : ratio b*U b=W b := by
    change (W b/U b)*U b=W b
    field_simp [hp.ne']
  dsimp [RoleLabel.d1,U,W] at hc hr ⊢
  linear_combination H.s*hc-(H.p+H.s*b)*hr

lemma RoleLabel.third_numerator (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) :
    H.d3 b*(U b)^5= -3*Q0*(H.s*Q0+(H.p-H.s/2)*W b) := by
  have hu := U_positive hb
  have hu0 : U b≠0 := hu.ne'
  have hc := UW_circle hb
  have hD : ratioD b=Q0/(U b)^3 := rfl
  have hDD : ratioDD b=3*Q0*(W b)/(U b)^5 := rfl
  have he : H.d3 b*(U b)^5=
      -3*Q0*(H.s*(U b)^2+(H.p+H.s*b)*W b) := by
    rw [RoleLabel.d3,hD,hDD]
    field_simp
    ring
  rw [he]
  simp only [W] at hc ⊢
  linear_combination -3*Q0*H.s*hc

/-- The hypotheses following the circle domain contain rational data only
when the reference and radical bracket are rational. -/
lemma RoleLabel.first_chart_reference (H : RoleLabel) {b l u dlo dhi : ℝ}
    (hb : b∈Icc 0 outerAxial)
    (hl : 0≤l) (hu : 0≤u)
    (hlo : l^2+(W b)^2<Q0) (hhi : Q0<u^2+(W b)^2)
    (hdlo : 0< min ((H.q+2*H.r*b-H.s/2-dlo)*l)
      ((H.q+2*H.r*b-H.s/2-dlo)*u)+
        H.s*(Q0-(W b)^2)-(H.p+H.s*b)*W b)
    (hdhi : max ((H.q+2*H.r*b-H.s/2-dhi)*l)
      ((H.q+2*H.r*b-H.s/2-dhi)*u)+
        H.s*(Q0-(W b)^2)-(H.p+H.s*b)*W b<0) :
    dlo<H.d1 b ∧ H.d1 b<dhi := by
  have hU := shifted_chart_reference hb hl hu hlo hhi
  have hp := U_positive hb
  have he := H.first_numerator hb
  have hlow := affine_min_le (c := H.q+2*H.r*b-H.s/2-dlo)
    ⟨hU.1.le,hU.2.le⟩
  have hhigh := affine_le_max (c := H.q+2*H.r*b-H.s/2-dhi)
    ⟨hU.1.le,hU.2.le⟩
  constructor <;> nlinarith

lemma primary_ratio_one {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    1≤ratio a := by
  have hp := U_positive (primary_domain ha)
  have hs := primary_state ha
  change 1≤W a/U a
  apply (one_le_div hp).2
  dsimp [U,W]
  linarith [hs.2.1]

lemma RoleLabel.affine_difference_hasDerivAt (H : RoleLabel) (c : ℝ)
    {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    HasDerivAt (fun t => c*t-H.outer t) (c-H.d1 b) b := by
  have h1 : HasDerivAt (fun t => c*t) (c*1) b := (hasDerivAt_id' b).const_mul c
  exact (h1.sub (H.outer_hasDerivAt hb)).congr_deriv (by ring)

lemma RoleLabel.tangent_upper (H : RoleLabel) {l u x t : ℝ}
    (hdom : Icc l u⊆Icc 0 outerAxial)
    (hx : x∈Icc l u) (ht : t∈Icc l u)
    (hsecond : ∀ y∈Icc l u, H.d2 y≤0) :
    H.outer x≤H.outer t+H.d1 t*(x-t) := by
  have hh := curvature_tangent (f := fun y => -H.outer y)
    (d := fun y => -H.d1 y) (dd := fun y => -H.d2 y) (κ := 0)
    hx ht
    (fun y hy => (H.outer_hasDerivAt (hdom hy)).neg)
    (fun y hy => (H.d1_hasDerivAt (hdom hy)).neg)
    (fun y hy => neg_nonneg.mpr (hsecond y hy))
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord

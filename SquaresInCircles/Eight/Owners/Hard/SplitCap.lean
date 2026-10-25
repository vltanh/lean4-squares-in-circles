module

public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: convex hard-quarter caps at the actual squared radius

The cap uses its own actual squared radius `q`.  The fixed ceiling is used
only for rational estimates.  Strict curvature is proved on the complete
interval `[0, 7/10]`, including the part where the cap is nonpositive.
The two formulas for the curvature numerator avoid a positivity assumption
on the cap itself.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HardSplitCap

/-- These are the scalar consequences of an actual hard contact and its
own corner-circle inequality.  No endpoint or extremality is assumed. -/
structure Feasible (q D : ℝ) : Prop where
  ceiling : q ≤ qCap
  transverse : 3/5 ≤ D
  corner : (D+1)^2+1/4 ≤ q

def contact (D θ : ℝ) : ℝ := D+Real.cos θ
def root (q D θ : ℝ) : ℝ := Real.sqrt (q-(contact D θ)^2)
def cap (q D θ : ℝ) : ℝ :=
  Real.cos θ*root q D θ-Real.sin θ*contact D θ
def cornerX (q D θ : ℝ) : ℝ :=
  Real.cos θ*contact D θ+Real.sin θ*root q D θ
def drift (q D θ : ℝ) : ℝ := root q D θ-Real.sin θ
def first (q D θ : ℝ) : ℝ := -cornerX q D θ*drift q D θ/root q D θ
def second (q D θ : ℝ) : ℝ :=
  (cap q D θ*root q D θ*(cornerX q D θ-(drift q D θ)^2)+
    cornerX q D θ*drift q D θ*contact D θ*Real.sin θ)/(root q D θ)^3

theorem parameter_bounds {q D : ℝ} (h : Feasible q D) :
    0 < D ∧ D < 183/200 ∧ D < 19/20 ∧ 0 < q := by
  have hD : 0 < D := by linarith [h.transverse]
  have hD' : D < 183/200 := by
    by_contra! hn
    have hc := h.ceiling
    dsimp [qCap] at hc
    nlinarith [h.corner,sq_nonneg (D-183/200)]
  exact ⟨hD,hD',by linarith,by nlinarith [h.corner,sq_nonneg (D+1)]⟩

theorem radicand_lower {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    1/4 ≤ q-(contact D θ)^2 ∧
      1/4 ≤ q-(contact D θ)^2-(Real.sin θ)^2 := by
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc1 := Real.cos_le_one θ
  have hD := (parameter_bounds h).1
  have hp := mul_nonneg hD.le (sub_nonneg.mpr hc1)
  have hc2 := pow_le_pow_left₀ (by linarith : 0 ≤ Real.cos θ) hc1 2
  dsimp [contact]
  constructor <;> nlinarith [h.corner,Real.sin_sq_add_cos_sq θ]

theorem root_sq {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    (root q D θ)^2=q-(contact D θ)^2 :=
  Real.sq_sqrt (by linarith [(radicand_lower h hθ).1])

theorem root_pos {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : 0 < root q D θ := by
  exact Real.sqrt_pos.mpr (by linarith [(radicand_lower h hθ).1])

theorem contact_pos {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : 0 < contact D θ := by
  dsimp [contact]
  linarith [(parameter_bounds h).1,(transport_trig_coarse hθ).1]

theorem drift_pos {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : 0 < drift q D θ := by
  have hr := root_pos h hθ
  have hrs := root_sq h hθ
  have hs := (transport_trig_coarse hθ).2.1
  have hb := (radicand_lower h hθ).2
  dsimp [drift]
  nlinarith

theorem cornerX_pos {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : 0 < cornerX q D θ := by
  have hc : 0 < Real.cos θ := by linarith [(transport_trig_coarse hθ).1]
  have hs := (transport_trig_coarse hθ).2.1
  exact add_pos_of_pos_of_nonneg (mul_pos hc (contact_pos h hθ))
    (mul_nonneg hs (root_pos h hθ).le)

/-- The half-angle comparison used for the first curvature factor is
proved by positive squaring.  It is uniform in the actual radius. -/
theorem root_half_angle {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    0 < (root q D θ-Real.sin θ)*(1+Real.cos θ)-D*Real.sin θ := by
  let c := Real.cos θ
  let s := Real.sin θ
  let w := root q D θ
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc1 := Real.cos_le_one θ
  obtain ⟨hD,hD915,hD95,hq⟩ := parameter_bounds h
  have hw : 0 < w := root_pos h hθ
  have hwsq : w^2=q-(D+c)^2 := root_sq h hθ
  have hunit : s^2+c^2=1 := Real.sin_sq_add_cos_sq θ
  have hden : 0 < 1+c := by dsimp [c]; linarith
  have hD2 : D^2 ≤ (19/20 : ℝ)^2 :=
    pow_le_pow_left₀ hD.le hD95.le 2
  have hgap : 0 ≤ 1-c := by dsimp [c]; linarith
  have hgap' : 1-c ≤ 1/4 := by dsimp [c]; linarith
  have hprod : D^2*(1-c) ≤ (19/20 : ℝ)^2*(1/4) := by
    calc
      D^2*(1-c) ≤ (19/20 : ℝ)^2*(1-c) :=
        mul_le_mul_of_nonneg_right hD2 hgap
      _ ≤ (19/20 : ℝ)^2*(1/4) :=
        mul_le_mul_of_nonneg_left hgap' (by norm_num)
  have hcore : 0 < (1+c)/4-D^2*(1-c) := by dsimp [c] at hprod ⊢; linarith
  have hf := mul_le_mul_of_nonneg_left h.corner (sq_nonneg (1+c))
  have hid : (w*(1+c))^2-(s*(1+c+D))^2=
      (1+c)^2*(q-(D+1)^2)-D^2*(1-c^2) := by
    calc
      (w*(1+c))^2-(s*(1+c+D))^2 =
          w^2*(1+c)^2-s^2*(1+c+D)^2 := by ring
      _ = (1+c)^2*(q-(D+1)^2)-D^2*(1-c^2) := by
        rw [hwsq,show s^2=1-c^2 by linarith [hunit]]
        ring
  have hdiff : 0 < (w*(1+c))^2-(s*(1+c+D))^2 := by
    rw [hid]
    have hp := mul_pos hden hcore
    linarith
  have hleft := mul_pos hw hden
  have hcomp : s*(1+c+D) < w*(1+c) := by
    by_contra! hn
    have hsq := pow_le_pow_left₀ hleft.le hn 2
    linarith
  change 0 < (w-s)*(1+c)-D*s
  linarith

theorem first_curvature_factor {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    611/2500 ≤ cornerX q D θ-(drift q D θ)^2 := by
  let c := Real.cos θ
  let s := Real.sin θ
  let w := root q D θ
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hden : 0 < 1+c := by dsimp [c]; linarith
  have hbr : 0 < (w-s)*(1+c)-D*s := root_half_angle h hθ
  have hmul := mul_nonneg hs hbr.le
  have hunit : s^2+c^2=1 := Real.sin_sq_add_cos_sq θ
  have hsq : w^2=q-(D+c)^2 := root_sq h hθ
  have hid : (s*(w-s)-D*(1-c))*(1+c)=
      s*((w-s)*(1+c)-D*s) := by
    linear_combination D*hunit
  have hnonneg : 0 ≤ s*(w-s)-D*(1-c) := by
    have hh : 0 ≤ (s*(w-s)-D*(1-c))*(1+c) := by rw [hid]; exact hmul
    exact nonneg_of_mul_nonneg_left hh hden
  have hf : cornerX q D θ-(drift q D θ)^2=
      D^2+3*D+2-q+3*(s*(w-s)-D*(1-c)) := by
    dsimp [cornerX,drift,contact]
    change c*(D+c)+s*w-(w-s)^2=
      D^2+3*D+2-q+3*(s*(w-s)-D*(1-c))
    nlinarith [hunit,hsq]
  have hD2 : (3/5 : ℝ)^2 ≤ D^2 :=
    pow_le_pow_left₀ (by norm_num) h.transverse 2
  have hq := h.ceiling
  dsimp [qCap] at hq
  rw [hf]
  nlinarith [h.transverse]

theorem second_curvature_factor {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    41/320 ≤ Real.cos θ*(root q D θ)^2-contact D θ*(Real.sin θ)^2 := by
  let c := Real.cos θ
  let s := Real.sin θ
  let w := root q D θ
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc1 := Real.cos_le_one θ
  obtain ⟨hD,hD915,hD95,hq⟩ := parameter_bounds h
  have hunit : s^2+c^2=1 := Real.sin_sq_add_cos_sq θ
  have hsq : w^2=q-(D+c)^2 := root_sq h hθ
  have hid : c*w^2-(D+c)*s^2=c*(q-D^2-1)-D*(1+c^2) := by
    linear_combination c*hsq-(D+c)*hunit
  have hp := mul_nonneg (by dsimp [c]; linarith : 0 ≤ c)
    (show 0 ≤ q-(D+1)^2-1/4 by linarith [h.corner])
  have hgap : (1-c)^2 ≤ (1/4 : ℝ)^2 :=
    pow_le_pow_left₀ (by dsimp [c]; linarith)
      (by dsimp [c]; linarith) 2
  have hprod : D*(1-c)^2 ≤ (19/20 : ℝ)*(1/4)^2 := by
    calc
      D*(1-c)^2 ≤ (19/20 : ℝ)*(1-c)^2 :=
        mul_le_mul_of_nonneg_right hD95.le (sq_nonneg _)
      _ ≤ (19/20 : ℝ)*(1/4)^2 :=
        mul_le_mul_of_nonneg_left hgap (by norm_num)
  change 41/320 ≤ c*w^2-(D+c)*s^2
  rw [hid]
  dsimp [c] at *
  nlinarith

theorem second_alternate (q D θ : ℝ) :
    second q D θ=
      (cornerX q D θ*(Real.cos θ*(root q D θ)^2-
          contact D θ*(Real.sin θ)^2)-
        cap q D θ*root q D θ*(drift q D θ)^2)/(root q D θ)^3 := by
  unfold second cap cornerX drift
  congr 1
  ring

/-- The sign split concerns the cap value on one continuous interval;
there is no angular subdivision or sampled certificate. -/
theorem second_pos {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : 0 < second q D θ := by
  have hw := root_pos h hθ
  have hX := cornerX_pos h hθ
  have hk := drift_pos h hθ
  have hC := contact_pos h hθ
  have hs := (transport_trig_coarse hθ).2.1
  by_cases hL : 0 < cap q D θ
  · unfold second
    apply div_pos _ (pow_pos hw 3)
    have hf : 0 < cornerX q D θ-(drift q D θ)^2 := by
      linarith [first_curvature_factor h hθ]
    exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos hL hw) hf)
      (mul_nonneg (mul_nonneg (mul_nonneg hX.le hk.le) hC.le) hs)
  · rw [second_alternate]
    apply div_pos _ (pow_pos hw 3)
    have hf : 0 < Real.cos θ*(root q D θ)^2-contact D θ*(Real.sin θ)^2 := by
      linarith [second_curvature_factor h hθ]
    have hn : cap q D θ*root q D θ*(drift q D θ)^2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hL) hw.le) (sq_nonneg _)
    linarith [mul_pos hX hf]

theorem root_deriv {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    HasDerivAt (root q D) (contact D θ*Real.sin θ/root q D θ) θ := by
  have hC := (Real.hasDerivAt_cos θ).const_add D
  have hr : q-(contact D θ)^2 ≠ 0 := by
    linarith [(radicand_lower h hθ).1]
  have hd := ((hC.pow 2).const_sub q).sqrt hr
  convert hd using 1
  · rfl
  · dsimp [contact,root]
    field_simp [(root_pos h hθ).ne']

theorem drift_deriv {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    HasDerivAt (drift q D) (-cap q D θ/root q D θ) θ := by
  convert (root_deriv h hθ).sub (Real.hasDerivAt_sin θ) using 1
  · rfl
  · dsimp [cap]
    field_simp [(root_pos h hθ).ne']
    ring

theorem cornerX_deriv {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    HasDerivAt (cornerX q D) (cap q D θ*drift q D θ/root q D θ) θ := by
  have hC := (Real.hasDerivAt_cos θ).const_add D
  have hd := ((Real.hasDerivAt_cos θ).mul hC).add
    ((Real.hasDerivAt_sin θ).mul (root_deriv h hθ))
  convert hd using 1
  · rfl
  · dsimp [cap,drift,contact]
    field_simp [(root_pos h hθ).ne']
    ring

theorem cap_deriv {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : HasDerivAt (cap q D) (first q D θ) θ := by
  have hC := (Real.hasDerivAt_cos θ).const_add D
  have hd := ((Real.hasDerivAt_cos θ).mul (root_deriv h hθ)).sub
    ((Real.hasDerivAt_sin θ).mul hC)
  convert hd using 1
  · rfl
  · dsimp [first,cornerX,drift,contact]
    field_simp [(root_pos h hθ).ne']
    ring

theorem first_deriv {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    HasDerivAt (first q D) (second q D θ) θ := by
  have hd := (((cornerX_deriv h hθ).neg).mul (drift_deriv h hθ)).div
    (root_deriv h hθ) (root_pos h hθ).ne'
  convert hd using 1
  · rfl
  · dsimp [second]
    field_simp [(root_pos h hθ).ne']
    ring

theorem first_neg {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : first q D θ < 0 := by
  unfold first
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_neg_of_pos (cornerX_pos h hθ)) (drift_pos h hθ))
    (root_pos h hθ)

/-- A reusable interval form that keeps the explicit derivative witnesses;
there is no assumption about an abstract second-derivative operator. -/
private theorem strictConvex_of_derivatives {f df ddf : ℝ → ℝ} {l u : ℝ}
    (hd : ∀ x ∈ Icc l u, HasDerivAt f (df x) x)
    (hdd : ∀ x ∈ Icc l u, HasDerivAt df (ddf x) x)
    (hp : ∀ x ∈ Icc l u, 0 < ddf x) : StrictConvexOn ℝ (Icc l u) f := by
  have hm : StrictMonoOn df (Icc l u) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc l u)
    · exact fun x hx => (hdd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [(hdd x (interior_subset hx)).deriv]
      exact hp x (interior_subset hx)
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc l u)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
  intro x hx y hy hxy
  rw [(hd x (interior_subset hx)).deriv,(hd y (interior_subset hy)).deriv]
  exact hm (interior_subset hx) (interior_subset hy) hxy

theorem cap_strictAnti {q D : ℝ} (h : Feasible q D) :
    StrictAntiOn (cap q D) (Icc 0 (7/10 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 (7/10 : ℝ))
  · exact fun θ hθ => (cap_deriv h hθ).continuousAt.continuousWithinAt
  · intro θ hθ
    rw [(cap_deriv h (interior_subset hθ)).deriv]
    exact first_neg h (interior_subset hθ)

/-- The two circles retain independent actual squared radii. -/
def split (qA DA qB DB α θ : ℝ) : ℝ := cap qA DA θ+cap qB DB (α-θ)

theorem split_strictConvex {qA DA qB DB α : ℝ}
    (hA : Feasible qA DA) (hB : Feasible qB DB)
    (hα : α ∈ Icc 0 (7/10 : ℝ)) :
    StrictConvexOn ℝ (Icc 0 α) (split qA DA qB DB α) := by
  apply strictConvex_of_derivatives
    (df := fun θ => first qA DA θ-first qB DB (α-θ))
    (ddf := fun θ => second qA DA θ+second qB DB (α-θ))
  · intro θ hθ
    have ht : θ ∈ Icc 0 (7/10 : ℝ) := ⟨hθ.1,hθ.2.trans hα.2⟩
    have hu : α-θ ∈ Icc 0 (7/10 : ℝ) := by constructor <;> linarith [hθ.1,hθ.2,hα.2]
    have hd := (cap_deriv hA ht).add
      ((cap_deriv hB hu).comp θ ((hasDerivAt_id θ).const_sub α))
    convert hd using 1
    · rfl
    · ring
  · intro θ hθ
    have ht : θ ∈ Icc 0 (7/10 : ℝ) := ⟨hθ.1,hθ.2.trans hα.2⟩
    have hu : α-θ ∈ Icc 0 (7/10 : ℝ) := by constructor <;> linarith [hθ.1,hθ.2,hα.2]
    have hd := (first_deriv hA ht).sub
      ((first_deriv hB hu).comp θ ((hasDerivAt_id θ).const_sub α))
    convert hd using 1
    · rfl
    · ring
  · intro θ hθ
    exact add_pos (second_pos hA ⟨hθ.1,hθ.2.trans hα.2⟩)
      (second_pos hB (by constructor <;> linarith [hθ.1,hθ.2,hα.2]))

private theorem strictConvex_lt_max {f : ℝ → ℝ} {l u x : ℝ}
    (h : StrictConvexOn ℝ (Icc l u) f) (hx : x ∈ Ioo l u) :
    f x < max (f l) (f u) := by
  have hlu : 0 < u-l := by linarith [hx.1,hx.2]
  let a : ℝ := (u-x)/(u-l)
  let b : ℝ := (x-l)/(u-l)
  have ha : 0 < a := div_pos (by linarith [hx.2]) hlu
  have hb : 0 < b := div_pos (by linarith [hx.1]) hlu
  have hab : a+b=1 := by dsimp [a,b]; field_simp [hlu.ne']; ring
  have harg : a*l+b*u=x := by dsimp [a,b]; field_simp [hlu.ne']; ring
  have hh := h.2 (left_mem_Icc.mpr (by linarith))
    (right_mem_Icc.mpr (by linarith)) (by linarith) ha hb hab
  simp only [smul_eq_mul,harg] at hh
  have hL := mul_le_mul_of_nonneg_left (le_max_left (f l) (f u)) ha.le
  have hU := mul_le_mul_of_nonneg_left (le_max_right (f l) (f u)) hb.le
  have hweight : a*max (f l) (f u)+b*max (f l) (f u)=max (f l) (f u) := by
    nlinarith [congrArg (fun z : ℝ => z*max (f l) (f u)) hab]
  linarith

theorem split_endpoint_strict {qA DA qB DB t u : ℝ}
    (hA : Feasible qA DA) (hB : Feasible qB DB)
    (ht : 0 < t) (hu : 0 < u) (hspan : t+u ≤ 7/10) :
    cap qA DA t+cap qB DB u <
      max (cap qA DA 0+cap qB DB (t+u))
        (cap qA DA (t+u)+cap qB DB 0) := by
  have hh := strictConvex_lt_max
    (split_strictConvex hA hB ⟨by linarith,hspan⟩)
    (show t ∈ Ioo 0 (t+u) by constructor <;> linarith)
  simpa [split] using hh

theorem split_endpoint {qA DA qB DB t u : ℝ}
    (hA : Feasible qA DA) (hB : Feasible qB DB)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hspan : t+u ≤ 7/10) :
    cap qA DA t+cap qB DB u ≤
      max (cap qA DA 0+cap qB DB (t+u))
        (cap qA DA (t+u)+cap qB DB 0) := by
  rcases eq_or_lt_of_le ht with ht | ht
  · subst t
    simpa using le_max_left (cap qA DA 0+cap qB DB u)
      (cap qA DA u+cap qB DB 0)
  rcases eq_or_lt_of_le hu with hu | hu
  · subst u
    simpa using le_max_right (cap qA DA 0+cap qB DB t)
      (cap qA DA t+cap qB DB 0)
  exact (split_endpoint_strict hA hB ht hu hspan).le

end SquaresInCircles.Eight.HardSplitCap

module

public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.NecessaryCycle
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: the hard split on a necessary seven-cycle

With HG, AB and TD aligned and the common A/B frame between those of T and G, the HG and TD
witnesses force the transverse bounds of the cap construction (`HardInput.aligned_pair_bounds`).
The move `HardInput.replaceMiddle` changes only A and B: H, G, T, D, E, the four witnesses not
incident to A or B, and the radius stay. The endpoint split is a hard input at the same radius
(`HardInput.exists_split_aligned`), and an interior split charges a strict loss to the anchors A
and B (`HardInput.exists_split_strict_loss`).

The three alignments and the position of the common frame are hypotheses.
-/

section
/-!
## Convex hard-quarter caps at the actual squared radius

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
    simp
  rcases eq_or_lt_of_le hu with hu | hu
  · subst u
    simp
  exact (split_endpoint_strict hA hB ht hu hspan).le

end SquaresInCircles.Eight.HardSplitCap
end
end
end

section
/-!
## Realizing the split of the hard quarter

The weak witnesses of the hard quarter and the circles of the anchors give the cap comparison
(`feasible_of_weak_contact`, `cap_majorizes_weak_contact`, `actual_cap_bound`). The construction
changes only the two middle centers and their common frame: G and T stay, and the two hard
projections are equalities for the owner axes `0` and `2` (`PairEndpoint`,
`actual_pair_endpoint`).

Each middle corner keeps its circle, so a strict loss at either middle anchor is kept, and an
interior split leaves strict slack on the aligned AB separator.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HardSplitCap

theorem primary_lower_of_contact {D θ X Z : ℝ}
    (hD : 3/5 ≤ D) (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hZ : 0 ≤ Z)
    (hcontact : D ≤ (X-1)*Real.cos θ-Z*Real.sin θ) : D+1 ≤ X := by
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc0 : 0 < Real.cos θ := by linarith
  have hZs := mul_nonneg hZ hs
  have hX : 0 ≤ X-1 := by
    by_contra! hn
    have hp := mul_neg_of_neg_of_pos hn hc0
    linarith
  have hp := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hX
  nlinarith

/-- The scalar cap is feasible as soon as the contact and the corner inequality hold, also when the
contact is slack. -/
theorem feasible_of_weak_contact {q D θ X Z : ℝ}
    (hQ : q ≤ qCap) (hD : 3/5 ≤ D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hZ : 1/2 ≤ Z)
    (hcontact : D ≤ (X-1)*Real.cos θ-Z*Real.sin θ)
    (hcircle : X^2+Z^2 ≤ q) : Feasible q D := by
  have hX := primary_lower_of_contact hD hθ (by linarith) hcontact
  have hXs := pow_le_pow_left₀ (by linarith : 0 ≤ D+1) hX 2
  have hZs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hZ 2
  exact ⟨hQ,hD,by nlinarith⟩

/-- For the rotated corner with its weak contact and in its own circle, the perpendicular
coordinate is at most the cap, a root at the radius `q`. -/
theorem cap_majorizes_weak_contact {q D θ X Z : ℝ}
    (h : Feasible q D) (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hZ : 0 ≤ Z)
    (hcontact : D ≤ (X-1)*Real.cos θ-Z*Real.sin θ)
    (hcircle : X^2+Z^2 ≤ q) : Z ≤ cap q D θ := by
  let P := X*Real.cos θ-Z*Real.sin θ
  let R := X*Real.sin θ+Z*Real.cos θ
  have hX := primary_lower_of_contact h.transverse hθ hZ hcontact
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc0 : 0 ≤ Real.cos θ := by linarith
  have hP : contact D θ ≤ P := by dsimp [P,contact]; nlinarith
  have hP2 := pow_le_pow_left₀ (contact_pos h hθ).le hP 2
  have hR0 : 0 ≤ R := by
    exact add_nonneg (mul_nonneg (by linarith [h.transverse]) hs)
      (mul_nonneg hZ hc0)
  have hrotation : P^2+R^2=X^2+Z^2 := by
    dsimp [P,R]
    calc
      (X*Real.cos θ-Z*Real.sin θ)^2+(X*Real.sin θ+Z*Real.cos θ)^2 =
          (X^2+Z^2)*((Real.sin θ)^2+(Real.cos θ)^2) := by ring
      _ = X^2+Z^2 := by rw [Real.sin_sq_add_cos_sq,mul_one]
  have hR : R ≤ root q D θ := by
    have hw := root_pos h hθ
    have hw2 := root_sq h hθ
    nlinarith
  have hback : Real.cos θ*R-Real.sin θ*P=Z := by
    dsimp [P,R]
    linear_combination Z*(Real.sin_sq_add_cos_sq θ)
  have hR' := mul_le_mul_of_nonneg_left hR hc0
  have hP' := mul_le_mul_of_nonneg_left hP hs
  dsimp [cap]
  linarith

/-- In its own frame, a corner with the hard-quarter contact and in the circle `q` makes the cap
feasible and lies below it. -/
theorem actual_cap_bound {q bG a b θ : ℝ}
    (hQ : q ≤ qCap) (hG : 1/10 ≤ bG) (hb : 0 ≤ b)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ))
    (hcontact : edgeWidth θ+bG ≤ a*Real.cos θ-b*Real.sin θ)
    (hcircle : (a+1/2)^2+(b+1/2)^2 ≤ q) :
    Feasible q (bG+1/2) ∧ b+1/2 ≤ cap q (bG+1/2) θ := by
  have hD : (3/5 : ℝ) ≤ bG+1/2 := by linarith
  have hc : bG+1/2 ≤ (a+1/2-1)*Real.cos θ-(b+1/2)*Real.sin θ := by
    rw [edgeWidth_positive_formula hθ] at hcontact
    nlinarith
  have hf := feasible_of_weak_contact hQ hD hθ (by linarith : 1/2 ≤ b+1/2)
    hc hcircle
  exact ⟨hf,cap_majorizes_weak_contact hf hθ (by linarith) hc hcircle⟩

theorem cap_upper {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : cap q D θ < 233/200 := by
  have hzero : (0:ℝ) ∈ Icc 0 (7/10 : ℝ) := by norm_num
  have hle : cap q D θ ≤ cap q D 0 := (cap_strictAnti h).antitoneOn hzero hθ hθ.1
  have hz : cap q D 0=root q D 0 := by simp [cap]
  have hsq := root_sq h hzero
  have hD : (8/5 : ℝ) ≤ D+1 := by linarith [h.transverse]
  have hD2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8/5) hD 2
  have hq := h.ceiling
  dsimp [qCap] at hq
  simp only [contact,Real.cos_zero] at hsq
  rw [hz] at hle
  have hw := root_pos h hzero
  nlinarith

theorem corner_contact (q D θ : ℝ) :
    (cornerX q D θ-1)*Real.cos θ-cap q D θ*Real.sin θ=D := by
  dsimp [cornerX,cap,contact]
  linear_combination (D+Real.cos θ)*(Real.sin_sq_add_cos_sq θ)

theorem corner_norm {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    (cornerX q D θ)^2+(cap q D θ)^2=q := by
  calc
    (cornerX q D θ)^2+(cap q D θ)^2 =
        ((Real.sin θ)^2+(Real.cos θ)^2)*
          ((contact D θ)^2+(root q D θ)^2) := by unfold cornerX cap; ring
    _ = q := by rw [Real.sin_sq_add_cos_sq,one_mul,root_sq h hθ]; ring

def positivePoint (q D θ : ℝ) : SignedPoint :=
  ⟨cornerX q D θ-1/2,cap q D θ-1/2⟩

theorem positivePoint_hard {q D θ : ℝ} (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    (positivePoint q D θ).a*Real.cos θ-(positivePoint q D θ).y*Real.sin θ=
      edgeWidth θ+D-1/2 := by
  rw [edgeWidth_positive_formula hθ]
  dsimp [positivePoint]
  nlinarith [corner_contact q D θ]

/-- When the cap exceeds `167/200`, the positive point on the cap is sorted, off the core and on
the circle `q`, with transverse coordinate in `(67/200, 133/200)` and primary at least `11/10`. -/
theorem positivePoint_properties {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hL : 167/200 < cap q D θ) :
    (67/200 < (positivePoint q D θ).y ∧ (positivePoint q D θ).y < 133/200) ∧
    11/10 ≤ (positivePoint q D θ).a ∧
    (positivePoint q D θ).Sorted ∧ (positivePoint q D θ).AvoidsCore ∧
    (positivePoint q D θ).circle=q := by
  have hU := cap_upper h hθ
  have hX := primary_lower_of_contact h.transverse hθ (by linarith : 0 ≤ cap q D θ)
    (corner_contact q D θ).ge
  have hy : 0 ≤ (positivePoint q D θ).y := by dsimp [positivePoint]; linarith
  have ha : 11/10 ≤ (positivePoint q D θ).a := by
    dsimp [positivePoint]
    linarith [h.transverse]
  refine ⟨⟨?_,?_⟩,ha,?_,?_,?_⟩
  · dsimp [positivePoint]; linarith
  · dsimp [positivePoint]; linarith
  · refine ⟨by linarith,?_⟩
    rw [abs_of_nonneg hy]
    dsimp [positivePoint] at *
    linarith
  · dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
    rw [max_eq_left (by linarith : 0 ≤ (positivePoint q D θ).a-1/2)]
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/5)
      (show 3/5 ≤ (positivePoint q D θ).a-1/2 by linarith) 2
    nlinarith [sq_nonneg (max (|(positivePoint q D θ).y|-1/2) 0)]
  · dsimp [SignedPoint.circle]
    rw [abs_of_nonneg hy]
    simpa [positivePoint] using corner_norm h hθ

private theorem choose_endpoint (qA DA qB DB t u : ℝ) :
    ∃ v w : ℝ, ((v=0 ∧ w=t+u) ∨ (v=t+u ∧ w=0)) ∧
      cap qA DA v+cap qB DB w=
        max (cap qA DA 0+cap qB DB (t+u))
          (cap qA DA (t+u)+cap qB DB 0) := by
  rcases le_total (cap qA DA 0+cap qB DB (t+u))
    (cap qA DA (t+u)+cap qB DB 0) with h | h
  · exact ⟨t+u,0,Or.inr ⟨rfl,rfl⟩,(max_eq_right h).symm⟩
  · exact ⟨0,t+u,Or.inl ⟨rfl,rfl⟩,(max_eq_left h).symm⟩

/-- The output of the two-center construction: new A and B at the two endpoint angles, sorted and
off the core, on the circles of the original A and B, with exact hard projections and AB aligned,
and strict AB slack when the split is interior. -/
structure PairEndpoint (G A B T : SignedPoint) (t u : ℝ) where
  angleA : ℝ
  angleB : ℝ
  pointA : SignedPoint
  pointB : SignedPoint
  endpoint : (angleA=0 ∧ angleB=t+u) ∨ (angleA=t+u ∧ angleB=0)
  span : angleA+angleB=t+u
  angleA_mem : angleA ∈ Icc 0 (7/10 : ℝ)
  angleB_mem : angleB ∈ Icc 0 (7/10 : ℝ)
  sorted_A : pointA.Sorted
  sorted_B : pointB.Sorted
  avoids_A : pointA.AvoidsCore
  avoids_B : pointB.AvoidsCore
  normal_A : 0 < pointA.y
  normal_B : pointB.y < 0
  primary_A : 11/10 ≤ pointA.a
  primary_B : 11/10 ≤ pointB.a
  transverse_A : 67/200 < pointA.y ∧ pointA.y < 133/200
  transverse_B : 67/200 < -pointB.y ∧ -pointB.y < 133/200
  circle_A : pointA.circle=A.circle
  circle_B : pointB.circle=B.circle
  GA_exact : quarterProjection G pointA (-angleA) 0=edgeWidth (-angleA)
  BT_exact : quarterProjection pointB T (-angleB) 2=edgeWidth (-angleB)
  AB_zero : zeroFeasible pointA pointB 0 0
  AB_two : zeroFeasible pointA pointB 0 2
  strict_if_interior : 0 < t → 0 < u → 1 < pointA.y-pointB.y

/-- The signed pair A, B has a split endpoint, by convexity of the cap. Each new corner lies on the
circle of the point it replaces, so a strict loss carried by A or B is kept; G and T do not
move. -/
theorem actual_pair_endpoint {G A B T : SignedPoint} {t u : ℝ}
    (hA : A.circle ≤ qCap) (hB : B.circle ≤ qCap)
    (hyA : 0 ≤ A.y) (hyB : B.y ≤ 0)
    (hyG : G.y ≤ -(1/10 : ℝ)) (hyT : (1/10 : ℝ) ≤ T.y)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hspan : t+u ≤ 7/10)
    (hGA : quarterFeasible G A (-t) 0)
    (hBT : quarterFeasible B T (-u) 2)
    (hAB : zeroFeasible A B 0 0) : Nonempty (PairEndpoint G A B T t u) := by
  have ht' : t ∈ Icc 0 (7/10 : ℝ) := ⟨ht,by linarith⟩
  have hu' : u ∈ Icc 0 (7/10 : ℝ) := ⟨hu,by linarith⟩
  have hAcircle : (A.a+1/2)^2+(A.y+1/2)^2 ≤ A.circle := by
    simp [SignedPoint.circle,abs_of_nonneg hyA]
  have hBcircle : (B.a+1/2)^2+(-B.y+1/2)^2 ≤ B.circle := by
    simp [SignedPoint.circle,abs_of_nonpos hyB]
  have hAhard : edgeWidth t+(-G.y) ≤ A.a*Real.cos t-A.y*Real.sin t := by
    have hh := hGA
    simp [quarterFeasible,quarterProjection] at hh
    linarith
  have hBhard : edgeWidth u+T.y ≤ B.a*Real.cos u-(-B.y)*Real.sin u := by
    have hh := hBT
    simp [quarterFeasible,quarterProjection] at hh
    nlinarith
  obtain ⟨hfA,hcapA⟩ := actual_cap_bound hA (by linarith : 1/10 ≤ -G.y) hyA ht'
    hAhard hAcircle
  obtain ⟨hfB,hcapB⟩ := actual_cap_bound hB hyT (by linarith : 0 ≤ -B.y) hu'
    hBhard hBcircle
  have hsource : 2 ≤ cap A.circle (-G.y+1/2) t+cap B.circle (T.y+1/2) u := by
    have hab : 1 ≤ A.y-B.y := by simpa [zeroFeasible,zeroProjection] using hAB
    linarith
  obtain ⟨v,w,hend,hmax⟩ := choose_endpoint A.circle (-G.y+1/2)
    B.circle (T.y+1/2) t u
  have hv : v ∈ Icc 0 (7/10 : ℝ) := by
    rcases hend with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> constructor <;> linarith
  have hw : w ∈ Icc 0 (7/10 : ℝ) := by
    rcases hend with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> constructor <;> linarith
  have hroom : 2 ≤ cap A.circle (-G.y+1/2) v+cap B.circle (T.y+1/2) w := by
    rw [hmax]
    exact hsource.trans (split_endpoint hfA hfB ht hu hspan)
  have hLA : 167/200 < cap A.circle (-G.y+1/2) v := by
    linarith [cap_upper hfB hw]
  have hLB : 167/200 < cap B.circle (T.y+1/2) w := by
    linarith [cap_upper hfA hv]
  obtain ⟨hAy,hAa,hAs,hAc,hAq⟩ := positivePoint_properties hfA hv hLA
  obtain ⟨hBy,hBa,hBs,hBc,hBq⟩ := positivePoint_properties hfB hw hLB
  let A' := positivePoint A.circle (-G.y+1/2) v
  let B' := (positivePoint B.circle (T.y+1/2) w).reflect
  have hnormalA : 0 < A'.y := by dsimp [A']; linarith [hAy.1]
  have hnormalB : B'.y < 0 := by dsimp [B',SignedPoint.reflect]; linarith [hBy.1]
  have hAB' : 1 ≤ A'.y-B'.y := by
    dsimp [A',B',positivePoint,SignedPoint.reflect]
    linarith
  refine ⟨{
    angleA := v
    angleB := w
    pointA := A'
    pointB := B'
    endpoint := hend
    span := ?_
    angleA_mem := hv
    angleB_mem := hw
    sorted_A := hAs
    sorted_B := by simpa [B'] using hBs
    avoids_A := hAc
    avoids_B := by simpa [B'] using hBc
    normal_A := hnormalA
    normal_B := hnormalB
    primary_A := hAa
    primary_B := by simpa [B',SignedPoint.reflect] using hBa
    transverse_A := hAy
    transverse_B := by simpa [B',SignedPoint.reflect] using hBy
    circle_A := hAq
    circle_B := by simpa [B'] using hBq
    GA_exact := ?_
    BT_exact := ?_
    AB_zero := by simpa [zeroFeasible,zeroProjection] using hAB'
    AB_two := by simpa [zeroFeasible,zeroProjection] using hAB'
    strict_if_interior := ?_
  }⟩
  · rcases hend with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> ring
  · have hh := positivePoint_hard (q := A.circle) (D := -G.y+1/2) hv
    change G.y+A'.a*Real.cos (-v)+A'.y*Real.sin (-v)=edgeWidth (-v)
    rw [Real.cos_neg,Real.sin_neg,edgeWidth_neg]
    dsimp [A']
    linarith
  · have hh := positivePoint_hard (q := B.circle) (D := T.y+1/2) hw
    change B'.a*Real.cos (-w)-B'.y*Real.sin (-w)-T.y=edgeWidth (-w)
    rw [Real.cos_neg,Real.sin_neg,edgeWidth_neg]
    dsimp [B',SignedPoint.reflect]
    nlinarith
  · intro hti hui
    have hstrict := split_endpoint_strict hfA hfB hti hui hspan
    rw [← hmax] at hstrict
    dsimp [A',B',positivePoint,SignedPoint.reflect]
    linarith

end SquaresInCircles.Eight.HardSplitCap
end
end
end

section
/-!
## Strict loss at both middle anchors for an interior hard split

The strict AB slack of the endpoint pays a small motion along each hard contact, by
`(-ε sin θ, -ε cos θ)` in positive own-frame coordinates (`inward`, `inward_properties`). Both
hard projections stay equalities, the AB slack stays positive, and both corner radii decrease
strictly (`InteriorImprovement`, `improve_interior`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HardSplitCap

def inward (p : SignedPoint) (θ ε : ℝ) : SignedPoint :=
  ⟨p.a-ε*Real.sin θ,p.y-ε*Real.cos θ⟩

/-- For `11/10 ≤ p.a`, `67/200 < p.y < 133/200` and `0 < ε ≤ 1/10`, the moved point is sorted, off
the core, with positive transverse coordinate and a strictly smaller circle; the cap endpoints
satisfy these margins. -/
theorem inward_properties {p : SignedPoint} {θ ε : ℝ}
    (hθ : θ ∈ Icc 0 (7/10 : ℝ))
    (ha : 11/10 ≤ p.a) (hy : 67/200 < p.y ∧ p.y < 133/200)
    (hε : 0 < ε) (hεu : ε ≤ 1/10) :
    (inward p θ ε).Sorted ∧ (inward p θ ε).AvoidsCore ∧
      0 < (inward p θ ε).y ∧ (inward p θ ε).circle < p.circle := by
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc0 : 0 ≤ Real.cos θ := by linarith
  have hes : 0 ≤ ε*Real.sin θ := mul_nonneg hε.le hs
  have hec : 0 ≤ ε*Real.cos θ := mul_nonneg hε.le hc0
  have hesu : ε*Real.sin θ ≤ 1/10 := by
    have hh := mul_le_mul_of_nonneg_left (Real.sin_le_one θ) hε.le
    nlinarith
  have hecu : ε*Real.cos θ ≤ 1/10 := by
    have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hε.le
    nlinarith
  have ha' : 1 ≤ (inward p θ ε).a := by dsimp [inward]; linarith
  have hy' : 0 < (inward p θ ε).y := by dsimp [inward]; linarith [hy.1]
  have hyu : (inward p θ ε).y < 133/200 := by dsimp [inward]; linarith [hy.2]
  have hyp : 0 < p.y := by linarith [hy.1]
  refine ⟨?_,?_,hy',?_⟩
  · exact ⟨by linarith,by rw [abs_of_pos hy']; linarith⟩
  · dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
    rw [max_eq_left (by linarith : 0 ≤ (inward p θ ε).a-1/2)]
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2)
      (show 1/2 ≤ (inward p θ ε).a-1/2 by linarith) 2
    nlinarith [sq_nonneg (max (|(inward p θ ε).y|-1/2) 0)]
  · let R := (p.a+1/2)*Real.sin θ+(p.y+1/2)*Real.cos θ
    have hfirst : 0 ≤ (p.a+1/2)*Real.sin θ :=
      mul_nonneg (by linarith) hs
    have hsecond : (167/200 : ℝ)*(3/4) ≤ (p.y+1/2)*Real.cos θ := by
      exact mul_le_mul (by linarith [hy.1]) (by linarith)
        (by norm_num) (by linarith [hy.1])
    have hR : 1/2 < R := by dsimp [R]; linarith
    have hid : (inward p θ ε).circle=p.circle-2*ε*R+ε^2 := by
      dsimp [SignedPoint.circle]
      rw [abs_of_pos hy',abs_of_pos hyp]
      dsimp [inward,R]
      linear_combination ε^2*(Real.sin_sq_add_cos_sq θ)
    have hdrop : 0 < ε*(2*R-ε) := mul_pos hε (by linarith)
    rw [hid]
    nlinarith

/-- An improvement of an interior split: the base endpoint fixes the total frame span and the
common endpoint frame, and the new A and B have strictly smaller corner circles than the original
ones, with exact hard projections and strict AB slack. -/
structure InteriorImprovement (G A B T : SignedPoint) (t u : ℝ) where
  base : PairEndpoint G A B T t u
  pointA : SignedPoint
  pointB : SignedPoint
  sorted_A : pointA.Sorted
  sorted_B : pointB.Sorted
  avoids_A : pointA.AvoidsCore
  avoids_B : pointB.AvoidsCore
  normal_A : 0 < pointA.y
  normal_B : pointB.y < 0
  circle_A : pointA.circle < A.circle
  circle_B : pointB.circle < B.circle
  GA_exact : quarterProjection G pointA (-base.angleA) 0=edgeWidth (-base.angleA)
  BT_exact : quarterProjection pointB T (-base.angleB) 2=edgeWidth (-base.angleB)
  AB_strict : 1 < pointA.y-pointB.y
  AB_zero : zeroFeasible pointA pointB 0 0
  AB_two : zeroFeasible pointA pointB 0 2

theorem improve_interior {G A B T : SignedPoint} {t u : ℝ}
    (O : PairEndpoint G A B T t u) (ht : 0 < t) (hu : 0 < u) :
    Nonempty (InteriorImprovement G A B T t u) := by
  have hslack := O.strict_if_interior ht hu
  let ε : ℝ := min (1/10) ((O.pointA.y-O.pointB.y-1)/4)
  have hε : 0 < ε := lt_min (by norm_num) (by linarith)
  have hεu : ε ≤ 1/10 := min_le_left _ _
  have hεs : ε ≤ (O.pointA.y-O.pointB.y-1)/4 := min_le_right _ _
  have hBprimary : 11/10 ≤ O.pointB.reflect.a := O.primary_B
  have hBtransverse : 67/200 < O.pointB.reflect.y ∧
      O.pointB.reflect.y < 133/200 := O.transverse_B
  obtain ⟨hAs,hAc,hAn,hAq⟩ := inward_properties O.angleA_mem O.primary_A
    O.transverse_A hε hεu
  obtain ⟨hBs,hBc,hBn,hBq⟩ := inward_properties O.angleB_mem hBprimary
    hBtransverse hε hεu
  let A' := inward O.pointA O.angleA ε
  let B' := (inward O.pointB.reflect O.angleB ε).reflect
  have hdrop : ε*(Real.cos O.angleA+Real.cos O.angleB) ≤ 2*ε := by
    have hh := mul_le_mul_of_nonneg_left
      (add_le_add (Real.cos_le_one O.angleA) (Real.cos_le_one O.angleB)) hε.le
    linarith
  have hAB : 1 < A'.y-B'.y := by
    dsimp [A',B',inward,SignedPoint.reflect]
    linarith
  refine ⟨{
    base := O
    pointA := A'
    pointB := B'
    sorted_A := hAs
    sorted_B := by simpa [B'] using hBs
    avoids_A := hAc
    avoids_B := by simpa [B'] using hBc
    normal_A := hAn
    normal_B := by show -(inward O.pointB.reflect O.angleB ε).y < 0; linarith
    circle_A := hAq.trans_eq O.circle_A
    circle_B := ?_
    GA_exact := ?_
    BT_exact := ?_
    AB_strict := hAB
    AB_zero := by simpa [zeroFeasible,zeroProjection] using hAB.le
    AB_two := by simpa [zeroFeasible,zeroProjection] using hAB.le
  }⟩
  · have hh : B'.circle < O.pointB.circle := by simpa [B'] using hBq
    exact hh.trans_eq O.circle_B
  · calc
      quarterProjection G A' (-O.angleA) 0 =
          quarterProjection G O.pointA (-O.angleA) 0 := by
        simp [quarterProjection,A',inward]
        ring
      _ = edgeWidth (-O.angleA) := O.GA_exact
  · calc
      quarterProjection B' T (-O.angleB) 2 =
          quarterProjection O.pointB T (-O.angleB) 2 := by
        simp [quarterProjection,B',inward,SignedPoint.reflect]
        ring
      _ = edgeWidth (-O.angleB) := O.BT_exact

end SquaresInCircles.Eight.HardSplitCap
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate HardSplitCap
namespace SignedCycle

def replaceMiddle (C : SignedCycle) (P R : SignedPoint) (β : ℝ) : SignedCycle where
  point := ![C.point H,C.point G,P,R,C.point T,C.point D,C.point E]
  theta := ![C.theta H,C.theta G,β,β,C.theta T,C.theta D,C.theta E]

theorem replaceMiddle_unchanged (C : SignedCycle) (P R : SignedPoint) (β : ℝ)
    (i : Vertex) (hi : i ≠ A) (hj : i ≠ B) :
    (replaceMiddle C P R β).point i=C.point i ∧
      (replaceMiddle C P R β).theta i=C.theta i := by
  fin_cases i <;> simp_all [replaceMiddle,H,G,A,B,T,D,E]

theorem replaceMiddle_spread {C : SignedCycle} {P R : SignedPoint} {β : ℝ}
    (h : C.Spread) (hβ : β=C.theta G ∨ β=C.theta T) :
    (replaceMiddle C P R β).Spread := by
  have hf (i : Vertex) : (replaceMiddle C P R β).theta i=
      if i=A ∨ i=B then β else C.theta i := by
    fin_cases i <;> simp [replaceMiddle,H,G,A,B,T,D,E]
  rcases hβ with hβ | hβ
  · intro i j
    rw [hf i,hf j,hβ]
    split_ifs <;> exact h _ _
  · intro i j
    rw [hf i,hf j,hβ]
    split_ifs <;> exact h _ _

theorem replaceMiddle_unaffected {C : SignedCycle} {P R : SignedPoint} {β : ℝ}
    {i : Vertex} (hi : i=H ∨ i=T ∨ i=D ∨ i=E) (j : Fin 4) :
    (replaceMiddle C P R β).Feasible i j ↔ C.Feasible i j := by
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

theorem replaceMiddle_GA (C : SignedCycle) (P R : SignedPoint) (β : ℝ) (j : Fin 4) :
    (replaceMiddle C P R β).Feasible G j ↔
      quarterFeasible (C.point G) P (β-C.theta G) j := by
  simp [Feasible,slack,edge,replaceMiddle,Candidate.word,next,delta,G,
    quarterFeasible,sub_nonneg]

theorem replaceMiddle_BT (C : SignedCycle) (P R : SignedPoint) (β : ℝ) (j : Fin 4) :
    (replaceMiddle C P R β).Feasible B j ↔
      quarterFeasible R (C.point T) (C.theta T-β) j := by
  simp [Feasible,slack,edge,replaceMiddle,Candidate.word,next,delta,B,T,
    quarterFeasible,sub_nonneg]

theorem replaceMiddle_AB (C : SignedCycle) (P R : SignedPoint) (β : ℝ) (j : Fin 4) :
    (replaceMiddle C P R β).Feasible A j ↔ zeroFeasible P R 0 j := by
  simp [Feasible,slack,edge,replaceMiddle,Candidate.word,next,delta,A,
    zeroFeasible,sub_nonneg]

def Witnesses.replaceMiddle {C : SignedCycle} (w : C.Witnesses)
    (P R : SignedPoint) (β : ℝ)
    (hGA : quarterFeasible (C.point G) P (β-C.theta G) 0)
    (hBT : quarterFeasible R (C.point T) (C.theta T-β) 2)
    (hAB0 : zeroFeasible P R 0 0) (hAB2 : zeroFeasible P R 0 2) :
    (SignedCycle.replaceMiddle C P R β).Witnesses where
  owner := ![w.owner H,0,w.owner A,2,w.owner T,w.owner D,w.owner E]
  feasible := by
    intro i
    fin_cases i
    · exact (replaceMiddle_unaffected (Or.inl rfl) _).2 (w.feasible H)
    · exact (replaceMiddle_GA C P R β 0).2 hGA
    · have hj : w.owner A=0 ∨ w.owner A=2 := by
        simpa [normalOwners,A] using w.allowed A
      rcases hj with hj | hj
      · exact (replaceMiddle_AB C P R β _).2 (by simpa [hj] using hAB0)
      · exact (replaceMiddle_AB C P R β _).2 (by simpa [hj] using hAB2)
    · exact (replaceMiddle_BT C P R β 2).2 hBT
    · exact (replaceMiddle_unaffected (Or.inr (Or.inl rfl)) _).2 (w.feasible T)
    · exact (replaceMiddle_unaffected (Or.inr (Or.inr (Or.inl rfl))) _).2 (w.feasible D)
    · exact (replaceMiddle_unaffected (Or.inr (Or.inr (Or.inr rfl))) _).2 (w.feasible E)
  allowed := by
    intro i
    fin_cases i
    · exact w.allowed H
    · norm_num [normalOwners,G]
    · exact w.allowed A
    · norm_num [normalOwners,B]
    · exact w.allowed T
    · exact w.allowed D
    · exact w.allowed E

def HardInput.replaceMiddle {q : ℝ} (I : HardInput q)
    (P R : SignedPoint) (β : ℝ)
    (hβ : β=I.cycle.theta G ∨ β=I.cycle.theta T)
    (hsP : P.Sorted) (hsR : R.Sorted)
    (hcP : P.AvoidsCore) (hcR : R.AvoidsCore)
    (hnP : 0 ≤ P.y) (hnR : R.y ≤ 0)
    (hqP : P.circle ≤ (I.cycle.point A).circle)
    (hqR : R.circle ≤ (I.cycle.point B).circle)
    (hGA : quarterFeasible (I.cycle.point G) P (β-I.cycle.theta G) 0)
    (hBT : quarterFeasible R (I.cycle.point T) (I.cycle.theta T-β) 2)
    (hAB0 : zeroFeasible P R 0 0) (hAB2 : zeroFeasible P R 0 2) : HardInput q where
  cycle := SignedCycle.replaceMiddle I.cycle P R β
  necessary := {
    sorted := by
      intro i
      fin_cases i
      · exact I.necessary.sorted H
      · exact I.necessary.sorted G
      · exact hsP
      · exact hsR
      · exact I.necessary.sorted T
      · exact I.necessary.sorted D
      · exact I.necessary.sorted E
    contained := by
      intro i
      fin_cases i
      · exact I.necessary.contained H
      · exact I.necessary.contained G
      · exact hqP.trans (I.necessary.contained A)
      · exact hqR.trans (I.necessary.contained B)
      · exact I.necessary.contained T
      · exact I.necessary.contained D
      · exact I.necessary.contained E
    core := by
      intro i
      fin_cases i
      · exact I.necessary.core H
      · exact I.necessary.core G
      · exact hcP
      · exact hcR
      · exact I.necessary.core T
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := replaceMiddle_spread I.necessary.spread hβ }
  anchors_normal := ⟨I.anchors_normal.H_nonneg,hnP,hnR,I.anchors_normal.D_nonpos⟩
  E_nonpos := I.E_nonpos
  witnesses := I.witnesses.replaceMiddle P R β hGA hBT hAB0 hAB2
  GA_hard := (replaceMiddle_GA I.cycle P R β 0).2 hGA
  BT_hard := (replaceMiddle_BT I.cycle P R β 2).2 hBT
  zero_signs := {
    HG_canceling := by intro h; exact I.zero_signs.HG_canceling h
    TD_canceling := by intro h; exact I.zero_signs.TD_canceling h }
  E_radial := I.E_radial

/-- At the three aligned zero edges either transverse owner has the same projection, which gives
`G.y < -1/10`, `1/10 < T.y` and the AB0 witness; the outer anchors need only containment. -/
theorem HardInput.aligned_pair_bounds {q : ℝ} (I : HardInput q) (hq : q ≤ qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta B=I.cycle.theta A)
    (hTD : I.cycle.theta T=I.cycle.theta D) :
    (I.cycle.point G).y < -(1/10 : ℝ) ∧
      (1/10 : ℝ) < (I.cycle.point T).y ∧
      zeroFeasible (I.cycle.point A) (I.cycle.point B) 0 0 := by
  have hHGw : zeroFeasible (I.cycle.point H) (I.cycle.point G)
      (I.cycle.theta G-I.cycle.theta H) (I.witnesses.owner H) := by
    simpa [Feasible,slack,edge,Candidate.word,next,delta,H,G,zeroFeasible,sub_nonneg]
      using I.witnesses.feasible H
  have hTDw : zeroFeasible (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta T) (I.witnesses.owner T) := by
    simpa [Feasible,slack,edge,Candidate.word,next,delta,T,D,zeroFeasible,sub_nonneg]
      using I.witnesses.feasible T
  have hABw : zeroFeasible (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta A) (I.witnesses.owner A) := by
    simpa [Feasible,slack,edge,Candidate.word,next,delta,A,B,zeroFeasible,sub_nonneg]
      using I.witnesses.feasible A
  rw [hHG,sub_self] at hHGw
  rw [hTD,sub_self] at hTDw
  rw [hAB,sub_self] at hABw
  have hHowner : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
    simpa [normalOwners,H] using I.witnesses.allowed H
  have hTowner : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
    simpa [normalOwners,T] using I.witnesses.allowed T
  have hAowner : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [normalOwners,A] using I.witnesses.allowed A
  have hHsep : 1 ≤ (I.cycle.point H).y-(I.cycle.point G).y := by
    rcases hHowner with hj | hj <;>
      simpa [hj,zeroFeasible,zeroProjection] using hHGw
  have hTsep : 1 ≤ (I.cycle.point T).y-(I.cycle.point D).y := by
    rcases hTowner with hj | hj <;>
      simpa [hj,zeroFeasible,zeroProjection] using hTDw
  have hHbound := (SignedPoint.coordinate_bounds (I.necessary.sorted H)
    (I.necessary.core H) (I.necessary.contained H) hq).2.2
  have hDbound := (SignedPoint.coordinate_bounds (I.necessary.sorted D)
    (I.necessary.core D) (I.necessary.contained D) hq).2.2
  refine ⟨?_,?_,?_⟩
  · linarith [le_abs_self (I.cycle.point H).y]
  · linarith [neg_le_abs (I.cycle.point D).y]
  · rcases hAowner with hj | hj <;>
      simpa [hj,zeroFeasible,zeroProjection] using hABw

theorem HardInput.aligned_pair_endpoint {q : ℝ} (I : HardInput q) (hq : q ≤ qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta B=I.cycle.theta A)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A ≤ I.cycle.theta G)
    (hright : I.cycle.theta T ≤ I.cycle.theta A) :
    Nonempty (HardSplitCap.PairEndpoint
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T)) := by
  obtain ⟨hyG,hyT,hABw⟩ := I.aligned_pair_bounds hq hHG hAB hTD
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-(I.cycle.theta G-I.cycle.theta A)) 0 := by
    simpa [Feasible,slack,edge,Candidate.word,next,delta,G,A,
      quarterFeasible,sub_nonneg,neg_sub] using I.GA_hard
  have hBT : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-(I.cycle.theta A-I.cycle.theta T)) 2 := by
    rw [neg_sub,← hAB]
    simpa [Feasible,slack,edge,Candidate.word,next,delta,B,T,
      quarterFeasible,sub_nonneg] using I.BT_hard
  have hspan : (I.cycle.theta G-I.cycle.theta A)+
      (I.cycle.theta A-I.cycle.theta T) ≤ 7/10 := by
    have hh := I.necessary.spread G T
    have ha := le_abs_self (I.cycle.theta G-I.cycle.theta T)
    dsimp [frameCap] at hh
    linarith
  exact actual_pair_endpoint ((I.necessary.contained A).trans hq)
    ((I.necessary.contained B).trans hq) I.anchors_normal.A_nonneg
    I.anchors_normal.B_nonpos hyG.le hyT.le (sub_nonneg.mpr hleft)
    (sub_nonneg.mpr hright) hspan hGA hBT hABw

theorem pair_endpoint_frames (C : SignedCycle)
    (O : HardSplitCap.PairEndpoint (C.point G) (C.point A) (C.point B) (C.point T)
      (C.theta G-C.theta A) (C.theta A-C.theta T)) :
    (C.theta G-O.angleA=C.theta G ∨ C.theta G-O.angleA=C.theta T) ∧
      (C.theta G-O.angleA)-C.theta G= -O.angleA ∧
      C.theta T-(C.theta G-O.angleA)= -O.angleB := by
  refine ⟨?_,by ring,?_⟩
  · rcases O.endpoint with h | h
    · left; linarith [h.1]
    · right; linarith [h.1]
  · linarith [O.span]

/-- The hard input with the new A and B at the common frame of G or of T, as the endpoint selects;
every other point and frame is that of the input. -/
def HardInput.fromPair {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.PairEndpoint
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T)) :
    HardInput q := by
  let hf := pair_endpoint_frames I.cycle O
  refine I.replaceMiddle O.pointA O.pointB (I.cycle.theta G-O.angleA) hf.1
    O.sorted_A O.sorted_B O.avoids_A O.avoids_B O.normal_A.le O.normal_B.le
    O.circle_A.le O.circle_B.le ?_ ?_ O.AB_zero O.AB_two
  · unfold quarterFeasible
    rw [hf.2.1]
    exact O.GA_exact.symm.le
  · unfold quarterFeasible
    rw [hf.2.2]
    exact O.BT_exact.symm.le

theorem HardInput.fromPair_unchanged {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.PairEndpoint
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T))
    (i : Vertex) (hi : i ≠ A) (hj : i ≠ B) :
    ((I.fromPair O).cycle.point i=I.cycle.point i) ∧
      ((I.fromPair O).cycle.theta i=I.cycle.theta i) :=
  replaceMiddle_unchanged I.cycle O.pointA O.pointB (I.cycle.theta G-O.angleA) i hi hj

theorem HardInput.fromPair_circles {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.PairEndpoint
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T))
    (i : Vertex) : ((I.fromPair O).cycle.point i).circle=(I.cycle.point i).circle := by
  fin_cases i
  · rfl
  · rfl
  · exact O.circle_A
  · exact O.circle_B
  · rfl
  · rfl
  · rfl

theorem HardInput.fromPair_endpoint {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.PairEndpoint
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T)) :
    (I.fromPair O).cycle.theta A=(I.fromPair O).cycle.theta G ∨
      (I.fromPair O).cycle.theta A=(I.fromPair O).cycle.theta T :=
  (pair_endpoint_frames I.cycle O).1

def HardInput.fromImprovement {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.InteriorImprovement
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T)) :
    HardInput q := by
  let hf := pair_endpoint_frames I.cycle O.base
  refine I.replaceMiddle O.pointA O.pointB (I.cycle.theta G-O.base.angleA) hf.1
    O.sorted_A O.sorted_B O.avoids_A O.avoids_B O.normal_A.le O.normal_B.le
    O.circle_A.le O.circle_B.le ?_ ?_ O.AB_zero O.AB_two
  · unfold quarterFeasible
    rw [hf.2.1]
    exact O.GA_exact.symm.le
  · unfold quarterFeasible
    rw [hf.2.2]
    exact O.BT_exact.symm.le

theorem HardInput.fromImprovement_unchanged {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.InteriorImprovement
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T))
    (i : Vertex) (hi : i ≠ A) (hj : i ≠ B) :
    ((I.fromImprovement O).cycle.point i=I.cycle.point i) ∧
      ((I.fromImprovement O).cycle.theta i=I.cycle.theta i) :=
  replaceMiddle_unchanged I.cycle O.pointA O.pointB (I.cycle.theta G-O.base.angleA) i hi hj

theorem HardInput.fromImprovement_nonincrease {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.InteriorImprovement
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T)) :
    AnchorNonincrease I.cycle (I.fromImprovement O).cycle := by
  intro i hi
  fin_cases i
  · exact le_rfl
  · exact le_rfl
  · exact O.circle_A.le
  · exact O.circle_B.le
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

theorem HardInput.fromImprovement_strict_A {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.InteriorImprovement
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T)) :
    ((I.fromImprovement O).cycle.point A).circle < (I.cycle.point A).circle := O.circle_A

theorem HardInput.fromImprovement_strict_B {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.InteriorImprovement
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T)) :
    ((I.fromImprovement O).cycle.point B).circle < (I.cycle.point B).circle := O.circle_B

/-- The endpoint split as a hard input at the same `q`: the common A/B frame at that of G or T,
every circle unchanged, and the five other points and frames kept. -/
theorem HardInput.exists_split_aligned {q : ℝ} (I : HardInput q) (hq : q ≤ qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta B=I.cycle.theta A)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A ≤ I.cycle.theta G)
    (hright : I.cycle.theta T ≤ I.cycle.theta A) :
    ∃ J : HardInput q,
      (J.cycle.theta A=J.cycle.theta G ∨ J.cycle.theta A=J.cycle.theta T) ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (∀ i, (J.cycle.point i).circle=(I.cycle.point i).circle) ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧
        J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨O⟩ := I.aligned_pair_endpoint hq hHG hAB hTD hleft hright
  exact ⟨I.fromPair O,I.fromPair_endpoint O,rfl,I.fromPair_circles O,
    I.fromPair_unchanged O⟩

/-- If the common frame lies strictly between those of T and G, the split loses strictly at both
middle anchors A and B. -/
theorem HardInput.exists_split_strict_loss {q : ℝ} (I : HardInput q) (hq : q ≤ qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta B=I.cycle.theta A)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A < I.cycle.theta G)
    (hright : I.cycle.theta T < I.cycle.theta A) :
    ∃ J : HardInput q,
      (J.cycle.theta A=J.cycle.theta G ∨ J.cycle.theta A=J.cycle.theta T) ∧
      J.cycle.theta A=J.cycle.theta B ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (J.cycle.point A).circle < (I.cycle.point A).circle ∧
      (J.cycle.point B).circle < (I.cycle.point B).circle ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧
        J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨O⟩ := I.aligned_pair_endpoint hq hHG hAB hTD hleft.le hright.le
  obtain ⟨P⟩ := HardSplitCap.improve_interior O (sub_pos.mpr hleft) (sub_pos.mpr hright)
  refine ⟨I.fromImprovement P,(pair_endpoint_frames I.cycle P.base).1,rfl,
    I.fromImprovement_nonincrease P,?_,I.fromImprovement_strict_A P,
    I.fromImprovement_strict_B P,I.fromImprovement_unchanged P⟩
  exact ⟨A,by simp [anchorVertices],I.fromImprovement_strict_A P⟩

end SignedCycle
end SquaresInCircles.Eight
end
end
end

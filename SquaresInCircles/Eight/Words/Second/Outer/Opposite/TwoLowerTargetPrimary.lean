module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoLowerPrimaryGeometry

/-!
# Eight squares: the original weak lower target-primary owner

The actual rotating target contact has curvature greater than 2.5.
Its aligned derivative is bounded below by the original circle-speed
product.  A single tangent parabola therefore controls the entire
physical contact and all weak original target-primary separators.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

theorem original_lower_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 1 a b A B (-1) 1 (Real.pi/2-x)) :
    (901/1000:ℝ)<value b B (Real.pi/2-x) := by
  have hcut : lowerPrimary a b x≤A := by
    have hw := lower_width hx
    norm_num [forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
    dsimp [lowerPrimary]
    linarith
  have hdom {t : ℝ} (htx : t∈Icc 0 x) : lowerPrimary a b t∈Icc 1 outerAxial :=
    lower_contact_domain hs hx (outer_bounds ht).2.1 hcut htx
  let f : ℝ→ℝ := fun t => Real.pi/2-t-P b+VPrimaryLabel.outer (lowerPrimary a b t)
  let df : ℝ→ℝ := fun t => -1+VPrimaryLabel.d1 (lowerPrimary a b t)*lowerSpeed a b t
  let ddf : ℝ→ℝ := fun t => VPrimaryLabel.d2 (lowerPrimary a b t)*(lowerSpeed a b t)^2+
    VPrimaryLabel.d1 (lowerPrimary a b t)*(1/2-lowerPrimary a b t)
  have hd {t : ℝ} (htx : t∈Icc 0 x) : HasDerivAt f (df t) t := by
    have hN := (VPrimaryLabel.outer_hasDerivAt (primary_domain
      (target_primary_domain (hdom htx)))).comp t (lowerPrimary_hasDerivAt a b t)
    exact (((hasDerivAt_id t).const_sub (Real.pi/2)).sub_const (P b)).add hN
  have hdd {t : ℝ} (htx : t∈Icc 0 x) : HasDerivAt df (ddf t) t := by
    have hN := (VPrimaryLabel.d1_hasDerivAt (primary_domain
      (target_primary_domain (hdom htx)))).comp t (lowerPrimary_hasDerivAt a b t)
    exact ((hN.mul (lowerSpeed_hasDerivAt a b t)).const_add (-1)).congr_deriv
      (by dsimp [ddf]; ring)
  have hcurv {t : ℝ} (htx : t∈Icc 0 x) : (5/2:ℝ)<ddf t := by
    have ht' : t∈Icc 0 (7/10) := ⟨htx.1,htx.2.trans hx.2⟩
    have he := lowerSpeed_eq_primarySpeed hs ht' (hdom htx)
    have hh := target_curvature_lower (hdom htx)
    dsimp [ddf]
    rw [he]
    nlinarith
  have hzero := hdom ⟨le_rfl,hx.1⟩
  rw [lowerPrimary_zero] at hzero
  have hbase : (227/250:ℝ)<f 0 := by
    have hj := primary_state (target_primary_domain hzero)
    have hh := aligned_left_original hs hj (le_refl (1+b))
    have he : VPrimaryLabel.outer (1+b)= -V (arc (1+b)) := VLabel.primary_actual hj
    dsimp [f]
    rw [lowerPrimary_zero,he]
    dsimp [value] at hh
    linarith
  have hfirst : -(9/50:ℝ)<df 0 := by
    have hh := targetProduct_lower hzero
    have hv := lowerSpeed_eq_primarySpeed (x := 0) hs (by norm_num)
      (by simpa only [lowerPrimary_zero] using hzero)
    rw [lowerPrimary_zero] at hv
    dsimp [df]
    rw [lowerPrimary_zero,hv]
    dsimp [targetProduct] at hh
    linarith
  have htan := curvature_tangent (κ := (5/2:ℝ))
    (show x∈Icc 0 x from ⟨hx.1,le_rfl⟩)
    (show (0:ℝ)∈Icc 0 x from ⟨le_rfl,hx.1⟩)
    (fun t htx => hd htx) (fun t htx => hdd htx) (fun t htx => (hcurv htx).le)
  have hlin := mul_nonneg (show 0≤df 0+9/50 by linarith) hx.1
  have hsq := sq_nonneg (x-9/125)
  have hf : (901/1000:ℝ)<f x := by nlinarith
  have htarget := V_primary_monotone
    (target_primary_domain (hdom ⟨hx.1,le_rfl⟩)) (primary_mem ht) hcut
  have he : VPrimaryLabel.outer A= -V B := VLabel.primary_actual ht
  rw [he] at htarget
  dsimp [f,value] at *
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeTwo

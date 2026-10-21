module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroPJReferences

/-!
# One decreasing curvature on the entire P/J critical interval

Uncompiled source draft.  Convexity gives one chord for P''' and a
lower tangent for P'.  Their exact differential identity then makes E
strictly decreasing throughout [.6,d].  The physical angular equation
itself excludes all smaller source coordinates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma third_chord {t : ℝ} (ht : t∈sourceInterval) :
    PLabel.d3 t<(91/250:ℝ)+(7/5)*(t-3/5) := by
  have hc : ConcaveOn ℝ sourceInterval
      (fun y => (91/250:ℝ)+(7/5)*(y-3/5)-PLabel.d3 y) := by
    apply concave_of_deriv2
      (d := fun y => (7/5:ℝ)-PLabel.d4 y) (dd := fun y => -PLabel.d5 y)
    · intro y hy
      convert ((((hasDerivAt_id y).sub_const (3/5)).const_mul (7/5)).const_add
        (91/250)).sub (PLabel.d3_hasDerivAt (outer_domain (source_domain hy))) using 1 <;> ring
    · intro y hy
      exact (PLabel.d4_hasDerivAt (outer_domain (source_domain hy))).const_sub (7/5)
    · intro y hy
      exact neg_nonpos.mpr (P_fifth_positive (source_domain hy)).le
  have hh := concave_gt_of_endpoints hc ht
    (show (0:ℝ)<91/250+(7/5)*(3/5-3/5)-PLabel.d3 (3/5) by
      linarith [six_reference.2.2.2.2])
    (show (0:ℝ)<91/250+(7/5)*(outerDiagonal-3/5)-PLabel.d3 outerDiagonal by
      linarith [diagonal_reference.2.2.2,fine_outer_endpoint_bounds.2])
  linarith

lemma second_lower {t : ℝ} (ht : t∈sourceInterval) :
    (253/1000:ℝ)<PLabel.d2 t := by
  have hh := P_second_monotone six_mem (source_domain ht) ht.1
  linarith [six_reference.2.2.1]

lemma first_tangent {t : ℝ} (ht : t∈sourceInterval) :
    (219/250:ℝ)+(253/1000)*(t-3/5)<p t := by
  have hm : MonotoneOn (fun y => p y-(253/1000)*y) sourceInterval :=
    monoOn_of_hasDeriv_nonneg
      (fun y hy => ((p_hasDerivAt (source_domain hy)).sub
        ((hasDerivAt_id y).const_mul (253/1000))).continuousAt.continuousWithinAt)
      (fun y hy => (p_hasDerivAt (source_domain (Ioo_subset_Icc_self hy))).sub
        ((hasDerivAt_id y).const_mul (253/1000)))
      (fun y hy => by linarith [second_lower (Ioo_subset_Icc_self hy)])
  have hh := hm ⟨le_rfl,six_mem.2⟩ ht ht.1
  linarith [six_reference.1]

lemma E_derivative_negative {t : ℝ} (ht : t∈sourceInterval) :
    ED t< -(29/100:ℝ) := by
  let x := t-3/5
  have hx : x∈Icc (0:ℝ) (3/10) := by
    dsimp [x]
    constructor <;> linarith [ht.1,ht.2,outer_endpoint_bounds.2.2.2]
  have hp := first_tangent ht
  have hpp := second_lower ht
  have hthird := third_chord ht
  have hp0 := p_positive (source_domain ht)
  have hlinear : (219/250:ℝ)+(253/1000)*x≤p t := by simpa [x] using hp.le
  have hlinear0 : 0≤(219/250:ℝ)+(253/1000)*x := by linarith [hx.1]
  have hcube := pow_le_pow_left₀ hlinear0 hlinear 3
  have hpbase : (219/250:ℝ)≤p t := by linarith [hx.1]
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤219/250) hpbase 2
  have hproduct := mul_le_mul hsq hpp.le (by norm_num : (0:ℝ)≤253/1000)
    (sq_nonneg (p t))
  have hweight : 0≤3*(1/10+x) := by linarith [hx.1]
  have hweighted := mul_le_mul_of_nonneg_left hproduct hweight
  have hx2 := sq_nonneg x
  have hx3 := pow_nonneg hx.1 3
  have he : t-1/2=1/10+x := by dsimp [x]; ring
  dsimp [ED]
  rw [he]
  have hthird' : PLabel.d3 t<(91/250:ℝ)+(7/5)*x := by simpa [x] using hthird
  nlinarith only [hthird',hcube,hweighted,hx.2,hx2,hx3]

lemma E_antitone : AntitoneOn E sourceInterval :=
  antiOn_of_hasDeriv_nonpos
    (fun t ht => (E_hasDerivAt (source_domain ht)).continuousAt.continuousWithinAt)
    (fun t ht => E_hasDerivAt (source_domain (Ioo_subset_Icc_self ht)))
    (fun t ht => by linarith [E_derivative_negative (Ioo_subset_Icc_self ht)])

theorem E_bounds {t : ℝ} (ht : t∈sourceInterval) :
    (43/1000:ℝ)<E t ∧ E t<187/1000 := by
  have hl := E_antitone ht ⟨six_mem.2,le_rfl⟩ ht.2
  have hu := E_antitone ⟨le_rfl,six_mem.2⟩ ht ht.1
  exact ⟨E_endpoints.1.trans_le hl,hu.trans_lt E_endpoints.2⟩

lemma velocity_circle {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (v B x+Real.cos x)^2+(b B x-1/2-Real.sin x)^2=Q0 := by
  have hU := UW_circle (outer_domain hB)
  have ht := Real.sin_sq_add_cos_sq x
  have he : v B x+Real.cos x=U B*Real.cos x+W B*Real.sin x := by
    dsimp [v,U,W]
    ring
  have hz : b B x-1/2-Real.sin x=W B*Real.cos x-U B*Real.sin x := by
    dsimp [b,U,W]
    ring
  rw [he,hz]
  linear_combination hU+((U B)^2+(W B)^2)*ht

lemma small_source_velocity {B x : ℝ} (hd : Domain B x) (hb : b B x≤3/5) :
    v B x<(1141/1000:ℝ) := by
  have hv := v_positive hd.1 hd.2.1
  have ht := positive_trig hd.2.1
  have hn := velocity_circle hd.1 (x := x)
  have htr := Real.sin_sq_add_cos_sq x
  have hproj := mul_le_mul_of_nonneg_right
    (show b B x-1/2≤(1/10:ℝ) by linarith) ht.2.2.1
  have hcos := mul_lt_mul_of_pos_left ht.1 hv
  by_contra! hlarge
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1141/1000) hlarge 2
  norm_num [Q0] at hn
  nlinarith [sq_nonneg (b B x-1/2),ht.2.2.2.1]

theorem stationary_source {B x : ℝ} (hd : Domain B x)
    (hstat : angleFirst PLabel B x=0) : (3/5:ℝ)<b B x := by
  by_contra! hsmall
  have hp := P_first_monotone hd.2.2 six_mem hsmall
  have hu : p (b B x)<876299/1000000 := hp.trans_lt six_reference.2.1
  have hv := small_source_velocity hd hsmall
  have hprod := mul_lt_mul hu hv (v_positive hd.1 hd.2.1)
    (by norm_num : (0:ℝ)≤876299/1000000)
  dsimp [angleFirst] at hstat
  change PLabel.d1 (b B x)*v B x<(876299/1000000)*(1141/1000) at hprod
  norm_num at hprod
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ

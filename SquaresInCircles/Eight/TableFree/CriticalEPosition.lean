module

public import SquaresInCircles.Eight.TableFree.CriticalESubstitution
public import SquaresInCircles.Eight.TableFree.StationaryPositionBounds

/-!
# The sharper affine strip for the actual critical position minimum

Uncompiled source. The comparison signs are obtained from the explicit
whole-interval polynomial enclosures of the original gradient. Strict
position convexity then locates the actual minimizingPosition between
the two affine curves. No root search or localization assumption enters
the theorem, and the tilt varies over the entire critical interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalEPosition
open Polynomial CriticalEPolynomials CriticalERadicals CriticalESubstitution
open WholeIntervalPolynomial ExactFamily.FiveCornerGeometry

theorem angle_mem {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) : t∈tiltInterval := by
  obtain ⟨hh,he⟩ := StationaryPrimitives.terminal_tangent ht
  rw [← he]
  exact StationaryPrimitives.arctan_mem_tiltInterval hh

theorem comparison_signs {q t : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25)) :
    positionHalf q (Real.cos t) (Real.sin t) (ev t uMinus)<0 ∧
    0<positionHalf q (Real.cos t) (Real.sin t) (ev t uPlus) := by
  have hl : ev t uMinus∈Icc (ev t (a .lower)) (ev t (b .lower)) := ⟨le_rfl,le_rfl⟩
  have hu : ev t uPlus∈Icc (ev t (a .upper)) (ev t (b .upper)) := ⟨le_rfl,le_rfl⟩
  have hrl := actual_radicals .lower hq ht hl
  have hru := actual_radicals .upper hq ht hu
  have hqlt : q<4 := by norm_num [qUpper] at hq; linarith [hq.2]
  have hdl := hrl.smoothDomain ht (by linarith [(endpoints ht .lower).1]) hqlt
  have hdu := hru.smoothDomain ht (by linarith [(endpoints ht .upper).1]) hqlt
  have hJl := (position_bounds ht hl hrl).2
  have hJu := (position_bounds ht hu hru).1
  have hpL := (interval_bounds (by norm_num [length]) position_identities.1 (local_parameter ht)).2
  have hpU := positive_on_interval (by norm_num [length]) position_identities.2
    position_reserves.2 (local_parameter ht)
  have hresL : (upperOn 64 0 length positionUpper:ℝ)<-1/50 := by
    exact_mod_cast position_reserves.1
  have hneg : clearedPosition q t (ev t uMinus)<0 := by
    change ev t positionUpper≤(upperOn 64 0 length positionUpper:ℝ) at hpL
    change clearedPosition q t (ev t uMinus)≤ev t positionUpper at hJl
    linarith
  have hpos : 0<clearedPosition q t (ev t uPlus) := by
    change (1/25:ℝ)<ev t positionLower at hpU
    change ev t positionLower≤clearedPosition q t (ev t uPlus) at hJu
    linarith
  have hdenL := mul_pos (mul_pos (mul_pos hdl.r_pos hdl.U_pos) hdl.Y_pos) hdl.w_pos
  have hdenU := mul_pos (mul_pos (mul_pos hdu.r_pos hdu.U_pos) hdu.Y_pos) hdu.w_pos
  rw [clearedPosition_identity hdl] at hneg
  rw [clearedPosition_identity hdu] at hpos
  constructor <;> nlinarith

theorem minimizingPosition_strip {q t : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25)) :
    499/500-(127/200)*t<minimizingPosition q t ∧
    minimizingPosition q t<501/500-(16/25)*t := by
  have hql : (79/40:ℝ)^2≤q := by norm_num [qLower] at hq; nlinarith [hq.1]
  have hqu : q≤9789/2500 := by norm_num [qUpper] at hq; linarith [hq.2]
  obtain ⟨hc,hs,_⟩ := tiltInterval_bounds (angle_mem ht)
  have hm := StationaryPrimitives.position_gradient_strictMono hql hqu hc hs.le (trig_unit t)
  have hu := windowMinimizer_mem q (Real.cos t) (Real.sin t)
  change minimizingPosition q t∈positionWindow at hu
  have hz := minimizingPosition_root hql hqu (angle_mem ht)
  change 2*positionHalf q (Real.cos t) (Real.sin t) (minimizingPosition q t)=0 at hz
  have hL : ev t uMinus∈positionWindow := by
    simp only [ev_minus,positionWindow]
    constructor <;> linarith [ht.1,ht.2]
  have hU : ev t uPlus∈positionWindow := by
    simp only [ev_plus,positionWindow]
    constructor <;> linarith [ht.1,ht.2]
  have hsign := comparison_signs hq ht
  have hl : ev t uMinus<minimizingPosition q t := by
    by_contra! hbad
    have he := hm.monotoneOn hu hL hbad
    linarith [hsign.1]
  have hh : minimizingPosition q t<ev t uPlus := by
    by_contra! hbad
    have he := hm.monotoneOn hU hu hbad
    linarith [hsign.2]
  simpa only [ev_minus,ev_plus] using And.intro hl hh

theorem minimizing_radicals {q t : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25)) :
    RadicalBounds .mixed q t (minimizingPosition q t) := by
  apply actual_radicals .mixed hq ht
  have hs := minimizingPosition_strip hq ht
  simpa only [a,b,ev_minus,ev_plus] using And.intro hs.1.le hs.2.le

end SquaresInCircles.Eight.TableFree.CriticalEPosition

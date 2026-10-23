module

public import SquaresInCircles.Eight.TableFree.SmallPositiveZeroEndpoint

/-!
# A uniform positive zero-tangent charge beyond the original frame span

Uncompiled source draft.  Crossed algebraic comparisons can evaluate a
zero-tangent endpoint out to 1.1 even though the original real frames
have spread at most .7.  One Taylor polynomial, expanded at .7, has a
positive quadratic reserve over the complete interval [.195,1.1].
These are scalar comparisons, not assertions of a new wider source.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CrossedZeroReserve
open EndpointRotationPenalty

theorem fixed_coefficient_strict {h : ℝ} (hh : h∈Icc (39/200 : ℝ) (11/10)) :
    7/1000<charge*h-(183/200)*Real.sin h-(1-Real.cos h)/2 := by
  let x := h-7/10
  let K := 493657/4800000+(121469/720000)*x-(263/24000)*x^2-
    (253/24000)*x^3-x^4/1440
  have hx : x∈Icc (-(101/200 : ℝ)) (2/5) := by
    dsimp [x]
    constructor <;> linarith [hh.1,hh.2]
  have habs : |x|≤101/200 := abs_le.mpr ⟨hx.1,by linarith [hx.2]⟩
  have hp (n : ℕ) : |x^n|≤(101/200 : ℝ)^n := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) habs n
  have h2 := (abs_le.mp (hp 2)).2
  have h3 := (abs_le.mp (hp 3)).2
  have h4 := (abs_le.mp (hp 4)).2
  have hK : 1/100≤K := by dsimp [K]; nlinarith [hx.1]
  have hquad := mul_le_mul_of_nonneg_right hK (sq_nonneg x)
  have hlinear : -(1/500)*|x|≤ -(3969253/2352000000)*x := by
    have hxabs := le_abs_self x
    have ha := abs_nonneg x
    nlinarith
  have hid : charge*h-(183/200)*(h-h^3/6+h^5/120)-
      (h^2/2-h^4/24+h^6/720)/2-7/1000=
      730999/3150000000-(3969253/2352000000)*x+K*x^2 := by
    dsimp [charge,x,K]
    ring
  have habssq : |x|^2=x^2 := sq_abs x
  have hpoly : 0<charge*h-(183/200)*(h-h^3/6+h^5/120)-
      (h^2/2-h^4/24+h^6/720)/2-7/1000 := by
    rw [hid]
    nlinarith [sq_nonneg (|x|-1/10)]
  have hh0 : 0≤h := by linarith [hh.1]
  have hs := sin_upper_five hh0
  have hc := cos_lower_six hh0
  linarith

theorem sin_nonneg {h : ℝ} (hh : h∈Icc (0:ℝ) (11/10)) : 0≤Real.sin h := by
  exact Real.sin_nonneg_of_nonneg_of_le_pi hh.1 (by linarith [hh.2,Real.pi_gt_three])

theorem strict {k h : ℝ} (hk : k≤183/200)
    (hh : h∈Icc (39/200 : ℝ) (11/10)) :
    7/1000<charge*h-k*Real.sin h-(1-Real.cos h)/2 := by
  have hs := sin_nonneg (show h∈Icc (0:ℝ) (11/10) from ⟨by linarith [hh.1],hh.2⟩)
  have hm := mul_le_mul_of_nonneg_right hk hs
  linarith [fixed_coefficient_strict hh]

theorem nonneg {k h : ℝ} (hk : k≤183/200)
    (hh : h∈Icc (0:ℝ) (11/10)) :
    0≤charge*h-k*Real.sin h-(1-Real.cos h)/2 := by
  by_cases hsmall : h≤39/200
  · have hs := Real.sin_le hh.1
    have hc := Real.one_sub_sq_div_two_le_cos h
    have hsq := mul_le_mul_of_nonneg_right hsmall hh.1
    have hmul := mul_le_mul_of_nonneg_right hk (sin_nonneg hh)
    dsimp [charge]
    nlinarith
  · exact (show (0:ℝ)≤7/1000 by norm_num).trans
      (strict hk ⟨(lt_of_not_ge hsmall).le,hh.2⟩).le

end SquaresInCircles.Eight.TableFree.CrossedZeroReserve

module

public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameStationaryReferences
public import SquaresInCircles.Eight.Owners.SplitConcavityTools

/-!
# Eight squares: the two concave stationary heights

The derivative of G is
positive on the full source arc. Its two written sign comparisons give
the source cutoffs; endpoint chords and the one written tangent then
bound the complete possible height ranges.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.Stationary
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open SecondWord (U W outer_domain outer_zero_mem UW_circle U_positive)

def Curved (r : Row) : Prop := r=1 ∨ r=3
def slopeFloor (r : Row) : ℝ := if r=1 then 23/25 else 17/20

lemma curved_coupled {r : Row} (hr : Curved r) : Coupled r := by
  unfold Coupled
  rcases hr with rfl | rfl <;> decide

lemma slope_lower (r : Row) (hr : Curved r) {b : ℝ} (hb : b∈sourceDomain) :
    slopeFloor r<l r b := by
  have hstart : (293/1000:ℝ)∈Icc 0 outerDiagonal :=
    SecondWord.Asymmetric.rational_outer_mem (by norm_num)
  have hm := l_monotone r (curved_coupled hr) hstart (source_outer hb) hb.1
  rcases hr with rfl | rfl <;> norm_num [slopeFloor] <;>
    linarith [References.initial_slopes.1,References.initial_slopes.2]

lemma G_derivative_positive (r : Row) (hr : Curved r) {b : ℝ}
    (hb : b∈sourceDomain) : 0<GD r b := by
  have hbi := source_outer hb
  have hu := U_positive (outer_domain hbi)
  have hU : (1399/1000:ℝ)<U b := (SecondWord.UW_bounds hbi).1
  have hw : 0≤W b ∧ W b<(7/5:ℝ) := by
    dsimp [W]
    constructor <;> linarith [hbi.1,hbi.2,outer_endpoint_bounds.2.2.2]
  have hl := l_positive r hbi
  have hfloor := slope_lower r hr hb
  have hf0 : 0<slopeFloor r := by
    rcases hr with rfl | rfl <;> norm_num [slopeFloor]
  have hu5 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hU.le 5
  have hl4 := pow_le_pow_left₀ hf0.le hfloor.le 4
  have hden := mul_le_mul hu5 hl4 (pow_nonneg hf0.le 4) (pow_nonneg hu.le 5)
  have hden0 : 0<(U b)^5*(l r b)^4 := mul_pos (pow_pos hu 5) (pow_pos hl 4)
  have hp : p r≤0 := (coupled_signs r (curved_coupled hr)).1
  have hpu := mul_nonpos_of_nonpos_of_nonneg hp hu.le
  have hq := (coefficient_signs r).1
  have hqw := mul_le_mul_of_nonneg_left hw.2.le hq.le
  have hn : q r*W b+p r*U b≤q r*(7/5) := by linarith
  have hcoef : 0≤3*(-p r)*Q0 :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by norm_num [Q0])
  have hnum := mul_le_mul_of_nonneg_left hn hcoef
  have hreserve : 3*(-p r)*Q0*q r*(7/5)<
      (1399/1000:ℝ)^5*(slopeFloor r)^4 := by
    rcases hr with rfl | rfl <;> norm_num [p,q,Q0,slopeFloor]
  have hquot : 3*(-p r)*Q0*(q r*W b+p r*U b)/((U b)^5*(l r b)^4)<1 := by
    apply (div_lt_one hden0).2
    nlinarith
  dsimp only [GD]
  linarith

lemma G_monotone (r : Row) (hr : Curved r) : MonotoneOn (G r) sourceDomain :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (G_hasDerivAt r (source_outer hb)).continuousAt.continuousWithinAt)
    (fun b hb => G_hasDerivAt r (source_outer (Ioo_subset_Icc_self hb)))
    (fun b hb => (G_derivative_positive r hr (Ioo_subset_Icc_self hb)).le)

lemma height_concave (r : Row) (hr : Curved r) : ConcaveOn ℝ sourceDomain (height r) :=
  concave_of_deriv2
    (fun b hb => height_hasDerivAt r (source_outer hb))
    (fun b hb => (G_hasDerivAt r (source_outer hb)).neg)
    (fun b hb => neg_nonpos.mpr (G_derivative_positive r hr hb).le)

lemma row_one_source {b : ℝ} (hb : b∈sourceDomain) (hG : G 1 b≤0) : b<(3/5:ℝ) := by
  by_contra! hn
  have hpoint : (3/5:ℝ)∈sourceDomain :=
    ⟨by norm_num,(SecondWord.Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hm := G_monotone 1 (Or.inl rfl) hpoint hb hn
  linarith [References.row_one_end.1]

lemma row_three_source {b : ℝ} (hb : b∈sourceDomain) (hG : G 3 b≤0) : b<(39/50:ℝ) := by
  by_contra! hn
  have hpoint : (39/50:ℝ)∈sourceDomain :=
    ⟨by norm_num,(SecondWord.Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hm := G_monotone 3 (Or.inr rfl) hpoint hb hn
  linarith [References.row_three_end.1]

lemma row_one_height {b : ℝ} (hb : b∈Icc (293/1000:ℝ) (3/5)) :
    (923/500:ℝ)<height 1 b ∧ height 1 b<1891/1000 ∧ l 1 b<943/1000 := by
  have hlast : (3/5:ℝ)∈sourceDomain :=
    ⟨by norm_num,(SecondWord.Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hfirst : (293/1000:ℝ)∈sourceDomain := ⟨le_rfl,by linarith [hlast.2]⟩
  have hbd : b∈sourceDomain := ⟨hb.1,hb.2.trans hlast.2⟩
  have hc := height_concave 1 (Or.inl rfl)
  have hmin := hc.min_le_of_mem_Icc hfirst hlast hb
  have hlo : (923/500:ℝ)<height 1 b :=
    (lt_min References.row_one_initial References.row_one_end.2.2.1).trans_le hmin
  have htan := SplitConcavityTools.tangent_upper hc hlast hbd
    (height_hasDerivAt 1 (source_outer hlast))
  have hG := abs_lt.mp References.row_one_end.2.1
  have hpay := mul_le_mul_of_nonneg_left
    (show G 1 (3/5)≤(1/250:ℝ) by linarith [hG.2])
    (show 0≤(3/5:ℝ)-b by linarith [hb.2])
  have hl := l_monotone 1 (curved_coupled (Or.inl rfl)) (source_outer hbd)
    (source_outer hlast) hb.2
  exact ⟨hlo,by linarith [hb.1,References.row_one_end.2.2.2.1],
    hl.trans_lt References.row_one_end.2.2.2.2⟩

def chordHeight (b : ℝ) : ℝ :=
  4369/2500+(2367/25000)/(487/1000)*(b-293/1000)

lemma row_three_chord {b : ℝ} (hb : b∈Icc (293/1000:ℝ) (39/50)) :
    chordHeight b<height 3 b := by
  have hlast : (39/50:ℝ)∈sourceDomain :=
    ⟨by norm_num,(SecondWord.Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hfirst : (293/1000:ℝ)∈sourceDomain := ⟨le_rfl,by linarith [hlast.2]⟩
  have hh := SplitConcavityTools.chord (height_concave 3 (Or.inr rfl))
    hfirst hlast (by norm_num) hb
  have hleft := mul_le_mul_of_nonneg_left References.row_three_initial.le
    (sub_nonneg.mpr hb.2)
  have hright := mul_le_mul_of_nonneg_left References.row_three_end.2.1.le
    (sub_nonneg.mpr hb.1)
  by_cases hfirsteq : b=293/1000
  · subst b
    simpa [chordHeight] using References.row_three_initial
  · have hstrict := mul_lt_mul_of_pos_left References.row_three_end.2.1
      (show 0<b-293/1000 by exact sub_pos.mpr (lt_of_le_of_ne hb.1 (Ne.symm hfirsteq)))
    dsimp [chordHeight]
    nlinarith

lemma row_three_height {b : ℝ} (hb : b∈Icc (293/1000:ℝ) (39/50)) :
    (4369/2500:ℝ)<height 3 b ∧ height 3 b<92117/50000 ∧ l 3 b<233/250 := by
  have hlast : (39/50:ℝ)∈sourceDomain :=
    ⟨by norm_num,(SecondWord.Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hbd : b∈sourceDomain := ⟨hb.1,hb.2.trans hlast.2⟩
  have href : (77/100:ℝ)∈sourceDomain := ⟨by norm_num,by linarith [hlast.2]⟩
  have htan := SplitConcavityTools.tangent_upper (height_concave 3 (Or.inr rfl))
    href hbd (height_hasDerivAt 3 (source_outer href))
  have habs : |b-77/100|≤(477/1000:ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hb.1,hb.2]
  have hpay : |G 3 (77/100)*(b-77/100)|≤(1/125000)*(477/1000:ℝ) := by
    rw [abs_mul]
    exact mul_le_mul References.row_three_tangent.2.le habs (abs_nonneg _)
      (by norm_num)
  have hchord := row_three_chord hb
  have hl := l_monotone 3 (curved_coupled (Or.inr rfl)) (source_outer hbd)
    (source_outer hlast) hb.2
  refine ⟨?_,?_,hl.trans_lt References.row_three_end.2.2⟩
  · dsimp only [chordHeight] at hchord
    linarith [hb.1]
  · have hp := (abs_le.mp hpay).1
    linarith [References.row_three_tangent.1]

end SquaresInCircles.Eight.ShortOuterZero.Same.Stationary

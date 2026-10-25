module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerFirstReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeUpperDiagonalData

/-!
# Eight squares: uniform Hessian and terminal curvature for the first lower minimum

The mixed derivative estimate is one exact polynomial on the whole
shifted-circle interval.  The terminal curvature is the convex cubic
in its physical speed quotient, propagated by its negative derivative.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerFirst
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open LowerContact LowerGeometry LowerInverse

lemma early_outer_curvature {b B : ℝ} (hb : b∈Icc 0 (1/10)) (hB : B∈Icc 0 (2/5)) :
    (7/25:ℝ)<outerSecond false b B := by
  have hbf : b∈Icc 0 (83/200) := ⟨hb.1,by linarith [hb.2]⟩
  have hm : AntitoneOn (outerSecond false b) (Icc 0 (2/5)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro y hy
      exact (outerSecond_hasDerivAt false (full_domain ⟨hy.1,by linarith [hy.2]⟩)
        (short_shift hbf)).continuousAt.continuousWithinAt
    · intro y hy
      exact outerSecond_hasDerivAt false (full_domain ⟨hy.1.le,by linarith [hy.2]⟩)
        (short_shift hbf)
    · intro y hy
      exact (early_third_negative hb (Ioo_subset_Icc_self hy)).le
  exact (four_curvature hb).trans_le (hm hB (by norm_num) hB.2)

lemma free_curvature_positive {b B : ℝ} (hb : b∈Icc 0 (83/200))
    (hB : B∈Icc 0 outerDiagonal) : 0<freeSecond false b B := by
  have hT := T_second_early (show b∈Icc 0 (3/5) from ⟨hb.1,by linarith [hb.2]⟩)
  have hv := (OppositeTwo.PrimaryInverse.data hB (short_shift hb)).2.2.1
  have hz : 0<b+1/2 := by linarith [hb.1]
  have hp := div_pos hz (pow_pos hv 3)
  simp only [freeSecond,LowerContact.inner,Bool.false_eq_true,↓reduceIte]
  linarith

lemma early_free_curvature {b B : ℝ} (hb : b∈Icc 0 (1/10)) (hB : B∈Icc 0 (2/5)) :
    (3/2:ℝ)<freeSecond false b B := by
  have hb' : b∈Icc 0 (83/200) := ⟨hb.1,by linarith [hb.2]⟩
  have hB' := full_domain ⟨hB.1,by linarith [hB.2]⟩
  have hh := OppositeTwo.PrimaryInverse.data hB' (short_shift hb')
  have hv : speed (b+1/2) B<(11/10:ℝ) := by
    have hq := (early_data hB).2.2.2.2.2.2.1
    nlinarith [hh.2.2.1,hh.2.2.2,hb.1,hb.2]
  have hcube := pow_le_pow_left₀ hh.2.2.1.le hv.le 3
  have hquot : (1/3:ℝ)<(b+1/2)/(speed (b+1/2) B)^3 := by
    apply (lt_div_iff₀ (pow_pos hh.2.2.1 3)).2
    nlinarith [hb.1]
  have hT := T_second_monotone (short_domain hb') UpperTarget.tenth_mem hb.2
  have he := UpperDiagonal.tenth_second
  simp only [freeSecond,LowerContact.inner,Bool.false_eq_true,↓reduceIte]
  linarith

lemma mixed_negative {b B : ℝ} (hb : b∈Icc 0 (83/200))
    (hB : B∈Icc 0 outerDiagonal) : mixed b B<0 := by
  have hr : 0<ratio B := by linarith [(outer_ratio_bounds hB).1]
  have hv := (OppositeTwo.PrimaryInverse.data hB (short_shift hb)).2.2.1
  dsimp [mixed]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hr) (pow_pos hv 3)

lemma mixed_polynomial {u : ℝ} (hu : u∈Icc (881/500:ℝ) (383/200)) :
    0<(1/4:ℝ)*u^2*(q u-9/25)^3-(Q0-u^2) := by
  let s : ℝ := u-9/5
  have hs : |s|≤(23/200:ℝ) := by
    rw [abs_le]
    dsimp [s]
    constructor <;> linarith [hu.1,hu.2]
  have h3 := pow_le_pow_left₀ (abs_nonneg s) hs 3
  have h4 := pow_le_pow_left₀ (abs_nonneg s) hs 4
  have h5 := pow_le_pow_left₀ (abs_nonneg s) hs 5
  rw [←abs_pow] at h3 h4 h5
  have hs' := abs_le.mp hs
  have h3' := abs_le.mp h3
  have h4' := abs_le.mp h4
  have h5' := abs_le.mp h5
  have he : (1/4:ℝ)*u^2*(q u-9/25)^3-(Q0-u^2)=
      48792979389/1562500000000-(8226392679/156250000000)*s+
      (348466455869/62500000000)*s^2+(30884037/12500000)*s^3-
        (10833/2500)*s^4-2*s^5 := by
    dsimp [s,q,NegativeTwo.Inverse.q,Q0]
    ring
  rw [he]
  nlinarith [sq_nonneg s]

lemma early_mixed {b B : ℝ} (hb : b∈Icc 0 (1/10)) (hB : B∈Icc 0 (2/5)) :
    |mixed b B|<(1/2:ℝ) := by
  have hb' : b∈Icc 0 (83/200) := ⟨hb.1,by linarith [hb.2]⟩
  have hB' := full_domain ⟨hB.1,by linarith [hB.2]⟩
  have hd := OppositeTwo.PrimaryInverse.data hB' (short_shift hb')
  have hu := U_positive (outer_domain hB')
  have hc := UW_circle (outer_domain hB')
  have hpol := mixed_polynomial ⟨(early_U hB).1.le,(early_U hB).2.le⟩
  have hq : 0≤q (U B)-9/25 := by linarith [(early_data hB).2.2.2.2.2.1]
  have hvs : q (U B)-9/25≤(speed (b+1/2) B)^2 := by
    nlinarith [hb.1,hb.2,hd.2.2.2]
  have hpow := pow_le_pow_left₀ hq hvs 3
  have hscaled := mul_le_mul_of_nonneg_left hpow (sq_nonneg (U B))
  have hn : 4*(W B)^2<(U B)^2*(speed (b+1/2) B)^6 := by
    nlinarith
  have he : (mixed b B)^2*((U B)^2*(speed (b+1/2) B)^6)=(W B)^2 := by
    have hr : mixed b B=-(W B/U B)/(speed (b+1/2) B)^3 := rfl
    have hU : U B≠0 := hu.ne'
    have hS : speed (b+1/2) B≠0 := hd.2.2.1.ne'
    rw [hr]
    generalize speed (b+1/2) B = S at hS ⊢
    field_simp
  have hden : 0<(U B)^2*(speed (b+1/2) B)^6 := mul_pos (pow_pos hu 2) (pow_pos hd.2.2.1 6)
  have hs : (mixed b B)^2<(1/4:ℝ) := by
    apply (mul_lt_mul_iff_left₀ hden).mp
    rw [he]
    linarith
  rw [abs_lt]
  constructor <;> nlinarith

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerFirst

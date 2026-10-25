module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerFirstReference
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerFirstTerminal
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerSourceShape
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeUpperDiagonalData

/-!
# Eight squares: the complete first lower-secondary owner

Early and middle coordinates move directly to the proved rectangle.
On the terminal physical segment, concavity reduces to its initial
coordinate or the actual aligned contact.  All states and weak axes
remain those of the original edge.
-/

section
/-!
## Uniform Hessian and terminal curvature for the first lower minimum

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
end
end
end

section
/-!
## The full convex rectangle at the first lower-secondary contact

Two tangent parabolas and the uniform mixed derivative bound give a
two-coordinate lower bound.  Both tangents use the same named interior
reference and every segment stays in the original rectangle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerFirst
open CommonQuarter CorePairGeometry Arithmetic
open LowerContact LowerGeometry LowerInverse

lemma first_outer_lipschitz {b u v : ℝ} (hb : b∈Icc 0 (1/10))
    (hu : u∈Icc 0 (2/5)) (hv : v∈Icc 0 (2/5)) :
    |freeFirst false b u-freeFirst false b v|≤(1/2:ℝ)*|u-v| := by
  have hb' : b∈Icc 0 (83/200) := ⟨hb.1,by linarith [hb.2]⟩
  have hd {y : ℝ} (hy : y∈Icc 0 (2/5)) :=
    freeFirst_outer_hasDerivAt false (full_domain ⟨hy.1,by linarith [hy.2]⟩)
      (short_shift hb')
  have hp {y : ℝ} (hy : y∈Icc 0 (2/5)) :
      HasDerivAt (fun t => freeFirst false b t+(1/2)*t) (mixed b y+1/2) y :=
    ((hd hy).fun_add ((hasDerivAt_id' y).const_mul (1/2))).congr_deriv (by ring)
  have hm {y : ℝ} (hy : y∈Icc 0 (2/5)) :
      HasDerivAt (fun t => freeFirst false b t-(1/2)*t) (mixed b y-1/2) y :=
    ((hd hy).fun_sub ((hasDerivAt_id' y).const_mul (1/2))).congr_deriv (by ring)
  have hplus : MonotoneOn (fun t => freeFirst false b t+(1/2)*t) (Icc 0 (2/5)) :=
    monoOn_of_hasDeriv_nonneg (fun y hy => (hp hy).continuousAt.continuousWithinAt)
      (fun y hy => hp (Ioo_subset_Icc_self hy))
      (fun y hy => by have hh := (abs_lt.mp (early_mixed hb (Ioo_subset_Icc_self hy))).1; linarith)
  have hminus : AntitoneOn (fun t => freeFirst false b t-(1/2)*t) (Icc 0 (2/5)) :=
    antiOn_of_hasDeriv_nonpos (fun y hy => (hm hy).continuousAt.continuousWithinAt)
      (fun y hy => hm (Ioo_subset_Icc_self hy))
      (fun y hy => by have hh := (abs_lt.mp (early_mixed hb (Ioo_subset_Icc_self hy))).2; linarith)
  rcases le_total u v with huv | hvu
  · have hpv := hplus hu hv huv
    have hmv := hminus hu hv huv
    simp only at hpv hmv
    rw [abs_of_nonpos (sub_nonpos.mpr huv),abs_le]
    constructor <;> linarith
  · have hpv := hplus hv hu hvu
    have hmv := hminus hv hu hvu
    simp only at hpv hmv
    rw [abs_of_nonneg (sub_nonneg.mpr hvu),abs_le]
    constructor <;> linarith

theorem rectangle_lower {b B : ℝ} (hb : b∈Icc 0 (1/10)) (hB : B∈Icc 0 (2/5)) :
    (89777/100000:ℝ)<LowerContact.cost false b B := by
  have hB' := full_domain ⟨hB.1,by linarith [hB.2]⟩
  have hb₀ : referenceFree∈Icc 0 (83/200) :=
    ⟨reference_free_mem.1,by linarith [reference_free_mem.2]⟩
  have hf := curvature_tangent (f := fun t => LowerContact.cost false t B)
    (d := fun t => freeFirst false t B) (dd := fun t => freeSecond false t B)
    (κ := (3/2:ℝ)) hb reference_free_mem
    (fun t ht => cost_free_hasDerivAt false
      (short_domain ⟨ht.1,by linarith [ht.2]⟩) hB'
      (short_shift ⟨ht.1,by linarith [ht.2]⟩))
    (fun t ht => freeFirst_free_hasDerivAt false
      (short_domain ⟨ht.1,by linarith [ht.2]⟩) hB'
      (short_shift ⟨ht.1,by linarith [ht.2]⟩))
    (fun t ht => (early_free_curvature ht hB).le)
  have ho := curvature_tangent (f := LowerContact.cost false referenceFree)
    (d := outerFirst false referenceFree) (dd := outerSecond false referenceFree)
    (κ := (7/25:ℝ)) hB reference_outer_mem
    (fun t ht => cost_outer_hasDerivAt false
      (full_domain ⟨ht.1,by linarith [ht.2]⟩) (short_shift hb₀))
    (fun t ht => outerFirst_outer_hasDerivAt false
      (full_domain ⟨ht.1,by linarith [ht.2]⟩) (short_shift hb₀))
    (fun t ht => (early_outer_curvature reference_free_mem ht).le)
  have hx : |b-referenceFree|≤(1/10:ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hb.1,hb.2,reference_free_mem.1,reference_free_mem.2]
  have hy : |B-referenceOuter|≤(2/5:ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hB.1,hB.2,reference_outer_mem.1,reference_outer_mem.2]
  have hLip := first_outer_lipschitz reference_free_mem hB reference_outer_mem
  have hcrossAbs := mul_le_mul_of_nonneg_right hLip (abs_nonneg (b-referenceFree))
  rw [←abs_mul] at hcrossAbs
  have hcross := (abs_le.mp hcrossAbs).1
  have hgrad₁ := mul_le_mul reference_gradient.1.le hx (abs_nonneg _) (by norm_num)
  have hgrad₂ := mul_le_mul reference_gradient.2.le hy (abs_nonneg _) (by norm_num)
  rw [←abs_mul] at hgrad₁ hgrad₂
  have hgrad₁' := (abs_le.mp hgrad₁).1
  have hgrad₂' := (abs_le.mp hgrad₂).1
  have hquadratic : (1/2:ℝ)*|B-referenceOuter| * |b-referenceFree|≤
      (3/4:ℝ)*(b-referenceFree)^2+(7/50:ℝ)*(B-referenceOuter)^2 := by
    nlinarith [sq_nonneg (|b-referenceFree|-|B-referenceOuter|/2),
      sq_abs (b-referenceFree),sq_abs (B-referenceOuter),
      sq_nonneg (b-referenceFree),sq_nonneg (B-referenceOuter)]
  linarith [reference_value]

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerFirst
end
end
end

section
/-!
## Direct coordinate reductions into the first lower minimum rectangle

The free derivative increases in the free coordinate and decreases in
the outer coordinate.  The middle outer derivative is positive by one
concave comparison curve.  These motions give whole-domain reductions
without selecting or assuming a stationary point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerFirst
open CommonQuarter CorePairGeometry Arithmetic
open LowerContact LowerGeometry LowerInverse

lemma free_first_monotone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    MonotoneOn (fun b => freeFirst false b B) (Icc 0 (83/200)) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hb => (freeFirst_free_hasDerivAt false (short_domain hb) hB
      (short_shift hb)).continuousAt.continuousWithinAt)
    (fun _ hb => freeFirst_free_hasDerivAt false (short_domain (Ioo_subset_Icc_self hb))
      hB (short_shift (Ioo_subset_Icc_self hb)))
    (fun _ hb => (free_curvature_positive (Ioo_subset_Icc_self hb) hB).le)

lemma free_first_outer_antitone {b : ℝ} (hb : b∈Icc 0 (83/200)) :
    AntitoneOn (freeFirst false b) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hB => (freeFirst_outer_hasDerivAt false hB (short_shift hb)).continuousAt.continuousWithinAt)
    (fun _ hB => freeFirst_outer_hasDerivAt false (Ioo_subset_Icc_self hB) (short_shift hb))
    (fun _ hB => (mixed_negative hb (Ioo_subset_Icc_self hB)).le)

lemma outer_first_free_antitone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    AntitoneOn (fun b => outerFirst false b B) (Icc 0 (83/200)) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hb => (outerFirst_free_hasDerivAt false hB (short_shift hb)).continuousAt.continuousWithinAt)
    (fun _ hb => outerFirst_free_hasDerivAt false hB (short_shift (Ioo_subset_Icc_self hb)))
    (fun _ hb => (mixed_negative (Ioo_subset_Icc_self hb) hB).le)

lemma early_free_positive {b B : ℝ} (hb : b∈Icc (1/10) (83/200))
    (hB : B∈Icc 0 (2/5)) : 0<freeFirst false b B := by
  have hB' := full_domain ⟨hB.1,by linarith [hB.2]⟩
  have h₁ := free_first_outer_antitone (by norm_num : (1/10:ℝ)∈Icc 0 (83/200))
    hB' (full_domain (by norm_num : (2/5:ℝ)∈Icc 0 (4/5))) hB.2
  have h₂ := free_first_monotone hB' (by norm_num : (1/10:ℝ)∈Icc 0 (83/200))
    ⟨by linarith [hb.1],hb.2⟩ hb.1
  linarith [free_first_references.1]

lemma middle_free_positive {b B : ℝ} (hb : b∈Icc (21/200) (83/200))
    (hB : B∈Icc (2/5) (1/2)) : 0<freeFirst false b B := by
  have hB' := full_domain ⟨by linarith [hB.1],by linarith [hB.2]⟩
  have h₁ := free_first_outer_antitone (by norm_num : (21/200:ℝ)∈Icc 0 (83/200))
    hB' (full_domain (by norm_num : (1/2:ℝ)∈Icc 0 (4/5))) hB.2
  have h₂ := free_first_monotone hB' (by norm_num : (21/200:ℝ)∈Icc 0 (83/200))
    ⟨by linarith [hb.1],hb.2⟩ hb.1
  linarith [free_first_references.2.2]

lemma middle_outer_positive {b B : ℝ} (hb : b∈Icc 0 (21/200))
    (hB : B∈Icc (2/5) (1/2)) : 0<outerFirst false b B := by
  have hz : (21/200:ℝ)+1/2∈shifts := short_shift (by norm_num)
  have hconc : ConcaveOn ℝ (Icc (2/5) (1/2)) (outerFirst false (21/200)) :=
    concave_of_deriv2
      (fun t ht => outerFirst_outer_hasDerivAt false
        (full_domain (show t∈Icc 0 (4/5) from ⟨by linarith [ht.1],by linarith [ht.2]⟩)) hz)
      (fun t ht => outerSecond_hasDerivAt false
        (full_domain (show t∈Icc 0 (4/5) from ⟨by linarith [ht.1],by linarith [ht.2]⟩)) hz)
      (fun t ht => (middle_third_negative ht).le)
  have hpos := concave_gt_of_endpoints hconc hB
    (show 0<outerFirst false (21/200) (2/5) by linarith [middle_first_endpoints.1])
    (show 0<outerFirst false (21/200) (1/2) by linarith [middle_first_endpoints.2])
  have hm := outer_first_free_antitone
    (full_domain (show B∈Icc 0 (4/5) from ⟨by linarith [hB.1],by linarith [hB.2]⟩))
    (show b∈Icc 0 (83/200) from ⟨hb.1,by linarith [hb.2]⟩)
    (by norm_num : (21/200:ℝ)∈Icc 0 (83/200)) hb.2
  exact hpos.trans_le hm

theorem early_lower {b B : ℝ} (hb : b∈Icc 0 (83/200)) (hB : B∈Icc 0 (2/5)) :
    (89777/100000:ℝ)<LowerContact.cost false b B := by
  by_cases hsmall : b≤1/10
  · exact rectangle_lower ⟨hb.1,hsmall⟩ hB
  have hB' := full_domain ⟨hB.1,by linarith [hB.2]⟩
  have hm : MonotoneOn (fun t => LowerContact.cost false t B) (Icc (1/10) (83/200)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro t ht
      have ht' : t∈Icc 0 (83/200) := ⟨by linarith [ht.1],ht.2⟩
      exact (cost_free_hasDerivAt false (short_domain ht') hB' (short_shift ht')).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t∈Icc 0 (83/200) := ⟨by linarith [ht.1],ht.2.le⟩
      exact cost_free_hasDerivAt false (short_domain ht') hB' (short_shift ht')
    · intro t ht
      exact (early_free_positive (Ioo_subset_Icc_self ht) hB).le
  exact (rectangle_lower (by norm_num : (1/10:ℝ)∈Icc 0 (1/10)) hB).trans_le
    (hm (by norm_num) ⟨by linarith,hb.2⟩ (by linarith))

theorem middle_lower {b B : ℝ} (hb : b∈Icc 0 (83/200)) (hB : B∈Icc (2/5) (1/2)) :
    (89777/100000:ℝ)<LowerContact.cost false b B := by
  let b' : ℝ := min b (21/200)
  have hb' : b'∈Icc 0 (21/200) :=
    ⟨le_min hb.1 (by norm_num),min_le_right _ _⟩
  have hbfull : b'∈Icc 0 (83/200) := ⟨hb'.1,by linarith [hb'.2]⟩
  have hB' := full_domain ⟨by linarith [hB.1],by linarith [hB.2]⟩
  have hmove : LowerContact.cost false b' B≤LowerContact.cost false b B := by
    by_cases hh : b≤21/200
    · dsimp [b']
      rw [min_eq_left hh]
    · have hm : MonotoneOn (fun t => LowerContact.cost false t B) (Icc (21/200) (83/200)) := by
        apply monoOn_of_hasDeriv_nonneg
        · intro t ht
          have ht' : t∈Icc 0 (83/200) := ⟨by linarith [ht.1],ht.2⟩
          exact (cost_free_hasDerivAt false (short_domain ht') hB' (short_shift ht')).continuousAt.continuousWithinAt
        · intro t ht
          have ht' : t∈Icc 0 (83/200) := ⟨by linarith [ht.1],ht.2.le⟩
          exact cost_free_hasDerivAt false (short_domain ht') hB' (short_shift ht')
        · intro t ht
          exact (middle_free_positive (Ioo_subset_Icc_self ht) hB).le
      dsimp [b']
      rw [min_eq_right (by linarith : (21/200:ℝ)≤b)]
      exact hm (by norm_num) ⟨by linarith,hb.2⟩ (by linarith)
  have houter : MonotoneOn (LowerContact.cost false b') (Icc (2/5) (1/2)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro t ht
      exact (cost_outer_hasDerivAt false
        (full_domain (show t∈Icc 0 (4/5) from ⟨by linarith [ht.1],by linarith [ht.2]⟩)) (short_shift hbfull)).continuousAt.continuousWithinAt
    · intro t ht
      exact cost_outer_hasDerivAt false
        (full_domain (show t∈Icc 0 (4/5) from ⟨by linarith [ht.1],by linarith [ht.2]⟩)) (short_shift hbfull)
    · intro t ht
      exact (middle_outer_positive hb' (Ioo_subset_Icc_self ht)).le
  exact (early_lower hbfull (by norm_num : (2/5:ℝ)∈Icc 0 (2/5))).trans_le
    ((houter (by norm_num) hB hB.1).trans hmove)

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerFirst
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerFirst
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open LowerContact LowerGeometry LowerInverse

theorem contact_lower {b B : ℝ} (hd : Domain b B) :
    (89777/100000:ℝ)<LowerContact.cost false b B := by
  have hb : b∈Icc 0 (83/200) := ⟨hd.1.1,(domain_bounds hd).1.le⟩
  by_cases hB0 : B≤2/5
  · exact early_lower hb ⟨hd.2.1.1,hB0⟩
  by_cases hB1 : B≤1/2
  · exact middle_lower hb ⟨by linarith,hB1⟩
  have hB : (1/2:ℝ)≤B := by linarith
  have hA := NegativeTwo.primary_mem (ShortOuterOne.SameContact.arc_state hd.2.1)
  have ha : 1+b∈Icc outerDiagonal outerAxial := by
    constructor
    · linarith [hd.1.1,outer_endpoint_bounds.2.2.2]
    · linarith [hd.2.2,hA.2]
  let e : ℝ := arc (1+b)
  have he_state : OuterState (1+b) e := ShortOuterOne.SameContact.primary_state ha
  have he : e∈Icc 0 outerDiagonal := NegativeTwo.source_mem he_state
  have hearc : arc e=1+b := (ShortOuterOne.SameContact.actual_arc he_state).1
  have hBe : B≤e := by
    have hm := ShortOuterOne.SameContact.arc_antitone (primary_domain ha) (primary_domain hA)
      (show 1+b≤arc B by linarith [hd.2.2])
    have hback := (ShortOuterOne.SameContact.actual_arc
      (ShortOuterOne.SameContact.arc_state hd.2.1)).2
    rw [hback] at hm
    exact hm
  have hend : Domain b e := ⟨hd.1,he,by rw [hearc]; linarith⟩
  have hpath {y : ℝ} (hy : y∈Icc (1/2) e) : Domain b y :=
    domain_downward hend ⟨by linarith [hy.1],hy.2⟩
  have hconc : ConcaveOn ℝ (Icc (1/2) e) (LowerContact.cost false b) :=
    concave_of_deriv2
      (fun y hy => cost_outer_hasDerivAt false (hpath hy).2.1 (domain_bounds (hpath hy)).2.2)
      (fun y hy => outerFirst_outer_hasDerivAt false (hpath hy).2.1
        (domain_bounds (hpath hy)).2.2)
      (fun y hy => by have hh := late_outer_curvature (hpath hy) hy.1; linarith)
  have hleft : (89777/100000:ℝ)<LowerContact.cost false b (1/2) := middle_lower hb (by norm_num)
  have hright : (89777/100000:ℝ)<LowerContact.cost false b e := by
    have hh := aligned_lower false hend (by rw [hearc]; ring)
    linarith
  exact concave_gt_of_endpoints hconc ⟨hB,hBe⟩ hleft hright

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerFirst

namespace SquaresInCircles.Eight.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 (Real.pi/2-x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2-x) := by
  obtain ⟨hd,hbetter⟩ := LowerContact.original_first_reduction hs ht hx hm
  exact (LowerFirst.contact_lower hd).trans_le hbetter

theorem original_lower_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) 1 (Real.pi/2-x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2-x) :=
  original_lower_source_secondary hs ht hx
    (original_lower_target_primary_implies_first hs ht hx hm)

end SquaresInCircles.Eight.SecondWord.OppositeThree
end
end
end

module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerFirstRectangle

/-!
# Negative curvature on the complete terminal contact surface

At the initial target coordinate the exact curvature is a convex cubic
of the positive speed quotient.  Its physical endpoints are the two
named endpoint substitutions.  Negative third derivative then transports
the result along each unchanged physical contact segment.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerFirst
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open LowerContact LowerGeometry LowerInverse

lemma domain_downward {b B y : ℝ} (hd : Domain b B) (hy : y∈Icc 0 B) : Domain b y := by
  have hy' : y∈Icc 0 outerDiagonal := ⟨hy.1,hy.2.trans hd.2.1.2⟩
  have hm := ShortOuterOne.SameContact.arc_antitone (outer_domain hy')
    (outer_domain hd.2.1) hy.2
  exact ⟨hd.1,hy',by linarith [hd.2.2]⟩

lemma half_outer_curvature {b : ℝ} (hd : Domain b (1/2)) :
    outerSecond false b (1/2)< -(11/100:ℝ) := by
  let l : ℝ := quotient ((0:ℝ)+1/2) (1/2)
  let r : ℝ := U (1/2)-1
  let c₃ : ℝ := (ratio (1/2))^2/(q (U (1/2)))^2
  let c₁ : ℝ := 3*(ratio (1/2))^2/(q (U (1/2)))^2-ratioD (1/2)/q (U (1/2))
  let c₀ : ℝ := -ratio (1/2)*factorD (U (1/2))-LLabel.d2 (1/2)
  let g : ℝ→ℝ := fun t => c₀+c₃*t^3+c₁*t
  have hhalf : (1/2:ℝ)∈Icc 0 outerDiagonal := full_domain (by norm_num)
  have hz0 : ((0:ℝ)+1/2)∈shifts := by norm_num [shifts,OppositeTwo.PrimaryInverse.shifts]
  have hv0 := (OppositeTwo.PrimaryInverse.data hhalf hz0).2.2.1
  have hv := (OppositeTwo.PrimaryInverse.data hhalf (domain_bounds hd).2.2).2.2.1
  have hl : 0≤l := by dsimp [l,quotient]; positivity
  have hhalfsmall : (1/2:ℝ)∈Icc 0 bOne :=
    ⟨by norm_num,by linarith [OppositeTwo.bOne_bounds.1]⟩
  have hj : Domain (arc (1/2)-1) (1/2) :=
    ⟨Aligned.j_mem hhalfsmall,hhalf,le_rfl⟩
  have hzj := (domain_bounds hj).2.2
  have hvj := (OppositeTwo.PrimaryInverse.data hhalf hzj).2.2.1
  have hez : arc (1/2)-1+1/2=r := by dsimp [r,U]; ring
  have hjv : speed (arc (1/2)-1+1/2) (1/2)=1 := by
    have hc := NegativeTwo.ContactInverse.base_circle hhalf
    have he := (OppositeTwo.PrimaryInverse.data hhalf hzj).2.2.2
    dsimp [W] at hc
    norm_num at hc
    have hz : arc (1/2)-1+1/2=U (1/2)-1 := by dsimp [U]; ring
    rw [hz] at he
    nlinarith
  have htlo : l≤quotient (b+1/2) (1/2) := by
    have hvle : speed (b+1/2) (1/2)≤speed ((0:ℝ)+1/2) (1/2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [hd.1.1]
    dsimp [l,quotient]
    apply (div_le_div_iff₀ hv0 hv).2
    nlinarith [hd.1.1]
  have hthi : quotient (b+1/2) (1/2)≤r := by
    have hp := physical_speed hd
    norm_num [W] at hp
    have hz : b+1/2≤r := by dsimp [r,U]; linarith [hd.2.2]
    have hr : 0≤r := by dsimp [r]; linarith [(late_U hj (by norm_num)).1]
    dsimp [quotient]
    apply (div_le_iff₀ hv).2
    nlinarith
  have hc₃ : 0≤c₃ := by dsimp [c₃]; positivity
  have hconc : ConcaveOn ℝ (Icc l r) (fun t => -g t) := by
    apply concave_of_deriv2 (f' := fun t => -3*c₃*t^2-c₁)
      (f'' := fun t => -6*c₃*t)
    · intro t ht
      have hp := ((((hasDerivAt_id t).pow 3).const_mul c₃).const_add c₀).
        add ((hasDerivAt_id t).const_mul c₁)
      convert hp.neg using 1 <;> dsimp [g] <;> ring
    · intro t ht
      convert ((((hasDerivAt_id t).pow 2).const_mul (-3*c₃)).sub_const c₁)
        using 1 <;> ring
    · intro t ht
      have ht0 : 0≤t := hl.trans ht.1
      have hp := mul_nonneg hc₃ ht0
      linarith
  have he₀ : g l=outerSecond false 0 (1/2) := by
    have he := second_cubic hhalf hz0
    dsimp [outerSecond,outer,g,c₀,c₁,c₃,l]
    rw [he]
    ring
  have he₁ : g r=outerSecond false (arc (1/2)-1) (1/2) := by
    have he := second_cubic hhalf hzj
    have ht : quotient (arc (1/2)-1+1/2) (1/2)=r := by
      dsimp [quotient]
      rw [hjv,div_one,hez]
    dsimp [outerSecond,outer,g,c₀,c₁,c₃]
    rw [he,ht]
    ring
  have hbound := concave_gt_of_endpoints hconc ⟨htlo,hthi⟩
    (show (11/100:ℝ)< -g l by rw [he₀]; linarith [half_endpoints.1])
    (show (11/100:ℝ)< -g r by rw [he₁]; linarith [half_endpoints.2])
  have he := second_cubic hhalf (domain_bounds hd).2.2
  dsimp [g,c₀,c₁,c₃] at hbound
  dsimp [outerSecond,outer]
  rw [he]
  linarith

lemma late_outer_curvature {b B : ℝ} (hd : Domain b B) (hB : 1/2≤B) :
    outerSecond false b B< -(11/100:ℝ) := by
  have hpath {y : ℝ} (hy : y∈Icc (1/2) B) : Domain b y :=
    domain_downward hd ⟨by linarith [hy.1],hy.2⟩
  have hm : AntitoneOn (outerSecond false b) (Icc (1/2) B) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro y hy
      exact (outerSecond_hasDerivAt false (hpath hy).2.1 (domain_bounds (hpath hy)).2.2).
        continuousAt.continuousWithinAt
    · intro y hy
      exact outerSecond_hasDerivAt false (hpath (Ioo_subset_Icc_self hy)).2.1
        (domain_bounds (hpath (Ioo_subset_Icc_self hy))).2.2
    · intro y hy
      exact (late_third_negative (hpath (Ioo_subset_Icc_self hy)) hy.1.le).le
  exact (hm ⟨le_rfl,hB⟩ ⟨hB,le_rfl⟩ hB).trans_lt
    (half_outer_curvature (hpath ⟨le_rfl,hB⟩))

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerFirst

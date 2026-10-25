module

public import SquaresInCircles.Eight.Frames.High.HighVaryingScalars
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroNegativePJ
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositePositiveZeroGeometry

/-!
# Eight squares: the four concave negative contact surfaces

The last
row uses the two simultaneous whole-domain projection estimates and
averages them. The preceding row uses its one convex quadratic on the
whole sine interval. No angle subdivision is introduced.
-/

section
/-!
## The six aligned opposite-sign short-word contacts

The physical interval is [1-d,d]. Four rows are concave on the whole
interval and two are monotone. Their two actual geometric endpoint
values are enclosed directly from the literal labels and circle roots.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open SecondWord (U W outer_domain outer_zero_mem UW_circle U_positive)
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra
open SecondWord.SameZero.PJ.Reference (dBox dUBox)
open SecondWord.OppositeZero.AlignedPJ (sourceBox sourceUBox)

lemma low_mem : low∈Icc 0 outerDiagonal := by
  dsimp [low]
  constructor <;> linarith [outer_endpoint_bounds.2.2.1,outer_endpoint_bounds.2.2.2]

lemma low_radical : (377/200:ℝ)<U low ∧ U low<(943/500:ℝ) := by
  have hc := UW_circle (outer_domain low_mem)
  have hu := U_positive (outer_domain low_mem)
  have hd := ShortMixedZero.fine_diagonal_bounds
  dsimp [W,low] at hc
  norm_num [Q0] at hc
  constructor <;> nlinarith [hd.1,hd.2]

lemma U_antitone : AntitoneOn U (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hb => ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)).continuousAt.continuousWithinAt)
    (fun _ hb => (ShortOuterOne.SameContact.arc_hasDerivAt
      (outer_domain (Ioo_subset_Icc_self hb))).add_const (1/2))
    (fun _ hb => neg_nonpos.mpr
      (ShortOuterOne.SameContact.ratio_pos (outer_domain (Ioo_subset_Icc_self hb))).le)

lemma band_root {b : ℝ} (hb : b∈Icc low outerDiagonal) :
    (1399/1000:ℝ)<U b ∧ U b<(943/500:ℝ) := by
  have hbi := (aligned_domains hb).1
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hlo := U_antitone hbi hdiag hb.2
  have hhi := U_antitone low_mem hbi hb.1
  rw [U,ShortOuterOne.SameContact.arc_diagonal] at hlo
  exact ⟨by linarith [ShortMixedZero.fine_diagonal_bounds.1],hhi.trans_lt low_radical.2⟩

lemma band_derivative_ratio {b B : ℝ} (hb : b∈Icc low outerDiagonal)
    (hB : B∈Icc low outerDiagonal) : ratioD b<(123/50:ℝ)*ratioD B := by
  have hu := band_root hb
  have hU := band_root hB
  have hulo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hu.1.le 3
  have hUhi := pow_le_pow_left₀ (by linarith [hU.1] : 0≤U B) hU.2.le 3
  have hp : (U B)^3<(123/50:ℝ)*(U b)^3 := by
    have href : (943/500:ℝ)^3<(123/50)*(1399/1000)^3 := by norm_num
    nlinarith
  have hub : 0<U b := by linarith [hu.1]
  have huB : 0<U B := by linarith [hU.1]
  change Q0/(U b)^3<(123/50)*(Q0/(U B)^3)
  apply (div_lt_iff₀ (pow_pos hub 3)).2
  apply (lt_of_mul_lt_mul_right _ (pow_nonneg huB.le 3))
  field_simp [huB.ne']
  have hq := mul_lt_mul_of_pos_left hp (by norm_num [Q0] : 0<Q0)
  nlinarith

lemma low_ratio : ratio low<(319/1000:ℝ) := by
  have hu := low_radical.1
  have hd := ShortMixedZero.fine_diagonal_bounds.1
  change (low+1/2)/U low<319/1000
  apply (div_lt_iff₀ (by linarith : 0<U low)).2
  dsimp [low]
  linarith

lemma aligned_endpoints (r : Row) : (89809/100000:ℝ)<aligned r low ∧
    (89809/100000:ℝ)<aligned r outerDiagonal := by
  have hd := SecondWord.diagonal_fine
  have hA : (1385379606/1000000000:ℝ)<arc (1-outerDiagonal) ∧
      arc (1-outerDiagonal)<1385379607/1000000000 := by
    have hsq1 : (3/2-outerDiagonal)^2<(3/2-89921406510940/100000000000000)^2 := by nlinarith
    have hsq2 : (3/2-89921406510941/100000000000000)^2<(3/2-outerDiagonal)^2 := by nlinarith
    simp only [ShortOuterOne.SameContact.arc]
    constructor
    · rw [lt_sub_iff_add_lt,Real.lt_sqrt (by norm_num)]
      norm_num [Q0] at hsq1 ⊢
      linarith
    · rw [sub_lt_iff_lt_add,Real.sqrt_lt' (by norm_num)]
      norm_num [Q0] at hsq2 ⊢
      linarith
  have h1 : aligned r low=c r+p r*arc (1-outerDiagonal)+q r*(1-outerDiagonal)+
      (v r+t r)*outerDiagonal := by
    simp only [aligned,source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval,
      sub_sub_cancel,ShortOuterOne.SameContact.arc_diagonal]
    ring
  have h2 : aligned r outerDiagonal=c r+(p r+q r)*outerDiagonal+v r*arc (1-outerDiagonal)+
      t r*(1-outerDiagonal) := by
    simp only [aligned,source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval,
      ShortOuterOne.SameContact.arc_diagonal]
    ring
  rw [h1,h2]
  obtain ⟨ha1,ha2⟩ := hA
  obtain ⟨hd1,hd2⟩ := hd
  generalize arc (1-outerDiagonal)=A at ha1 ha2 ⊢
  fin_cases r <;> norm_num [c,p,q,v,t] <;> constructor <;> linarith

def ConcaveRow (r : Row) : Prop := r=0 ∨ r=1 ∨ r=4 ∨ r=5

lemma aligned_curvature (r : Row) (hr : ConcaveRow r)
    {b : ℝ} (hb : b∈Icc low outerDiagonal) : alignedSecond r b<0 := by
  have hother : 1-b∈Icc low outerDiagonal :=
    ⟨by dsimp [low] at *; linarith [hb.2],by dsimp [low] at *; linarith [hb.1]⟩
  have hleft := ShortOuterOne.SameContact.ratioD_pos (outer_domain (aligned_domains hb).1)
  have hright := ShortOuterOne.SameContact.ratioD_pos (outer_domain (aligned_domains hb).2)
  have hLR := band_derivative_ratio hb hother
  have hRL := band_derivative_ratio hother hb
  rcases hr with rfl | rfl | rfl | rfl <;>
    norm_num [alignedSecond,p,v] <;> nlinarith

lemma aligned_monotone_two : MonotoneOn (aligned 2) (Icc low outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (aligned_hasDerivAt 2 hb).continuousAt.continuousWithinAt)
    (fun b hb => aligned_hasDerivAt 2 (Ioo_subset_Icc_self hb))
    (fun b hb => by
      have hh := SecondWord.outer_ratio_bounds (aligned_domains (Ioo_subset_Icc_self hb)).2
      norm_num [alignedFirst,l,h,p,q,v,t]
      linarith [hh.2.1])

lemma aligned_antitone_three : AntitoneOn (aligned 3) (Icc low outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (aligned_hasDerivAt 3 hb).continuousAt.continuousWithinAt)
    (fun b hb => aligned_hasDerivAt 3 (Ioo_subset_Icc_self hb))
    (fun b hb => by
      have hh := SecondWord.outer_ratio_bounds (aligned_domains (Ioo_subset_Icc_self hb)).1
      norm_num [alignedFirst,l,h,p,q,v,t]
      linarith [hh.2.1])

/-- All six aligned minima, on the complete geometric interval. -/
theorem aligned_lower (r : Row) {b : ℝ} (hb : b∈Icc low outerDiagonal) :
    (89809/100000:ℝ)<aligned r b := by
  by_cases htwo : r=2
  · subst r
    exact (aligned_endpoints 2).1.trans_le
      (aligned_monotone_two ⟨le_rfl,low_mem.2⟩ hb hb.1)
  by_cases hthree : r=3
  · subst r
    exact (aligned_endpoints 3).2.trans_le
      (aligned_antitone_three hb ⟨low_mem.2,le_rfl⟩ hb.2)
  have hr : ConcaveRow r := by
    fin_cases r <;> simp_all [ConcaveRow]
  have hc : ConcaveOn ℝ (Icc low outerDiagonal) (aligned r) :=
    concave_of_deriv2 (fun b hb => aligned_hasDerivAt r hb)
      (fun b hb => alignedFirst_hasDerivAt r hb)
      (fun b hb => (aligned_curvature r hr hb).le)
  exact concave_gt_of_endpoints hc hb (aligned_endpoints r).1 (aligned_endpoints r).2

theorem aligned_original (r : Row) {b B : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal) (he : b+B=1) :
    (89809/100000:ℝ)<c r+(source r).outer b+(target r).outer B := by
  have hband : b∈Icc low outerDiagonal := ⟨by dsimp [low]; linarith [hB.2],hb.2⟩
  have hB' : B=1-b := by linarith
  simpa [aligned,hB'] using aligned_lower r hband

end SquaresInCircles.Eight.ShortOuterZero.Opposite
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open SecondWord (U W outer_domain UW_circle U_positive)

def ratioQuotient (b B : ℝ) : ℝ := (U B)^3/(U b)^3
abbrev lowerRatio : ℝ := (1399/1000)^3/(943/500)^3

def curvature (r : Row) (B x : ℝ) : ℝ :=
  -p r*ratioQuotient (minus B x) B*(minusK B x)^2-
    l r (minus B x)*Real.sin x-v r

lemma ratioQuotient_identity {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) : ratioD b=ratioQuotient b B*ratioD B := by
  have hu := U_positive (outer_domain hb)
  have hU := U_positive (outer_domain hB)
  change Q0/(U b)^3=((U B)^3/(U b)^3)*(Q0/(U B)^3)
  field_simp [hu.ne',hU.ne']

lemma curvature_identity (r : Row) {B x : ℝ} (hd : MinusDomain B x) :
    minusTargetCurvature r B x=ratioD B*curvature r B x := by
  rw [minusTargetCurvature,ratioQuotient_identity hd.2.2 hd.1]
  dsimp [curvature]
  ring

lemma ratioQuotient_bounds {b B : ℝ} (hb : b∈Icc low outerDiagonal)
    (hB : B∈Icc low outerDiagonal) :
    0<ratioQuotient b B ∧ lowerRatio≤ratioQuotient b B ∧ ratioQuotient b B<123/50 := by
  have hu := band_root hb
  have hU := band_root hB
  have hup : 0<U b := by linarith [hu.1]
  have hUp : 0<U B := by linarith [hU.1]
  have hulo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hu.1.le 3
  have hUlo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hU.1.le 3
  have huhi := pow_le_pow_left₀ hup.le hu.2.le 3
  have hUhi := pow_le_pow_left₀ hUp.le hU.2.le 3
  refine ⟨div_pos (pow_pos hUp 3) (pow_pos hup 3),?_,?_⟩
  · apply (le_div_iff₀ (pow_pos hup 3)).2
    dsimp [lowerRatio]
    have hp := mul_le_mul_of_nonneg_left huhi
      (by norm_num : (0:ℝ)≤(1399/1000)^3/(943/500)^3)
    norm_num at hp
    linarith
  · apply (div_lt_iff₀ (pow_pos hup 3)).2
    have href : (943/500:ℝ)^3<(123/50)*(1399/1000)^3 := by norm_num
    nlinarith

lemma projection_lower {B x : ℝ} (hd : MinusDomain B x) :
    (Real.cos x)^2≤(minusK B x)^2 := by
  have tr := positive_trig hd.2.1
  have hR := ShortOuterOne.SameContact.ratio_pos (outer_domain hd.1)
  have hp := mul_nonneg hR.le tr.2.2.1
  have hk : Real.cos x≤ minusK B x := by
    dsimp [minusK,SecondWord.OppositeZero.minusK]
    linarith
  exact pow_le_pow_left₀ (by linarith [tr.1]) hk 2

lemma projection_upper {B x : ℝ} (hd : MinusDomain B x) :
    (minusK B x)^2≤1+2*Real.sin x := by
  have tr := positive_trig hd.2.1
  have hr := SecondWord.outer_ratio_bounds hd.1
  have hs := mul_le_mul_of_nonneg_right hr.2.1 tr.2.2.1
  have hk : minusK B x≤Real.cos x+Real.sin x := by
    dsimp [minusK,SecondWord.OppositeZero.minusK]
    linarith
  have hk0 := (SecondWord.OppositeZero.positive_data hd.1 hd.2.1).2.2.2
  have hsq := pow_le_pow_left₀ hk0.le hk 2
  have hcs := mul_le_mul_of_nonneg_right tr.2.1 tr.2.2.1
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma projection_cauchy {B x : ℝ} (hd : MinusDomain B x) :
    (U B*Real.cos x+W B*Real.sin x)^2≤Q0 := by
  have hc := UW_circle (outer_domain hd.1)
  have ht := Real.sin_sq_add_cos_sq x
  have hs := sq_nonneg (U B*Real.sin x-W B*Real.cos x)
  nlinarith [hc,ht,
    show (U B*Real.cos x+W B*Real.sin x)^2+
      (U B*Real.sin x-W B*Real.cos x)^2=Q0 by
        linear_combination hc+((U B)^2+(W B)^2)*ht]

lemma weighted_projection {B x : ℝ} (hd : MinusDomain B x) :
    ratioQuotient (minus B x) B*(minusK B x)^2=
      U B*(U B*Real.cos x+W B*Real.sin x)^2/(U (minus B x))^3 := by
  have hu := U_positive (outer_domain hd.2.2)
  have hU := U_positive (outer_domain hd.1)
  have hr : ratio B=W B/U B := rfl
  simp only [ratioQuotient,minusK,SecondWord.OppositeZero.minusK]
  rw [hr]
  field_simp

lemma projection_product_bounds {B x : ℝ} (hd : MinusDomain B x) :
    lowerRatio*(Real.cos x)^2≤ratioQuotient (minus B x) B*(minusK B x)^2 ∧
    ratioQuotient (minus B x) B*(minusK B x)^2≤(123/50)*(1+2*Real.sin x) ∧
    ratioQuotient (minus B x) B*(minusK B x)^2<
      Q0*(943/500)/(1399/1000)^3 := by
  have hb := band_coordinates hd
  have hr := ratioQuotient_bounds hb.2 hb.1
  have hu := band_root hb.2
  have hU := band_root hb.1
  refine ⟨mul_le_mul hr.2.1 (projection_lower hd) (sq_nonneg _)
    hr.1.le,?_,?_⟩
  · exact mul_le_mul hr.2.2.le (projection_upper hd) (sq_nonneg _) (by norm_num)
  · rw [weighted_projection hd]
    have hC := projection_cauchy hd
    have hprod := mul_le_mul_of_nonneg_left hC (by linarith [hU.1] : 0≤U B)
    have hprodU := mul_lt_mul_of_pos_right hU.2 (by norm_num [Q0] : 0<Q0)
    have hu3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hu.1.le 3
    apply (div_lt_iff₀ (pow_pos (by linarith [hu.1] : 0<U (minus B x)) 3)).2
    have hden := mul_le_mul_of_nonneg_left hu3
      (by norm_num [Q0] : (0:ℝ)≤Q0*(943/500)/(1399/1000)^3)
    have hc : Q0*(943/500)/(1399/1000)^3*(1399/1000)^3=Q0*(943/500) := by
      field_simp
    linarith only [hden,hc,hprod,hprodU]

abbrev coefficientA : ℝ := (51554/100000)*lowerRatio
abbrev coefficientB : ℝ := (19335/100000)*(123/50)
abbrev coefficientC : ℝ := (19335/100000)*Q0*(943/500)/(1399/1000)^3

def rowFourQuadratic (s : ℝ) : ℝ :=
  coefficientA*s^2-(68355/100000)*s+19335/100000-coefficientA

lemma rowFourQuadratic_negative {s : ℝ} (hs : s∈Icc (0:ℝ) (129/200)) :
    rowFourQuadratic s<0 := by
  have hA : 0<coefficientA := by norm_num [coefficientA,lowerRatio]
  have hproduct := mul_nonneg hs.1 (sub_nonneg.mpr hs.2)
  have hlinear : rowFourQuadratic s≤
      rowFourQuadratic 0+(s/(129/200))*(rowFourQuadratic (129/200)-rowFourQuadratic 0) := by
    dsimp [rowFourQuadratic]
    nlinarith
  have hl : rowFourQuadratic 0<0 := by norm_num [rowFourQuadratic,coefficientA,lowerRatio]
  have hu : rowFourQuadratic (129/200)<0 := by norm_num [rowFourQuadratic,coefficientA,lowerRatio]
  have hweight : s/(129/200)∈Icc (0:ℝ) 1 := by constructor <;> linarith [hs.1,hs.2]
  have hleft := mul_nonpos_of_nonneg_of_nonpos (show 0≤1-s/(129/200) by linarith [hweight.2]) hl.le
  have hright := mul_nonpos_of_nonneg_of_nonpos hweight.1 hu.le
  by_cases hz : s=0
  · simpa [hz] using hl
  · have hstrict := mul_neg_of_pos_of_neg (show 0<s/(129/200) by
      have hp : 0<s := lt_of_le_of_ne hs.1 (Ne.symm hz); positivity) hu
    linarith

lemma curvature_negative (r : Row) (hr : ConcaveRow r) {B x : ℝ}
    (hd : MinusDomain B x) : curvature r B x<0 := by
  have tr := positive_trig hd.2.1
  have hL := slope_bounds r hd.2.2
  have hp := projection_product_bounds hd
  have hR := ratioQuotient_bounds (band_coordinates hd).2 (band_coordinates hd).1
  have hK := (SecondWord.OppositeZero.positive_data hd.1 hd.2.1).2.2.2
  have hs : Real.sin x∈Icc (0:ℝ) (129/200) := ⟨tr.2.2.1,by linarith [tr.2.2.2.1]⟩
  rcases hr with rfl | rfl | rfl | rfl
  · have hnon := mul_nonneg (by linarith [hL.1] : 0≤l 0 (minus B x)) hs.1
    norm_num [curvature,p,v]
    linarith
  · have hstrict := mul_pos hR.1 (sq_pos_of_pos hK)
    have hnon := mul_nonneg (by linarith [hL.1] : 0≤l 1 (minus B x)) hs.1
    norm_num [curvature,p,v]
    nlinarith
  · have hprod := mul_le_mul_of_nonneg_left hp.1 (by norm_num : (0:ℝ)≤51554/100000)
    have hlabel := mul_le_mul_of_nonneg_right hL.1 hs.1
    have hquad := rowFourQuadratic_negative hs
    have hid := Real.sin_sq_add_cos_sq x
    dsimp [curvature,rowFourQuadratic,coefficientA] at *
    norm_num [p,v] at *
    nlinarith
  · have hprod1 := mul_le_mul_of_nonneg_left hp.2.1 (by norm_num : (0:ℝ)≤19335/100000)
    have hprod2 := mul_lt_mul_of_pos_left hp.2.2 (by norm_num : (0:ℝ)<19335/100000)
    have hlabel : (76744/100000:ℝ)≤l 5 (minus B x) := by
      have hratio := ShortOuterOne.SameContact.ratio_pos (outer_domain hd.2.2)
      norm_num [l,p,q]
      linarith
    have hlabelS := mul_le_mul_of_nonneg_right hlabel hs.1
    have href : (coefficientB+coefficientC)/2-(51554/100000:ℝ)< -(2/125:ℝ) ∧
        coefficientB<(76744/100000:ℝ) := by
      constructor <;> norm_num [coefficientB,coefficientC,Q0]
    have hneg := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr href.2.le) hs.1
    dsimp [curvature,coefficientB,coefficientC] at *
    norm_num [p,v] at *
    nlinarith

/-- All four target-concave rows, with both original coordinates coupled. -/
theorem target_curvature_negative (r : Row) (hr : ConcaveRow r) {B x : ℝ}
    (hd : MinusDomain B x) : minusTargetCurvature r B x<0 := by
  rw [curvature_identity r hd]
  exact mul_neg_of_pos_of_neg (ShortOuterOne.SameContact.ratioD_pos (outer_domain hd.1))
    (curvature_negative r hr hd)

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative
end
end
end

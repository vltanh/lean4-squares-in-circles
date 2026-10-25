module

public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeNegativeCurvature
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositePositiveZeroGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameAxial
public import SquaresInCircles.Eight.Words.Wrong.WordCircleSupport

/-!
# Eight squares: both positive-source-coefficient stationary exclusions

The two bounds concern the original coupled source and target at angular stationarity
(`stationary_descent`). Row 4 first uses the sign of the angular curvature to obtain `b < 1/5`
(`row_four_source`); all later estimates use that same `b` and its target circle.
-/

section
/-!
## Interior geometry for the positive opposite-sign contact

The lower endpoint is either the original target axis or the original
source diagonal. Every intermediate target remains on the same contact
surface. The derivative continuity facts are local facts on that actual
surface, needed for the written stationary-point tests.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open SecondWord (outer_domain outer_zero_mem)

lemma lower_entry {B x : ℝ} (hd : PlusDomain B x) :
    ∃a, a∈Icc 0 B ∧ PlusDomain a x ∧ (a=0 ∨ plus a x=outerDiagonal) ∧
      ∀C∈Icc a B, PlusDomain C x := by
  have hinterval {a : ℝ} (ha : PlusDomain a x) (haB : a≤B) :
      ∀C∈Icc a B, PlusDomain C x := by
    intro C hC
    have hCi : C∈Icc 0 outerDiagonal := ⟨ha.1.1.trans hC.1,hC.2.trans hd.1.2⟩
    have hlo := SecondWord.OppositeZero.plus_target_antitone hd.2.1 hCi hd.1 hC.2
    have hhi := SecondWord.OppositeZero.plus_target_antitone hd.2.1 ha.1 hCi hC.1
    exact ⟨hCi,hd.2.1,⟨hd.2.2.1.trans hlo,hhi.trans ha.2.2.2⟩⟩
  by_cases hzero : plus 0 x≤outerDiagonal
  · have hsource := SecondWord.OppositeZero.plus_target_antitone hd.2.1 outer_zero_mem hd.1 hd.1.1
    have hz : PlusDomain 0 x := ⟨outer_zero_mem,hd.2.1,⟨hd.2.2.1.trans hsource,hzero⟩⟩
    exact ⟨0,⟨le_rfl,hd.1.1⟩,hz,Or.inl rfl,hinterval hz hd.1.1⟩
  · have hc : Continuous (fun C => plus C x) := by dsimp [plus,SecondWord.OppositeZero.plus,arc]; fun_prop
    obtain ⟨a,ha,he⟩ := intermediate_value_Icc hd.1.1 hc.neg.continuousOn
      (show -outerDiagonal∈Icc (-plus 0 x) (-plus B x) from
        ⟨by linarith,by linarith [hd.2.2.2]⟩)
    have heq : plus a x=outerDiagonal := by simpa using he
    have had : PlusDomain a x :=
      ⟨⟨ha.1,ha.2.trans hd.1.2⟩,hd.2.1,by show plus a x∈_; rw [heq]; exact Negative.diagonal_mem⟩
    exact ⟨a,ha,had,Or.inr heq,hinterval had ha.2⟩

lemma initial_target_coordinate {B x : ℝ} (hd : PlusDomain B x)
    (hentry : B=0 ∨ plus B x=outerDiagonal) : B≤low := by
  rcases hentry with rfl | hdiag
  · exact low_mem.1
  · have hh := SecondWord.OppositeZero.plus_angle_antitone hd.1
      (by norm_num) hd.2.1 hd.2.1.1
    rw [show SecondWord.OppositeZero.plus B x=outerDiagonal from hdiag] at hh
    norm_num [plus,SecondWord.OppositeZero.plus] at hh
    dsimp [low]
    linarith

lemma ratio_monotone : MonotoneOn ratio (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hB => (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).continuousAt.continuousWithinAt)
    (fun _ hB => ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (Ioo_subset_Icc_self hB)))
    (fun _ hB => (ShortOuterOne.SameContact.ratioD_pos (outer_domain (Ioo_subset_Icc_self hB))).le)

lemma ratioD_monotone : MonotoneOn ratioD (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hB)).continuousAt.continuousWithinAt)
    (fun B hB => ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain (Ioo_subset_Icc_self hB)))
    (fun B hB => by
      have hu := SecondWord.U_positive (outer_domain (Ioo_subset_Icc_self hB))
      change 0≤3*Q0*(B+1/2)/(SecondWord.U B)^5
      exact div_nonneg (mul_nonneg (by norm_num [Q0]) (by linarith [hB.1])) (pow_pos hu 5).le)

lemma target_projection_upper {B x : ℝ} (hd : PlusDomain B x) : plusK B x≤1 := by
  have tr := positive_trig hd.2.1
  have hr := ShortOuterOne.SameContact.ratio_pos (outer_domain hd.1)
  have hp := mul_nonneg hr.le tr.2.2.1
  dsimp [plusK,SecondWord.OppositeZero.plusK]
  linarith [tr.2.1]

lemma plusTargetCurvature_continuousAt (r : Row) {B x : ℝ} (hd : PlusDomain B x) :
    ContinuousAt (fun C => plusTargetCurvature r C x) B := by
  have hb := (SecondWord.OppositeZero.plus_target_hasDerivAt hd.1 x).continuousAt
  have hD := (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hd.2.2)).continuousAt.comp
    (x := B) hb
  have hL := (l_hasDerivAt r hd.2.2).continuousAt.comp (x := B) hb
  have hR := (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hd.1)).continuousAt
  have hDt := (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hd.1)).continuousAt
  have hK : ContinuousAt (fun C => plusK C x) B :=
    continuousAt_const.sub (hR.mul continuousAt_const)
  exact ((continuousAt_const.mul hD).mul (hK.pow 2)).add
    (((hL.mul continuousAt_const).sub continuousAt_const).mul hDt)

/-- The affine-source row cannot have a target local minimum in the interior. -/
lemma row_zero_stationary_curvature {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusTarget 0 B x=0) : plusTargetCurvature 0 B x<0 := by
  have tr := positive_trig hd.2.1
  have hr := ShortOuterOne.SameContact.ratio_pos (outer_domain hd.1)
  have hD := ShortOuterOne.SameContact.ratioD_pos (outer_domain hd.1)
  have hid : plusTarget 0 B x=t 0-q 0*Real.cos x+
      (q 0*Real.sin x-v 0)*ratio B := by
    norm_num [plusTarget,h,l,p,plusK,SecondWord.OppositeZero.plusK]
    ring
  have hpositive : 0<t 0-q 0*Real.cos x := by norm_num [t,q]; linarith [tr.2.1]
  have hnegative : q 0*Real.sin x-v 0<0 := by
    rw [hid] at hstat
    by_contra! hn
    have hp := mul_nonneg hn hr.le
    linarith
  have hprod := mul_neg_of_neg_of_pos hnegative hD
  simpa [plusTargetCurvature,l,p] using hprod

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive
end
end
end

section
/-!
## The two target-derivative-shape rows

Along a fixed contact interval the normalized target second derivative is nonincreasing
(`normalized_antitone`). The first derivative is positive at the lower endpoint
(`entry_first_positive`). At any stationary point the second derivative is therefore negative
(`stationary_curvature_negative`), which excludes an interior minimum.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Shape
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio ratioD)
open SecondWord (outer_domain)

def Rows (r : Row) : Prop := r=3 ∨ r=5

def normalized (r : Row) (B x : ℝ) : ℝ :=
  (-p r)*(ratioD (plus B x)/ratioD B)*(plusK B x)^2+
    l r (plus B x)*Real.sin x-v r

lemma normalized_identity (r : Row) {B x : ℝ} (hd : PlusDomain B x) :
    plusTargetCurvature r B x=normalized r B x*ratioD B := by
  have hD := ShortOuterOne.SameContact.ratioD_pos (outer_domain hd.1)
  dsimp [plusTargetCurvature,normalized]
  field_simp [hD.ne']
  ring

lemma l_monotone (r : Row) (hr : Rows r) : MonotoneOn (l r) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (l_hasDerivAt r hb).continuousAt.continuousWithinAt)
    (fun b hb => l_hasDerivAt r (Ioo_subset_Icc_self hb))
    (fun b hb => by
      have hp : 0≤-p r := by rcases hr with rfl | rfl <;> norm_num [p]
      exact mul_nonneg hp
        (ShortOuterOne.SameContact.ratioD_pos (outer_domain (Ioo_subset_Icc_self hb))).le)

lemma normalized_antitone (r : Row) (hr : Rows r) {A B x : ℝ}
    (ha : PlusDomain A x) (hb : PlusDomain B x) (hAB : A≤B) :
    normalized r B x≤normalized r A x := by
  have hsource := SecondWord.OppositeZero.plus_target_antitone ha.2.1 ha.1 hb.1 hAB
  have hsourceD := Positive.ratioD_monotone hb.2.2 ha.2.2 hsource
  have htargetD := Positive.ratioD_monotone ha.1 hb.1 hAB
  have hDa := ShortOuterOne.SameContact.ratioD_pos (outer_domain ha.1)
  have hDb := ShortOuterOne.SameContact.ratioD_pos (outer_domain hb.1)
  have hDsA := ShortOuterOne.SameContact.ratioD_pos (outer_domain ha.2.2)
  have hDsB := ShortOuterOne.SameContact.ratioD_pos (outer_domain hb.2.2)
  have hR : ratioD (plus B x)/ratioD B≤ratioD (plus A x)/ratioD A :=
    (div_le_div_of_nonneg_right hsourceD hDb.le).trans
      (div_le_div_of_nonneg_left hDsA.le hDa htargetD)
  have hR0 : 0≤ratioD (plus B x)/ratioD B := div_nonneg hDsB.le hDb.le
  have hratio := Positive.ratio_monotone ha.1 hb.1 hAB
  have hsin := (positive_trig ha.2.1).2.2.1
  have hratioSin := mul_le_mul_of_nonneg_right hratio hsin
  have hK : plusK B x≤plusK A x := by
    dsimp [plusK,SecondWord.OppositeZero.plusK]
    linarith
  have hKB := (SecondWord.OppositeZero.positive_data hb.1 hb.2.1).2.2.1
  have hKs := pow_le_pow_left₀ hKB.le hK 2
  have hprod := mul_le_mul hR hKs (sq_nonneg _) (div_nonneg hDsA.le hDa.le)
  have hp : 0≤-p r := by rcases hr with rfl | rfl <;> norm_num [p]
  have hweighted := mul_le_mul_of_nonneg_left hprod hp
  have hL := l_monotone r hr hb.2.2 ha.2.2 hsource
  have hLs := mul_le_mul_of_nonneg_right hL hsin
  dsimp [normalized]
  nlinarith

lemma entry_first_positive (r : Row) (hr : Rows r) {B x : ℝ}
    (hd : PlusDomain B x) (he : B=0 ∨ plus B x=outerDiagonal) :
    0<plusTarget r B x := by
  have hB := initial_target_coordinate hd he
  have hratio := Positive.ratio_monotone hd.1 low_mem hB
  have hratioU : ratio B<(319/1000:ℝ) := hratio.trans_lt low_ratio
  have hsourceR := SecondWord.outer_ratio_bounds hd.2.2
  have hp : 0≤-p r ∧ 0≤v r := by
    rcases hr with rfl | rfl <;> norm_num [p,v]
  have hL : l r (plus B x)≤q r-p r := by
    have hh := mul_le_mul_of_nonneg_left hsourceR.2.1 hp.1
    dsimp [l]
    nlinarith
  have hL0 : 0≤l r (plus B x) := by linarith [(slope_bounds r hd.2.2).1]
  have hproj := mul_le_mul_of_nonneg_left (target_projection_upper hd) hL0
  have htarget := mul_le_mul_of_nonneg_left hratioU.le hp.2
  have href : 0<t r-v r*(319/1000)-(q r-p r) := by
    rcases hr with rfl | rfl <;> norm_num [t,v,q,p]
  dsimp [plusTarget,h]
  nlinarith

/-- A stationary target coordinate cannot have nonnegative second derivative. -/
theorem stationary_curvature_negative (r : Row) (hr : Rows r) {B x : ℝ}
    (hd : PlusDomain B x) (hstat : plusTarget r B x=0) :
    plusTargetCurvature r B x<0 := by
  by_contra! hcurv
  obtain ⟨a,ha,had,hentry,hdom⟩ := lower_entry hd
  have hD := ShortOuterOne.SameContact.ratioD_pos (outer_domain hd.1)
  have hN : 0≤normalized r B x := by
    rw [normalized_identity r hd] at hcurv
    exact nonneg_of_mul_nonneg_left hcurv hD
  have hcurvature {C : ℝ} (hC : C∈Icc a B) : 0≤plusTargetCurvature r C x := by
    have hCd := hdom C hC
    have hm := normalized_antitone r hr hCd hd hC.2
    rw [normalized_identity r hCd]
    exact mul_nonneg (hN.trans hm)
      (ShortOuterOne.SameContact.ratioD_pos (outer_domain hCd.1)).le
  have hm : MonotoneOn (fun C => plusTarget r C x) (Icc a B) :=
    monoOn_of_hasDeriv_nonneg
      (fun C hC => (plusTarget_hasDerivAt r (hdom C hC)).continuousAt.continuousWithinAt)
      (fun C hC => plusTarget_hasDerivAt r (hdom C (Ioo_subset_Icc_self hC)))
      (fun C hC => hcurvature (Ioo_subset_Icc_self hC))
  have hh := hm ⟨le_rfl,ha.2⟩ ⟨ha.2,le_rfl⟩ ha.2
  have hpositive := entry_first_positive r hr had hentry
  simp only at hh
  rw [hstat] at hh
  linarith

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Shape
end
end
end

section
/-!
## The original stationary projection for opposite-sign zero contacts

The source coordinate, the target circle and the contact speed are kept together. Angular
stationarity determines the sum of the two shifted target coordinates (`actual_sum`); the two
coordinates are not treated as independent interval variables.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Stationary
open CommonQuarter CorePairGeometry Arithmetic WrongWordCircleSupport
open ShortOuterOne.SameContact (arc ratio ratioD)
open SecondWord (U W outer_domain outer_zero_mem U_positive UW_circle)

def z (b : ℝ) : ℝ := 1/2-b
def mass (r : Row) (b : ℝ) : ℝ := (z b)^2+1/(l r b)^2
def sumCoordinate (r : Row) (b : ℝ) : ℝ := (Q0+2-mass r b)/2
def G (r : Row) (b : ℝ) : ℝ := z b-p r*ratioD b/(l r b)^3
def angleSecond (r : Row) (B x : ℝ) : ℝ :=
  -p r*ratioD (plus B x)*(plusSpeed B x)^2-l r (plus B x)*(plus B x-1/2)

lemma l_positive (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : 0<l r b := by
  linarith [(slope_bounds r hb).1]

lemma mass_positive (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : 0< mass r b := by
  have hl := l_positive r hb
  dsimp [mass]
  positivity

lemma plusAngle_hasDerivAt (r : Row) {B x : ℝ} (hd : PlusDomain B x) :
    HasDerivAt (plusAngle r B) (angleSecond r B x) x := by
  have hl : HasDerivAt (fun y => l r (plus B y)) (-p r*ratioD (plus B x)*(-plusSpeed B x)) x :=
    (l_hasDerivAt r hd.2.2).comp x (SecondWord.OppositeZero.plus_hasDerivAt B x)
  have h := (hl.fun_mul (SecondWord.OppositeZero.plusSpeed_hasDerivAt B x)).const_sub 1
  have he : plusAngle r B=fun y => 1-l r (plus B y)*plusSpeed B y := rfl
  rw [he]
  convert h using 1
  simp only [angleSecond]
  ring

lemma angleSecond_continuousAt (r : Row) {B x : ℝ} (hd : PlusDomain B x) :
    ContinuousAt (angleSecond r B) x := by
  have hb := (SecondWord.OppositeZero.plus_hasDerivAt B x).continuousAt
  have hv := (SecondWord.OppositeZero.plusSpeed_hasDerivAt B x).continuousAt
  have hD := (ShortOuterOne.SameContact.ratioD_hasDerivAt
    (outer_domain hd.2.2)).continuousAt.comp (x := x) hb
  have hL := (l_hasDerivAt r hd.2.2).continuousAt.comp (x := x) hb
  show ContinuousAt (fun y => -p r*ratioD (plus B y)*(plusSpeed B y)^2-
    l r (plus B y)*(plus B y-1/2)) x
  exact ((continuousAt_const.mul hD).mul (hv.pow 2)).sub
    (hL.mul (hb.sub continuousAt_const))

lemma angular_speed (r : Row) {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusAngle r B x=0) : plusSpeed B x=1/l r (plus B x) := by
  have hl := l_positive r hd.2.2
  dsimp [plusAngle] at hstat
  apply (eq_div_iff hl.ne').2
  nlinarith

lemma actual_mass (r : Row) {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusAngle r B x=0) :
    mass r (plus B x)=Q0+2-2*(U B+W B) := by
  have hn := SecondWord.OppositeZero.plus_norm hd.1 x
  have hs : SecondWord.OppositeZero.plusSpeed B x=1/l r (plus B x) := angular_speed r hd hstat
  rw [hs] at hn
  simp only [mass,z,U,W]
  linear_combination hn

lemma actual_sum (r : Row) {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusAngle r B x=0) : sumCoordinate r (plus B x)=U B+W B := by
  rw [sumCoordinate,actual_mass r hd hstat]
  ring

lemma actual_second (r : Row) {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusAngle r B x=0) :
    angleSecond r B x=l r (plus B x)*G r (plus B x) := by
  have hl := l_positive r hd.2.2
  rw [angleSecond,angular_speed r hd hstat]
  dsimp [G,z]
  field_simp [hl.ne']
  ring

lemma projection_identity {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    U B*(Q0+2-2*(U B+W B))*plusK B x=
      (Q0-(U B+W B))*plusSpeed B x+(W B-U B)*z (plus B x) := by
  have hu := U_positive (outer_domain hB)
  have hc := UW_circle (outer_domain hB)
  have hK : U B*plusK B x=U B*Real.cos x-W B*Real.sin x := by
    change U B*(Real.cos x-(W B/U B)*Real.sin x)=_
    field_simp
  have he : U B*(Q0+2-2*(U B+W B))*plusK B x=(Q0+2-2*(U B+W B))*(U B*plusK B x) := by ring
  rw [he,hK]
  simp only [plusSpeed,SecondWord.OppositeZero.plusSpeed,z,plus,SecondWord.OppositeZero.plus,
    U,W] at hc ⊢
  linear_combination (-(Real.cos x-Real.sin x))*hc

/-- The two original projection equations give the target derivative. -/
lemma actual_target (r : Row) {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusAngle r B x=0) :
    plusTarget r B x=t r-v r*ratio B-
      (Q0-(U B+W B))/(U B*mass r (plus B x))-
      (ratio B-1)*z (plus B x)*l r (plus B x)/mass r (plus B x) := by
  have hl := l_positive r hd.2.2
  have hu := U_positive (outer_domain hd.1)
  have hm := mass_positive r hd.2.2
  have hp := projection_identity hd.1 (x := x)
  rw [←actual_mass r hd hstat,angular_speed r hd hstat] at hp
  have hK : plusK B x=((Q0-(U B+W B))*(1/l r (plus B x))+(W B-U B)*z (plus B x))/
      (U B*mass r (plus B x)) := by
    rw [eq_div_iff (mul_pos hu hm).ne']
    linarith [hp]
  simp only [plusTarget,h]
  rw [hK]
  have hr : ratio B=W B/U B := rfl
  rw [hr]
  field_simp
  ring

lemma original_sum_lower {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    outerAxial+1≤U B+W B := by
  have hs := ShortOuterOne.SameContact.arc_state hB
  have hh := outer_concave_lower hs (by norm_num : (0:ℝ)≤1)
    (one_mul outerAxial).ge
    (show outerAxial≤(1+1)*outerDiagonal by
      linarith [outer_endpoint_bounds.2.1,outer_endpoint_bounds.2.2.1])
  dsimp [U,W]
  linarith

/-- Positive squaring of the target circle and its ordered coordinates. -/
lemma original_U_lower {B S₀ u₀ : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hS : U B+W B≤S₀) (hsum : u₀≤U B+W B)
    (hcheck : S₀^2-2*u₀*S₀+2*u₀^2<Q0) : u₀<U B := by
  have hc := UW_circle (outer_domain hB)
  have hs := ShortOuterOne.SameContact.arc_state hB
  have huv : W B≤U B := by dsimp [U,W]; linarith [hs.2.1]
  by_contra! hbad
  have hp := mul_nonneg (sub_nonneg.mpr hbad)
    (sub_nonneg.mpr (huv.trans hbad))
  have hq := mul_nonneg (sub_nonneg.mpr hS)
    (show 0≤S₀+(U B+W B)-2*u₀ by linarith)
  nlinarith

lemma angular_nonnegative_source (r : Row) (hr : r=1 ∨ r=4) {b : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hG : 0≤G r b) : 0<z b := by
  have hp : 0<p r := by rcases hr with rfl | rfl <;> norm_num [p]
  have hD := ShortOuterOne.SameContact.ratioD_pos (outer_domain hb)
  have hl := l_positive r hb
  have hquot := div_pos (mul_pos hp hD) (pow_pos hl 3)
  dsimp [G] at hG
  linarith

lemma target_lower (r : Row) (hr : r=1 ∨ r=4) {B x : ℝ}
    (hd : PlusDomain B x) (hstat : plusAngle r B x=0)
    (hG : 0≤G r (plus B x)) :
    t r-v r*ratio B-(Q0-(U B+W B))/(U B*mass r (plus B x))≤plusTarget r B x := by
  have hz := angular_nonnegative_source r hr hd.2.2 hG
  have hl := l_positive r hd.2.2
  have hm := mass_positive r hd.2.2
  have hratio := (SecondWord.outer_ratio_bounds hd.1).2.1
  have hprod : (ratio B-1)*z (plus B x)*l r (plus B x)/mass r (plus B x)≤0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) hz.le) hl.le) hm.le
  rw [actual_target r hd hstat]
  linarith

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Stationary
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Stationary
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open SecondWord (U W outer_domain outer_zero_mem U_positive UW_circle)

lemma source_slope_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    l 1 b<(10033/10000:ℝ) ∧ l 4 b<(213/200:ℝ) := by
  have hr := (SecondWord.outer_ratio_bounds hb).1
  norm_num [l,q,p]
  constructor <;> linarith

lemma fine_target_ratio {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (5223/20000:ℝ)<ratio B := by
  have hh := Positive.ratio_monotone outer_zero_mem hB hB.1
  rw [Same.Axial.zero_ratio] at hh
  exact Same.PositiveCoefficient.rho_bounds.1.trans_le hh

lemma target_sum_lower {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (2414575671/1000000000:ℝ)<U B+W B := by
  linarith [original_sum_lower hB,ShortOuterZero.fine_axial_bounds.1]

lemma reciprocal_lower {L U₀ M : ℝ} (hL : 0<L) (hU : L<U₀)
    (hM : 0≤M) (hcheck : M*U₀^2<1) : M<1/L^2 := by
  apply (lt_div_iff₀ (pow_pos hL 2)).2
  have hs := pow_le_pow_left₀ hL.le hU.le 2
  have hm := mul_le_mul_of_nonneg_left hs hM
  nlinarith

lemma row_one_mass {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (993/1000:ℝ)< mass 1 b := by
  have hi := reciprocal_lower (l_positive 1 hb) (source_slope_upper hb).1
    (by norm_num : (0:ℝ)≤993/1000) (by norm_num)
  dsimp [mass]
  linarith [sq_nonneg (z b)]

lemma fifth_mem : (1/5:ℝ)∈Icc 0 outerDiagonal :=
  ⟨by norm_num,by linarith [outer_endpoint_bounds.2.2.1]⟩

lemma fifth_references : (617/1000:ℝ)<ratioD (1/5) ∧ l 4 (1/5)<201/200 := by
  have hc := UW_circle (outer_domain fifth_mem)
  have hu := U_positive (outer_domain fifth_mem)
  have hU : (37/20:ℝ)<U (1/5) ∧ U (1/5)<1851/1000 := by
    norm_num [W,Q0] at hc
    constructor <;> nlinarith
  have hR : (189/500:ℝ)<ratio (1/5) := by
    change (189/500:ℝ)<((1/5:ℝ)+1/2)/U (1/5)
    apply (lt_div_iff₀ hu).2
    linarith [hU.2]
  have hD : (617/1000:ℝ)<ratioD (1/5) := by
    change (617/1000:ℝ)<Q0/(U (1/5))^3
    apply (lt_div_iff₀ (pow_pos hu 3)).2
    have hh := pow_le_pow_left₀ hu.le hU.2.le 3
    norm_num [Q0] at *
    nlinarith
  exact ⟨hD,by norm_num [l,p,q]; linarith⟩

/-- The sign condition `0 ≤ G 4 b` excludes the whole source interval `[1/5,d]`. -/
lemma row_four_source {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (hG : 0≤G 4 b) : b<1/5 := by
  by_contra! hlarge
  have hR := Positive.ratio_monotone fifth_mem hb hlarge
  have hD := Positive.ratioD_monotone fifth_mem hb hlarge
  have hL : l 4 b<201/200 := by
    have hh : l 4 b≤l 4 (1/5) := by norm_num [l,p,q] at *; linarith
    exact hh.trans_lt fifth_references.2
  have hl := l_positive 4 hb
  have hlpow := pow_le_pow_left₀ hl.le hL.le 3
  have hdlo : (617/1000:ℝ)<ratioD b := fifth_references.1.trans_le hD
  have hquot : (3/10:ℝ)<p 4*ratioD b/(l 4 b)^3 := by
    apply (lt_div_iff₀ (pow_pos hl 3)).2
    norm_num [p]
    nlinarith
  dsimp [G,z] at hG
  linarith

lemma row_four_mass {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (hG : 0≤G 4 b) :
    (19433/20000:ℝ)< mass 4 b := by
  have hcut := row_four_source hb hG
  have hz : (3/10:ℝ)<z b := by dsimp [z]; linarith
  have hi := reciprocal_lower (l_positive 4 hb) (source_slope_upper hb).2
    (by norm_num : (0:ℝ)≤17633/20000) (by norm_num)
  dsimp [mass]
  nlinarith

lemma actual_U_one {B x : ℝ} (hd : PlusDomain B x) (hstat : plusAngle 1 B x=0) :
    (189/100:ℝ)<U B := by
  have hm := row_one_mass hd.2.2
  have he := actual_sum 1 hd hstat
  have hS : U B+W B≤(Q0+2-993/1000)/2 := by
    dsimp [sumCoordinate] at he
    linarith
  exact original_U_lower hd.1 hS (by linarith [target_sum_lower hd.1])
    (by norm_num [Q0])

lemma actual_U_four {B x : ℝ} (hd : PlusDomain B x) (hstat : plusAngle 4 B x=0)
    (hG : 0≤G 4 (plus B x)) : (9459/5000:ℝ)<U B := by
  have hm := row_four_mass hd.2.2 hG
  have he := actual_sum 4 hd hstat
  have hS : U B+W B≤(Q0+2-19433/20000)/2 := by
    dsimp [sumCoordinate] at he
    linarith
  exact original_U_lower hd.1 hS (by linarith [target_sum_lower hd.1])
    (by norm_num [Q0])

lemma fraction_upper (r : Row) {B x u₀ m₀ : ℝ} (hd : PlusDomain B x)
    (hu₀ : 0<u₀) (hm₀ : 0< m₀) (hu : u₀≤U B) (hm : m₀≤ mass r (plus B x)) :
    (Q0-(U B+W B))/(U B*mass r (plus B x))≤
      (Q0-2414575671/1000000000)/(u₀*m₀) := by
  have hden := mul_le_mul hu hm hm₀.le (U_positive (outer_domain hd.1)).le
  have hpos := mul_pos (U_positive (outer_domain hd.1)) (mass_positive r hd.2.2)
  have hn : Q0-(U B+W B)≤Q0-2414575671/1000000000 := by
    linarith [target_sum_lower hd.1]
  exact (div_le_div_of_nonneg_right hn hpos.le).trans
    (div_le_div_of_nonneg_left (by norm_num [Q0]) (mul_pos hu₀ hm₀) hden)

lemma row_one_target_positive {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusAngle 1 B x=0) (hG : 0≤G 1 (plus B x)) :
    (147/1000:ℝ)<plusTarget 1 B x := by
  have hl := target_lower 1 (Or.inl rfl) hd hstat hG
  have hf := fraction_upper 1 hd (by norm_num : (0:ℝ)<189/100)
    (by norm_num : (0:ℝ)<993/1000) (actual_U_one hd hstat).le (row_one_mass hd.2.2).le
  have he : (147/1000:ℝ)<t 1-
      (Q0-2414575671/1000000000)/((189/100)*(993/1000)) := by norm_num [t,Q0]
  norm_num [v] at hl
  linarith

lemma row_four_target_positive {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusAngle 4 B x=0) (hG : 0≤G 4 (plus B x)) :
    (67/50000:ℝ)<plusTarget 4 B x := by
  have hl := target_lower 4 (Or.inr rfl) hd hstat hG
  have hf := fraction_upper 4 hd (by norm_num : (0:ℝ)<9459/5000)
    (by norm_num : (0:ℝ)<19433/20000) (actual_U_four hd hstat hG).le
    (row_four_mass hd.2.2 hG).le
  have hr := fine_target_ratio hd.1
  have he : (67/50000:ℝ)<t 4-v 4*(5223/20000)-
      (Q0-2414575671/1000000000)/((9459/5000)*(19433/20000)) := by norm_num [t,v,Q0]
  norm_num [t,v,Q0] at hl he hf
  linarith

/-- Both positive-p rows have a descent at every angular stationary point. -/
theorem stationary_descent (r : Row) (hr : r=1 ∨ r=4) {B x : ℝ}
    (hd : PlusDomain B x) (hstat : plusAngle r B x=0) :
    angleSecond r B x<0 ∨ 0<plusTarget r B x := by
  by_cases hG : 0≤G r (plus B x)
  · right
    rcases hr with rfl | rfl
    · linarith [row_one_target_positive hd hstat hG]
    · linarith [row_four_target_positive hd hstat hG]
  · left
    rw [actual_second r hd hstat]
    exact mul_neg_of_pos_of_neg (l_positive r hd.2.2) (lt_of_not_ge hG)

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Stationary
end
end
end

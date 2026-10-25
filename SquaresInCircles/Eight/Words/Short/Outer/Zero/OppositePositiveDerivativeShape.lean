module

public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositePositiveInteriorGeometry

/-!
# Eight squares: the two target-derivative-shape rows

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

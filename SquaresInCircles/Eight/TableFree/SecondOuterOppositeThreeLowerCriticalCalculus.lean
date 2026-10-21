module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerCriticalData

/-!
# Weighted one-variable derivatives of the actual critical cost

The positive weight is the derivative of the recovered original
source coordinate.  Stationarity cancels only the free-coordinate
term; the remaining first, second and third source derivatives are
proved from the explicit radical parameterization.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerCritical
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open LowerInverse LowerEnvelope

lemma phase_hasDerivAt {B : ℝ} (hB : Domain B) :
    HasDerivAt (fun t => LowerInverse.phase (z t) (source t))
      (1/LowerInverse.speed (z B) (source B)+
        LowerInverse.first (z B) (source B)*sourceD B) B := by
  have hb := source_domain hB
  have hz := shift_mem hB.1
  have hd := OppositeTwo.PrimaryInverse.data hb hz
  have hr : 0<LowerInverse.radius (source B) := by linarith [hd.1]
  have hv := hd.2.2.1
  have ha := OppositeTwo.PrimaryInverse.argument_bounds hb hz
  have hs := source_hasDerivAt hB.1
  have hrad := (NegativeTwo.ContactInverse.radius_hasDerivAt hb).comp B hs
  have harg := (z_hasDerivAt B).div hrad hr.ne'
  have hbeta := (Real.hasDerivAt_arcsin
    (by linarith : z B/LowerInverse.radius (source B)≠-1)
    (by linarith : z B/LowerInverse.radius (source B)≠1)).comp B harg
  have hbase := (NegativeTwo.ContactInverse.base_hasDerivAt hb).comp B hs
  convert hbase.neg.add hbeta using 1
  · rfl
  · rw [OppositeTwo.PrimaryInverse.inverse_root hb hz]
    dsimp [LowerInverse.first]
    rw [←hd.2.1]
    field_simp [hr.ne',hv.ne']
    ring

lemma cost_hasDerivAt {B : ℝ} (hB : Domain B) : HasDerivAt cost (first B*sourceD B) B := by
  have hs := source_hasDerivAt hB.1
  have hb := source_domain hB
  have hphase := phase_hasDerivAt hB
  have hcost := ((hphase.const_add (Real.pi/2)).sub
    (LLabel.outer_hasDerivAt (outer_domain (mem_outer hB.1)))).sub
      ((TLabel.outer_hasDerivAt (outer_domain hb)).comp B hs)
  have hstat := stationary hB.1
  have hfirst := actual_first hB.1
  convert hcost using 1
  · funext t
    dsimp [cost,LowerContact.cost,LowerContact.inner,LowerContact.outer,z]
  · change first B*sourceD B=
      (1/LowerInverse.speed (z B) (source B)+LowerInverse.first (z B) (source B)*sourceD B)-
        p B-TLabel.d1 (source B)*sourceD B
    change 1/LowerInverse.speed (z B) (source B)-p B=0 at hstat
    change LowerInverse.first (z B) (source B)-TLabel.d1 (source B)=first B at hfirst
    nlinarith

lemma first_hasDerivAt {B : ℝ} (hB : Domain B) :
    HasDerivAt first (second B*sourceD B) B := by
  have hb := source_domain hB
  have hs := source_hasDerivAt hB.1
  have hu := U_positive (outer_domain hb)
  have hq : 0<q (U (source B)) := by linarith [NegativeTwo.Inverse.actual_q_positive hb]
  have hU := ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)).comp B hs
  have hf := (NegativeTwo.Inverse.factor_hasDerivAt hu.ne' hq.ne').comp B hU
  have hr := (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).comp B hs
  have hg := g₁_hasDerivAt (mem_short hB.1)
  have ht := (TLabel.d1_hasDerivAt (outer_domain hb)).comp B hs
  have hder := (hf.add ((hr.const_mul 2).mul hg)).sub ht
  convert hder using 1
  · rfl
  · have he := source_ratio_identity hB.1
    dsimp [second]
    linear_combination 4*ratio (source B)*g₂ B*he

lemma second_hasDerivAt {B : ℝ} (hB : Domain B) :
    HasDerivAt second (third B*sourceD B) B := by
  have hb := source_domain hB
  have hs := source_hasDerivAt hB.1
  have hu := U_positive (outer_domain hb)
  have hq : 0<q (U (source B)) := by linarith [NegativeTwo.Inverse.actual_q_positive hb]
  have hU := ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)).comp B hs
  have hr := (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).comp B hs
  have hrD := (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hb)).comp B hs
  have hfD := (LowerInverse.factorD_hasDerivAt hu.ne' hq.ne').comp B hU
  have hg₁ := g₁_hasDerivAt (mem_short hB.1)
  have hg₂ := g₂_hasDerivAt (mem_short hB.1)
  have ht := (TLabel.d2_hasDerivAt (outer_domain hb)).comp B hs
  have hder := ((((hr.neg.mul hfD).add (((hr.pow 2).const_mul 4).mul hg₂)).
    add ((hrD.const_mul 2).mul hg₁)).sub ht)
  convert hder using 1
  · rfl
  · have he := source_ratio_identity hB.1
    dsimp [third,LowerInverse.X]
    linear_combination (8*(ratio (source B))^2*g₃ B+4*ratioD (source B)*g₂ B)*he

theorem third_negative {B : ℝ} (hB : Domain B) : third B<0 := by
  have hb := source_domain hB
  have hX := LowerSource.X_upper hB.2
  have hT := T_third_lower hb
  have hg₁ := envelope_first_negative hB.1
  have hg₂ := envelope_second_upper hB.1
  have hg₃ := envelope_third_negative hB.1
  have hr : 0<ratio (source B) := by linarith [(outer_ratio_bounds hb).1]
  have hrd := ShortOuterOne.SameContact.ratioD_pos (outer_domain hb)
  have hrdd : 0<ratioDD (source B) := by
    have hu := U_positive (outer_domain hb)
    have hw : 0<source B+1/2 := by linarith [hB.2.1]
    dsimp [ratioDD]
    norm_num [Q0]
    positivity
  have hs := S_positive (mem_outer hB.1)
  have hratio := LowerSource.ratio_product_upper hB.2
  rw [source_q hB.1] at hratio
  have hweight : 0<ratio (source B)*ratioD (source B)/(S B)^2 := by positivity
  have hp := mul_lt_mul_of_pos_left hg₂ hweight
  have hq := mul_lt_mul_of_pos_right hratio (by norm_num : (0:ℝ)<63/200)
  have he : (ratio (source B)*ratioD (source B)/(S B)^2)*((S B)^2*g₂ B)=
      ratio (source B)*ratioD (source B)*g₂ B := by field_simp [hs.ne']; ring
  rw [he] at hp
  have hneg₁ : 8*(ratio (source B))^3*g₃ B≤0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hg₃.le
  have hneg₂ : 2*ratioDD (source B)*g₁ B≤0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hg₁.le
  dsimp [third]
  nlinarith

lemma second_antitone_between {l u : ℝ} (hl : Domain l) (hu : Domain u) :
    AntitoneOn second (Icc l u) :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (second_hasDerivAt (domain_between hl hu hB)).continuousAt.continuousWithinAt)
    (fun B hB => second_hasDerivAt (domain_between hl hu (Ioo_subset_Icc_self hB)))
    (fun B hB => mul_nonpos_of_nonpos_of_nonneg
      (third_negative (domain_between hl hu (Ioo_subset_Icc_self hB))).le
      (sourceD_positive (domain_between hl hu (Ioo_subset_Icc_self hB)).1).le)

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerCritical

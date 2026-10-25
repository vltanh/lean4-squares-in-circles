module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerCriticalRootReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerSourceShape

/-!
# Eight squares: weighted one-variable derivatives of the actual critical cost

The positive weight is the derivative of the recovered original
source coordinate.  Stationarity cancels only the free-coordinate
term; the remaining first, second and third source derivatives are
proved from the explicit radical parameterization.
-/

section
/-!
## The three uniform envelope derivative estimates

The positive relation `D > 3 S / 2` preserves the stationary equation's
dependence and proves the third derivative sign on the full target
interval.  No source partition enters the argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerEnvelope
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)

lemma envelope_first_negative {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : g₁ B<0 := by
  have hh : 0<h B := by linarith [(product_bounds hB).1]
  have hs := S_positive (mem_outer hB)
  dsimp [g₁]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hh) (by positivity)

lemma envelope_second_upper {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    (S B)^2*g₂ B<(63/200:ℝ) := by
  have hs := S_positive (mem_outer hB)
  have hd := D_positive (mem_short hB)
  have hlarge := D_large hB
  have hh := (product_bounds hB).2
  have hj := (product_first_bounds hB).1
  have he : 4*D B*((S B)^2*g₂ B)=2*D B*h B-h₁ B*S B := by
    dsimp [g₂]
    field_simp [hs.ne',hd.ne']
    ring
  have hp := mul_lt_mul_of_pos_left hh (show 0<2*D B by positivity)
  have hq := mul_lt_mul_of_pos_right hj hs
  have hpay : 4*D B*((S B)^2*g₂ B)<4*D B*(63/200) := by
    linarith
  exact lt_of_mul_lt_mul_left hpay (by positivity)

lemma envelope_third_negative {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : g₃ B<0 := by
  have hs := S_positive (mem_outer hB)
  have hd := D_positive (mem_short hB)
  have hlarge := D_large hB
  have hdlo : (159/100:ℝ)<D B := by linarith [(S_bounds hB).1]
  have hv : S B/D B∈Icc (0:ℝ) (2/3) := by
    constructor
    · exact (div_pos hs hd).le
    · apply (div_le_iff₀ hd).2
      linarith
  have hi : 1/D B∈Icc (0:ℝ) (100/159) := by
    constructor
    · positivity
    · apply (div_le_iff₀ hd).2
      linarith
  let V : Interval (S B/D B) := Interval.of_bounds hv
  let I : Interval (1/D B) := Interval.of_bounds hi
  let H : Interval (h B) := Interval.of_bounds ⟨(product_bounds hB).1.le,(product_bounds hB).2.le⟩
  let J : Interval (h₁ B) := Interval.of_bounds
    ⟨(product_first_bounds hB).1.le,(product_first_bounds hB).2.le⟩
  let K : Interval (h₂ B) := Interval.of_bounds
    ⟨(product_second_bounds hB).1.le,(product_second_bounds hB).2.le⟩
  let E : Interval (D₁ B) := Interval.of_bounds ⟨(D_first_bounds hB).1.le,(D_first_bounds hB).2.le⟩
  let Z₀ := ((((Interval.point (-1/8)).mul K).mul V.square).add
    (((Interval.point (1/2)).mul J).mul V)).add
      (((((Interval.point (1/8)).mul J).mul E).mul I).mul V.square)
  let Z := Z₀.sub H
  have hz : Z.hi<0 := by
    norm_num [Z,Z₀,V,I,H,J,K,E,Interval.point,Interval.of_bounds,Interval.mul,
      Interval.square,Interval.add,Interval.sub]
  have he : (S B)^3*g₃ B=
      (-1/8)*h₂ B*(S B/D B)^2+(1/2)*h₁ B*(S B/D B)+
        (1/8)*h₁ B*D₁ B*(1/D B)*(S B/D B)^2-h B := by
    dsimp [g₃]
    field_simp [hs.ne',hd.ne']
  have hnegative : (S B)^3*g₃ B<0 := by rw [he]; exact Z.mem.2.trans_lt hz
  by_contra hn
  have hp := mul_nonneg (pow_nonneg hs.le 3) (le_of_not_gt hn)
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerEnvelope
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerCritical
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
  have hv : 0<LowerInverse.speed (z B) (source B) := hd.2.2.1
  have hr2 : (LowerInverse.radius (source B))^2=q (U (source B)) := hd.2.1
  have ha := OppositeTwo.PrimaryInverse.argument_bounds hb hz
  have hs := source_hasDerivAt hB.1
  have hrad := (NegativeTwo.ContactInverse.radius_hasDerivAt hb).comp B hs
  have harg := (z_hasDerivAt B).fun_div hrad hr.ne'
  have hbeta := (Real.hasDerivAt_arcsin
    (by linarith : z B/LowerInverse.radius (source B)≠-1)
    (by linarith : z B/LowerInverse.radius (source B)≠1)).comp B harg
  have hbase := (NegativeTwo.ContactInverse.base_hasDerivAt hb).comp B hs
  have h : HasDerivAt (fun t => LowerInverse.phase (z t) (source t)) _ B :=
    hbase.fun_neg.fun_add hbeta
  refine h.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [OppositeTwo.PrimaryInverse.inverse_root hb hz]
  simp only [LowerInverse.first]
  rw [← hr2]
  have hr' := hr.ne'
  have hv' := hv.ne'
  field_simp
  ring

lemma cost_hasDerivAt {B : ℝ} (hB : Domain B) : HasDerivAt cost (first B*sourceD B) B := by
  have hs := source_hasDerivAt hB.1
  have hb := source_domain hB
  have hphase := phase_hasDerivAt hB
  have hT := (TLabel.outer_hasDerivAt (outer_domain hb)).comp B hs
  have hcost : HasDerivAt cost _ B := ((hphase.const_add (Real.pi/2)).fun_sub
    (LLabel.outer_hasDerivAt (outer_domain (mem_outer hB.1)))).fun_sub hT
  have hstat := stationary hB.1
  have hfirst := actual_first hB.1
  change 1/LowerInverse.speed (z B) (source B)-LLabel.d1 B=0 at hstat
  change LowerInverse.first (z B) (source B)-TLabel.d1 (source B)=first B at hfirst
  refine hcost.congr_deriv ?_
  linear_combination hstat+sourceD B*hfirst

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
  have hU : HasDerivAt (U ∘ source) (-ratio (source B)*sourceD B) B :=
    ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)).comp B hs
  have hr := (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).comp B hs
  have hrD := (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hb)).comp B hs
  have hfD := (LowerInverse.factorD_hasDerivAt hu.ne' hq.ne').comp B hU
  have hg₁ := g₁_hasDerivAt (mem_short hB.1)
  have hg₂ := g₂_hasDerivAt (mem_short hB.1)
  have ht := (TLabel.d2_hasDerivAt (outer_domain hb)).comp B hs
  have hder := ((((hr.neg.mul hfD).add (((hr.pow 2).const_mul 4).mul hg₂)).add
    ((hrD.const_mul 2).mul hg₁)).sub ht)
  convert hder using 1
  · rfl
  · have he := source_ratio_identity hB.1
    simp only [third,LowerInverse.X,Function.comp_apply,Pi.neg_apply,Pi.pow_apply,
      Nat.reduceSub,pow_one,Nat.cast_ofNat]
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
    have hQ : (0:ℝ)<Q0 := by norm_num [Q0]
    exact div_pos (mul_pos (mul_pos (by norm_num) hQ) hw) (pow_pos hu 5)
  have hs := S_positive (mem_outer hB.1)
  have hratio := LowerSource.ratio_product_upper hB.2
  rw [source_q hB.1] at hratio
  have hweight : 0<ratio (source B)*ratioD (source B)/(S B)^2 :=
    div_pos (mul_pos hr hrd) (pow_pos hs 2)
  have hp := mul_lt_mul_of_pos_left hg₂ hweight
  have hq := mul_lt_mul_of_pos_right hratio (by norm_num : (0:ℝ)<63/200)
  have he : (ratio (source B)*ratioD (source B)/(S B)^2)*((S B)^2*g₂ B)=
      ratio (source B)*ratioD (source B)*g₂ B := by field_simp [hs.ne']
  rw [he] at hp
  have hneg₁ : 8*(ratio (source B))^3*g₃ B≤0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) (pow_pos hr 3).le) hg₃.le
  have hneg₂ : 2*ratioDD (source B)*g₁ B≤0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hg₁.le
  simp only [third]
  linarith

lemma second_antitone_between {l u : ℝ} (hl : Domain l) (hu : Domain u) :
    AntitoneOn second (Icc l u) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hB => (second_hasDerivAt (domain_between hl hu hB)).continuousAt.continuousWithinAt)
    (fun _ hB => second_hasDerivAt (domain_between hl hu (Ioo_subset_Icc_self hB)))
    (fun _ hB => mul_nonpos_of_nonpos_of_nonneg
      (third_negative (domain_between hl hu (Ioo_subset_Icc_self hB))).le
      (sourceD_positive (domain_between hl hu (Ioo_subset_Icc_self hB)).1).le)

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerCritical
end
end
end

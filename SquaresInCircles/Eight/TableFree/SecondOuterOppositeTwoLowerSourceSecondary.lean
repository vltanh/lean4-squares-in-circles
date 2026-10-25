module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoAxial
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoUpperSourcePrimary

/-!
# The original lower source-secondary owner

The original target remains fixed while the source follows its
maximal allowed transverse contact.  Its paid angular derivative is
negative on the entire physical interval.  An intermediate-value
argument reaches the actual zero source, where the completed axial
bound applies.  No endpoint witness is assumed.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.LowerSecondary

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def sourceInterval : Set ℝ := Icc 0 (83/200)
def envelope (b : ℝ) : ℝ := Real.sqrt (Q0-(b+3/2)^2)
def product (b : ℝ) : ℝ := PLabel.d1 b*envelope b
def productD (b : ℝ) : ℝ :=
  PLabel.d2 b*envelope b-PLabel.d1 b*(b+3/2)/envelope b
def cost (A B x : ℝ) : ℝ := Real.pi/2-x-P (lowerCut A B x)-V B

lemma source_mem {b : ℝ} (hb : b∈sourceInterval) : b∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem ⟨hb.1,by linarith [hb.2]⟩

lemma envelope_data {b : ℝ} (hb : b∈sourceInterval) :
    0<envelope b ∧ (envelope b)^2+(b+3/2)^2=Q0 := by
  have hrad : 0<Q0-(b+3/2)^2 := by
    have hs := pow_le_pow_left₀ (show 0≤b+3/2 by linarith [hb.1])
      (show b+3/2≤(383/200:ℝ) by linarith [hb.2]) 2
    norm_num [Q0]
    nlinarith
  refine ⟨Real.sqrt_pos.mpr hrad,?_⟩
  have hh := Real.sq_sqrt hrad.le
  dsimp [envelope]
  linarith

lemma envelope_hasDerivAt {b : ℝ} (hb : b∈sourceInterval) :
    HasDerivAt envelope (-(b+3/2)/envelope b) b := by
  have hd := envelope_data hb
  have hrad : Q0-(b+3/2)^2≠0 := by nlinarith [sq_pos_of_pos hd.1]
  have hq := ((((hasDerivAt_id' b).add_const (3/2)).fun_pow 2).const_sub Q0).sqrt hrad
  refine hq.congr_deriv ?_
  have he : Real.sqrt (Q0-(b+3/2)^2)=envelope b := rfl
  rw [he]
  field_simp
  norm_num
  ring

lemma product_hasDerivAt {b : ℝ} (hb : b∈sourceInterval) :
    HasDerivAt product (productD b) b :=
  ((PLabel.d1_hasDerivAt (outer_domain (source_mem hb))).fun_mul
    (envelope_hasDerivAt hb)).congr_deriv (by dsimp [productD]; ring)

lemma productD_negative {b : ℝ} (hb : b∈sourceInterval) : productD b<0 := by
  have hd := envelope_data hb
  have h2 := P_second_small hb
  have h1 := P_first_lower_actual (source_mem hb)
  have hmain := mul_lt_mul_of_pos_right h2 (sq_pos_of_pos hd.1)
  have hlast := mul_le_mul h1.le
    (show (3/2:ℝ)≤b+3/2 by linarith [hb.1]) (by norm_num : (0:ℝ)≤3/2)
    (by linarith : 0≤PLabel.d1 b)
  have henv : (envelope b)^2≤Q0-9/4 := by
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/2)
      (show (3/2:ℝ)≤b+3/2 by linarith [hb.1]) 2
    nlinarith [hd.2]
  have he : productD b*envelope b=
      PLabel.d2 b*(envelope b)^2-PLabel.d1 b*(b+3/2) := by
    dsimp [productD]
    field_simp [hd.1.ne']
  norm_num [Q0] at henv
  nlinarith

lemma product_antitone : AntitoneOn product sourceInterval :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (product_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun b hb => product_hasDerivAt (Ioo_subset_Icc_self hb))
    (fun b hb => (productD_negative (Ioo_subset_Icc_self hb)).le)

lemma product_zero : product 0<1 := by
  have hP := P_first_zero
  have he : envelope 0=bOne+1/2 := by
    norm_num [envelope,bOne,arc]
  have hp := (envelope_data (show (0:ℝ)∈sourceInterval by norm_num [sourceInterval])).1
  have hm := mul_lt_mul_of_pos_right hP hp
  dsimp [product]
  rw [he] at *
  nlinarith [bOne_bounds.2]

lemma product_paid {b : ℝ} (hb : b∈sourceInterval) : product b<1 :=
  (product_antitone (by norm_num [sourceInterval]) hb hb.1).trans_lt product_zero

lemma cut_eq {A B : ℝ} (ht : OuterState A B) (x : ℝ) :
    lowerCut A B x= -NegativeTwo.TargetContact.B B x := by
  dsimp [lowerCut,NegativeTwo.TargetContact.B]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  ring

lemma cut_zero (A B : ℝ) : lowerCut A B 0=A-1 := by norm_num [lowerCut]; ring

lemma cut_antitone {A B : ℝ} (ht : OuterState A B) :
    AntitoneOn (lowerCut A B) (Icc 0 (7/10)) := by
  intro s hs t ht' hst
  rw [cut_eq ht s,cut_eq ht t]
  exact neg_le_neg (NegativeTwo.TargetContact.B_angle_monotone
    ⟨ht.1,(outer_bounds ht).2.2⟩ hs ht' hst)

lemma cut_upper {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10)) :
    lowerCut A B x≤A-1 := by
  have hh := cut_antitone ht (by norm_num) hx hx.1
  simpa [cut_zero] using hh

lemma cut_mem {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hcut : 0≤lowerCut A B x) : lowerCut A B x∈sourceInterval := by
  refine ⟨hcut,?_⟩
  linarith [cut_upper ht hx,(outer_bounds ht).2.1,outer_endpoint_bounds.2.1]

lemma cut_hasDerivAt {A B : ℝ} (ht : OuterState A B) (x : ℝ) :
    HasDerivAt (lowerCut A B) (-NegativeTwo.TargetContact.v B x) x := by
  have hf : lowerCut A B=fun t => -NegativeTwo.TargetContact.B B t := funext (cut_eq ht)
  rw [hf]
  exact (NegativeTwo.TargetContact.B_angle_hasDerivAt B x).neg

lemma speed_paid {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hcut : 0≤lowerCut A B x) :
    PLabel.d1 (lowerCut A B x)*NegativeTwo.TargetContact.v B x<1 := by
  have hb : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2⟩
  have hc := cut_mem ht hx hcut
  have henv := envelope_data hc
  have hv := NegativeTwo.TargetContact.v_positive hb hx
  have hn := NegativeTwo.TargetContact.norm_identity hb x
  have hcutupper := cut_upper ht hx
  have he : NegativeTwo.TargetContact.B B x= -lowerCut A B x := by
    linarith [cut_eq ht x]
  rw [he] at hn
  have hU : U B=A+1/2 := by
    dsimp [U]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  rw [hU] at hn
  dsimp [NegativeTwo.Inverse.q] at hn
  have hspeed : NegativeTwo.TargetContact.v B x≤envelope (lowerCut A B x) := by
    nlinarith [henv.2]
  have hm := mul_le_mul_of_nonneg_left hspeed
    (show 0≤PLabel.d1 (lowerCut A B x) by linarith [P_first_lower_actual (source_mem hc)])
  exact hm.trans_lt (product_paid hc)

lemma cost_hasDerivAt {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hcut : 0≤lowerCut A B x) :
    HasDerivAt (cost A B)
      (-1+PLabel.d1 (lowerCut A B x)*NegativeTwo.TargetContact.v B x) x := by
  have hP := (PLabel.outer_hasDerivAt
    (outer_domain (source_mem (cut_mem ht hx hcut)))).comp x (cut_hasDerivAt ht x)
  exact ((((hasDerivAt_id' x).const_sub (Real.pi/2)).fun_sub hP).sub_const (V B)).congr_deriv
    (by ring)

lemma cap_positive {B : ℝ} (hb : B∈Icc 0 outerDiagonal) :
    0<NegativeTwo.TargetContact.B B (7/10) := by
  have hm := NegativeTwo.TargetContact.B_source_monotone (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num)
    outer_zero_mem hb hb.1
  have hzero := NegativeTwo.TargetContact.Cap.zero_target.1
  change (613013931/5000000000:ℝ)<NegativeTwo.TargetContact.B 0 (7/10) at hzero
  linarith

theorem original {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 0 a b A B (-1) 1 (Real.pi/2-x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2-x) := by
  have hcut : b≤lowerCut A B x := by
    have hw := lower_width hx
    norm_num [forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
    dsimp [lowerCut]
    linarith
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2⟩
  have hstart : NegativeTwo.TargetContact.B B x≤0 := by
    linarith [cut_eq ht x,hs.1]
  have hcontinuous : Continuous (NegativeTwo.TargetContact.B B) :=
    continuous_iff_continuousAt.2 fun y =>
      (NegativeTwo.TargetContact.B_angle_hasDerivAt B y).continuousAt
  obtain ⟨t,htime,hzero⟩ := intermediate_value_Icc hx.2 hcontinuous.continuousOn
    (show (0:ℝ)∈Icc (NegativeTwo.TargetContact.B B x)
      (NegativeTwo.TargetContact.B B (7/10)) from ⟨hstart,(cap_positive hB).le⟩)
  have ht' : t∈Icc 0 (7/10) := ⟨hx.1.trans htime.1,htime.2⟩
  have hcutzero : lowerCut A B t=0 := by rw [cut_eq ht t,hzero]; ring
  have hdom {s : ℝ} (hs' : s∈Icc x t) : s∈Icc 0 (7/10) :=
    ⟨hx.1.trans hs'.1,hs'.2.trans ht'.2⟩
  have hnonneg {s : ℝ} (hs' : s∈Icc x t) : 0≤lowerCut A B s := by
    have hh := cut_antitone ht (hdom hs') ht' hs'.2
    rw [hcutzero] at hh
    exact hh
  have hcost : AntitoneOn (cost A B) (Icc x t) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun s hs' => (cost_hasDerivAt ht (hdom hs') (hnonneg hs')).continuousAt.continuousWithinAt
    · exact fun s hs' => cost_hasDerivAt ht (hdom (Ioo_subset_Icc_self hs'))
        (hnonneg (Ioo_subset_Icc_self hs'))
    · intro s hs'
      linarith [speed_paid ht (hdom (Ioo_subset_Icc_self hs')) (hnonneg (Ioo_subset_Icc_self hs'))]
  have hstep := hcost ⟨le_rfl,htime.1⟩ ⟨htime.1,le_rfl⟩ htime.1
  have hP := P_increasing ⟨hs.1,(outer_bounds hs).2.2⟩
    (source_mem (cut_mem ht hx (by linarith [hs.1]))) hcut
  have haxis := Axial.original ht ht' hcutzero
  dsimp [cost,value] at *
  rw [hcutzero] at hstep
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.LowerSecondary

module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoPrimaryInverse

/-!
# Eight squares: the zero-target boundary of the upper source-primary contact

On source primary heights between the diagonal and one, the source
primary label has second derivative greater than .9.  Its derivative
times the actual contact speed increases toward one and remains
strictly below one there.  The complete boundary cost therefore
decreases to the already proved aligned endpoint.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.PrimaryAxis

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def interval : Set ℝ := Icc outerDiagonal 1
def speed (a : ℝ) : ℝ := NegativeTwo.ContactInverse.speed (a-1/2) 0
def product (a : ℝ) : ℝ := PPrimaryLabel.d1 a*speed a
def productD (a : ℝ) : ℝ :=
  PPrimaryLabel.d2 a*speed a-PPrimaryLabel.d1 a*(a-1/2)/speed a
def cost (a : ℝ) : ℝ :=
  Real.pi/2+PrimaryInverse.X (a-1/2) 0+PPrimaryLabel.outer a-V 0
def first (a : ℝ) : ℝ := PPrimaryLabel.d1 a-1/speed a

lemma primary_mem {a : ℝ} (ha : a∈interval) : a∈Icc outerDiagonal outerAxial :=
  ⟨ha.1,ha.2.trans primary_one_mem.2⟩

lemma shift_mem {a : ℝ} (ha : a∈interval) : a-1/2∈PrimaryInverse.shifts := by
  constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2]

lemma source_first_formula (a : ℝ) :
    PPrimaryLabel.d1 a=2363/100000+(2363/50000)*a+(2211/20000)*arc a+
      (22663/25000-(2211/20000)*a)*ratio a := by
  dsimp [RoleLabel.d1,PPrimaryLabel,RoleLabel.primary,PLabel]
  ring

lemma source_second_formula (a : ℝ) :
    PPrimaryLabel.d2 a=2363/50000-(2211/10000)*ratio a+
      (22663/25000-(2211/20000)*a)*ratioD a := by
  dsimp [RoleLabel.d2,PPrimaryLabel,RoleLabel.primary,PLabel]
  ring

lemma ratio_upper {a : ℝ} (ha : a∈interval) : ratio a<117/100 := by
  have hp : 0<arc a+1/2 := U_positive (primary_domain (primary_mem ha))
  have hm := ShortOuterOne.SameContact.arc_antitone
    (primary_domain (primary_mem ha)) (primary_domain primary_one_mem) ha.2
  change bOne≤arc a at hm
  change (a+1/2)/(arc a+1/2)<117/100
  apply (div_lt_iff₀ hp).2
  linarith [bOne_bounds.1,ha.2]

lemma ratioD_lower {a : ℝ} (ha : a∈interval) : (71/50:ℝ)<ratioD a := by
  have hp := U_positive (primary_domain (primary_mem ha))
  have hb := primary_secondary_mem (primary_mem ha)
  have hU : U a<7/5 := by dsimp [U]; linarith [hb.2,outer_endpoint_bounds.2.2.2]
  have hcube := pow_le_pow_left₀ hp.le hU.le 3
  change (71/50:ℝ)<Q0/(U a)^3
  apply (lt_div_iff₀ (pow_pos hp 3)).2
  norm_num [Q0]
  nlinarith

lemma source_first_positive {a : ℝ} (ha : a∈interval) : 0<PPrimaryLabel.d1 a := by
  have hr := primary_ratio_one (primary_mem ha)
  have hb := primary_secondary_mem (primary_mem ha)
  have hc : 0<22663/25000-(2211/20000)*a := by linarith [ha.2]
  have hm := mul_pos hc (show 0<ratio a by linarith)
  rw [source_first_formula]
  nlinarith [ha.1,fine_outer_endpoint_bounds.2,hb.1]

lemma source_second_lower {a : ℝ} (ha : a∈interval) : (9/10:ℝ)<PPrimaryLabel.d2 a := by
  have hr := ratio_upper ha
  have hD := ratioD_lower ha
  have hc : (159/200:ℝ)<22663/25000-(2211/20000)*a := by linarith [ha.2]
  have hm := mul_lt_mul hc hD.le (by norm_num : (0:ℝ)<71/50)
    (by linarith : 0≤22663/25000-(2211/20000)*a)
  rw [source_second_formula]
  nlinarith

lemma source_first_monotone : MonotoneOn PPrimaryLabel.d1 interval :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ha => (PPrimaryLabel.d1_hasDerivAt (primary_domain (primary_mem ha))).continuousAt.continuousWithinAt)
    (fun _ ha => PPrimaryLabel.d1_hasDerivAt (primary_domain (primary_mem (Ioo_subset_Icc_self ha))))
    (fun _ ha => by linarith [source_second_lower (Ioo_subset_Icc_self ha)])

lemma source_first_one : PPrimaryLabel.d1 1<(271/250:ℝ) := by
  have hh := PPrimaryLabel.first_chart_reference (b := (1:ℝ))
    (l := (129058126439213/100000000000000:ℝ))
    (u := (64529063219607/50000000000000:ℝ))
    (dlo := (27/25:ℝ)) (dhi := (271/250:ℝ)) (primary_domain primary_one_mem)
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [PPrimaryLabel,RoleLabel.primary,PLabel,W,Q0])
    (by norm_num [PPrimaryLabel,RoleLabel.primary,PLabel,W,Q0])
  exact hh.2

lemma source_first_upper {a : ℝ} (ha : a∈interval) : PPrimaryLabel.d1 a<(271/250:ℝ) :=
  (source_first_monotone ha ⟨primary_one_mem.1,le_rfl⟩ ha.2).trans_lt source_first_one

lemma speed_data {a : ℝ} (ha : a∈interval) :
    0<speed a ∧ (a-1/2)^2+(speed a)^2=Inverse.q (U 0) := by
  have hd := PrimaryInverse.data outer_zero_mem (shift_mem ha)
  exact ⟨hd.2.2.1,hd.2.2.2⟩

lemma speed_square_lower {a : ℝ} (ha : a∈interval) : (209/250:ℝ)<(speed a)^2 := by
  have hd := speed_data ha
  have hz : 0≤a-1/2 := by linarith [ha.1,fine_outer_endpoint_bounds.2]
  have hz2 := pow_le_pow_left₀ hz (show a-1/2≤(1/2:ℝ) by linarith [ha.2]) 2
  nlinarith [TargetRatio.zero_q.1,hd.2]

lemma speed_hasDerivAt {a : ℝ} (ha : a∈interval) :
    HasDerivAt speed (-(a-1/2)/speed a) a := by
  have hd := speed_data ha
  have hrad : Inverse.q (U 0)-(a-1/2)^2≠0 := by nlinarith [sq_pos_of_pos hd.1]
  have hin : HasDerivAt (fun y => Inverse.q (U 0)-(y-1/2)^2) (-(2*(a-1/2))) a :=
    ((hasDerivAt_const a (Inverse.q (U 0))).sub
      (((hasDerivAt_id a).sub_const (1/2)).pow 2)).congr_deriv (by simp)
  have hv : speed a=Real.sqrt (Inverse.q (U 0)-(a-1/2)^2) := rfl
  refine (hin.sqrt hrad).congr_deriv ?_
  rw [← hv]
  field_simp [hd.1.ne']

lemma product_hasDerivAt {a : ℝ} (ha : a∈interval) :
    HasDerivAt product (productD a) a := by
  exact ((PPrimaryLabel.d1_hasDerivAt (primary_domain (primary_mem ha))).mul
    (speed_hasDerivAt ha)).congr_deriv (by dsimp only [productD]; ring)

lemma productD_positive {a : ℝ} (ha : a∈interval) : 0<productD a := by
  have hd := speed_data ha
  have hM := source_first_positive ha
  have hz : 0≤a-1/2 := by linarith [ha.1,fine_outer_endpoint_bounds.2]
  have hmain := mul_le_mul (source_second_lower ha).le (speed_square_lower ha).le
    (by norm_num : (0:ℝ)≤209/250) (by linarith [source_second_lower ha])
  have hlast := mul_le_mul (source_first_upper ha).le
    (show a-1/2≤(1/2:ℝ) by linarith [ha.2]) hz (by norm_num : (0:ℝ)≤271/250)
  have he : productD a*speed a=
      PPrimaryLabel.d2 a*(speed a)^2-PPrimaryLabel.d1 a*(a-1/2) := by
    dsimp [productD]
    field_simp [hd.1.ne']
  nlinarith

lemma product_monotone : MonotoneOn product interval :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ha => (product_hasDerivAt ha).continuousAt.continuousWithinAt)
    (fun _ ha => product_hasDerivAt (Ioo_subset_Icc_self ha))
    (fun _ ha => (productD_positive (Ioo_subset_Icc_self ha)).le)

lemma speed_one : speed 1=outerAxial-1/2 := by
  have hd := speed_data ⟨primary_one_mem.1,le_rfl⟩
  have hc := UW_circle (outer_domain outer_zero_mem)
  have hu : U 0=outerAxial+1/2 := by
    simp [U,ShortOuterOne.SameContact.arc_zero]
  norm_num [W] at hc
  rw [hu] at hc hd
  dsimp [Inverse.q,NegativeTwo.Inverse.q] at hd
  have hp : 0<outerAxial-1/2 := by linarith [ShortOuterZero.fine_axial_bounds.1]
  nlinarith

lemma product_one : product 1<1 := by
  have hM := source_first_one
  have hMp := source_first_positive ⟨primary_one_mem.1,le_rfl⟩
  have hv : 0<outerAxial-1/2 := by linarith [ShortOuterZero.fine_axial_bounds.1]
  have hm := mul_lt_mul_of_pos_right hM hv
  dsimp [product]
  rw [speed_one]
  nlinarith [ShortOuterZero.fine_axial_bounds.2]

lemma product_paid {a : ℝ} (ha : a∈interval) : product a<1 :=
  (product_monotone ha ⟨primary_one_mem.1,le_rfl⟩ ha.2).trans_lt product_one

lemma cost_hasDerivAt {a : ℝ} (ha : a∈interval) : HasDerivAt cost (first a) a := by
  have hX := (PrimaryInverse.X_shift_hasDerivAt outer_zero_mem (shift_mem ha)).comp a
    ((hasDerivAt_id a).sub_const (1/2))
  exact (((hX.const_add (Real.pi/2)).add
    (PPrimaryLabel.outer_hasDerivAt (primary_domain (primary_mem ha)))).sub_const (V 0)).congr_deriv
    (by dsimp only [first,speed]; ring)

lemma first_negative {a : ℝ} (ha : a∈interval) : first a<0 := by
  have hv := (speed_data ha).1
  have hp := product_paid ha
  have he : first a*speed a=product a-1 := by
    dsimp [first,product]
    field_simp [hv.ne']
  nlinarith

lemma cost_antitone : AntitoneOn cost interval :=
  antiOn_of_hasDeriv_nonpos
    (fun _ ha => (cost_hasDerivAt ha).continuousAt.continuousWithinAt)
    (fun _ ha => cost_hasDerivAt (Ioo_subset_Icc_self ha))
    (fun _ ha => (first_negative (Ioo_subset_Icc_self ha)).le)

theorem cost_lower {a : ℝ} (ha : a∈interval) : (44889/50000:ℝ)<cost a := by
  have hm := cost_antitone ha ⟨primary_one_mem.1,le_rfl⟩ ha.2
  have hX := PrimaryInverse.aligned outer_zero_mem (show (1-1/2:ℝ)=W 0 by norm_num [W])
  have hM : PPrimaryLabel.outer 1= -P bOne :=
    PLabel.primary_actual (primary_state primary_one_mem)
  dsimp [cost] at hm ⊢
  rw [hX,hM] at hm
  linarith [aligned_axial_value]

end SquaresInCircles.Eight.SecondWord.OppositeTwo.PrimaryAxis

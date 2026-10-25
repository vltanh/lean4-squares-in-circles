module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeStationaryCurve

/-!
# Eight squares: no interior contact minimum for the last negative edge-three owner

At an angular stationary point, targets at least `.1` give a negative
angular second derivative.  Smaller targets determine a narrow original
source-circle arc; its exact projection identity gives a strictly
positive source derivative.  Both conclusions concern the original
two-variable contact cost.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.Contact

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open NegativeTwo

def cost (b x : ℝ) : ℝ := value b (TargetContact.B b x) (Real.pi/2-x)
def sourceFirst (b x : ℝ) : ℝ :=
  -TLabel.d1 b+KLabel.d1 (TargetContact.B b x)*TargetContact.k b x
def angleFirst (b x : ℝ) : ℝ :=
  -1+KLabel.d1 (TargetContact.B b x)*TargetContact.v b x
def angleSecond (b x : ℝ) : ℝ :=
  KLabel.d2 (TargetContact.B b x)*(TargetContact.v b x)^2-
    KLabel.d1 (TargetContact.B b x)*(TargetContact.B b x-1/2)

lemma cost_source_hasDerivAt {b x : ℝ} (hd : TargetContact.Domain b x) :
    HasDerivAt (fun t => cost t x) (sourceFirst b x) b := by
  have hh := ((TLabel.outer_hasDerivAt (outer_domain hd.1)).neg).add
    ((KLabel.outer_hasDerivAt (outer_domain hd.2.2)).comp b
      (TargetContact.B_source_hasDerivAt hd.1 x))
  convert hh.const_add (Real.pi/2-x) using 1 <;>
    dsimp [cost,value,sourceFirst,T,K] <;> ring

lemma cost_angle_hasDerivAt {b x : ℝ} (hd : TargetContact.Domain b x) :
    HasDerivAt (cost b) (angleFirst b x) x := by
  have hh := (((hasDerivAt_id' x).const_sub (Real.pi/2)).sub_const (T b)).add
    ((KLabel.outer_hasDerivAt (outer_domain hd.2.2)).comp x
      (TargetContact.B_angle_hasDerivAt b x))
  exact hh.congr_deriv (by simp only [angleFirst])

lemma angleFirst_hasDerivAt {b x : ℝ} (hd : TargetContact.Domain b x) :
    HasDerivAt (angleFirst b) (angleSecond b x) x := by
  have hh := (((KLabel.d1_hasDerivAt (outer_domain hd.2.2)).comp x
    (TargetContact.B_angle_hasDerivAt b x)).mul
      (TargetContact.v_angle_hasDerivAt b x)).const_add (-1)
  exact hh.congr_deriv (by simp only [angleSecond,Function.comp_apply]; ring)

def charge (B : ℝ) : ℝ := KLabel.d2 B-(B-1/2)*(KLabel.d1 B)^3
def chargeFirst (B : ℝ) : ℝ :=
  KLabel.d3 B-(KLabel.d1 B)^3-3*(B-1/2)*(KLabel.d1 B)^2*KLabel.d2 B

lemma charge_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt charge (chargeFirst B) B := by
  have hk := KLabel.d1_hasDerivAt (outer_domain hB)
  have hh := (KLabel.d2_hasDerivAt (outer_domain hB)).sub
    (((hasDerivAt_id' B).sub_const (1/2)).mul (hk.pow 3))
  exact hh.congr_deriv (by simp only [chargeFirst,Pi.pow_apply]; norm_num; ring)

lemma chargeFirst_negative {B : ℝ} (hB : B∈Icc (1/10) (1/2)) :
    chargeFirst B<0 := by
  have hm : B∈Icc 0 outerDiagonal :=
    ⟨by linarith [hB.1],by linarith [hB.2,fine_outer_endpoint_bounds.2]⟩
  have hk : 0<KLabel.d1 B := StationaryCurve.slope_pos hm
  have hp := mul_nonneg_of_nonpos_of_nonpos
    (show B-1/2≤0 by linarith [hB.2])
    (show KLabel.d2 B≤0 by linarith [K_second_upper hm])
  have hprod := mul_nonneg (sq_nonneg (KLabel.d1 B)) hp
  dsimp [chargeFirst]
  nlinarith [K_third_upper hm,pow_pos hk 3]

lemma charge_tenth : charge (1/10)<0 := by
  have hm : (1/10:ℝ)∈Icc 0 outerDiagonal := StationaryCurve.small_mem (by norm_num)
  have hk := StationaryCurve.slope_pos hm
  have hh := pow_lt_pow_left₀ StationaryCurve.tenth_slope_reference.2 hk.le
    (by norm_num : (3:ℕ)≠0)
  dsimp [charge]
  norm_num at hh ⊢
  linarith [StationaryCurve.tenth_curvature_reference]

lemma charge_negative {B : ℝ} (hB : B∈Icc (1/10) outerDiagonal) : charge B<0 := by
  have hm : B∈Icc 0 outerDiagonal := ⟨by linarith [hB.1],hB.2⟩
  rcases le_total B (1/2) with h | h
  · have hanti : AntitoneOn charge (Icc (1/10) (1/2)) :=
      antiOn_of_hasDeriv_nonpos
        (fun t ht => (charge_hasDerivAt
          ⟨by linarith [ht.1],by linarith [ht.2,fine_outer_endpoint_bounds.2]⟩).continuousAt.continuousWithinAt)
        (fun t ht => charge_hasDerivAt
          ⟨by linarith [ht.1],by linarith [ht.2,fine_outer_endpoint_bounds.2]⟩)
        (fun t ht => (chargeFirst_negative (Ioo_subset_Icc_self ht)).le)
    exact (hanti (by norm_num) ⟨hB.1,h⟩ hB.1).trans_lt charge_tenth
  · have hp := mul_nonneg (show 0≤B-1/2 by linarith)
      (pow_nonneg (StationaryCurve.slope_pos hm).le 3)
    dsimp [charge]
    linarith [K_second_upper hm]

lemma angular_stationary_large {b x : ℝ} (hd : TargetContact.Domain b x)
    (hB : (1/10:ℝ)≤TargetContact.B b x) (hs : angleFirst b x=0) :
    angleSecond b x<0 := by
  have hk := StationaryCurve.slope_pos hd.2.2
  have hv := TargetContact.v_positive hd.1 hd.2.1
  have he : KLabel.d1 (TargetContact.B b x)*TargetContact.v b x=1 := by
    dsimp [angleFirst] at hs
    linarith
  have hvformula : TargetContact.v b x=1/KLabel.d1 (TargetContact.B b x) := by
    apply (eq_div_iff hk.ne').2
    simpa only [mul_comm] using he
  have hid : angleSecond b x=(TargetContact.v b x)^2*charge (TargetContact.B b x) := by
    rw [hvformula]
    dsimp [angleSecond,charge]
    rw [hvformula]
    field_simp [hk.ne']
  rw [hid]
  exact mul_neg_of_pos_of_neg (pow_pos hv 2) (charge_negative ⟨hB,hd.2.2.2⟩)

lemma stationary_height {b x : ℝ} (hd : TargetContact.Domain b x)
    (hs : angleFirst b x=0) : U b=StationaryCurve.height (TargetContact.B b x) := by
  have hk := StationaryCurve.slope_pos hd.2.2
  have hv : KLabel.d1 (TargetContact.B b x)*TargetContact.v b x=1 := by
    dsimp [angleFirst] at hs
    linarith
  have hv2 : (KLabel.d1 (TargetContact.B b x))^2*(TargetContact.v b x)^2=1 := by
    nlinarith [sq_nonneg (KLabel.d1 (TargetContact.B b x)*TargetContact.v b x-1)]
  have hn := TargetContact.norm_identity hd.1 x
  have hn' := congrArg (fun t : ℝ => t*(KLabel.d1 (TargetContact.B b x))^2) hn
  have hc := StationaryCurve.height_identity hd.2.2
  dsimp [NegativeTwo.Inverse.q] at hn'
  have he : (U b-StationaryCurve.height (TargetContact.B b x))*
      (KLabel.d1 (TargetContact.B b x))^2=0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (pow_ne_zero 2 hk.ne'))

lemma projection_identity {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) :
    TargetContact.k b x/TargetContact.v b x=
      (Q0-U b)/(U b*NegativeTwo.Inverse.q (U b))+
        (W b/U b)*(TargetContact.B b x-1/2)/
          (NegativeTwo.Inverse.q (U b)*TargetContact.v b x) := by
  have hu := U_positive (outer_domain hb)
  have hq : 0<NegativeTwo.Inverse.q (U b) := by
    linarith [NegativeTwo.Inverse.actual_q_positive hb]
  have hv := TargetContact.v_positive hb hx
  have hc := UW_circle (outer_domain hb)
  have hk : TargetContact.k b x=W b/U b*Real.cos x+Real.sin x := rfl
  have hB : TargetContact.B b x-1/2=-(U b-1)*Real.cos x+W b*Real.sin x := by
    simp only [TargetContact.B,U,W]; ring
  have hvv : TargetContact.v b x=(U b-1)*Real.sin x+W b*Real.cos x := by
    simp only [TargetContact.v,U,W]; ring
  have hqq : NegativeTwo.Inverse.q (U b)=Q0+1-2*U b := rfl
  rw [hk,hB]
  field_simp
  rw [hvv,hqq]
  linear_combination (-Real.sin x)*hc

lemma source_slope_reference : TLabel.d1 (197/500)<(17/25:ℝ) := by
  have hm : (197/500:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hh := TLabel.first_chart_reference (outer_domain hm)
    (l := (17653/10000:ℝ)) (u := (8827/5000:ℝ))
    (dlo := (0:ℝ)) (dhi := (17/25:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  exact hh.2

lemma source_slope_small {b : ℝ} (hb : b∈Icc (197/500) (21/50)) :
    TLabel.d1 b<(17/25:ℝ) := by
  have hanti : AntitoneOn TLabel.d1 (Icc (197/500) (21/50)) :=
    antiOn_of_hasDeriv_nonpos
      (fun t ht => (TLabel.d1_hasDerivAt (outer_domain
        ⟨by linarith [ht.1],by linarith [ht.2,fine_outer_endpoint_bounds.2]⟩)).continuousAt.continuousWithinAt)
      (fun t ht => TLabel.d1_hasDerivAt (outer_domain
        ⟨by linarith [ht.1],by linarith [ht.2,fine_outer_endpoint_bounds.2]⟩))
      (fun t ht => by
        linarith [T_second_early (show t∈Icc 0 (3/5) from
          ⟨by linarith [ht.1],by linarith [ht.2]⟩)])
  exact (hanti (by norm_num) hb hb.1).trans_lt source_slope_reference

lemma angular_stationary_small {b x : ℝ} (hd : TargetContact.Domain b x)
    (hB : TargetContact.B b x≤(1/10:ℝ)) (hs : angleFirst b x=0) :
    0<sourceFirst b x := by
  have hu := StationaryCurve.height_bounds ⟨hd.2.2.1,hB⟩
  rw [←stationary_height hd hs] at hu
  have hc := UW_circle (outer_domain hd.1)
  have hw0 : (1/2:ℝ)≤W b := by dsimp [W]; linarith [hd.1.1]
  have hbsmall : b∈Ioo (197/500) (21/50) := by
    norm_num [Q0] at hc
    have hu2lo : (219/125:ℝ)^2<(U b)^2 := by nlinarith [hu.1]
    have hu2hi : (U b)^2<(353/200:ℝ)^2 := by nlinarith [hu.1,hu.2]
    dsimp [W] at hc hw0
    constructor <;> nlinarith
  have hvpos := TargetContact.v_positive hd.1 hd.2.1
  have hstat : KLabel.d1 (TargetContact.B b x)*TargetContact.v b x=1 := by
    dsimp [angleFirst] at hs
    linarith
  have hK := (K_first_bounds hd.2.2).2
  have hv : (1077/1000:ℝ)<TargetContact.v b x := by
    have hp := mul_lt_mul_of_pos_right hK hvpos
    nlinarith
  have hp := stationary_projection_lower hu
    (show W b∈Icc (1/2) (23/25) from ⟨hw0,by dsimp [W]; linarith [hbsmall.2]⟩)
    (show TargetContact.B b x-1/2∈Icc (-(1/2)) (-(2/5)) from
      ⟨by linarith [hd.2.2.1],by linarith⟩) hv
  have hproj := projection_identity hd.1 hd.2.1
  norm_num [Q0,NegativeTwo.Inverse.q] at hproj hp
  have he : KLabel.d1 (TargetContact.B b x)*TargetContact.k b x=
      TargetContact.k b x/TargetContact.v b x := by
    apply (eq_div_iff hvpos.ne').2
    linear_combination (TargetContact.k b x)*hstat
  dsimp [sourceFirst]
  rw [he]
  linarith [source_slope_small ⟨hbsmall.1.le,hbsmall.2.le⟩]

theorem stationary_alternatives {b x : ℝ} (hd : TargetContact.Domain b x)
    (hs : angleFirst b x=0) :
    angleSecond b x<0 ∨ 0<sourceFirst b x := by
  rcases le_total (1/10:ℝ) (TargetContact.B b x) with h | h
  · exact Or.inl (angular_stationary_large hd h hs)
  · exact Or.inr (angular_stationary_small hd h hs)

end SquaresInCircles.Eight.SecondWord.NegativeThree.Contact

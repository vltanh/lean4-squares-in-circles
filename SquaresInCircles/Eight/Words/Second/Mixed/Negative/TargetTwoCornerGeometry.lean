module

public import SquaresInCircles.Eight.Words.Second.Mixed.CoreCorner
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeLowerFourth

/-!
# Eight squares: the whole negative-core corner contact rectangle

One pair of harmonic coordinates gives every contact height and
angular speed. The original core circle supplies the exact slope
ratio and its derivative, including both closed endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

def angles : Set ℝ := Icc lowerAngle (1191/1000)
def lateAngles : Set ℝ := Icc (11/10) (1191/1000)
def u (B φ : ℝ) : ℝ := 1+(MixedCorner.a B+1/2)*Real.cos φ-(B-1/2)*Real.sin φ
def speed (B φ : ℝ) : ℝ := (MixedCorner.a B+1/2)*Real.sin φ+(B-1/2)*Real.cos φ
def L (B φ : ℝ) : ℝ := Real.sin φ+MixedCorner.w B*Real.cos φ
def N (B φ : ℝ) : ℝ := Real.cos φ-MixedCorner.w B*Real.sin φ
def D (B : ℝ) : ℝ := (1+(MixedCorner.w B)^2)/MixedCorner.z B

lemma terminal_trig :
    (46437/50000:ℝ)<Real.sin (1191/1000) ∧ Real.sin (1191/1000)<928741/1000000 ∧
    (370731/1000000:ℝ)<Real.cos (1191/1000) ∧ Real.cos (1191/1000)<92683/250000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (1191/1000:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (1191/1000:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (1191/1000:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (1191/1000:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma transition_trig :
    (891207/1000000:ℝ)<Real.sin (11/10) ∧ Real.sin (11/10)<111401/125000 ∧
    (113399/250000:ℝ)<Real.cos (11/10) ∧ Real.cos (11/10)<453597/1000000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (11/10:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (11/10:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (11/10:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (11/10:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma lower_mem {φ : ℝ} (hφ : φ∈angles) : Lower φ :=
  ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩
lemma late_subset : lateAngles⊆angles := fun _ hφ =>
  ⟨by dsimp [lowerAngle]; linarith [hφ.1,pi_hand_enclosure.2],hφ.2⟩

lemma u_bounds {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈angles) :
    (6689/5000:ℝ)<u B φ ∧ u B φ<(17/10:ℝ) := by
  have hc := CoreAngleEndpoint.state_bounds (MixedCorner.state hB)
  have hd := MixedCorner.chart_bounds hB
  have ht := lower_trig (lower_mem hφ)
  have he : (1191/1000:ℝ)∈angles := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],le_rfl⟩
  have hs := PositiveThree.lower_sin_monotone (lower_mem hφ) (lower_mem he) hφ.2
  have hcos := PositiveThree.lower_cos_antitone (lower_mem hφ) (lower_mem he) hφ.2
  have hAl : (13973139/25000000:ℝ)<MixedCorner.a B := by
    dsimp [MixedCorner.a]
    linarith [hd.1,CoreAngleEndpoint.diagonal_bounds.1]
  have hBu : B<(55892557/100000000:ℝ) := hB.2.trans_lt CoreAngleEndpoint.diagonal_bounds.2
  have hl := mul_le_mul
    (show (26473139/25000000:ℝ)≤MixedCorner.a B+1/2 by linarith) terminal_trig.2.2.1.le
    (by norm_num : (0:ℝ)≤370731/1000000) (by linarith [hAl] : 0≤MixedCorner.a B+1/2)
  have hcs := mul_le_mul_of_nonneg_left hcos
    (by linarith [hAl] : 0≤MixedCorner.a B+1/2)
  have hu := mul_le_mul
    (show B-1/2≤5892557/100000000 by linarith) (hs.trans terminal_trig.2.1.le)
    (by linarith [ht.1] : 0≤Real.sin φ) (by norm_num : (0:ℝ)≤5892557/100000000)
  have hupper := mul_le_mul (show MixedCorner.a B+1/2≤13/12 by linarith [hc.2.1]) ht.2.2.2.1.le
    ht.2.2.1 (by norm_num : (0:ℝ)≤13/12)
  have hnonneg := mul_nonneg (sub_nonneg.mpr hB.1) (by linarith [ht.1] : 0≤Real.sin φ)
  dsimp [u]
  constructor <;> nlinarith

lemma early_height {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈angles) (he : φ≤11/10) :
    u B φ∈Icc (7/5:ℝ) (17/10) := by
  have ht := lower_trig (lower_mem hφ)
  have hi : (11/10:ℝ)∈angles := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],by norm_num⟩
  have hc := PositiveThree.lower_cos_antitone (lower_mem hφ) (lower_mem hi) he
  have hcore := MixedCorner.chart_bounds hB
  have ha : (10589/10000:ℝ)≤MixedCorner.a B+1/2 := by
    dsimp [MixedCorner.a]
    linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1]
  have hb : B-1/2≤59/1000 := by linarith [hB.2,CoreAngleEndpoint.diagonal_bounds.2]
  have hp := mul_le_mul ha (transition_trig.2.2.1.le.trans hc)
    (by norm_num : (0:ℝ)≤113399/250000) (by linarith [ha] : 0≤MixedCorner.a B+1/2)
  have hq := mul_le_mul hb (Real.sin_le_one φ) (by linarith [ht.1] : 0≤Real.sin φ)
    (by norm_num : (0:ℝ)≤59/1000)
  exact ⟨by dsimp [u]; nlinarith,(u_bounds hB hφ).2.le⟩

lemma late_height {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈lateAngles) :
    u B φ∈Icc (133/100:ℝ) (373/250) := by
  have hi : (11/10:ℝ)∈angles := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],by norm_num⟩
  have hc := PositiveThree.lower_cos_antitone (lower_mem hi) (lower_mem (late_subset hφ)) hφ.1
  have ht := lower_trig (lower_mem (late_subset hφ))
  have hcore := CoreAngleEndpoint.state_bounds (MixedCorner.state hB)
  have hp := mul_le_mul (show MixedCorner.a B+1/2≤13/12 by linarith [hcore.2.1])
    (hc.trans transition_trig.2.2.2.le) ht.2.2.1 (by norm_num : (0:ℝ)≤13/12)
  have hq := mul_nonneg (sub_nonneg.mpr hB.1) (by linarith [ht.1] : 0≤Real.sin φ)
  exact ⟨by linarith [(u_bounds hB (late_subset hφ)).1],by dsimp [u]; nlinarith⟩

lemma terminal_height {B : ℝ} (hB : B∈MixedCorner.domain) :
    u B (1191/1000)∈Icc (6689/5000:ℝ) (701/500) := by
  have he : (1191/1000:ℝ)∈angles := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],le_rfl⟩
  have hcore := CoreAngleEndpoint.state_bounds (MixedCorner.state hB)
  have hp := mul_le_mul (show MixedCorner.a B+1/2≤13/12 by linarith [hcore.2.1]) terminal_trig.2.2.2.le
    (by linarith [terminal_trig.2.2.1] : 0≤Real.cos (1191/1000)) (by norm_num : (0:ℝ)≤13/12)
  have hq := mul_nonneg (sub_nonneg.mpr hB.1) (by linarith [terminal_trig.1] : 0≤Real.sin (1191/1000))
  exact ⟨(u_bounds hB he).1.le,by dsimp [u]; nlinarith⟩

lemma D_bounds {B : ℝ} (hB : B∈MixedCorner.domain) :
    0<D B ∧ 12*(1+(MixedCorner.w B)^2)≤D B ∧ D B<34 := by
  have hz := MixedCorner.z_positive hB
  have hw := MixedCorner.w_bounds hB
  have hc := MixedCorner.chart_bounds hB
  have hwp : (MixedCorner.w B)^2≤1 := by nlinarith
  have he : D B*MixedCorner.z B=1+(MixedCorner.w B)^2 := by
    dsimp [D]
    field_simp [hz.ne']
  have hp : 0<D B := by dsimp [D]; positivity
  have hlo := mul_le_mul_of_nonneg_left hc.2.1 hp.le
  have hhi := mul_le_mul_of_nonneg_left
    (show (589/10000:ℝ)≤MixedCorner.z B by linarith [hc.1,CoreAngleEndpoint.diagonal_bounds.1]) hp.le
  exact ⟨hp,by nlinarith,by nlinarith⟩

lemma harmonic_circle (B φ : ℝ) : (u B φ-1)^2+(speed B φ)^2=
    (MixedCorner.a B+1/2)^2+(B-1/2)^2 := by
  dsimp [u,speed]
  linear_combination ((MixedCorner.a B+1/2)^2+(B-1/2)^2)*(Real.sin_sq_add_cos_sq φ)

lemma speed_bounds {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈angles) :
    0<speed B φ ∧ speed B φ<(109/100:ℝ) := by
  have ht := lower_trig (lower_mem hφ)
  have hc := CoreAngleEndpoint.state_bounds (MixedCorner.state hB)
  have hfirst := mul_pos (show 0<MixedCorner.a B+1/2 by linarith [hc.1])
    (show 0<Real.sin φ by linarith [ht.1])
  have hsecond := mul_nonneg (sub_nonneg.mpr hB.1) ht.2.2.1
  have hpos : 0<speed B φ := by dsimp [speed]; linarith
  have he := harmonic_circle B φ
  have hm := (MixedCorner.endpoint_mass hB).2
  exact ⟨hpos,by nlinarith [sq_nonneg (u B φ-1)]⟩

lemma LN_circle (B φ : ℝ) : (L B φ)^2+(N B φ)^2=1+(MixedCorner.w B)^2 := by
  dsimp [L,N]
  linear_combination (1+(MixedCorner.w B)^2)*(Real.sin_sq_add_cos_sq φ)

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner

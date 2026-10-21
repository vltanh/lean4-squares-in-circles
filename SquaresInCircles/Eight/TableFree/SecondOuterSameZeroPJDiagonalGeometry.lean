module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroPJDiagonalPolynomial

/-!
# Original-contact identities on the source-diagonal branch

Uncompiled source draft.  The explicit rotated circle equals the
original target whenever the source is diagonal.  The inverse-contact
derivatives and the forward speed satisfy their exact reciprocal
identities, including the closed target-zero endpoint.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ.Diagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma whole_bounds {x : ℝ} (hx : x∈Icc start (7/10)) :
    (33/20:ℝ)<horizontal x ∧ horizontal x<383/200 ∧
      (4/5:ℝ)<speed x ∧ height x<outerDiagonal := by
  have hl := horizontal_antitone hx (show (7/10:ℝ)∈Icc start (7/10) by norm_num [start]) hx.2
  have hu := horizontal_antitone (show start∈Icc start (7/10) by norm_num [start]) hx hx.1
  have hh := height_monotone hx (show (7/10:ℝ)∈Icc start (7/10) by norm_num [start]) hx.2
  have hlo := Reference.diagonal_endpoint_bounds.1.trans_le hl
  have hhi := hu.trans_lt Reference.diagonal_endpoint_bounds.2.1
  have hp := mul_lt_mul hlo (coordinates_positive hx).2.2 (by norm_num)
    (by linarith [hlo] : 0≤horizontal x)
  exact ⟨hlo,hhi,by dsimp [speed]; nlinarith,
    hh.trans_lt Reference.diagonal_endpoint_bounds.2.2⟩

lemma target_mem {x : ℝ} (hx : Domain x) : height x∈Icc 0 outerDiagonal :=
  ⟨hx.2,(whole_bounds hx.1).2.2.2.le⟩

lemma actual_coordinates {x : ℝ} (hx : Domain x) :
    U (height x)=horizontal x ∧ W (height x)=vertical x := by
  have hc := circle hx.1
  have hu : 0<horizontal x := by linarith [(whole_bounds hx.1).1]
  have ht := UW_circle (outer_domain (target_mem hx))
  have hU := U_positive (outer_domain (target_mem hx))
  have hw : W (height x)=vertical x := by dsimp [W,height]; ring
  rw [hw] at ht
  exact ⟨by nlinarith,hw⟩

lemma contact {x : ℝ} (hx : Domain x) : b (height x) x=outerDiagonal := by
  have hu := (actual_coordinates hx).1
  have hv := (actual_coordinates hx).2
  have he : b (height x) x=1/2+W (height x)*Real.cos x-
      (U (height x)-1)*Real.sin x := by dsimp [b,U,W]; ring
  rw [he,hu,hv]
  dsimp [horizontal,vertical,Z,z₀]
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma contact_domain {x : ℝ} (hx : Domain x) : SameZero.Domain (height x) x :=
  ⟨target_mem hx,angle_mem hx.1,by rw [contact hx]; exact ⟨outer_zero_mem.2,le_rfl⟩⟩

lemma original_coordinates {B x : ℝ} (hd : SameZero.Domain B x)
    (he : b B x=outerDiagonal) : Domain x ∧ height x=B := by
  have hb0 := b_target_monotone hd.2.1 outer_zero_mem hd.1 hd.1.1
  rw [he] at hb0
  have hstart : start<x := by
    by_contra! hn
    have hh := b_angle_antitone outer_zero_mem hd.2.1
      (show start∈Icc 0 (7/10) by norm_num [start]) hn
    linarith [Reference.zero_start]
  have hxi : x∈Icc start (7/10) := ⟨hstart.le,hd.2.1.2⟩
  have hZ : Z x=W B*Real.cos x-U B*Real.sin x := by
    dsimp [b,U,W] at he
    dsimp [Z,z₀,U,W]
    linarith
  have hY : Y x=U B*Real.cos x+W B*Real.sin x := by
    have hnorm := UW_circle (outer_domain hd.1)
    have hroot := (radical_data hxi).2.2.2.2
    have hpositive : 0<U B*Real.cos x+W B*Real.sin x := by
      have h1 := mul_pos (U_positive (outer_domain hd.1))
        (by linarith [(positive_trig hd.2.1).1] : 0<Real.cos x)
      have h2 := mul_nonneg (by dsimp [W]; linarith [hd.1.1] : 0≤W B)
        (positive_trig hd.2.1).2.2.1
      linarith
    have heq : (U B*Real.cos x+W B*Real.sin x)^2+(Z x)^2=Q0 := by
      rw [hZ]
      linear_combination hnorm+((U B)^2+(W B)^2)*(Real.sin_sq_add_cos_sq x)
    nlinarith [(radical_data hxi).2.2.1]
  have hheight : height x=B := by
    dsimp [height,vertical]
    rw [hY,hZ]
    dsimp [W]
    nlinarith [Real.sin_sq_add_cos_sq x]
  exact ⟨⟨hxi,by rw [hheight]; exact hd.1.1⟩,hheight⟩

def inverseFirst (x : ℝ) : ℝ :=
  NegativeTwo.Inverse.factor (U (height x))+
    z₀*ratio (height x)/(NegativeTwo.Inverse.q (U (height x))*v (height x) x)
def inverseSecond (x : ℝ) : ℝ :=
  PJCritical.inverseTarget (U (height x)) (ratio (height x)) z₀ (v (height x) x)

lemma speed_identity {x : ℝ} (hx : Domain x) :
    v (height x) x=Y x-Real.cos x := by
  have hu := (actual_coordinates hx).1
  have hv := (actual_coordinates hx).2
  change (U (height x)-1)*Real.cos x+W (height x)*Real.sin x=_
  rw [hu,hv]
  dsimp [horizontal,vertical]
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma inverse_first_identity {x : ℝ} (hx : Domain x) :
    inverseFirst x*speed x=1 := by
  have hc := contact_domain hx
  have hi := projection_identity hc.1 hc.2.1
  rw [contact hx] at hi
  have he : inverseFirst x=k (height x) x/v (height x) x := by
    dsimp [inverseFirst,z₀,ratio]
    rw [hi]
    ring
  rw [he,speed_identity hx]
  have hu := (actual_coordinates hx).1
  have hv := (actual_coordinates hx).2
  have hup := U_positive (outer_domain hc.1)
  have hyp : 0<Y x := by linarith [(radical_data hx.1).2.2.1]
  have hden : 0<Y x-Real.cos x := by
    linarith [(radical_data hx.1).2.2.1,(positive_trig hc.2.1).2.1]
  dsimp [k,ratio,speed,factor]
  change ((Real.cos x+(W (height x)/U (height x))*Real.sin x)/(Y x-Real.cos x))*
    (horizontal x*(1-Real.cos x/Y x))=1
  rw [hu,hv]
  field_simp [hup.ne',hyp.ne',hden.ne']
  dsimp [horizontal,vertical]
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma inverse_second_identity {x : ℝ} (hx : Domain x) :
    inverseSecond x*(speed x)^2+inverseFirst x*acceleration x=0 := by
  have hu := (actual_coordinates hx).1
  have hv := (actual_coordinates hx).2
  have hcircle := circle hx.1
  have hrad := (radical_data hx.1).2.2.2.2
  have htrig := Real.sin_sq_add_cos_sq x
  have hup : 0<horizontal x := by linarith [(whole_bounds hx.1).1]
  have hyp : 0<Y x := by linarith [(radical_data hx.1).2.2.1]
  have hspeed : 0<Y x-Real.cos x := by
    linarith [(radical_data hx.1).2.2.1,(positive_trig (angle_mem hx.1)).2.1]
  have hq : 0<NegativeTwo.Inverse.q (horizontal x) := by
    rw [←hu]
    linarith [NegativeTwo.Inverse.actual_q_positive (target_mem hx)]
  dsimp [inverseSecond,inverseFirst,PJCritical.inverseTarget,PJCritical.heightFactorD,
    NegativeTwo.Inverse.factorD,NegativeTwo.Inverse.factor,NegativeTwo.Inverse.brace,
    NegativeTwo.Inverse.N,ratio]
  rw [hu,hv,speed_identity hx]
  dsimp [speed,acceleration,factor,factorD,NegativeTwo.Inverse.q]
  field_simp [hup.ne',hyp.ne',hspeed.ne',hq.ne']
  dsimp [horizontal,vertical,Z] at hcircle hrad ⊢
  nlinarith [htrig]

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ.Diagonal

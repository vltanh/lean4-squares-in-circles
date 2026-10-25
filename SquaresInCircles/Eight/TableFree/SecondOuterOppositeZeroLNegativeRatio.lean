module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroLNegativeLocation

/-!
# The second descent direction for a negative symmetric contact

Uncompiled transcription of Section 9 of the whole-angle hand proof.
The ratio K/v is the explicit function J(B,z). Its coordinate derivatives
and the single endpoint estimate (19) give the target descent direction.
The rational radical lower bounds below only verify those named endpoint
comparisons; they do not subdivide a state or angle interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

def qB (B : ℝ) : ℝ := Q0-2*B
def inverseRoot (B z : ℝ) : ℝ := Real.sqrt (qB B-z^2)
def inverseSlope (B z : ℝ) : ℝ :=
  (Q0-B-1/2)/(U B*qB B)+z/(qB B*inverseRoot B z)
def inverseSlopeB (B z : ℝ) : ℝ :=
  (Q0-1)/(U B*(qB B)^2)+
    (Q0-B-1/2)*(B+1/2)/((U B)^3*qB B)+
      z*(2/((qB B)^2*inverseRoot B z)+1/(qB B*(inverseRoot B z)^3))

lemma inverse_data {B z : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(2/5):ℝ) (2/5)) :
    0<U B ∧ 0<qB B ∧ 0< inverseRoot B z ∧
      (inverseRoot B z)^2=qB B-z^2 := by
  have hq : (5289/2500:ℝ)<qB B := by
    norm_num [qB,Q0]
    linarith [hB.2,outer_endpoint_bounds.2.2.2]
  have hz2 : z^2≤(4/25:ℝ) := by nlinarith [hz.1,hz.2]
  have hr : 0<qB B-z^2 := by linarith
  exact ⟨U_positive (outer_domain hB),by linarith,Real.sqrt_pos.mpr hr,
    Real.sq_sqrt hr.le⟩

lemma inverseRoot_z_hasDerivAt {B z : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(2/5):ℝ) (2/5)) :
    HasDerivAt (inverseRoot B) (-z/inverseRoot B z) z := by
  have h := inverse_data hB hz
  have hn : qB B-z^2≠0 := by nlinarith [h.2.2.1,h.2.2.2]
  have hin : HasDerivAt (fun y : ℝ => qB B-y^2) (-(2*z)) z := by
    convert ((hasDerivAt_id' z).fun_pow 2).const_sub (qB B) using 1
    norm_num
  change HasDerivAt (fun y : ℝ => Real.sqrt (qB B-y^2)) _ z
  convert hin.sqrt hn using 1
  have hr : inverseRoot B z=Real.sqrt (qB B-z^2) := rfl
  rw [← hr]
  field_simp [h.2.2.1.ne']

lemma inverseRoot_B_hasDerivAt {B z : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(2/5):ℝ) (2/5)) :
    HasDerivAt (fun t => inverseRoot t z) (-1/inverseRoot B z) B := by
  have h := inverse_data hB hz
  have hn : qB B-z^2≠0 := by nlinarith [h.2.2.1,h.2.2.2]
  have hin : HasDerivAt (fun t : ℝ => qB t-z^2) (-2) B :=
    ((((hasDerivAt_id' B).const_mul 2).const_sub Q0).sub_const (z^2)).congr_deriv (by ring)
  change HasDerivAt (fun t : ℝ => Real.sqrt (qB t-z^2)) _ B
  convert hin.sqrt hn using 1
  have hr : inverseRoot B z=Real.sqrt (qB B-z^2) := rfl
  rw [← hr]
  field_simp [h.2.2.1.ne']

lemma inverseSlope_z_hasDerivAt {B z : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(2/5):ℝ) (2/5)) :
    HasDerivAt (inverseSlope B) (1/(inverseRoot B z)^3) z := by
  have h := inverse_data hB hz
  have hd := ((hasDerivAt_id z).div ((inverseRoot_z_hasDerivAt hB hz).const_mul (qB B))
    (mul_ne_zero h.2.1.ne' h.2.2.1.ne')).const_add ((Q0-B-1/2)/(U B*qB B))
  convert hd using 1
  · rfl
  · have hq : qB B=(inverseRoot B z)^2+z^2 := by linarith [h.2.2.2]
    simp only [id]
    rw [hq]
    have hr := h.2.2.1.ne'
    have hq0 : (inverseRoot B z)^2+z^2≠0 := by positivity
    field_simp
    ring

lemma inverseSlope_B_hasDerivAt {B z : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(2/5):ℝ) (2/5)) :
    HasDerivAt (fun t => inverseSlope t z) (inverseSlopeB B z) B := by
  have h := inverse_data hB hz
  have hU := (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).add_const (1/2)
  have hq : HasDerivAt qB (-2) B :=
    (((hasDerivAt_id' B).const_mul 2).const_sub Q0).congr_deriv (by ring)
  have hn := ((hasDerivAt_id B).const_sub Q0).sub_const (1/2)
  have hfirst := hn.div (hU.mul hq) (mul_ne_zero h.1.ne' h.2.1.ne')
  have hsecond := (hasDerivAt_const B z).div
    (hq.mul (inverseRoot_B_hasDerivAt hB hz)) (mul_ne_zero h.2.1.ne' h.2.2.1.ne')
  convert hfirst.add hsecond using 1
  · rfl
  · have key : inverseSlopeB B z=
        (-1*((arc B+1/2)*qB B)-(Q0-B-1/2)*(-ratio B*qB B+(arc B+1/2)*(-2)))/
          ((arc B+1/2)*qB B)^2+
        (0*(qB B*inverseRoot B z)-z*(-2*inverseRoot B z+qB B*(-1/inverseRoot B z)))/
          (qB B*inverseRoot B z)^2 := by
      have hu : U B=arc B+1/2 := rfl
      have hr : ratio B=(B+1/2)/(arc B+1/2) := rfl
      have hQ : Q0=qB B+2*B := by simp only [qB]; ring
      have ha : arc B+1/2≠0 := hu ▸ h.1.ne'
      have hq0 := h.2.1.ne'
      have hr0 := h.2.2.1.ne'
      rw [inverseSlopeB,hu,hr,hQ]
      generalize arc B+1/2=a at *
      generalize qB B=q at *
      generalize inverseRoot B z=r at *
      field_simp [ha,hq0,hr0]
      ring
    rw [key]
    rfl

lemma inverseSlope_z_monotone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    MonotoneOn (inverseSlope B) (Icc (-(2/5):ℝ) (2/5)) :=
  monoOn_of_hasDeriv_nonneg
    (fun z hz => (inverseSlope_z_hasDerivAt hB hz).continuousAt.continuousWithinAt)
    (fun z hz => inverseSlope_z_hasDerivAt hB (Ioo_subset_Icc_self hz))
    (fun z hz => by
      have := (inverse_data hB (Ioo_subset_Icc_self hz)).2.2.1
      positivity)

lemma inverseSlope_B_nonneg {B z : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈Icc (0:ℝ) (2/5)) : 0≤ inverseSlopeB B z := by
  have h := inverse_data hB ⟨by linarith [hz.1],hz.2⟩
  have hn : 0<Q0-B-1/2 := by norm_num [Q0]; linarith [hB.2,outer_endpoint_bounds.2.2.2]
  have hQ : 0<Q0-1 := by norm_num [Q0]
  have hW : 0<B+1/2 := by linarith [hB.1]
  dsimp only [inverseSlopeB]
  have t1 : 0≤(Q0-1)/(U B*(qB B)^2) :=
    div_nonneg hQ.le (mul_pos h.1 (pow_pos h.2.1 2)).le
  have t2 : 0≤(Q0-B-1/2)*(B+1/2)/((U B)^3*qB B) :=
    div_nonneg (mul_pos hn hW).le (mul_pos (pow_pos h.1 3) h.2.1).le
  have t3 : 0≤z*(2/((qB B)^2*inverseRoot B z)+1/(qB B*(inverseRoot B z)^3)) :=
    mul_nonneg hz.1 (add_nonneg
      (div_nonneg (by norm_num) (mul_pos (pow_pos h.2.1 2) h.2.2.1).le)
      (div_nonneg (by norm_num) (mul_pos h.2.1 (pow_pos h.2.2.1 3)).le))
  linarith

lemma inverseSlope_B_monotone {z : ℝ} (hz : z∈Icc (0:ℝ) (2/5)) :
    MonotoneOn (fun B => inverseSlope B z) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (inverseSlope_B_hasDerivAt hB ⟨by linarith [hz.1],hz.2⟩).continuousAt.continuousWithinAt)
    (fun B hB => inverseSlope_B_hasDerivAt (Ioo_subset_Icc_self hB) ⟨by linarith [hz.1],hz.2⟩)
    (fun B hB => inverseSlope_B_nonneg (Ioo_subset_Icc_self hB) hz)

lemma inverseSlope_actual {B x : ℝ} (hd : MinusDomain B x) :
    minusK B x/minusSpeed B x=inverseSlope B (minus B x-1/2) := by
  have hz := minus_z_bound hd
  have h := inverse_data hd.1 ⟨hz.1.le,hz.2.le⟩
  have hv := (positive_data hd.1 hd.2.1).2.1
  have hc := UW_circle (outer_domain hd.1)
  have hn := minus_norm hd.1 x
  have he : inverseRoot B (minus B x-1/2)=minusSpeed B x := by
    dsimp [qB] at h
    nlinarith [h.2.2.1,h.2.2.2]
  have hq : qB B=(U B)^2+(B-1/2)^2 := by
    dsimp [qB]
    dsimp [W] at hc
    nlinarith
  have hnum : Q0-B-1/2=(U B)^2+(B-1/2)*(B+1/2) := by
    dsimp [W] at hc
    nlinarith
  have hq0 : (U B)^2+(B-1/2)^2≠0 := hq ▸ h.2.1.ne'
  have hu0 := h.1.ne'
  have hv0 := hv.ne'
  rw [inverseSlope,he,hq,hnum]
  simp only [minusK,minusSpeed,minus,ratio,U] at hq0 hu0 hv0 ⊢
  generalize arc B+1/2=a at *
  generalize Real.cos x=c at *
  generalize Real.sin x=s at *
  obtain ⟨v,hvdef⟩ : ∃ v,v=a*c+(B-1/2)*s := ⟨_,rfl⟩
  rw [← hvdef] at hv0 ⊢
  field_simp [hq0,hu0,hv0]
  rw [hvdef]
  ring

lemma seven_radical_lower : (1573/1000:ℝ)<U (7/10) := by
  have hB : (7/10:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hc := UW_circle (outer_domain hB)
  have hu := U_positive (outer_domain hB)
  norm_num [Q0,W] at hc
  nlinarith

lemma slope_seven_small : inverseSlope (7/10) (3/50)<(351/500:ℝ) := by
  have hB : (7/10:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have h := inverse_data hB (by norm_num : (3/50:ℝ)∈Icc (-(2/5)) (2/5))
  have hv : (198/125:ℝ)< inverseRoot (7/10) (3/50) := by
    have hs := h.2.2.2
    norm_num [qB,Q0] at hs
    nlinarith [h.2.2.1]
  have hn : 0≤Q0-(7/10:ℝ)-1/2 := by norm_num [Q0]
  have h1 : (Q0-7/10-1/2)/(U (7/10)*qB (7/10))≤
      (Q0-7/10-1/2)/((1573/1000)*qB (7/10)) := by
    apply div_le_div_of_nonneg_left hn (by norm_num [qB,Q0])
    exact mul_le_mul_of_nonneg_right seven_radical_lower.le h.2.1.le
  have h2 : (3/50)/(qB (7/10)*inverseRoot (7/10) (3/50))≤
      (3/50)/(qB (7/10)*(198/125)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num [qB,Q0])
    exact mul_le_mul_of_nonneg_left hv.le h.2.1.le
  dsimp [inverseSlope]
  norm_num [qB,Q0] at h1 h2 ⊢
  linarith

lemma slope_seven_large : inverseSlope (7/10) (4/25)<(727/1000:ℝ) := by
  have hB : (7/10:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have h := inverse_data hB (by norm_num : (4/25:ℝ)∈Icc (-(2/5)) (2/5))
  have hv : (1577/1000:ℝ)< inverseRoot (7/10) (4/25) := by
    have hs := h.2.2.2
    norm_num [qB,Q0] at hs
    nlinarith [h.2.2.1]
  have h1 : (Q0-7/10-1/2)/(U (7/10)*qB (7/10))≤
      (Q0-7/10-1/2)/((1573/1000)*qB (7/10)) := by
    apply div_le_div_of_nonneg_left (by norm_num [Q0]) (by norm_num [qB,Q0])
    exact mul_le_mul_of_nonneg_right seven_radical_lower.le h.2.1.le
  have h2 : (4/25)/(qB (7/10)*inverseRoot (7/10) (4/25))≤
      (4/25)/(qB (7/10)*(1577/1000)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num [qB,Q0])
    exact mul_le_mul_of_nonneg_left hv.le h.2.1.le
  dsimp [inverseSlope]
  norm_num [qB,Q0] at h1 h2 ⊢
  linarith

/-- The positive-term majorant in equation (19), on the entire final interval. -/
lemma inverseSlopeB_upper {B : ℝ} (hB : B∈Icc (7/10:ℝ) outerDiagonal) :
    inverseSlopeB B (4/25)<(6/5:ℝ) := by
  have hBi : B∈Icc 0 outerDiagonal := ⟨by linarith [hB.1],hB.2⟩
  have h := inverse_data hBi (by norm_num : (4/25:ℝ)∈Icc (-(2/5)) (2/5))
  have hq : (5289/2500:ℝ)≤qB B := by
    norm_num [qB,Q0]
    linarith [hB.2,outer_endpoint_bounds.2.2.2]
  have hU : (699/500:ℝ)≤U B := by
    have hc := UW_circle (outer_domain hBi)
    have hW : W B≤(7/5:ℝ) := by dsimp [W]; linarith [hB.2,outer_endpoint_bounds.2.2.2]
    have hW0 : 0≤W B := by dsimp [W]; linarith [hBi.1]
    have hs := pow_le_pow_left₀ hW0 hW 2
    norm_num [Q0] at hc
    nlinarith [h.1]
  have hv : (289/200:ℝ)≤ inverseRoot B (4/25) := by
    nlinarith [h.2.2.1,h.2.2.2]
  have hn0 : 0≤Q0-B-1/2 := by norm_num [Q0]; linarith [hB.2,outer_endpoint_bounds.2.2.2]
  have hn : Q0-B-1/2≤Q0-6/5 := by linarith [hB.1]
  have hW : B+1/2≤(7/5:ℝ) := by linarith [hB.2,outer_endpoint_bounds.2.2.2]
  have hW0 : 0≤B+1/2 := by linarith [hB.1]
  have hq2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤5289/2500) hq 2
  have hU3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤699/500) hU 3
  have hv3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤289/200) hv 3
  have hden1 := mul_le_mul hU hq2 (by norm_num) h.1.le
  have hden2 := mul_le_mul hU3 hq (by norm_num) (pow_nonneg h.1.le 3)
  have hden3 := mul_le_mul hq2 hv (by norm_num) (sq_nonneg (qB B))
  have hden4 := mul_le_mul hq hv3 (by norm_num) h.2.1.le
  have hnum := mul_le_mul hn hW hW0 (by norm_num [Q0] : (0:ℝ)≤Q0-6/5)
  have h1 := div_le_div_of_nonneg_left
    (by norm_num [Q0] : (0:ℝ)≤Q0-1) (by norm_num : (0:ℝ)<(699/500)*(5289/2500)^2) hden1
  have h2a := div_le_div_of_nonneg_right hnum (mul_pos (pow_pos h.1 3) h.2.1).le
  have h2b := div_le_div_of_nonneg_left
    (by norm_num [Q0] : (0:ℝ)≤(Q0-6/5)*(7/5))
    (by norm_num : (0:ℝ)<(699/500)^3*(5289/2500)) hden2
  have h3 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤2)
    (by norm_num : (0:ℝ)<(5289/2500)^2*(289/200)) hden3
  have h4 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1)
    (by norm_num : (0:ℝ)<(5289/2500)*(289/200)^3) hden4
  have href : (Q0-1)/((699/500)*(5289/2500)^2)+
      (Q0-6/5)*(7/5)/((699/500)^3*(5289/2500))+
      (4/25)*(2/((5289/2500)^2*(289/200))+1/((5289/2500)*(289/200)^3))<(6/5:ℝ) := by
    norm_num [Q0]
  dsimp [inverseSlopeB]
  linarith

lemma slope_gap_late {B : ℝ} (hB : B∈Icc (7/10:ℝ) outerDiagonal) :
    inverseSlope B (4/25)<LLabel.d1 B := by
  let f : ℝ→ℝ := fun t => LLabel.d1 t-inverseSlope t (4/25)
  have hdom {t : ℝ} (ht : t∈Icc (7/10:ℝ) outerDiagonal) : t∈Icc 0 outerDiagonal :=
    ⟨by linarith [ht.1],ht.2⟩
  have hd (t : ℝ) (ht : t∈Icc (7/10:ℝ) outerDiagonal) :
      HasDerivAt f (LLabel.d2 t-inverseSlopeB t (4/25)) t :=
    (LLabel.d1_hasDerivAt (outer_domain (hdom ht))).sub
      (inverseSlope_B_hasDerivAt (hdom ht) (by norm_num))
  have hm : MonotoneOn f (Icc (7/10:ℝ) outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => hd t (Ioo_subset_Icc_self ht))
      (fun t ht => by
        have hcurv := L_seven_second.trans_le (L_second_monotone
          (Asymmetric.rational_outer_mem (by norm_num)) (hdom (Ioo_subset_Icc_self ht)) ht.1.le)
        linarith [inverseSlopeB_upper (Ioo_subset_Icc_self ht)])
  have hh := hm ⟨le_rfl,(Asymmetric.rational_outer_mem (by norm_num)).2⟩ hB hB.1
  dsimp [f] at hh
  linarith [L_seven_first,slope_seven_large]

lemma target_derivative_positive {B x : ℝ} (hd : MinusDomain B x)
    (hfirst : minusFirst LLabel B x≤0) : 0< minusTarget LLabel LLabel B x := by
  obtain ⟨hB,hsource,hsmall⟩ := nonpositive_angular_location hd hfirst
  have hz := minus_z_bound hd
  have hv := (positive_data hd.1 hd.2.1).2.1
  have hK := (positive_data hd.1 hd.2.1).2.2.2
  have hwork : LLabel.d1 (minus B x)*minusSpeed B x≤1 := by
    dsimp [minusFirst] at hfirst
    linarith
  have hD : LLabel.d1 (minus B x)≤1/minusSpeed B x :=
    (le_div_iff₀ hv).2 hwork
  have hpay := mul_le_mul_of_nonneg_right hD hK.le
  have hratio : inverseSlope B (minus B x-1/2)<LLabel.d1 B := by
    by_cases he : B≤7/10
    · have hsourceSmall := hsmall he
      have h1 := inverseSlope_z_monotone hd.1 ⟨hz.1.le,hz.2.le⟩
        (by norm_num : (3/50:ℝ)∈Icc (-(2/5)) (2/5)) (by linarith)
      have h2 := inverseSlope_B_monotone (by norm_num : (3/50:ℝ)∈Icc 0 (2/5))
        hd.1 (Asymmetric.rational_outer_mem (by norm_num)) he
      have h3 := L_first_late_monotone
        ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num)).2⟩
        ⟨by linarith,hd.1.2⟩ hB.le
      linarith [slope_seven_small,L_67_first]
    · have h1 := inverseSlope_z_monotone hd.1 ⟨hz.1.le,hz.2.le⟩
        (by norm_num : (4/25:ℝ)∈Icc (-(2/5)) (2/5)) (by linarith)
      exact h1.trans_lt (slope_gap_late ⟨by linarith,hd.1.2⟩)
  rw [← inverseSlope_actual hd] at hratio
  have he : 1/minusSpeed B x*minusK B x=minusK B x/minusSpeed B x := by ring
  dsimp only [minusTarget]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.Symmetric

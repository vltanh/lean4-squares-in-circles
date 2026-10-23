module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2LowEndpoints

/-!
# The four original negative-A cut endpoints

Uncompiled transcription of equations (57)--(63) in the scalar
companion. The GA angle remains 1/4 and the AB angle remains 19/50.
Their rotated H/G/B norms are the unaffected pairs from the original
secant assignment.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity Explicit
open PositiveTD.Certificate (C10 C12 S9 S11 C4 S5 h)

theorem cut_domain (e : Cut) : (cutAngle e:ℝ)∈Icc 0 frameCap := by
  cases e <;> norm_num [cutAngle,cutAtG,frameCap]

theorem cut_high_domain (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) : z∈Icc (1/5:ℝ) (7/10:ℝ) := by
  cases e <;> norm_num [cutAngle,cutAtG,h] at hz <;>
    exact ⟨by linarith [hz.1],hz.2⟩

theorem cut_theta_domain (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) : z-(cutAngle e:ℝ)∈Icc 0 frameCap := by
  have hs := cut_domain e
  dsimp [h,frameCap] at hz hs ⊢
  exact ⟨by linarith [hz.1],by linarith [hz.2,hs.1]⟩

@[simp] theorem gammaLo_cast (e : Cut) :
    (gammaLo e:ℝ)=aeval (cutAngle e:ℝ) C10 := by
  cases e <;> norm_num [gammaLo,cutAngle,cutAtG,C10,C4]
@[simp] theorem gammaHi_cast (e : Cut) :
    (gammaHi e:ℝ)=aeval (cutAngle e:ℝ) C12 := by
  cases e <;> norm_num [gammaHi,cutAngle,cutAtG,C12,C10,C4]
@[simp] theorem tauLo_cast (e : Cut) :
    (tauLo e:ℝ)=aeval (cutAngle e:ℝ) S11 := by
  cases e <;> norm_num [tauLo,cutAngle,cutAtG,S11,S9,S5]
@[simp] theorem tauHi_cast (e : Cut) :
    (tauHi e:ℝ)=aeval (cutAngle e:ℝ) S9 := by
  cases e <;> norm_num [tauHi,cutAngle,cutAtG,S9,S5]

theorem cut_trig_bounds (e : Cut) :
    0≤(gammaLo e:ℝ) ∧ (gammaLo e:ℝ)≤Real.cos (cutAngle e:ℝ) ∧
    Real.cos (cutAngle e:ℝ)≤(gammaHi e:ℝ) ∧
    0≤(tauLo e:ℝ) ∧ (tauLo e:ℝ)≤Real.sin (cutAngle e:ℝ) ∧
    Real.sin (cutAngle e:ℝ)≤(tauHi e:ℝ) := by
  have hh := PositiveTD.Certificate.taylor_bounds (cut_domain e)
  simp only [gammaLo_cast,gammaHi_cast,tauLo_cast,tauHi_cast]
  exact ⟨by linarith [hh.2.2.2.1],hh.2.2.2.2.1,hh.2.2.2.2.2,
    hh.1,hh.2.1,hh.2.2.1⟩

theorem theta_trig_lower (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) :
    aeval z (thetaCosLo e)≤Real.cos (z-(cutAngle e:ℝ)) ∧
      aeval z (thetaSinLo e)≤Real.sin (z-(cutAngle e:ℝ)) := by
  have hz' := family_frame_domain .high (cut_high_domain e hz)
  have ht := PositiveTD.Certificate.taylor_bounds hz'
  obtain ⟨hg0,hglo,hghi,hs0,hslo,hshi⟩ := cut_trig_bounds e
  have hcos0 : 0≤Real.cos (cutAngle e:ℝ) := by
    linarith [(transport_trig (cut_domain e)).1]
  have hsin0 : 0≤Real.sin (cutAngle e:ℝ) := (transport_trig (cut_domain e)).2.2.1
  have hzcos0 : 0≤Real.cos z := by linarith [(transport_trig hz').1]
  have hzsin0 : 0≤Real.sin z := (transport_trig hz').2.2.1
  have hC0 : 0≤aeval z C10 := by linarith [ht.2.2.2.1]
  have hCC := mul_le_mul hglo ht.2.2.2.2.1 hC0 hcos0
  have hSS := mul_le_mul hslo ht.2.1 ht.1 hsin0
  have hCS := mul_le_mul hglo ht.2.1 ht.1 hcos0
  have hSC := mul_le_mul hshi ht.2.2.2.2.2 hzcos0
    (show 0≤(tauHi e:ℝ) by linarith)
  constructor
  · simp only [thetaCosLo,map_add,map_mul,aeval_C,Real.cos_sub]
    nlinarith only [hCC,hSS]
  · simp only [thetaSinLo,map_sub,map_mul,aeval_C,Real.sin_sub]
    nlinarith only [hCS,hSC]

def cutPCoefficient : Cut→ℝ→ℝ
  | .gaH,z => Explicit.k .high z | .gaB,z => Explicit.l .high z
  | .abG,z => Explicit.k .high z | .abH,z => Explicit.k .high z
def cutQCoefficient : Cut→ℝ→ℝ
  | .gaH,_ => 1 | .gaB,z => Explicit.m .high z
  | .abG,z => Explicit.l .high z | .abH,_ => 1
def cutCostCoefficient (e : Cut) (z : ℝ) : ℝ :=
  if cutRole e=0 then 1 else Explicit.l .high z
def cutV (e : Cut) (z : ℝ) : ℝ :=
  cutCostCoefficient e z*(Real.cos (z-(cutAngle e:ℝ))-1)-
    R*(pairNorm (cutPCoefficient e z) (cutQCoefficient e z) (-(z-(cutAngle e:ℝ)))-
      pairNorm (cutPCoefficient e z) (cutQCoefficient e z) 0)
def cutNorms (e : Cut) (z : ℝ) : Fin 4→ℝ :=
  Function.update (scaledNorms .high (cutAtG e) (cutAngle e:ℝ) z) (cutRole e)
    (Real.cos (cutAngle e:ℝ)*
      pairNorm (cutPCoefficient e z) (cutQCoefficient e z) (-(z-(cutAngle e:ℝ))))

theorem cut_coefficients_positive (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) :
    0<cutPCoefficient e z ∧ 0<cutQCoefficient e z ∧ 0<cutCostCoefficient e z := by
  obtain ⟨hk,hl,_,hm⟩ := family_positive .high (cut_high_domain e hz)
  cases e
  · simpa [cutPCoefficient,cutQCoefficient,cutCostCoefficient,cutRole] using hk
  · simpa [cutPCoefficient,cutQCoefficient,cutCostCoefficient,cutRole] using ⟨hl,hm,hl⟩
  · simpa [cutPCoefficient,cutQCoefficient,cutCostCoefficient,cutRole] using ⟨hk,hl,hl⟩
  · simpa [cutPCoefficient,cutQCoefficient,cutCostCoefficient,cutRole] using hk

theorem cut_norms_nonnegative (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) (i : Fin 4) : 0≤cutNorms e z i := by
  have hc : 0≤Real.cos (cutAngle e:ℝ) := by
    linarith [(transport_trig (cut_domain e)).1]
  by_cases hi : i=cutRole e
  · subst i
    simpa [cutNorms] using mul_nonneg hc
      (PositiveTD.Certificate.pairNorm_nonneg (cutPCoefficient e z)
        (cutQCoefficient e z) (-(z-(cutAngle e:ℝ))))
  · simpa [cutNorms,hi] using scaled_norms_nonnegative .high (cutAtG e)
      (z:=z) (cut_domain e) i

theorem cut_scaled_identity (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) :
    Real.cos (cutAngle e:ℝ)*
        (reducedBaseline .high (cutAtG e) (cutAngle e:ℝ) z+cutV e z)=
      Real.cos (cutAngle e:ℝ)*(nonradical .high z-Explicit.l .high z)+Explicit.l .high z+
        (13/12)*Explicit.l .high z*Real.sin (cutAngle e:ℝ)+
        Real.cos (cutAngle e:ℝ)*cutCostCoefficient e z*(Real.cos (z-(cutAngle e:ℝ))-1)-
        R*normSum .high (cutNorms e z) := by
  have he := scaled_identity .high (cutAtG e) (cut_high_domain e hz) (cut_domain e)
  cases e <;>
    simp only [cutNorms,cutV,cutPCoefficient,cutQCoefficient,cutCostCoefficient,
      cutRole,cutAtG,normSum,scaledNorms,norms,lambdaG,lambdaB,
      Function.update_same,Function.update_noteq,↓reduceIte,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Explicit.m] at he ⊢ <;>
    nlinarith only [he]

theorem cut_elementary_lower (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) :
    aeval z (cutA e)≤
      Real.cos (cutAngle e:ℝ)*(nonradical .high z-Explicit.l .high z)+Explicit.l .high z+
        (13/12)*Explicit.l .high z*Real.sin (cutAngle e:ℝ)+
        Real.cos (cutAngle e:ℝ)*cutCostCoefficient e z*(Real.cos (z-(cutAngle e:ℝ))-1) := by
  have hz' := cut_high_domain e hz
  obtain ⟨hg0,hglo,hghi,hs0,hslo,hshi⟩ := cut_trig_bounds e
  have hc0 : 0≤Real.cos (cutAngle e:ℝ) := by
    linarith [(transport_trig (cut_domain e)).1]
  have hgHi0 : 0≤(gammaHi e:ℝ) := hc0.trans hghi
  have hI := elementary_lower .high hz'
  have hI0 : 0≤aeval z (elementary .high)-Explicit.l .high z := by
    linarith [elementary_minus_l_positive .high hz']
  have hprod := mul_le_mul hglo (sub_le_sub_right hI (Explicit.l .high z)) hI0 hc0
  have hsine := mul_le_mul_of_nonneg_left hslo
    (show 0≤(13/12)*Explicit.l .high z by
      have hh := (family_positive .high hz').2.1; positivity)
  have hq := (cut_coefficients_positive e hz).2.2
  have htheta := (theta_trig_lower e hz).1
  have hcos₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right htheta 1)
    (show 0≤(gammaHi e:ℝ)*cutCostCoefficient e z by positivity)
  have hcos₂ := mul_le_mul_of_nonpos_right
    (mul_le_mul_of_nonneg_right hghi hq.le)
    (sub_nonpos.mpr (Real.cos_le_one (z-(cutAngle e:ℝ))))
  have hqeval : aeval z (if cutRole e=0 then (1:ℚ[X]) else l .high)=cutCostCoefficient e z := by
    by_cases hh : cutRole e=0 <;> simp [hh,cutCostCoefficient]
  norm_num only [cutA,map_add,map_sub,map_mul,map_one,aeval_C,Rat.cast_mul,
    l_eval,hqeval]
  nlinarith only [hprod,hsine,hcos₁,hcos₂]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate

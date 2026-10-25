module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHSlopes

/-!
# Removing far-EH same-block saturation with its original charge

Uncompiled equations (15)--(17) of the far-low companion. The two
identities retain both original positive and negative masses. Their
strict numerical reserves are weakened to closed inequalities, so the
zero-mass cases are included in the same theorem statements.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEH.SameBlock
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem short_trig {t : ℝ} (ht : t∈Icc (0:ℝ) (3/5)) :
    (33/40:ℝ)<Real.cos t ∧ Real.sin t<113/200 ∧
      (47/50)*t≤Real.sin t := by
  have hb := trig_bracket (l:=0) (u:=(3/5:ℝ)) (by norm_num)
    (by linarith [Real.pi_gt_three]) ht
  have hs := sin_lower_seven ht.1
  have ht2 : t^2≤(3/5:ℝ)^2 := by nlinarith [ht.1,ht.2]
  have ht3 : t^3≤(9/25)*t := by nlinarith [mul_le_mul_of_nonneg_right ht2 ht.1]
  have hh : 0≤t^5*(42-t^2) := mul_nonneg (pow_nonneg ht.1 5) (by linarith)
  norm_num at hb
  exact ⟨by linarith [hb.2.2.1],by linarith [hb.2.1],by nlinarith⟩

theorem short_cosine_loss {t : ℝ} (ht : t∈Icc (0:ℝ) (3/5)) :
    1-Real.cos t≤(31/100)*Real.sin t := by
  have hd (x : ℝ) : HasDerivAt (fun x => (31/100)*Real.sin x+Real.cos x-1)
      ((31/100)*Real.cos x-Real.sin x) x := by
    convert (((Real.hasDerivAt_sin x).const_mul (31/100)).add
      (Real.hasDerivAt_cos x)).sub_const 1 using 1 <;> ring
  have hdd (x : ℝ) : HasDerivAt (fun x => (31/100)*Real.cos x-Real.sin x)
      (-(31/100)*Real.sin x-Real.cos x) x := by
    convert ((Real.hasDerivAt_cos x).const_mul (31/100)).sub
      (Real.hasDerivAt_sin x) using 1 <;> ring
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (3/5))
      (fun x => (31/100)*Real.sin x+Real.cos x-1) := by
    apply concave_of_deriv2 (fun x _ => hd x) (fun x _ => hdd x)
    intro x hx
    have hs := (transport_trig (show x∈Icc 0 frameCap by
      exact ⟨hx.1,by norm_num [frameCap]; linarith [hx.2]⟩)).2.2.1
    linarith [(short_trig hx).1]
  have he : 0≤(31/100)*Real.sin (3/5:ℝ)+Real.cos (3/5:ℝ)-1 := by
    have hs := sin_lower_seven (show (0:ℝ)≤3/5 by norm_num)
    have hh := cos_lower_six (show (0:ℝ)≤3/5 by norm_num)
    norm_num at hs hh
    linarith
  have hh := hc.min_le_of_mem_Icc (by norm_num) (by norm_num) ht
  simp only [Real.sin_zero,Real.cos_zero,mul_zero,zero_add,sub_self,min_eq_left he] at hh
  linarith

theorem cap_phi : (1409/1000:ℝ)<PositiveAngularEnvelope.phi frameCap ∧
    (3/25:ℝ)<Real.cos frameCap-Real.sin frameCap := by
  have hb := trig_bracket (l:=0) (u:=frameCap) (by norm_num [frameCap])
    (by dsimp [frameCap]; linarith [Real.pi_gt_three])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  norm_num [frameCap] at hb
  exact ⟨OrdinaryAngleConcavity.phi_cap_lower,by linarith [hb.2.2.1,hb.2.1]⟩

def phiD (t : ℝ) : ℝ := Real.cos t-Real.sin t
theorem phi_derivative (t : ℝ) : HasDerivAt PositiveAngularEnvelope.phi (phiD t) t :=
  ((Real.hasDerivAt_cos t).fun_add (Real.hasDerivAt_sin t)).congr_deriv
    (by dsimp only [phiD]; ring)
theorem phiD_derivative (t : ℝ) : HasDerivAt phiD (-PositiveAngularEnvelope.phi t) t :=
  ((Real.hasDerivAt_cos t).fun_sub (Real.hasDerivAt_sin t)).congr_deriv
    (by dsimp only [PositiveAngularEnvelope.phi]; ring)

theorem phiD_antitone : AntitoneOn phiD (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun t _ => (phiD_derivative t).continuousAt.continuousWithinAt)
    (fun t _ => phiD_derivative t)
  intro t ht
  have hh := transport_trig (Ioo_subset_Icc_self ht)
  dsimp [PositiveAngularEnvelope.phi]
  linarith [hh.1,hh.2.2.1]

theorem phi_difference {P N : ℝ} (hN : 0≤N) (hNP : N≤P)
    (hP : P≤frameCap) :
    PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)≤PositiveAngularEnvelope.phi P-PositiveAngularEnvelope.phi (P-N) := by
  have hNcap : N≤frameCap := hNP.trans hP
  have hd (x : ℝ) : HasDerivAt
      (fun x => PositiveAngularEnvelope.phi x-PositiveAngularEnvelope.phi (x-N))
      (phiD x-phiD (x-N)) x :=
    (phi_derivative x).fun_sub (HasDerivAt.comp_sub_const x N (phi_derivative (x-N)))
  have hm : AntitoneOn
      (fun x => PositiveAngularEnvelope.phi x-PositiveAngularEnvelope.phi (x-N))
      (Icc N frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
    intro x hx
    have hh := phiD_antitone
      (show x-N∈Icc 0 frameCap from ⟨by linarith [hx.1],by linarith [hx.2]⟩)
      (show x∈Icc 0 frameCap from ⟨by linarith [hx.1],hx.2.le⟩)
      (by linarith)
    linarith
  exact hm ⟨hNP,hP⟩ ⟨hNcap,le_rfl⟩ hP

theorem negative_reserve {a b P N : ℝ} (ha : (3/5:ℝ)≤a)
    (hab : b≤(5/3)*a) (hP : 0≤P) (hPN : P≤N) (hN : N≤3/5) :
    (4/125)*P≤ mixedBlock R a b P N-V R a b (N-P) := by
  have ha0 : 0≤a := by linarith
  have hNs : N∈Icc (0:ℝ) (3/5) := ⟨hP.trans hPN,hN⟩
  have hPs : P∈Icc (0:ℝ) (3/5) := ⟨hP,hPN.trans hN⟩
  have hNP : N-P∈Icc (0:ℝ) N := ⟨by linarith,by linarith⟩
  have hcos : Real.cos N≤Real.cos (N-P) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hNP.1
      (by linarith [Real.pi_gt_three]) hNP.2
  have hcoef := mul_le_mul_of_nonpos_right hab (sub_nonpos.mpr hcos)
  have hc := short_trig hNs
  have hs := short_trig hPs
  have hfirst : 0≤(1-(5/3)*Real.cos N)*(Real.cos P-1) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith [hc.1])
      (sub_nonpos.mpr (Real.cos_le_one P))
  have hsin : 0≤Real.sin P := by linarith [hs.2.2]
  have hsecond : (329/10000)*P≤a*(1-(5/3)*Real.sin N)*Real.sin P := by
    have hfactor : (7/120:ℝ)≤1-(5/3)*Real.sin N := by linarith [hc.2.1]
    have hprod := mul_le_mul ha hfactor (by norm_num : (0:ℝ)≤7/120) ha0
    have hprod' := mul_le_mul hprod hs.2.2
      (by positivity : (0:ℝ)≤(47/50)*P) (by positivity : (0:ℝ)≤a*(1-(5/3)*Real.sin N))
    nlinarith only [hprod']
  have hid : mixedBlock R a b P N-V R a b (N-P)=
      a*(PositiveAngularEnvelope.phi P-1)+b*(Real.cos N-Real.cos (N-P)) := by
    dsimp only [mixedBlock,V]
    rw [show -(N-P)=P-N by ring]
    ring
  have htrig : PositiveAngularEnvelope.phi P-1+(5/3)*(Real.cos N-Real.cos (N-P))=
      (1-(5/3)*Real.cos N)*(Real.cos P-1)+
        (1-(5/3)*Real.sin N)*Real.sin P := by
    rw [Real.cos_sub]
    dsimp only [PositiveAngularEnvelope.phi]
    ring
  have htrig' := congrArg (fun x : ℝ => a*x) htrig
  rw [hid]
  nlinarith [mul_nonneg ha0 hfirst]

theorem positive_reserve {a b P N : ℝ} (ha : (3/5:ℝ)≤a)
    (hab : b≤(5/3)*a) (hN : 0≤N) (hNP : N≤P)
    (hP : P≤frameCap) (hNs : N≤3/5) :
    (11/500)*N≤ mixedBlock R a b P N-U R a b (P-N) := by
  have ha0 : 0≤a := by linarith
  have hn : N∈Icc (0:ℝ) (3/5) := ⟨hN,hNs⟩
  have hs := short_trig hn
  have hsin : 0≤Real.sin N := by linarith [hs.2.2]
  have hloss := short_cosine_loss hn
  have hcos := Real.cos_le_one N
  have hcoef := mul_le_mul_of_nonpos_right hab (by linarith : Real.cos N-1≤0)
  have hdiff := mul_le_mul_of_nonneg_left (phi_difference hN hNP hP) ha0
  have hc := cap_phi
  have hcap : (11/500)*N≤a*(PositiveAngularEnvelope.phi frameCap-
      PositiveAngularEnvelope.phi (frameCap-N)+(5/3)*(Real.cos N-1)) := by
    have hid : PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)+
        (5/3)*(Real.cos N-1)=
        (PositiveAngularEnvelope.phi frameCap-5/3)*(1-Real.cos N)+
          (Real.cos frameCap-Real.sin frameCap)*Real.sin N := by
      dsimp only [PositiveAngularEnvelope.phi]
      rw [Real.cos_sub,Real.sin_sub]
      ring
    have hfirst := mul_le_mul_of_nonneg_right hc.1.le (by linarith : 0≤1-Real.cos N)
    have hsecond := mul_le_mul_of_nonneg_right hc.2.le hsin
    have hl : (11/300)*N≤PositiveAngularEnvelope.phi frameCap-
        PositiveAngularEnvelope.phi (frameCap-N)+(5/3)*(Real.cos N-1) := by
      rw [hid]
      nlinarith
    have hm := mul_le_mul ha hl (by positivity : (0:ℝ)≤(11/300)*N) ha0
    nlinarith only [hm]
  have hid : mixedBlock R a b P N-U R a b (P-N)=
      a*(PositiveAngularEnvelope.phi P-PositiveAngularEnvelope.phi (P-N))+
        b*(Real.cos N-1) := by
    dsimp only [mixedBlock,U]
    ring
  rw [hid]
  nlinarith only [hcap,hdiff,hcoef]

theorem negative_charged {a b P N : ℝ} (ha : (3/5:ℝ)≤a)
    (hab : b≤(5/3)*a) (hP : 0≤P) (hPN : P≤N) (hN : N≤3/5) :
    V R a b (N-P)≤ mixedBlock R a b P N-epsilon*P := by
  have hh := negative_reserve ha hab hP hPN hN
  dsimp [epsilon]
  nlinarith

theorem positive_charged {a b P N : ℝ} (ha : (3/5:ℝ)≤a)
    (hab : b≤(5/3)*a) (hN : 0≤N) (hNP : N≤P)
    (hP : P≤frameCap) (hNs : N≤3/5) :
    U R a b (P-N)-epsilon*(P-N)≤ mixedBlock R a b P N-epsilon*P := by
  have hh := positive_reserve ha hab hN hNP hP hNs
  dsimp [epsilon]
  nlinarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEH.SameBlock

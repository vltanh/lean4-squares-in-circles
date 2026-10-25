module

public import SquaresInCircles.Eight.TableFree.ActualSortedSupport
public import SquaresInCircles.Eight.TableFree.BalancedNegativeGain
public import SquaresInCircles.Eight.TableFree.SoleNegativeTGain
public import SquaresInCircles.Eight.TableFree.GlobalGAOneAngleFunctions

/-!
# The changed sorted-D support after a genuine negative T primary

Uncompiled source. The D baseline is the clipped support at the actual
q. Its negative increment is bounded by the minimum of the old D and A
charges. The diagonal comparison uses an explicit supporting point and
the sorting inequality, so it also covers the support-transition tie.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SoleNegativeTDSupport
open ActualSortedSupport PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope SingleAngleConcavity SoleNormGain

def increment (q p g d : ℝ) : ℝ :=
  p*(edgeWidth d-1)+ActualSortedSupport.support q p g-ActualSortedSupport.support q (p*Real.cos d) (g+p*Real.sin d)

def actualIncrement (q p g d : ℝ) (D : SignedPoint) : ℝ :=
  p*(edgeWidth d-1)+ActualSortedSupport.support q p g-
    (p*Real.cos d*D.a+(g+p*Real.sin d)*(-D.y))

@[simp] theorem increment_zero (q p g : ℝ) : increment q p g 0=0 := by
  simp [increment,edgeWidth,pairWidth]

theorem full_identity {q p g d : ℝ} (hd : |d|≤frameCap) :
    p*(edgeWidth d-1)+full q p g-full q (p*Real.cos d) (g+p*Real.sin d)=
      p*psi d-Real.sqrt q*(pairNorm p g d-pairNorm p g 0) := by
  have hn := GlobalGA.Secondary.one_force_norm g p d
  rw [pairNorm_symm g p d] at hn
  dsimp [full]
  rw [hn,← pairNorm_zero p g]
  have hw := width_add_half_phi hd
  dsimp [PositiveAngularEnvelope.phi] at hw
  nlinarith [congrArg (fun x : ℝ => p*x) hw]

theorem force_sum_positive {p g d : ℝ} (hp : 0<p) (hgp : p/2≤g)
    (hd : |d|≤frameCap) : 0<p*Real.cos d+(g+p*Real.sin d) := by
  obtain ⟨hc,hs⟩ := small_angle hd
  have hs' := (abs_le.mp hs).1
  have hcos := mul_le_mul_of_nonneg_left hc hp.le
  have hsin := mul_le_mul_of_nonneg_left hs' hp.le
  norm_num [frameCap] at hcos hsin
  linarith

theorem increment_le_actual {q p g d : ℝ} {D : SignedPoint}
    (hq : 0≤q) (hs : D.Sorted) (hy : D.y≤0) (hc : D.Contained q)
    (hp : 0<p) (hgp : p/2≤g) (hd : |d|≤frameCap) :
    increment q p g d≤actualIncrement q p g d D := by
  have hh := actual_negative_support (f:=p*Real.cos d) (g:=g+p*Real.sin d)
    hq hs hy hc (force_sum_positive hp hgp hd).le
  dsimp [increment,actualIncrement]
  linarith

theorem full_lower {q p g d : ℝ} (hq : 0≤q) (hp : 0<p)
    (hgp : g<p) (hglo : p/2≤g) (hd : |d|≤frameCap) :
    p*psi d-Real.sqrt q*(pairNorm p g d-pairNorm p g 0)≤ increment q p g d := by
  have hh := support_le_full hq (force_sum_positive hp hglo hd).le
  rw [← full_identity hd]
  dsimp [increment]
  rw [ActualSortedSupport.support,if_neg (not_le.mpr hgp)]
  linarith

theorem positive_diagonal_identity {q p g v : ℝ}
    (hp : 0≤p) (hpg : p≤g) (hv : v∈Icc 0 frameCap) :
    increment q p g v= -(corner q-1/2)*p*(PositiveAngularEnvelope.phi v-1) := by
  have hsin := (transport_trig hv).2.2.1
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one v) hp
  have hs := mul_nonneg hp hsin
  have hforce : p*Real.cos v≤g+p*Real.sin v := by linarith
  rw [increment,ActualSortedSupport.support,if_pos hpg,ActualSortedSupport.support,if_pos hforce,edgeWidth_positive_formula hv]
  dsimp [ActualSortedSupport.diagonal,PositiveAngularEnvelope.phi]
  ring

theorem positive_diagonal_lower {q p g v : ℝ}
    (hL : qLow≤q) (hQ : q≤qCap) (hp : 0≤p) (hpg : p≤g)
    (hv : v∈Icc 0 frameCap) : -(2/5)*p*v≤ increment q p g v := by
  rw [positive_diagonal_identity hp hpg hv]
  have hphi : 0≤PositiveAngularEnvelope.phi v-1 := sub_nonneg.mpr (CorrelatedSameBlock.one_le_phi hv)
  have hphiU : PositiveAngularEnvelope.phi v-1≤v := by
    dsimp [PositiveAngularEnvelope.phi]
    linarith [Real.cos_le_one v,Real.sin_le hv.1]
  have hcorner := corner_bounds hL hQ
  have hpv := mul_le_mul_of_nonneg_left hphiU hp
  have hmult := mul_le_mul_of_nonneg_left hpv (by linarith : 0≤corner q-1/2)
  have hcoef := mul_le_mul_of_nonneg_right
    (show corner q-1/2≤2/5 by linarith) (mul_nonneg hp hv.1)
  nlinarith

theorem positive_full_lower {q p g v : ℝ}
    (hq : 0≤q) (hp : 0<p) (hgp : g<p) (hglo : p/2≤g)
    (hv : v∈Icc 0 frameCap) :
    U (Real.sqrt q) g p v≤ increment q p g v := by
  have hh := full_lower hq hp hgp hglo
    (show |v|≤frameCap by rw [abs_of_nonneg hv.1]; exact hv.2)
  have hpsi := psi_positive hv
  have hphi := sub_nonneg.mpr (CorrelatedSameBlock.one_le_phi hv)
  have hcoef := mul_le_mul_of_nonneg_right hgp.le hphi
  rw [hpsi,pairNorm_symm p g v,pairNorm_symm p g 0] at hh
  dsimp [U]
  linarith

theorem negative_diagonal_lower {q p g v : ℝ}
    (hq : 0≤q) (hp : 0<p) (hpg : p≤g) (hv : v∈Icc 0 frameCap) :
    p*Vnu (Real.sqrt q) 1 1 1 v≤ increment q p g (-v) := by
  obtain ⟨hc,_,hs,hsU,_⟩ := transport_trig hv
  have hgn : 0<g-p*Real.sin v := by
    have hh := mul_lt_mul_of_pos_left hsU hp
    linarith
  have hsum : 0≤p*Real.cos v+(g-p*Real.sin v) := by
    have hh := mul_pos hp (show 0<Real.cos v by linarith)
    linarith
  obtain ⟨Ka,Kb,Kcircle,_,_,_,Ktangent,Ksupports⟩ := point hq hsum hgn
  have hfull := raw_full (f:=p*Real.cos v) (g:=p*(1-Real.sin v)) hq Kcircle.le
  have hsort := mul_le_mul_of_nonneg_left Ktangent (sub_nonneg.mpr hpg)
  have hbase : full q p p=diagonal q p p :=
    full_diagonal hq rfl (by linarith)
  have hfullid := full_identity (q:=q) (p:=p) (g:=p)
    (show |-v|≤frameCap by rw [abs_neg,abs_of_nonneg hv.1]; exact hv.2)
  rw [psi_negative hv] at hfullid
  have hhom0 := pairNorm_homogeneous hp.le 1 1 0
  have hhomv := pairNorm_homogeneous hp.le 1 1 (-v)
  simp only [mul_one] at hhom0 hhomv
  rw [hhom0,hhomv,hbase] at hfullid
  simp only [Real.cos_neg,Real.sin_neg] at hfullid
  have he : p+p*(-Real.sin v)=p*(1-Real.sin v) := by ring
  rw [he] at hfullid
  have hidentity : p*Vnu (Real.sqrt q) 1 1 1 v=
      p*(edgeWidth (-v)-1)+diagonal q p p-
        full q (p*Real.cos v) (p*(1-Real.sin v)) := by
    simp only [Vnu]
    linear_combination -hfullid
  have hinc : increment q p g (-v)=p*(edgeWidth (-v)-1)+diagonal q p g-
      (p*Real.cos v*Ka+(g-p*Real.sin v)*Kb) := by
    rw [increment,Real.cos_neg,Real.sin_neg,
      show g+p*-Real.sin v=g-p*Real.sin v by ring,← Ksupports,ActualSortedSupport.support,
      if_pos hpg]
  rw [hidentity,hinc]
  simp only [ActualSortedSupport.diagonal] at hidentity hbase ⊢
  linarith

theorem negative_full_old {q p c g v : ℝ}
    (hq : 0≤q) (hp : 0<p) (hc : 0<c) (hcg : c≤g)
    (hgp : g<p) (hpc : p≤2*c) (hv : v∈Icc 0 frameCap) :
    Vnu (Real.sqrt q) p c (max p c) v≤ increment q p g (-v) := by
  have hcp : c≤p := hcg.trans hgp.le
  have hcgain := normGain_smaller_mono (Real.sqrt_nonneg q) hp hv
    (show c∈Icc (p/2) p from ⟨by linarith,hcp⟩)
    (show g∈Icc (p/2) p from ⟨by linarith,hgp.le⟩) hcg
  have hh := full_lower hq hp hgp (by linarith : p/2≤g)
    (show |-v|≤frameCap by rw [abs_neg,abs_of_nonneg hv.1]; exact hv.2)
  rw [psi_negative hv] at hh
  rw [max_eq_left hcp]
  dsimp [normGain] at hcgain
  rw [pairNorm_symm c p 0,pairNorm_symm c p (-v),
    pairNorm_symm g p 0,pairNorm_symm g p (-v)] at hcgain
  dsimp [Vnu]
  linarith

theorem negative_min {q p c g k l v : ℝ}
    (hL : qLow≤q) (hp : 1≤p) (hc : 0<c) (hcg : c≤g) (hpc : p≤2*c)
    (hk : 0<k) (hl : 0<l) (hkl : k+l≤2) (hlinear : 11*k+l≤12)
    (hv : v∈Icc 0 frameCap) :
    min (Vnu (Real.sqrt q) p c (max p c) v)
      (Vnu (Real.sqrt q) l k l v)≤ increment q p g (-v) := by
  have hq : 0≤q := by norm_num [qLow] at hL; linarith
  have hR : 3/2≤Real.sqrt q := by
    have hh := Real.sq_sqrt hq
    norm_num [qLow] at hL
    nlinarith [Real.sqrt_nonneg q]
  by_cases hpg : p≤g
  · have hA := BalancedNegativeGain.dominates_A hR hk hl hkl hlinear hp hv
    exact (min_le_right _ _).trans
      (hA.trans (negative_diagonal_lower hq (by linarith) hpg hv))
  · exact (min_le_left _ _).trans
      (negative_full_old hq (by linarith) hc hcg (lt_of_not_ge hpg) hpc hv)

theorem TD_gain {q p c s : ℝ}
    (hL : qLow≤q) (hQ : q≤qCap) (hp : 0≤p) (hc : 0<c)
    (hs : s∈Ioc 0 (3/10:ℝ)) :
    (21/20)*c*s<c*((1/Real.cos s-1)/2+(13/12)*Real.tan s)-
      ActualSortedSupport.support q p (c/Real.cos s)+ActualSortedSupport.support q p c := by
  have hs' : s∈Icc 0 frameCap :=
    ⟨hs.1.le,by norm_num [frameCap]; linarith [hs.2]⟩
  have hcos : 0<Real.cos s := by linarith [(transport_trig hs').1]
  have hsec : c≤c/Real.cos s := by
    apply (le_div_iff₀ hcos).2
    have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one s) hc.le
    simpa only [mul_one] using hh
  have hlip := second_lipschitz_nine_tenths hL hQ
    (show 0≤p+c by positivity) (show 0≤p+c/Real.cos s by positivity)
    (div_pos hc hcos) hsec
  have hgain := mul_lt_mul_of_pos_left (SoleNegativeTGain.TD_strict hs) hc
  have hid : c/Real.cos s-c=c*(1/Real.cos s-1) := by ring
  rw [hid] at hlip
  nlinarith

theorem sorted_correction {q p c : ℝ}
    (hL : qLow≤q) (hQ : q≤qCap) (hp : 0≤p) (hc : 0≤c) (hpc : p≤c)
    (hN : Real.sqrt (p^2+c^2)≤307/200) :
    (8/25)*(c-p)^2≤full q p c-ActualSortedSupport.support q p c := by
  rw [ActualSortedSupport.support,if_pos hpc]
  exact full_gap hL hQ hp hc hN

end SquaresInCircles.Eight.TableFree.SoleNegativeTDSupport

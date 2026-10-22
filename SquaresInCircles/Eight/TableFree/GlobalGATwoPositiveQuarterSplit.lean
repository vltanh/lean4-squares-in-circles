module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveScalar

/-!
# Fixed-total split concavity through one quarter radian

Uncompiled Section 5 of the far-low genuine-EH companion. The original
A support is axial on this entire interval. The two sine contributions
are bounded with their fixed sum a+z, rather than separately replacing
both angles by the upper endpoint. The shifted coefficient function and
its original min/max kink are retained without alteration.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.QuarterSplit
open Candidate Secondary PositiveTD PositiveAngularEnvelope OrdinaryAngleConcavity
open SplitConcavityTools Split

theorem frame {t : ℝ} (ht : t∈Icc (0:ℝ) (1/4)) : t∈Icc 0 frameCap :=
  ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩

theorem trig {x : ℝ} (hx : x∈Icc (0:ℝ) (1/4)) :
    (31/32:ℝ)≤Real.cos x ∧ 0≤Real.sin x ∧ Real.sin x≤x := by
  have h2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hc := Real.one_sub_sq_div_two_le_cos (x:=x)
  exact ⟨by nlinarith,(transport_trig (frame hx)).2.2.1,Real.sin_le_self hx.1⟩

theorem charge_axial {a : ℝ} (ha : a≤1/4) : ASupport.charge a=ASupport.axialCharge a := by
  rw [ASupport.charge,if_pos (show a≤ASupport.alpha by linarith [ASupport.alpha_bounds.1])]

theorem tilted_upper {c z : ℝ} (hc : 0<c) : tilted c z≤(1043/1000)*c := by
  have hid : (Real.cos z+eta*Real.sin z)^2+
      (Real.sin z-eta*Real.cos z)^2=1+eta^2 := by
    linear_combination (1+eta^2)*(Real.sin_sq_add_cos_sq z)
  have hfactor : Real.cos z+eta*Real.sin z≤(1043/1000:ℝ) := by
    dsimp [eta] at hid
    nlinarith [sq_nonneg (Real.sin z-eta*Real.cos z)]
  have hh := mul_le_mul_of_nonneg_left hfactor hc.le
  simpa only [tilted,mul_comm] using hh

theorem rest_curvature {c l t a : ℝ} (hc : 0<c) (hl : 0<l)
    (hcl : c≤(3/2)*l) (ht : t∈Icc (0:ℝ) (1/4)) (ha : a∈Icc 0 t) :
    smoothDD c t a+l*ASupport.axialDD a+(12/25)*tilted c (t-a)<-(1/10)*l := by
  have ha' : a∈Icc (0:ℝ) (1/4) := ⟨ha.1,ha.2.trans ht.2⟩
  have hz : t-a∈Icc (0:ℝ) (1/4) := ⟨by linarith [ha.2],by linarith [ht.2,ha.1]⟩
  have hta := trig ha'
  have htz := trig hz
  have hsig := mul_le_mul_of_nonneg_right
    (show sigma-1/2≤229/250 by linarith [sigma_bound]) htz.2.1
  have hax := mul_le_mul_of_nonneg_right
    (show axial-1/2≤183/200 by linarith [axial_bounds.2]) hta.2.1
  have hcz : -Real.cos (t-a)/2+(sigma-1/2)*Real.sin (t-a)≤
      -31/64+(229/250)*(t-a) := by linarith [htz.1,htz.2.2]
  have hla : ASupport.axialDD a≤-31/64+(183/200)*a := by
    dsimp [ASupport.axialDD]
    linarith [hta.1,hta.2.2]
  have hczpaid := mul_le_mul_of_nonneg_left hcz hc.le
  have hlapaid := mul_le_mul_of_nonneg_left hla hl.le
  have hmpaid := mul_le_mul_of_nonneg_left (tilted_upper (z:=t-a) hc)
    (by norm_num : (0:ℝ)≤12/25)
  have hratio := mul_le_mul_of_nonneg_right hcl
    (show 0≤-31/64+(229/250)*(t-a)+(12/25)*(1043/1000) by linarith [hz.1])
  have htotal := mul_le_mul_of_nonneg_left ht.2 hl.le
  have hapos := mul_nonneg hl.le ha.1
  dsimp [smoothDD] at hczpaid ⊢
  nlinarith only [hczpaid,hlapaid,hmpaid,hratio,htotal,hapos,hl]

theorem rest_concave {c l t : ℝ} (hc : 0<c) (hl : 0<l)
    (hcl : c≤(3/2)*l) (ht : t∈Icc (0:ℝ) (1/4)) :
    ConcaveOn ℝ (Icc 0 t) (axialRest (12/25) c l t) := by
  apply concave_of_deriv2 (fun a _ => axial_derivative (12/25) c l t a)
    (fun a _ => axial_second (12/25) c l t a)
  intro a ha
  linarith [rest_curvature hc hl hcl ht ha]

theorem tilted_lower {c t a : ℝ} (hc : 0<c)
    (ht : t∈Icc (0:ℝ) (1/4)) (ha : a∈Icc 0 t) : c/2≤tilted c (t-a) := by
  have hz : t-a∈Icc (0:ℝ) (1/4) := ⟨by linarith [ha.2],by linarith [ht.2,ha.1]⟩
  have htr := trig hz
  have hp := mul_nonneg (show 0≤eta by norm_num [eta]) htr.2.1
  have hf : (1/2:ℝ)≤Real.cos (t-a)+eta*Real.sin (t-a) := by linarith [htr.1]
  have hh := mul_le_mul_of_nonneg_left hf hc.le
  simpa [tilted,div_eq_mul_inv,mul_comm] using hh

theorem scalar_concave {c l t s g e : ℝ}
    (hc : 0<c) (hl : 0<l) (hcl : c≤(3/2)*l)
    (ht : t∈Icc (0:ℝ) (1/4)) (hs : |s|≤frameCap)
    (hg : 0≤g) (he : e≤0) (heLow : Real.cos frameCap-1≤e)
    (hePos : 0<s→e=0)
    (hm : ∀a∈Icc 0 t,tilted c (t-a)≤(3/2)*l) :
    ConcaveOn ℝ (Icc 0 t)
      (fun a => Coefficient.H l s g e (tilted c (t-a))+rest c l t a) := by
  have hH := Coefficient.H_shifted_low (L:=c/2) (U:=(3/2)*l)
    hl (by positivity) le_rfl hs hg he heLow hePos
  have hcomp := compose hH.1 hH.2 (tilted_concave hc (frame ht))
    (fun a ha => ⟨tilted_lower hc ht ha,hm a ha⟩)
  have hsum := hcomp.add (rest_concave hc hl hcl ht)
  have heq {a : ℝ} (ha : a∈Icc 0 t) :
      Coefficient.H l s g e (tilted c (t-a))+(12/25)*tilted c (t-a)+
        axialRest (12/25) c l t a=
      Coefficient.H l s g e (tilted c (t-a))+rest c l t a := by
    rw [rest,charge_axial (ha.2.trans ht.2)]
    dsimp [axialRest]
    ring
  refine ⟨hsum.1,?_⟩
  intro x hx y hy r v hr hv hrv
  have hh := hsum.2 hx hy hr hv hrv
  simp only [Pi.add_apply] at hh
  rw [heq hx,heq hy,heq (hsum.1 hx hy hr hv hrv)] at hh
  exact hh

theorem increment_concave {k c l t s g e : ℝ}
    (hc : 0<c) (hl : 0<l) (hcl : c≤(3/2)*l)
    (ht : t∈Icc (0:ℝ) (1/4)) (hs : |s|≤frameCap)
    (hg : 0≤g) (he : e≤0) (heLow : Real.cos frameCap-1≤e)
    (hePos : 0<s→e=0)
    (hm : ∀a∈Icc 0 t,tilted c (t-a)≤(3/2)*l) :
    ConcaveOn ℝ (Icc 0 t)
      (fun a => splitBase k l c t a+increment l (tilted c (t-a)) s g e) := by
  have hh := add_constant (scalar_concave hc hl hcl ht hs hg he heLow hePos hm)
    (constant k l c)
  apply congr_on hh
  intro a ha
  rw [increment_identity (frame ht) ha]
  ring

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.QuarterSplit

module

public import SquaresInCircles.Eight.TableFree.ExceptionalContactStress

/-!
# Exact endpoint supports for the exceptional contact stress

Uncompiled source. Norm supports are introduced after the concave
fixed-point expression. The ordinary increment still contains the
original signed angles, including the original EH0 angle. E is bounded
on the same radius as the other points. The E and G endpoint baselines
are explicit and share one ordinary four-block problem.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalContactSupport
open Candidate SignedStress SoleResiduals SecondaryEStress ActualCoreEBlocks
open PositiveAngularEnvelope ExceptionalContactStress

def anchorSupport (C : SignedCycle) (ab : Fin 4) (R k l c eta x e : ℝ) : ℝ :=
  R*SoleEStress.anchorNorms C ab 2 0 3 0 (k*tilt eta x) k l c c 1 (tilt eta e)-
    SoleEStress.halfShift C ab 2 0 3 0 (k*tilt eta x) k l c c 1 (tilt eta e)

def increment (C : SignedCycle) (ab : Fin 4) (R k l c eta x e : ℝ) : ℝ :=
  SoleEStress.increment C ab 2 0 3 0 (k*tilt eta x) k l c c 1 (tilt eta e) R

def baseline (R k l c eta x e : ℝ) : ℝ :=
  (3/2)*(k*tilt eta x)+2*l+3*c+(1+tilt eta e)/2+k*(edgeWidth x+1/2)+
    edgeWidth e+tilt eta e-
    R*SoleEStress.zeroNorms (k*tilt eta x) k l c c 1 (tilt eta e)-
    k*sigma R eta*Real.sin x-sigma R eta*Real.sin e

theorem anchorWork_le {C : SignedCycle} {ab : Fin 4} (R k l c eta x e : ℝ)
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) :
    anchorWork C ab k l c eta x e≤anchorSupport C ab R k l c eta x e := by
  have hH := work_le_signed_support hR (hc H) (Or.inl rfl)
    (by simp [abs_of_nonneg hn.H_nonneg]) (ExceptionalContactStress.forces C ab k l c eta x e H)
  have hA := work_le_signed_support hR (hc A) (Or.inl rfl)
    (by simp [abs_of_nonneg hn.A_nonneg]) (ExceptionalContactStress.forces C ab k l c eta x e A)
  have hB := work_le_signed_support hR (hc B) (Or.inr rfl)
    (by simp [abs_of_nonpos hn.B_nonpos]) (ExceptionalContactStress.forces C ab k l c eta x e B)
  have hD := work_le_signed_support hR (hc D) (Or.inr rfl)
    (by simp [abs_of_nonpos hn.D_nonpos]) (ExceptionalContactStress.forces C ab k l c eta x e D)
  have hsum := SoleEStress.sum_bounds C hab (Or.inl rfl) (Or.inl rfl)
    (Or.inr rfl) (Or.inl rfl) (k*tilt eta x) k l c c 1 (tilt eta e) R
  simp only [SoleEStress.bound,Fin.sum_univ_seven,Matrix.cons_val] at hsum
  unfold anchorWork anchorSupport
  unfold ExceptionalContactStress.forces at hH hA hB hD ⊢
  unfold signedSupport at hsum
  linarith

theorem eWork_le {C : SignedCycle} {R eta e : ℝ}
    (hR : 0≤R) (heta : 0≤eta) (he : e∈Icc 0 frameCap)
    (hs : (C.point E).Sorted) (hc : (C.point E).Contained (R^2)) :
    eWork C eta e≤ sigma R eta*Real.sin e := by
  have hsin := (transport_trig he).2.2.1
  have hh := work_le_circleSupport hR hs hc (Real.sin e,Real.sin e*eta)
  rw [(scaled_primary_support (R := R) hsin heta).2] at hh
  dsimp [work,eWork,sigma] at *
  nlinarith

theorem variable_decomposition {C : SignedCycle} {ab : Fin 4} (R k l c eta x e : ℝ)
    (hab : ab=0 ∨ ab=2) (ha : ∀ i,|delta C.theta i|≤frameCap) :
    variableDemand C k l c eta x e-anchorSupport C ab R k l c eta x e-
      k*sigma R eta*Real.sin x-sigma R eta*Real.sin e=
        baseline R k l c eta x e+increment C ab R k l c eta x e := by
  rcases hab with rfl | rfl <;>
    simp only [variableDemand,anchorSupport,baseline,increment,SoleEStress.increment,
      SoleEStress.anchorNorms,SoleEStress.halfShift,SoleEStress.zeroNorms,
      ordinaryDE,ordinaryEH,ite_true,ite_false,show (3:Fin 4)≠2 by decide,
      show (2:Fin 4)≠0 by decide,width_eq (ha H),width_eq (ha A),width_eq (ha B),
      width_eq (ha T),width_eq (ha E),phi_zero,psi_zero,zero_add,add_zero,mul_zero,mul_one] <;> ring

theorem value_lower {C : SignedCycle} {ab : Fin 4} {R k l c eta t x : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (heta : 0≤eta)
    (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hcontact : Contact C) :
    baseline R k l c eta x (t-x)+increment C ab R k l c eta x (t-x)≤
      value C ab R k l c eta t x := by
  have he : t-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [ht.2,hx.1]⟩
  have hanchor := anchorWork_le R k l c eta x (t-x) hab hR hc hn
  have hework := eWork_le hR heta he (hs E) (hc E)
  have hid := variable_decomposition R k l c eta x (t-x) hab ha
  rw [value_eq_stress R k l c eta hab ht hx hn hcontact]
  dsimp [stress]
  linarith

def contactScalar (R eta t : ℝ) : ℝ :=
  1+2*Real.cos t+(1+2*eta-R*Real.sqrt (1+eta^2))*Real.sin t

def atE (R k l c eta t : ℝ) : ℝ :=
  3*k+2*l+3*c+contactScalar R eta t-
    R*(pairNorm (tilt eta t) k 0+pairNorm k l 0+pairNorm l c 0+pairNorm 1 c 0)

def atG (R k l c eta t : ℝ) : ℝ :=
  3+2*l+3*c+k*contactScalar R eta t-
    R*(pairNorm 1 (k*tilt eta t) 0+pairNorm k l 0+pairNorm l c 0+pairNorm 1 c 0)

theorem baseline_at_E {R k l c eta t : ℝ} (ht : t∈Icc 0 frameCap) :
    baseline R k l c eta 0 t=atE R k l c eta t := by
  have hw0 : edgeWidth (0:ℝ)=1 := by simp [edgeWidth,pairWidth]
  simp [baseline,atE,contactScalar,ExceptionalContactStress.tilt,SoleEStress.zeroNorms,sigma,hw0,
    edgeWidth_positive_formula ht]
  ring

theorem baseline_at_G {R k l c eta t : ℝ} (ht : t∈Icc 0 frameCap) :
    baseline R k l c eta t 0=atG R k l c eta t := by
  have hw0 : edgeWidth (0:ℝ)=1 := by simp [edgeWidth,pairWidth]
  simp [baseline,atG,contactScalar,ExceptionalContactStress.tilt,SoleEStress.zeroNorms,sigma,hw0,
    edgeWidth_positive_formula ht]
  ring

theorem endpoint_difference (R k l c eta t : ℝ) :
    atG R k l c eta t-atE R k l c eta t=
      (1-k)*(3-contactScalar R eta t)+
        R*(pairNorm (tilt eta t) k 0-pairNorm 1 (k*tilt eta t) 0) := by
  dsimp [atG,atE]
  ring

theorem endpoint_norm_order {k p : ℝ} (hk : k∈Icc 0 1) (hp : 1≤p) :
    pairNorm 1 (k*p) 0≤pairNorm p k 0 := by
  have hk2 : 0≤1-k^2 := by nlinarith [hk.1,hk.2]
  have hp2 : 0≤p^2-1 := by nlinarith
  have hh := mul_nonneg hk2 hp2
  simp only [pairNorm,Real.sin_zero,mul_zero,add_zero]
  apply Real.sqrt_le_sqrt
  nlinarith

theorem E_le_G {R k l c eta t : ℝ} (hR : 0≤R) (hk : k∈Icc 0 1)
    (hp : 1≤tilt eta t) (hC : contactScalar R eta t≤3) :
    atE R k l c eta t≤atG R k l c eta t := by
  have hnorm := endpoint_norm_order hk hp
  have hfirst := mul_nonneg (sub_nonneg.mpr hk.2) (sub_nonneg.mpr hC)
  have hsecond := mul_nonneg hR (sub_nonneg.mpr hnorm)
  have hd := endpoint_difference R k l c eta t
  linarith

/-- The sharp critical family can have a zero E endpoint. Its strict
G endpoint follows from k<1 and the contact scalar, without replacing
the genuine sharp zero by a rational-radius strict bound. -/
theorem E_lt_G {R k l c eta t : ℝ} (hR : 0≤R) (hk : k∈Ico 0 1)
    (hp : 1≤tilt eta t) (hC : contactScalar R eta t<3) :
    atE R k l c eta t<atG R k l c eta t := by
  have hnorm := endpoint_norm_order ⟨hk.1,hk.2.le⟩ hp
  have hfirst := mul_pos (sub_pos.mpr hk.2) (sub_pos.mpr hC)
  have hsecond := mul_nonneg hR (sub_nonneg.mpr hnorm)
  have hd := endpoint_difference R k l c eta t
  linarith

end SquaresInCircles.Eight.TableFree.ExceptionalContactSupport

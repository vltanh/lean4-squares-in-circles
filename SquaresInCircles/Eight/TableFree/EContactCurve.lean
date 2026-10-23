module

public import SquaresInCircles.Eight.TableFree.EInteriorGeometry

/-!
# The exact two-contact E curve

Uncompiled draft.  The formula solves the two retained mixed contacts.
Its energy is exactly the original corner polynomial, including when a
small local variation has not yet been restricted to nonnegative tangent.
The derivative identities are obtained by ordinary differentiation of
the explicit first and second harmonics.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EContactCurve
open EInteriorGeometry

def A (α : ℝ) : ℝ := Real.cos (α/2)/(2*Real.sin (α/2))
def B (α : ℝ) : ℝ := Real.sin (α/2)/(2*Real.cos (α/2))
def M (m α : ℝ) : ℝ := m/(2*Real.sin (α/2))
def N (n α : ℝ) : ℝ := n/(2*Real.cos (α/2))

def U (m α z : ℝ) : ℝ := A α*Real.cos z-M m α
def V (n α z : ℝ) : ℝ := B α*Real.sin z+N n α
def x (m n α z : ℝ) : ℝ := U m α z*Real.cos z-V n α z*Real.sin z
def b (m n α z : ℝ) : ℝ := U m α z*Real.sin z+V n α z*Real.cos z
def curve (m n α z : ℝ) : State := (x m n α z+1/2,b m n α z,α/2-z)

def K0 (m n α : ℝ) : ℝ :=
  (A α^2+2*A α+B α^2-2*B α)/2+M m α^2+N n α^2+5/4
def Kc (α : ℝ) : ℝ := (A α^2+2*A α-B α^2+2*B α)/2
def Ks (α : ℝ) : ℝ := (A α+B α)/2
def Lc (m n α : ℝ) : ℝ := -2*M m α*(A α+1)+N n α
def Ls (m n α : ℝ) : ℝ := 2*N n α*(B α-1)-M m α

def energy (m n α z : ℝ) : ℝ :=
  K0 m n α+Kc α*Real.cos (2*z)+Ks α*Real.sin (2*z)+
    Lc m n α*Real.cos z+Ls m n α*Real.sin z
def energyD (m n α z : ℝ) : ℝ :=
  -2*Kc α*Real.sin (2*z)+2*Ks α*Real.cos (2*z)-
    Lc m n α*Real.sin z+Ls m n α*Real.cos z
def energyDD (m n α z : ℝ) : ℝ :=
  -4*Kc α*Real.cos (2*z)-4*Ks α*Real.sin (2*z)-
    Lc m n α*Real.cos z-Ls m n α*Real.sin z

theorem rotated_components (m n α z : ℝ) :
    x m n α z*Real.cos z+b m n α z*Real.sin z=U m α z ∧
      -x m n α z*Real.sin z+b m n α z*Real.cos z=V n α z := by
  constructor
  · dsimp [x,b]
    linear_combination U m α z*(Real.sin_sq_add_cos_sq z)
  · dsimp [x,b]
    linear_combination V n α z*(Real.sin_sq_add_cos_sq z)

theorem corner_curve (m n α z : ℝ) :
    corner (curve m n α z)=energy m n α z := by
  dsimp [corner,curve,x,b,U,V,energy,K0,Kc,Ks,Lc,Ls]
  rw [Real.sin_two_mul,Real.cos_two_mul]
  linear_combination
    ((A α*Real.cos z-M m α)^2+(B α*Real.sin z+N n α)^2+B α^2-2*B α)*
      (Real.sin_sq_add_cos_sq z)

theorem energy_hasDerivAt (m n α z : ℝ) :
    HasDerivAt (energy m n α) (energyD m n α z) z := by
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2*t)) (-2*Real.sin (2*z)) z := by
    convert ((hasDerivAt_id z).const_mul 2).cos using 1 <;> ring
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2*t)) (2*Real.cos (2*z)) z := by
    convert ((hasDerivAt_id z).const_mul 2).sin using 1 <;> ring
  have hd := (((hasDerivAt_const z (K0 m n α)).add (hc.const_mul (Kc α))).add
    (hs.const_mul (Ks α))).add ((Real.hasDerivAt_cos z).const_mul (Lc m n α))
  convert hd.add ((Real.hasDerivAt_sin z).const_mul (Ls m n α)) using 1 <;>
    dsimp [energy,energyD] <;> ring

theorem energyD_hasDerivAt (m n α z : ℝ) :
    HasDerivAt (energyD m n α) (energyDD m n α z) z := by
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2*t)) (-2*Real.sin (2*z)) z := by
    convert ((hasDerivAt_id z).const_mul 2).cos using 1 <;> ring
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2*t)) (2*Real.cos (2*z)) z := by
    convert ((hasDerivAt_id z).const_mul 2).sin using 1 <;> ring
  convert (((hs.const_mul (-2*Kc α)).add (hc.const_mul (2*Ks α))).sub
    ((Real.hasDerivAt_sin z).const_mul (Lc m n α))).add
    ((Real.hasDerivAt_cos z).const_mul (Ls m n α)) using 1 <;>
    dsimp [energyD,energyDD] <;> ring

theorem half_trig {α : ℝ} (hα : α∈Ioo 0 (27/100 : ℝ)) :
    0<Real.sin (α/2) ∧ 0<Real.cos (α/2) ∧ 0<Real.sin α := by
  refine ⟨?_,?_,?_⟩
  · exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hα.1])
      (by linarith [hα.2,Real.pi_gt_three])
  · exact transport_cos_pos (by rw [abs_of_pos (by linarith [hα.1] : 0<α/2)];
      linarith [hα.2])
  · exact Real.sin_pos_of_pos_of_lt_pi hα.1 (by linarith [hα.2,Real.pi_gt_three])

theorem U_equation {α : ℝ} (hs : Real.sin (α/2)≠0) (m z : ℝ) :
    2*Real.sin (α/2)*U m α z=Real.cos (α/2)*Real.cos z-m := by
  dsimp [U,A,M]
  field_simp [hs]
  ring

theorem V_equation {α : ℝ} (hc : Real.cos (α/2)≠0) (n z : ℝ) :
    2*Real.cos (α/2)*V n α z=Real.sin (α/2)*Real.sin z+n := by
  dsimp [V,B,N]
  field_simp [hc]
  ring

/-- Both physical primary contacts hold identically along this curve. -/
theorem curve_contacts {α : ℝ} (hα : α∈Ioo 0 (27/100 : ℝ)) (m n z : ℝ) :
    deValue ((m-n+1)/2) (curve m n α z)=W (α/2-z) ∧
      ehValue ((m+n+1)/2) α (curve m n α z)=W (α/2+z) := by
  have ht := half_trig hα
  have hu := U_equation ht.1.ne' m z
  have hv := V_equation ht.2.1.ne' n z
  have hr := rotated_components m n α z
  have hrs := congrArg (fun y : ℝ => Real.sin (α/2)*y) hr.1
  have hrc := congrArg (fun y : ℝ => Real.cos (α/2)*y) hr.2
  constructor
  · dsimp [deValue,curve,W]
    rw [Real.sin_sub,Real.cos_sub]
    nlinarith
  · have heq : α-(α/2-z)=α/2+z := by ring
    dsimp [ehValue,curve]
    rw [heq]
    dsimp [W]
    rw [Real.sin_add,Real.cos_add]
    nlinarith

theorem contact_unique {α m n a β z : ℝ}
    (hα : α∈Ioo 0 (27/100 : ℝ))
    (hDE : (m-n+1)/2+a*Real.sin (α/2-z)+β*Real.cos (α/2-z)=W (α/2-z))
    (hEH : (m+n+1)/2+a*Real.sin (α/2+z)-β*Real.cos (α/2+z)=W (α/2+z)) :
    a=x m n α z+1/2 ∧ β=b m n α z := by
  have ht := half_trig hα
  have hDE' := hDE
  have hEH' := hEH
  dsimp [W] at hDE' hEH'
  rw [Real.sin_sub,Real.cos_sub] at hDE'
  rw [Real.sin_add,Real.cos_add] at hEH'
  have hU : (a-1/2)*Real.cos z+β*Real.sin z=U m α z := by
    have hu := U_equation ht.1.ne' m z
    have heq : 2*Real.sin (α/2)*((a-1/2)*Real.cos z+β*Real.sin z)=
        2*Real.sin (α/2)*U m α z := by nlinarith
    exact (mul_left_cancel₀ (mul_ne_zero (by norm_num) ht.1.ne')) heq
  have hV : -(a-1/2)*Real.sin z+β*Real.cos z=V n α z := by
    have hv := V_equation ht.2.1.ne' n z
    have heq : 2*Real.cos (α/2)*(-(a-1/2)*Real.sin z+β*Real.cos z)=
        2*Real.cos (α/2)*V n α z := by nlinarith
    exact (mul_left_cancel₀ (mul_ne_zero (by norm_num) ht.2.1.ne')) heq
  constructor
  · have hu := congrArg (fun y : ℝ => Real.cos z*y) hU
    have hv := congrArg (fun y : ℝ => Real.sin z*y) hV
    have hn := congrArg (fun y : ℝ => (a-1/2)*y) (Real.sin_sq_add_cos_sq z)
    dsimp [x]
    nlinarith
  · have hu := congrArg (fun y : ℝ => Real.sin z*y) hU
    have hv := congrArg (fun y : ℝ => Real.cos z*y) hV
    have hn := congrArg (fun y : ℝ => β*y) (Real.sin_sq_add_cos_sq z)
    dsimp [b]
    nlinarith

def scaledSecond (m n α z : ℝ) : ℝ :=
  -2*(Real.cos α/Real.sin α+2)*Real.cos (2*z)-2*Real.sin (2*z)+
    m*Real.cos (α/2)*((Real.cos (α/2)/Real.sin (α/2)+2)*Real.cos z+Real.sin z)-
    n*Real.sin (α/2)*(Real.cos z+(Real.sin (α/2)/Real.cos (α/2)-2)*Real.sin z)

theorem coefficient_sum {α : ℝ} (hα : α∈Ioo 0 (27/100 : ℝ)) :
    A α+B α=1/Real.sin α ∧ A α-B α=Real.cos α/Real.sin α := by
  have ht := half_trig hα
  have hsin := Real.sin_two_mul (α/2)
  have hcos := Real.cos_two_mul (α/2)
  rw [show 2*(α/2)=α by ring] at hsin hcos
  constructor
  · rw [hsin]
    dsimp [A,B]
    field_simp [ht.1.ne',ht.2.1.ne']
    nlinarith [Real.sin_sq_add_cos_sq (α/2)]
  · rw [hsin,hcos]
    dsimp [A,B]
    field_simp [ht.1.ne',ht.2.1.ne']
    nlinarith [Real.sin_sq_add_cos_sq (α/2)]

/-- The large terms are kept together before any numerical estimate. -/
theorem scaled_second_identity {α : ℝ} (hα : α∈Ioo 0 (27/100 : ℝ)) (m n z : ℝ) :
    Real.sin α*energyDD m n α z=scaledSecond m n α z := by
  have ht := half_trig hα
  have hab := coefficient_sum hα
  have hsin := Real.sin_two_mul (α/2)
  rw [show 2*(α/2)=α by ring] at hsin
  have hM : Real.sin α*M m α=m*Real.cos (α/2) := by
    rw [hsin]
    dsimp [M]
    field_simp [ht.1.ne']
    ring
  have hN : Real.sin α*N n α=n*Real.sin (α/2) := by
    rw [hsin]
    dsimp [N]
    field_simp [ht.2.1.ne']
    ring
  have hAB : Real.sin α*(A α+B α)=1 := by
    rw [hab.1]
    field_simp [ht.2.2.ne']
  have hABdiff : Real.sin α*(A α+B α)*(A α-B α+2)=Real.cos α/Real.sin α+2 := by
    rw [hAB,one_mul,hab.2]
  have hK : Real.sin α*(4*Kc α)=2*(Real.cos α/Real.sin α+2) := by
    dsimp [Kc]
    nlinarith [hABdiff]
  have hS : Real.sin α*(4*Ks α)=2 := by dsimp [Ks]; nlinarith
  have hLc : Real.sin α*(-Lc m n α)=
      m*Real.cos (α/2)*(Real.cos (α/2)/Real.sin (α/2)+2)-n*Real.sin (α/2) := by
    dsimp [Lc]
    rw [show Real.sin α*(-(-2*M m α*(A α+1)+N n α))=
      2*(Real.sin α*M m α)*(A α+1)-Real.sin α*N n α by ring,hM,hN]
    dsimp [A]
    ring
  have hLs : Real.sin α*(-Ls m n α)=
      m*Real.cos (α/2)-n*Real.sin (α/2)*(Real.sin (α/2)/Real.cos (α/2)-2) := by
    dsimp [Ls]
    rw [show Real.sin α*(-(2*N n α*(B α-1)-M m α))=
      Real.sin α*M m α-2*(Real.sin α*N n α)*(B α-1) by ring,hM,hN]
    dsimp [B]
    ring
  have h1 := congrArg (fun y : ℝ => y*Real.cos (2*z)) hK
  have h2 := congrArg (fun y : ℝ => y*Real.sin (2*z)) hS
  have h3 := congrArg (fun y : ℝ => y*Real.cos z) hLc
  have h4 := congrArg (fun y : ℝ => y*Real.sin z) hLs
  dsimp [energyDD,scaledSecond]
  nlinarith

end SquaresInCircles.Eight.TableFree.EContactCurve

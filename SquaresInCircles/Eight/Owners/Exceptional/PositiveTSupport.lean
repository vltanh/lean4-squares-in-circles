module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.Exceptional.ContactSupport
public import SquaresInCircles.Eight.Owners.Sole.FixedSplit

/-!
# Eight squares: positive-T endpoint supports after the split

The four anchors are bounded by their signed circle supports (`anchorWork_le`) only after `x + e`
is split with `z` fixed (`decomposition`). Every ordinary angle, the two angles of H included,
stays in the increment, and the stress is at least the baseline plus the increment
(`value_lower`).
-/

section
/-!
## The original ordinary angles in the exceptional contact stress

EH0 remains an original ordinary angle, so H is a
two-angle block even when contact is not aligned. The actual AB owner
selects which block contains its error. Positive and negative budgets
are identities of the original seven frames; changing the scalar split
does not change those budgets or the weak owner selection.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalContactBlocks
open Candidate ExceptionalContactStress ExceptionalContactSupport
open ActualOrdinaryBlocks ActualCoreEBlocks PositiveAngularEnvelope SingleAngleConcavity

def alpha (_k l _c eta _x e : ℝ) : Fin 4 → ℝ := ![tilt eta e,l,l,1]
def beta (k _l c eta x _e : ℝ) : Fin 4 → ℝ := ![k*tilt eta x,k,c,c]
def small (k l c eta x e : ℝ) (i : Fin 4) : ℝ :=
  min (alpha k l c eta x e i) (beta k l c eta x e i)
def large (k l c eta x e : ℝ) (i : Fin 4) : ℝ :=
  max (alpha k l c eta x e i) (beta k l c eta x e i)
def single : Fin 4 → Bool := ![false,true,false,false]
def nu (k l c eta x e : ℝ) : Fin 4 → ℝ :=
  ![large k l c eta x e 0,l,c,large k l c eta x e 3]

def blocks (C : SignedCycle) (ab : Fin 4) (k l c eta x e : ℝ) : Fin 4 → Block :=
  SoleEStress.blocks C ab 2 0 3 0 (k*tilt eta x) k l c c 1 (tilt eta e)

theorem coefficients (C : SignedCycle) (ab : Fin 4) (k l c eta x e : ℝ) (i : Fin 4) :
    (blocks C ab k l c eta x e i).p=small k l c eta x e i ∧
      (blocks C ab k l c eta x e i).q=large k l c eta x e i := by
  fin_cases i <;>
    simp [blocks,SoleEStress.blocks,Block.p,Block.q,small,large,alpha,beta,min_comm,max_comm]

theorem small_le_large (k l c eta x e : ℝ) (i : Fin 4) :
    small k l c eta x e i≤large k l c eta x e i :=
  min_le_max

theorem nu_between (k l c eta x e : ℝ) (i : Fin 4) :
    small k l c eta x e i≤nu k l c eta x e i ∧
      nu k l c eta x e i≤large k l c eta x e i := by
  fin_cases i <;> simp [nu,small,large,alpha,beta,
    ]

theorem small_pos {k l c eta x e : ℝ} (hk : 0<k) (hl : 0<l) (hc : 0<c)
    (hx : 0<tilt eta x) (he : 0<tilt eta e) (i : Fin 4) :
    0<small k l c eta x e i := by
  fin_cases i <;> simp [small,alpha,beta,hk,hl,hc,he,mul_pos hk hx]

theorem single_data (C : SignedCycle) (ab : Fin 4) (k l c eta x e : ℝ)
    (i : Fin 4) (hi : single i=true) :
    (blocks C ab k l c eta x e i).v=0 ∧
      (blocks C ab k l c eta x e i).alpha=nu k l c eta x e i := by
  fin_cases i <;> simp_all [single,blocks,SoleEStress.blocks,nu]

theorem parts (C : SignedCycle) (ab : Fin 4) (k l c eta x e : ℝ) (i : Fin 4) :
    (blocks C ab k l c eta x e i).P=
      (ActualCoreEBlocks.blocks C ab 2 0 3 0 (k*tilt eta x) k l c c i).P ∧
    (blocks C ab k l c eta x e i).N=
      (ActualCoreEBlocks.blocks C ab 2 0 3 0 (k*tilt eta x) k l c c i).N := by
  fin_cases i <;> constructor <;> rfl

theorem original_budgets {C : SignedCycle} {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (k l c eta t x e : ℝ) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t) :
    0≤t ∧ (∑i,(blocks C ab k l c eta x e i).P)≤frameCap-t ∧
      (∑i,(blocks C ab k l c eta x e i).N)=t+∑i,(blocks C ab k l c eta x e i).P := by
  have hh := ActualCoreEBlocks.block_budgets hab (Or.inl rfl) (Or.inl rfl)
    (Or.inr rfl) (Or.inl rfl) (k*tilt eta x) k l c c hvar hG
    (by intro h; norm_num at h) (by intro h; norm_num at h)
    (by simpa [eTotal,primaryDE,primaryEH] using hD)
  have hP := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => (parts C ab k l c eta x e i).1)
  have hN := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => (parts C ab k l c eta x e i).2)
  simp only [removed,eTotal,primaryDE,primaryEH,show (2:Fin 4)≠3 by decide,
    show (0:Fin 4)≠2 by decide,show (0:Fin 4)≠1 by decide,ite_false,ite_true,add_zero] at hh
  refine ⟨by linarith,?_,?_⟩
  · rw [hP]
    linarith [hh.2.2.1]
  · rw [hN,hP]
    linarith [hh.2.2.2]

theorem angles_small {C : SignedCycle} (ab : Fin 4) (k l c eta x e : ℝ)
    (hs : ∀ i,|delta C.theta i|≤frameCap) (i : Fin 4) :
    |(blocks C ab k l c eta x e i).u|≤frameCap ∧
      |(blocks C ab k l c eta x e i).v|≤frameCap := by
  have hz : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hz' : (0:ℝ)≤frameCap := by norm_num [frameCap]
  have hA : |if ab=0 then 0 else delta C.theta A|≤frameCap := by
    split_ifs <;> first | exact hz | exact hs A
  have hB : |if ab=0 then delta C.theta A else 0|≤frameCap := by
    split_ifs <;> first | exact hz | exact hs A
  fin_cases i <;>
    simp [blocks,SoleEStress.blocks,ordinaryDE,ordinaryEH,hs H,hs E,hs B,hs T,hz',hA,hB]

theorem single_parts (C : SignedCycle) (ab : Fin 4) (k l c eta x e : ℝ)
    (i : Fin 4) (hi : single i=true) :
    (blocks C ab k l c eta x e i).P=0 ∨ (blocks C ab k l c eta x e i).N=0 := by
  have hv := (single_data C ab k l c eta x e i hi).1
  by_cases hu : 0≤(blocks C ab k l c eta x e i).u
  · right
    simp [Block.N,hv,negativePart,max_eq_right (show -(blocks C ab k l c eta x e i).u≤0 by linarith)]
  · left
    simp [Block.P,hv,positivePart,max_eq_right (le_of_lt (lt_of_not_ge hu))]

theorem individual_budgets {C : SignedCycle} {ab : Fin 4} {k l c eta t x e : ℝ}
    (ht : 0≤t) (hP : (∑i,(blocks C ab k l c eta x e i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab k l c eta x e i).N)=t+∑i,(blocks C ab k l c eta x e i).P)
    (i : Fin 4) :
    (blocks C ab k l c eta x e i).P≤frameCap ∧ (blocks C ab k l c eta x e i).N≤frameCap := by
  have hp := Finset.single_le_sum (fun j _ => (blocks C ab k l c eta x e j).P_nonneg)
    (Finset.mem_univ i)
  have hn := Finset.single_le_sum (fun j _ => (blocks C ab k l c eta x e j).N_nonneg)
    (Finset.mem_univ i)
  constructor <;> linarith

theorem block_minorant {C : SignedCycle} {ab : Fin 4} {R k l c eta t x e : ℝ}
    (ht : 0≤t) (hp : ∀ i,0≤ small k l c eta x e i)
    (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hP : (∑i,(blocks C ab k l c eta x e i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab k l c eta x e i).N)=t+∑i,(blocks C ab k l c eta x e i).P)
    (i : Fin 4) :
    F (single i) R (small k l c eta x e i) (large k l c eta x e i)
      (nu k l c eta x e i) (blocks C ab k l c eta x e i).P (blocks C ab k l c eta x e i).N≤
      (blocks C ab k l c eta x e i).increment R := by
  obtain ⟨hsmall,hlarge⟩ := coefficients C ab k l c eta x e i
  obtain ⟨hbP,hbN⟩ := individual_budgets ht hP hN i
  by_cases hi : single i=true
  · obtain ⟨hv,hn⟩ := single_data C ab k l c eta x e i hi
    have hh := SoleOriginalBlocks.one_angle_minorant (blocks C ab k l c eta x e i) R hv
      (angles_small ab k l c eta x e ha i).1
    simpa only [hi,hsmall,hlarge,hn] using hh
  · have hi' : single i=false := Bool.eq_false_of_not_eq_true hi
    have hh := (blocks C ab k l c eta x e i).minorant R
      (by rw [hsmall]; exact hp i) hbP hbN
    simpa only [F,hi',Bool.false_eq_true,↓reduceIte,hsmall,hlarge] using hh

theorem sum_minorant {C : SignedCycle} {ab : Fin 4} {R k l c eta t x e : ℝ}
    (hab : ab=0 ∨ ab=2) (ht : 0≤t) (hp : ∀ i,0≤ small k l c eta x e i)
    (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hP : (∑i,(blocks C ab k l c eta x e i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab k l c eta x e i).N)=t+∑i,(blocks C ab k l c eta x e i).P) :
    (∑i,F (single i) R (small k l c eta x e i) (large k l c eta x e i)
      (nu k l c eta x e i) (blocks C ab k l c eta x e i).P (blocks C ab k l c eta x e i).N)≤
      ExceptionalContactSupport.increment C ab R k l c eta x e := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => block_minorant (R := R) ht hp ha hP hN i)
  have heq := SoleEStress.increment_eq C hab (Or.inl rfl) (Or.inl rfl)
    3 0 (k*tilt eta x) k l c c 1 (tilt eta e) R
  simpa only [ExceptionalContactSupport.increment,blocks,heq] using hh

end SquaresInCircles.Eight.ExceptionalContactBlocks
end
end
end

section
/-!
## Curvature at fixed coordinates with the positive-T weight

The contact equality removes the varying EH multiplier. For a weight `k` up to `521/500` the two
endpoint estimates give the same negative harmonic bound `-4/25` on the whole G/E split
(`comparison_harmonic`, `curvature`), so the stress is concave (`concave`). The tangent of E is
nonnegative, and the EH contact is that of the cycle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ExceptionalPositiveTCurvature
open SoleFixedSplit

theorem comparison_harmonic {k t x : ℝ} (hk : k∈Icc (431/500:ℝ) (521/500))
    (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t) :
    SoleFixedSplit.harmonic (-(87/200)*k) ((957/1000)*k) (-(1/2)) (183/200) t x≤-4/25 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig ht
  have hkc := mul_le_mul_of_nonneg_right hk.1 (show 0≤Real.cos t by linarith)
  have hks := mul_le_mul_of_nonneg_right hk.2 hs0
  have hcl := mul_lt_mul_of_pos_left hc (by norm_num : (0:ℝ)<431/500)
  rw [show (-4/25:ℝ) = -(4/25) by norm_num]
  apply harmonic_endpoint_upper ht hx (by norm_num)
  · simp only [SoleFixedSplit.harmonic,Real.cos_zero,Real.sin_zero,sub_zero,mul_one,mul_zero,
      add_zero]
    nlinarith [hk.1]
  · simp only [SoleFixedSplit.harmonic,sub_self,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,
      add_zero]
    nlinarith

theorem curvature {MH k eta sigma a b t x : ℝ}
    (hMH : -(13/200:ℝ)≤MH) (hk : k∈Icc (431/500:ℝ) (521/500))
    (heta : eta∈Icc 0 (327/1000:ℝ)) (hsigma : sigma-1/2≤187/200)
    (ha : a≤283/200) (hb : 0≤b) (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t) :
    -SoleFixedSplit.harmonic (k*MH+k/2) (k*eta*MH+k/2-k*sigma)
      (1/2+b) (1/2-a) t x≤-4/25 := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans ht.2⟩
  have he : t-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [ht.2,hx.1]⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hx'
  obtain ⟨hce,hce1,hse0,hse,hsce⟩ := transport_trig he
  have hk0 : 0≤k := by linarith [hk.1]
  have hn : 0≤k*(Real.cos x+eta*Real.sin x) :=
    mul_nonneg hk0 (by nlinarith [mul_nonneg heta.1 hs0])
  have hmH := mul_le_mul_of_nonneg_right hMH hn
  have hcoef : sigma-1/2+(13/200)*eta≤957/1000 := by linarith [heta.2]
  have hcoefG := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hk0 hs0)
  have hcoefE := mul_le_mul_of_nonneg_right ha hse0
  have hminor := mul_nonneg hb (show 0≤Real.cos (t-x) by linarith)
  have hmajor : -SoleFixedSplit.harmonic (k*MH+k/2) (k*eta*MH+k/2-k*sigma)
      (1/2+b) (1/2-a) t x≤
      SoleFixedSplit.harmonic (-(87/200)*k) ((957/1000)*k) (-(1/2)) (183/200) t x := by
    dsimp [SoleFixedSplit.harmonic]
    nlinarith
  exact hmajor.trans (comparison_harmonic hk ht hx)

theorem concave {K MH k eta sigma a b t : ℝ}
    (hMH : -(13/200:ℝ)≤MH) (hk : k∈Icc (431/500:ℝ) (521/500))
    (heta : eta∈Icc 0 (327/1000:ℝ)) (hsigma : sigma-1/2≤187/200)
    (ha : a≤283/200) (hb : 0≤b) (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 t) (high K MH k eta sigma a b t) := by
  apply concave_of_deriv2
    (f' := harmonicDeriv (k*MH+k/2) (k*eta*MH+k/2-k*sigma) (1/2+b) (1/2-a) t)
    (f'' := fun x => -SoleFixedSplit.harmonic (k*MH+k/2) (k*eta*MH+k/2-k*sigma) (1/2+b) (1/2-a) t x)
  · intro x hx
    exact (SoleFixedSplit.harmonic_hasDerivAt _ _ _ _ _ _).const_add _
  · intro x hx
    exact harmonicDeriv_hasDerivAt _ _ _ _ _ _
  · intro x hx
    exact (curvature hMH hk heta hsigma ha hb ht hx).trans (by norm_num)

end SquaresInCircles.Eight.ExceptionalPositiveTCurvature
end
end
end

section
/-!
## The positive-T stress at an EH0 contact

The T primary stays fixed while the G/E split varies, and its force is bounded on the same
containing circle as G (`T_work_le`). The varying EH multiplier cancels against the EH contact,
signed angle included; the point and frame of H do not move. The weak owners make the stress
nonpositive (`necessary`), and it is concave in the split (`concave`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalPositiveTStress
open Candidate SignedStress SoleResiduals SecondaryEStress ActualCoreEBlocks
open PositiveAngularEnvelope ExceptionalContactStress

def btOwner (td : Bool) : Fin 4 := if td then 2 else 3
def tdOwner (td : Bool) : Fin 4 := if td then 2 else 0
def primary (C : SignedCycle) (td : Bool) : ℝ :=
  if td then delta C.theta T else delta C.theta B
def bWeight (td : Bool) (c eta z : ℝ) : ℝ := if td then c*tilt eta z else c
def tWeight (td : Bool) (c eta z : ℝ) : ℝ := if td then c else c*tilt eta z

theorem bt_cases (td : Bool) : btOwner td=2 ∨ btOwner td=3 := by
  cases td <;> simp [btOwner]
theorem td_cases (td : Bool) : tdOwner td=0 ∨ tdOwner td=2 := by
  cases td <;> simp [tdOwner]

def forces (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta z x e : ℝ) : Vertex → Point :=
  SoleEStress.forces C ab (btOwner td) (tdOwner td) 3 0
    (k*tilt eta x) k l (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e)

def variableDemand (C : SignedCycle) (td : Bool) (k l c eta z x e : ℝ) : ℝ :=
  k*tilt eta x*edgeWidth (delta C.theta H)+k*edgeWidth x+
    l*edgeWidth (delta C.theta A)+bWeight td c eta z*edgeWidth (delta C.theta B)+
    tWeight td c eta z*edgeWidth (delta C.theta T)+edgeWidth e+
    tilt eta e*edgeWidth (delta C.theta E)

def anchorWork (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta z x e : ℝ) : ℝ :=
  work (forces C ab td k l c eta z x e H) (C.point H)+
    work (forces C ab td k l c eta z x e A) (C.point A)+
    work (forces C ab td k l c eta z x e B) (C.point B)+
    work (forces C ab td k l c eta z x e D) (C.point D)

def tWork (C : SignedCycle) (td : Bool) (c eta z : ℝ) : ℝ :=
  c*Real.sin z*((C.point T).a+(if td then -eta else eta)*(C.point T).y)

def adjustment (C : SignedCycle) (td : Bool) (R c eta z : ℝ) : ℝ :=
  bWeight td c eta z*(edgeWidth (delta C.theta B)-C.edge B (btOwner td))+
    tWeight td c eta z*(edgeWidth (delta C.theta T)-C.edge T (tdOwner td))-
    c*(edgeWidth (delta C.theta B)-C.edge B 2)-
    c*(edgeWidth (delta C.theta T)-C.edge T 0)+tWork C td c eta z-
    c*sigma R eta*Real.sin z

def value (C : SignedCycle) (ab : Fin 4) (td : Bool) (R k l c eta t z x : ℝ) : ℝ :=
  ExceptionalContactStress.value C ab R k l c eta (t-z) x+adjustment C td R c eta z

def stress (C : SignedCycle) (ab : Fin 4) (td : Bool) (R k l c eta z x e : ℝ) : ℝ :=
  variableDemand C td k l c eta z x e-anchorWork C ab td k l c eta z x e-
    k*sigma R eta*Real.sin x-c*sigma R eta*Real.sin z-eWork C eta e

def anchorSupport (C : SignedCycle) (ab : Fin 4) (td : Bool) (R k l c eta z x e : ℝ) : ℝ :=
  R*SoleEStress.anchorNorms C ab (btOwner td) (tdOwner td) 3 0
    (k*tilt eta x) k l (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e)-
    SoleEStress.halfShift C ab (btOwner td) (tdOwner td) 3 0
      (k*tilt eta x) k l (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e)

def increment (C : SignedCycle) (ab : Fin 4) (td : Bool) (R k l c eta z x e : ℝ) : ℝ :=
  SoleEStress.increment C ab (btOwner td) (tdOwner td) 3 0
    (k*tilt eta x) k l (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e) R

def baseline (td : Bool) (R k l c eta z x e : ℝ) : ℝ :=
  k*ExceptionalContactSupport.contactScalar R eta x+
    c*ExceptionalContactSupport.contactScalar R eta z+2*l+
    ExceptionalContactSupport.contactScalar R eta e-
    R*SoleEStress.zeroNorms (k*tilt eta x) k l
      (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e)

theorem value_eq_stress {C : SignedCycle} {ab : Fin 4} (td : Bool) (R k l c eta : ℝ)
    {t z x : ℝ} (hab : ab=0 ∨ ab=2) (ht : t∈Icc 0 frameCap)
    (hz : z∈Icc 0 t) (hx : x∈Icc 0 (t-z))
    (hsource : primary C td=z) (hn : C.NormalAnchors) (hcontact : Contact C) :
    value C ab td R k l c eta t z x=stress C ab td R k l c eta z x (t-z-x) := by
  have hw : t-z∈Icc 0 frameCap := ⟨by linarith [hz.2],by linarith [hz.1,ht.2]⟩
  rw [value,ExceptionalContactStress.value_eq_stress R k l c eta hab hw hx hn hcontact]
  rcases hab with rfl | rfl <;> cases td <;>
    simp only [primary, Bool.false_eq_true, ↓reduceIte] at hsource <;> subst hsource <;>
    simp [stress,variableDemand,anchorWork,ExceptionalPositiveTStress.forces,adjustment,tWork,
      ExceptionalContactStress.stress,ExceptionalContactStress.variableDemand,
      ExceptionalContactStress.anchorWork,ExceptionalContactStress.forces,
      SoleEStress.forces,SoleEStress.weights,CoreEStress.owners,force,previous,source,
      target,word,add,scale,work,SignedCycle.edge,zeroProjection,quarterProjection,
      H,A,B,T,D,E,next,btOwner,tdOwner,bWeight,tWeight,ExceptionalContactStress.tilt] <;> ring

theorem concave {C : SignedCycle} (ab : Fin 4) (td : Bool) {R k l c eta t z : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap) (hk : k∈Icc (431/500:ℝ) (521/500))
    (heta : eta∈Icc (1/4:ℝ) (327/1000)) (ht : t∈Icc 0 frameCap)
    (hz : z∈Icc 0 t) (hs : ∀ i,(C.point i).Sorted)
    (hc : ∀ i,(C.point i).Contained qCap)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hEy : 0≤(C.point E).y) :
    ConcaveOn ℝ (Icc 0 (t-z)) (value C ab td R k l c eta t z) := by
  have hw : t-z∈Icc 0 frameCap := ⟨by linarith [hz.2],by linarith [hz.1,ht.2]⟩
  have hh := ExceptionalPositiveTCurvature.concave
    (K:=ExceptionalContactStress.constant C ab k l c+(C.point E).y)
    (transverse_residual (hs H) (hc H) (ha H)).le hk
    ⟨by linarith [heta.1],heta.2⟩
    (tilt_reserve hR hQU ⟨heta.1,by linarith [heta.2]⟩).le
    (contained_bounds (hs E) (hc E)).1.le hEy hw
  exact hh.add_const (adjustment C td R c eta z)

theorem G_work_le {C : SignedCycle} (ab : Fin 4) (td : Bool) {R k eta : ℝ}
    (l c z e : ℝ) (hR : 0≤R) (hk : 0≤k) (heta : 0≤eta)
    (hx : delta C.theta G∈Icc 0 frameCap)
    (hs : (C.point G).Sorted) (hc : (C.point G).Contained (R^2)) :
    work (forces C ab td k l c eta z (delta C.theta G) e G) (C.point G)≤
      k*sigma R eta*Real.sin (delta C.theta G) := by
  have hh := work_le_circleSupport hR hs hc
    (ExceptionalPositiveTStress.forces C ab td k l c eta z (delta C.theta G) e G)
  have hf : ExceptionalPositiveTStress.forces C ab td k l c eta z (delta C.theta G) e G=
      SecondaryEStress.forces C ab (btOwner td) (tdOwner td) (tiltedWeight k eta (delta C.theta G)) k l
        (bWeight td c eta z) (tWeight td c eta z) G := by
    rw [ExceptionalPositiveTStress.forces,SoleEStress.force_G]; rfl
  have hsup := positive_G_support (R:=R) (ab:=ab) (bt:=btOwner td) (td:=tdOwner td)
    (l:=l) (b:=bWeight td c eta z) (t:=tWeight td c eta z) hk heta hx
  rw [hf] at hh ⊢
  rw [hsup] at hh
  refine hh.trans (le_of_eq ?_)
  unfold primarySupport sigma
  ring

theorem T_work_le {C : SignedCycle} (ab : Fin 4) (td : Bool) {R c eta z : ℝ}
    (k l x e : ℝ) (hR : 0≤R) (hc0 : 0≤c) (heta : 0≤eta)
    (hz : z∈Icc 0 frameCap) (hsource : primary C td=z)
    (hs : (C.point T).Sorted) (hc : (C.point T).Contained (R^2)) :
    work (forces C ab td k l c eta z x e T) (C.point T)≤
      c*sigma R eta*Real.sin z := by
  have hh := work_le_circleSupport hR hs hc
    (ExceptionalPositiveTStress.forces C ab td k l c eta z x e T)
  have hsin := mul_nonneg hc0 (transport_trig hz).2.2.1
  have hvec : ExceptionalPositiveTStress.forces C ab td k l c eta z x e T=
      (c*Real.sin z,(if td then -(c*Real.sin z) else c*Real.sin z)*eta) := by
    rw [ExceptionalPositiveTStress.forces,SoleEStress.force_T]
    cases td
    · rw [show btOwner false=3 from rfl,show tdOwner false=0 from rfl,force_T_bt_primary]
      simp only [primary,Bool.false_eq_true,↓reduceIte] at hsource
      subst hsource
      simp only [bWeight,tWeight,ExceptionalContactStress.tilt,Bool.false_eq_true,↓reduceIte]
      exact Prod.ext (by dsimp only) (by dsimp only; ring)
    · rw [show btOwner true=2 from rfl,show tdOwner true=2 from rfl,force_T_td_primary]
      simp only [primary,↓reduceIte] at hsource
      subst hsource
      simp only [bWeight,tWeight,ExceptionalContactStress.tilt,↓reduceIte]
      exact Prod.ext (by dsimp only) (by dsimp only; ring)
  rw [hvec] at hh ⊢
  cases td
  · simp only [Bool.false_eq_true,↓reduceIte] at hh ⊢
    rw [(scaled_primary_support (R:=R) hsin heta).2] at hh
    refine hh.trans (le_of_eq ?_)
    unfold sigma; ring
  · simp only [↓reduceIte] at hh ⊢
    rw [(scaled_primary_support (R:=R) hsin heta).1] at hh
    refine hh.trans (le_of_eq ?_)
    unfold sigma; ring

theorem E_work (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta z x : ℝ) :
    work (forces C ab td k l c eta z x (delta C.theta D) E) (C.point E)=
      eWork C eta (delta C.theta D) := by
  rw [ExceptionalPositiveTStress.forces,SoleEStress.force_E (Or.inr rfl) (Or.inl rfl)]
  simp [primaryDE,primaryEH,ExceptionalContactStress.tilt,work,eWork]
  ring

theorem necessary {C : SignedCycle} {ab : Fin 4} (td : Bool) {R k l c eta t z : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hk : 0≤k) (hl : 0≤l) (hc0 : 0≤c)
    (heta : 0≤eta) (ht : t∈Icc 0 frameCap) (hz : z∈Icc 0 t)
    (hsource : primary C td=z) (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D+z=t)
    (hpoints : ∀ i,(C.point i).Sorted) (hcircle : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab (btOwner td) (tdOwner td) 3 0 i)) :
    value C ab td R k l c eta t z (delta C.theta G)≤0 := by
  let x := delta C.theta G
  let e := delta C.theta D
  have hx : x∈Icc 0 (t-z) := ⟨hG,by dsimp [x,e] at *; linarith⟩
  have he : e∈Icc 0 (t-z) := ⟨hD,by dsimp [x,e] at *; linarith⟩
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,by linarith [hx.2,hz.1,ht.2]⟩
  have he' : e∈Icc 0 frameCap := ⟨he.1,by linarith [he.2,hz.1,ht.2]⟩
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,hz.2.trans ht.2⟩
  have hxe : t-z-x=e := by dsimp [x,e]; linarith
  have hn0 := mul_nonneg hk (tilt_nonneg heta hx')
  have hp0 := tilt_nonneg heta he'
  have hm0 := mul_nonneg hc0 (tilt_nonneg heta hz')
  have hb0 : 0≤bWeight td c eta z := by cases td <;> simp_all [bWeight]
  have ht0 : 0≤tWeight td c eta z := by cases td <;> simp_all [tWeight]
  have hw : ∀ i,0≤SoleEStress.weights (k*tilt eta x) k l
      (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e) i := by
    intro i
    fin_cases i <;> simp [SoleEStress.weights,hn0,hk,hl,hb0,ht0,hp0]
  let Bnd : Vertex → ℝ := ![
    work (forces C ab td k l c eta z x e H) (C.point H),k*sigma R eta*Real.sin x,
    work (forces C ab td k l c eta z x e A) (C.point A),
    work (forces C ab td k l c eta z x e B) (C.point B),c*sigma R eta*Real.sin z,
    work (forces C ab td k l c eta z x e D) (C.point D),eWork C eta e]
  have hb : ∀ i,work (forces C ab td k l c eta z x e i) (C.point i)≤Bnd i := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact G_work_le ab td l c z e hR hk heta hx' (hpoints G) (hcircle G)
    · exact le_rfl
    · exact le_rfl
    · exact T_work_le ab td k l x e hR hc0 heta hz' hsource (hpoints T) (hcircle T)
    · exact le_rfl
    · exact (E_work C ab td k l c eta z x).le
  have hsep := weighted_separation_le hw hf hb
  have hd : variableDemand C td k l c eta z x e=
      demand C (SoleEStress.weights (k*tilt eta x) k l
        (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e)) := by
    rw [SoleEStress.demand_eq]
    simp [variableDemand,x,e]
  rw [value_eq_stress td R k l c eta hab ht hz hx hsource hn hcontact,hxe]
  dsimp only [stress]
  rw [hd]
  simp only [Bnd,Fin.sum_univ_seven,Matrix.cons_val] at hsep
  dsimp only [anchorWork]
  linarith

end SquaresInCircles.Eight.ExceptionalPositiveTStress
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalPositiveTSupport
open Candidate SignedStress SoleResiduals SecondaryEStress ActualCoreEBlocks
open PositiveAngularEnvelope ExceptionalContactStress ExceptionalPositiveTStress

theorem anchorWork_le {C : SignedCycle} {ab : Fin 4} (td : Bool)
    (R k l c eta z x e : ℝ) (hab : ab=0 ∨ ab=2) (hR : 0≤R)
    (hc : ∀ i,(C.point i).Contained (R^2)) (hn : C.NormalAnchors) :
    ExceptionalPositiveTStress.anchorWork C ab td k l c eta z x e≤
      anchorSupport C ab td R k l c eta z x e := by
  have hH : work (ExceptionalPositiveTStress.forces C ab td k l c eta z x e H) (C.point H)≤
      signedSupport R 1 (ExceptionalPositiveTStress.forces C ab td k l c eta z x e H) :=
    work_le_signed_support hR (hc H) (Or.inl rfl)
      (by simp [abs_of_nonneg hn.H_nonneg]) _
  have hA : work (ExceptionalPositiveTStress.forces C ab td k l c eta z x e A) (C.point A)≤
      signedSupport R 1 (ExceptionalPositiveTStress.forces C ab td k l c eta z x e A) :=
    work_le_signed_support hR (hc A) (Or.inl rfl)
      (by simp [abs_of_nonneg hn.A_nonneg]) _
  have hB : work (ExceptionalPositiveTStress.forces C ab td k l c eta z x e B) (C.point B)≤
      signedSupport R (-1) (ExceptionalPositiveTStress.forces C ab td k l c eta z x e B) :=
    work_le_signed_support hR (hc B) (Or.inr rfl)
      (by simp [abs_of_nonpos hn.B_nonpos]) _
  have hD : work (ExceptionalPositiveTStress.forces C ab td k l c eta z x e D) (C.point D)≤
      signedSupport R (-1) (ExceptionalPositiveTStress.forces C ab td k l c eta z x e D) :=
    work_le_signed_support hR (hc D) (Or.inr rfl)
      (by simp [abs_of_nonpos hn.D_nonpos]) _
  have hsum := SoleEStress.sum_bounds C hab (bt_cases td) (td_cases td)
    (Or.inr rfl) (Or.inl rfl) (k*tilt eta x) k l
    (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e) R
  simp only [SoleEStress.bound,Fin.sum_univ_succ,Fin.sum_univ_zero] at hsum
  simp only [ExceptionalPositiveTStress.anchorWork,anchorSupport,ExceptionalPositiveTStress.forces]
  simp only [ExceptionalPositiveTStress.forces] at hH hA hB hD
  simp [H,G,A,B,T,D,E] at hsum hH hA hB hD ⊢
  linarith

theorem decomposition {C : SignedCycle} {ab : Fin 4} (td : Bool)
    (R k l c eta : ℝ) {z x e : ℝ}
    (hab : ab=0 ∨ ab=2) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hz : z∈Icc 0 frameCap) (hx : x∈Icc 0 frameCap) (he : e∈Icc 0 frameCap)
    (hsource : primary C td=z) :
    variableDemand C td k l c eta z x e-anchorSupport C ab td R k l c eta z x e-
      k*sigma R eta*Real.sin x-c*sigma R eta*Real.sin z-sigma R eta*Real.sin e=
      baseline td R k l c eta z x e+increment C ab td R k l c eta z x e := by
  rcases hab with rfl | rfl <;> cases td <;>
    simp [primary] at hsource <;>
    simp [ExceptionalPositiveTStress.variableDemand,anchorSupport,baseline,
      ExceptionalPositiveTStress.increment,SoleEStress.increment,
      SoleEStress.anchorNorms,SoleEStress.halfShift,SoleEStress.zeroNorms,
      ExceptionalContactSupport.contactScalar,btOwner,tdOwner,bWeight,tWeight,
      ordinaryDE,ordinaryEH,hsource,width_eq (ha H),width_eq (ha A),
      width_eq (ha B),width_eq (ha T),width_eq (ha E),
      edgeWidth_positive_formula hz,edgeWidth_positive_formula hx,
      edgeWidth_positive_formula he,PositiveAngularEnvelope.phi,PositiveAngularEnvelope.psi,
      ExceptionalContactStress.tilt,sigma] <;> ring

theorem value_lower {C : SignedCycle} {ab : Fin 4} (td : Bool)
    {R k l c eta t z x : ℝ} (hab : ab=0 ∨ ab=2) (hR : 0≤R) (heta : 0≤eta)
    (ht : t∈Icc 0 frameCap) (hz : z∈Icc 0 t) (hx : x∈Icc 0 (t-z))
    (hsource : primary C td=z) (hs : ∀ i,(C.point i).Sorted)
    (hc : ∀ i,(C.point i).Contained (R^2)) (hn : C.NormalAnchors)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hcontact : Contact C) :
    baseline td R k l c eta z x (t-z-x)+
      increment C ab td R k l c eta z x (t-z-x)≤
        value C ab td R k l c eta t z x := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,hz.2.trans ht.2⟩
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,by linarith [hx.2,hz.1,ht.2]⟩
  have he : t-z-x∈Icc 0 frameCap :=
    ⟨by linarith [hx.2],by linarith [hx.1,hz.1,ht.2]⟩
  have hw := anchorWork_le td R k l c eta z x (t-z-x) hab hR hc hn
  have hE := ExceptionalContactSupport.eWork_le hR heta he (hs E) (hc E)
  have hid := decomposition td R k l c eta hab ha hz' hx' he hsource
  rw [value_eq_stress td R k l c eta hab ht hz hx hsource hn hcontact]
  dsimp only [ExceptionalPositiveTStress.stress]
  linarith

end SquaresInCircles.Eight.ExceptionalPositiveTSupport
end
end
end

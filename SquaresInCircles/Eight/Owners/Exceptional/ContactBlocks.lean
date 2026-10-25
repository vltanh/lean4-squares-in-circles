module

public import SquaresInCircles.Eight.Owners.Exceptional.ContactSupport

/-!
# Eight squares: the original ordinary angles in the exceptional contact stress

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

def alpha (_k l c eta _x e : ℝ) : Fin 4 → ℝ := ![tilt eta e,l,l,1]
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

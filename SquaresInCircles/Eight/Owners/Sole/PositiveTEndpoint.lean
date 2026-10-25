module

public import SquaresInCircles.Eight.Owners.Sole.EndpointSupport
public import SquaresInCircles.Eight.Owners.Sole.PositiveTEnvelope
public import SquaresInCircles.Eight.Owners.Sole.PositiveTSplitSupport

/-!
# Eight squares: positive-T endpoint support at the unchanged original radius

The concave G/E split has already been defined with
the original anchor coordinates fixed. Only here are its two endpoint
values bounded by the four circle supports. The T support permits both
signed tangents, and the E support retains the actual same-radius axis.
-/

section
/-!
## Original signed blocks for sole E and positive T

The AB weak owner determines the location of its
ordinary angle. A sole-DE D block is written in the reverse coefficient
order so its one actual ordinary angle has the first coefficient. This
is an algebraic swap of the same block, not a change of physical owner.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SolePositiveTOriginalBlocks
open Candidate SoleTScalarModel SolePositiveTSplitModel SolePositiveTOrdinaryData
open ActualOrdinaryBlocks ActualCoreEBlocks PositiveAngularEnvelope SingleAngleConcavity

def rawBlocks (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ) : Fin 4 → Block :=
  SoleEStress.blocks C ab (btOwner s.td) (tdOwner s.td) (deOwner s.family) (ehOwner s.family)
    (n s t z) (k s.family t z) (ell s.family t z)
    (btWeight s.family s.td t z) (tdWeight s.family s.td t z) (p s t z) (lambda s.family)

def swap (B : Block) : Block := ⟨B.beta,B.alpha,B.v,B.u⟩

def blocks (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ) (i : Fin 4) : Block :=
  if i=3 ∧ isDE s.family=true then swap (rawBlocks C ab s t z i) else rawBlocks C ab s t z i

def increment (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (R t z : ℝ) : ℝ :=
  SoleEStress.increment C ab (btOwner s.td) (tdOwner s.td) (deOwner s.family) (ehOwner s.family)
    (n s t z) (k s.family t z) (ell s.family t z)
    (btWeight s.family s.td t z) (tdWeight s.family s.td t z) (p s t z) (lambda s.family) R

theorem btOwner_cases (td : Bool) : btOwner td=2 ∨ btOwner td=3 := by cases td <;> simp [btOwner]
theorem tdOwner_cases (td : Bool) : tdOwner td=0 ∨ tdOwner td=2 := by cases td <;> simp [tdOwner]

theorem swap_data (B : Block) (R : ℝ) :
    (swap B).p=B.p ∧ (swap B).q=B.q ∧ (swap B).P=B.P ∧
    (swap B).N=B.N ∧ (swap B).increment R=B.increment R := by
  simp [swap,Block.p,Block.q,Block.P,Block.N,Block.increment,min_comm,max_comm,
    pairNorm_symm,add_comm]

theorem coefficients (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    (blocks C ab s t z i).p=small s t z i ∧
      (blocks C ab s t z i).q=large s t z i := by
  rcases s with ⟨f,td,atG,j⟩
  fin_cases i <;> cases td <;> cases hD : isDE f <;>
    simp [blocks,rawBlocks,swap,SoleEStress.blocks,Block.p,Block.q,small,large,first,second,
      btWeight,tdWeight,mWeight,m,hD,min_comm,max_comm]

theorem single_data (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ)
    (i : Fin 4) (hi : single s i=true) :
    (blocks C ab s t z i).v=0 ∧ (blocks C ab s t z i).alpha=actualNu s t z i := by
  rcases s with ⟨f,td,atG,j⟩
  fin_cases i <;> cases td <;> cases hD : isDE f <;>
    simp_all [single,blocks,rawBlocks,swap,SoleEStress.blocks,actualNu,
      btOwner,tdOwner,deOwner,ehOwner,ordinaryDE,ordinaryEH,btWeight,tdWeight,mWeight,m]

theorem parts (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    (blocks C ab s t z i).P=
      (ActualCoreEBlocks.blocks C ab (btOwner s.td) (tdOwner s.td)
        (deOwner s.family) (ehOwner s.family) (n s t z) (k s.family t z) (ell s.family t z)
        (btWeight s.family s.td t z) (tdWeight s.family s.td t z) i).P ∧
    (blocks C ab s t z i).N=
      (ActualCoreEBlocks.blocks C ab (btOwner s.td) (tdOwner s.td)
        (deOwner s.family) (ehOwner s.family) (n s t z) (k s.family t z) (ell s.family t z)
        (btWeight s.family s.td t z) (tdWeight s.family s.td t z) i).N := by
  fin_cases i <;> simp only [blocks,rawBlocks,swap,SoleEStress.blocks,ActualCoreEBlocks.blocks] <;>
    split_ifs <;> simp [Block.P,Block.N,add_comm]

theorem original_budgets {C : SignedCycle} {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (s : ScalarCase) (t z : ℝ) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤ePrimary C s.family) (hT : 0≤tPrimary C s.td)
    (htotal : delta C.theta G+ePrimary C s.family+tPrimary C s.td=t) :
    0≤t ∧ (∑i,(blocks C ab s t z i).P)≤frameCap-t ∧
      (∑i,(blocks C ab s t z i).N)=t+∑i,(blocks C ab s t z i).P := by
  have hBT : btOwner s.td=3 → 0 ≤ delta C.theta B := by
    intro h
    cases htd : s.td
    · simpa [tPrimary,htd] using hT
    · simp [btOwner,htd] at h
  have hTD : tdOwner s.td=2 → 0 ≤ delta C.theta T := by
    intro h
    cases htd : s.td
    · simp [tdOwner,htd] at h
    · simpa [tPrimary,htd] using hT
  have hEtotal : eTotal C (deOwner s.family) (ehOwner s.family)=ePrimary C s.family := by
    cases hD : isDE s.family <;>
      simp [eTotal,primaryDE,primaryEH,deOwner,ehOwner,ePrimary,hD]
  have hremoved : removed C (btOwner s.td) (tdOwner s.td)=delta C.theta G+tPrimary C s.td := by
    cases htd : s.td <;> simp [removed,btOwner,tdOwner,tPrimary]
  have hh := ActualCoreEBlocks.block_budgets hab (btOwner_cases s.td) (tdOwner_cases s.td)
    (SolePositiveTSplitSupport.deOwner_cases s.family) (SolePositiveTSplitSupport.ehOwner_cases s.family)
    (n s t z) (k s.family t z) (ell s.family t z)
    (btWeight s.family s.td t z) (tdWeight s.family s.td t z) hvar hG hBT hTD
    (by rw [hEtotal]; exact hE)
  have hP := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => (parts C ab s t z i).1)
  have hN := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => (parts C ab s t z i).2)
  rw [hEtotal,hremoved] at hh
  obtain ⟨h1,h2,h3,h4⟩ := hh
  refine ⟨by linarith [h1.1,h2.1],?_,?_⟩
  · rw [hP]
    linarith
  · rw [hN,hP]
    linarith

theorem individual_budgets {C : SignedCycle} {ab : Fin 4} {s : ScalarCase} {t z : ℝ}
    (ht : 0≤t) (hP : (∑i,(blocks C ab s t z i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab s t z i).N)=t+∑i,(blocks C ab s t z i).P) (i : Fin 4) :
    (blocks C ab s t z i).P≤frameCap ∧ (blocks C ab s t z i).N≤frameCap := by
  have hp := Finset.single_le_sum (fun j _ => (blocks C ab s t z j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (fun j _ => (blocks C ab s t z j).N_nonneg) (Finset.mem_univ i)
  constructor <;> linarith

theorem single_parts (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ)
    (i : Fin 4) (hi : single s i=true) :
    (blocks C ab s t z i).P=0 ∨ (blocks C ab s t z i).N=0 := by
  have hv := (single_data C ab s t z i hi).1
  by_cases hu : 0≤(blocks C ab s t z i).u
  · right
    simp [Block.N,hv,negativePart,max_eq_right (show -(blocks C ab s t z i).u≤0 by linarith)]
  · left
    simp [Block.P,hv,positivePart,max_eq_right (le_of_lt (lt_of_not_ge hu))]

theorem angles_small {C : SignedCycle} (ab : Fin 4) (s : ScalarCase) (t z : ℝ)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (i : Fin 4) :
    |(blocks C ab s t z i).u|≤frameCap ∧ |(blocks C ab s t z i).v|≤frameCap := by
  have hzero : |(0:ℝ)| ≤ frameCap := by norm_num [frameCap]
  have hite : ∀ (P : Prop) [Decidable P] (j : Vertex),
      |(if P then delta C.theta j else 0)| ≤ frameCap := by
    intro P _ j
    split_ifs
    · exact ha j
    · exact hzero
  fin_cases i <;> simp only [blocks,rawBlocks,swap,SoleEStress.blocks] <;> split_ifs <;>
    exact ⟨by first | exact ha _ | exact hzero | exact hite _ _,
      by first | exact ha _ | exact hzero | exact hite _ _⟩

theorem block_minorant {C : SignedCycle} {ab : Fin 4} {s : ScalarCase} {R t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hP : (∑i,(blocks C ab s t z i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab s t z i).N)=t+∑i,(blocks C ab s t z i).P) (i : Fin 4) :
    F (single s i) R (small s t z i) (large s t z i) (actualNu s t z i)
      (blocks C ab s t z i).P (blocks C ab s t z i).N≤(blocks C ab s t z i).increment R := by
  obtain ⟨hp,hq⟩ := coefficients C ab s t z i
  have hb := individual_budgets (angle ht).1 hP hN i
  cases hi : single s i
  · have hh := (blocks C ab s t z i).minorant R
      (by rw [hp]; exact (small_pos s ht hz i).le) hb.1 hb.2
    rw [hp,hq] at hh
    simpa only [F,Bool.false_eq_true,↓reduceIte] using hh
  · obtain ⟨hv,hnu⟩ := single_data C ab s t z i hi
    have hh := SoleOriginalBlocks.one_angle_minorant (blocks C ab s t z i) R hv
      (angles_small ab s t z ha i).1
    rw [hp,hq,hnu] at hh
    exact hh

theorem increment_eq {C : SignedCycle} {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (s : ScalarCase) (R t z : ℝ) :
    increment C ab s R t z=∑i,(blocks C ab s t z i).increment R := by
  rw [increment,SoleEStress.increment_eq C hab (btOwner_cases s.td) (tdOwner_cases s.td)]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [blocks]
  split_ifs
  · exact (swap_data (rawBlocks C ab s t z i) R).2.2.2.2.symm
  · rfl

theorem original_increment {C : SignedCycle} {ab : Fin 4} (s : ScalarCase) {R t z L : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤ePrimary C s.family) (hT : 0≤tPrimary C s.td)
    (htotal : delta C.theta G+ePrimary C s.family+tPrimary C s.td=t)
    (hpure : ∀ i,L≤pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t) :
    L≤ increment C ab s R t z := by
  obtain ⟨ht0,hP,hN⟩ := original_budgets hab s t z hvar hG hE hT htotal
  have henvelope := SolePositiveTEnvelope.ordinary_lower s
    (fun i => (blocks C ab s t z i).P) (fun i => (blocks C ab s t z i).N)
    hR hQL hQU ht hz (fun i => (blocks C ab s t z i).P_nonneg)
    (fun i => (blocks C ab s t z i).N_nonneg) hP hN
    (single_parts C ab s t z) hpure
  have hminor := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => block_minorant (R := R) ht hz ha hP hN i)
  rw [increment_eq hab s R t z]
  exact henvelope.trans hminor

end SquaresInCircles.Eight.SolePositiveTOriginalBlocks
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SolePositiveTEndpoint
open Candidate SignedStress SoleResiduals SecondaryEStress ActualCoreEBlocks
open SoleTScalarModel SolePositiveTSplitModel SolePositiveTSplitSupport
open SolePositiveTOrdinaryData PositiveAngularEnvelope

def faceForces (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ) : Vertex → Point :=
  SoleEStress.forces C ab (btOwner s.td) (tdOwner s.td) (deOwner s.family) (ehOwner s.family)
    (n s t z) (k s.family t z) (ell s.family t z)
    (btWeight s.family s.td t z) (tdWeight s.family s.td t z) (p s t z) (lambda s.family)

def anchorSupport (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (R t z : ℝ) : ℝ :=
  R*SoleEStress.anchorNorms C ab (btOwner s.td) (tdOwner s.td) (deOwner s.family) (ehOwner s.family)
      (n s t z) (k s.family t z) (ell s.family t z)
      (btWeight s.family s.td t z) (tdWeight s.family s.td t z) (p s t z) (lambda s.family)-
    SoleEStress.halfShift C ab (btOwner s.td) (tdOwner s.td) (deOwner s.family) (ehOwner s.family)
      (n s t z) (k s.family t z) (ell s.family t z)
      (btWeight s.family s.td t z) (tdWeight s.family s.td t z) (p s t z) (lambda s.family)

def eWork (s : ScalarCase) (R M t z : ℝ) : ℝ :=
  if tiltedE s.family then sigma R (epsilon s.family t)*Real.sin (SoleTScalarModel.e s t z)
  else if isDE s.family then M*Real.sin (SoleTScalarModel.e s t z)
  else SoleEndpointSupport.highWork R (SoleTScalarModel.e s t z)

theorem T_support {C : SignedCycle} (ab : Fin 4) (s : ScalarCase) {R t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (hsource : z=tPrimary C s.td) :
    circleSupport R (faceForces C ab s t z T)=primarySupport R (c s.family t z) (eta t) z := by
  have hc := (coefficient_positive ht hz).2.2.1.le
  have hη := (coefficient_positive ht hz).2.2.2.2.2
  have hs := (transport_trig (split_angles s ht hz).1).2.2.1
  have hκ : 0 ≤ c s.family t z*Real.sin z := mul_nonneg hc hs
  unfold faceForces
  rw [SoleEStress.force_T]
  cases htd : s.td
  · have hδ : delta C.theta B=z := by simpa [tPrimary,htd] using hsource.symm
    simp only [btOwner,tdOwner,btWeight,tdWeight,Bool.false_eq_true,↓reduceIte]
    rw [SecondaryEStress.force_T_bt_primary,hδ]
    have he : (c s.family t z*Real.sin z,mWeight s.family t z-c s.family t z*Real.cos z)=
        (c s.family t z*Real.sin z,(c s.family t z*Real.sin z)*eta t) := by
      simp only [mWeight,Prod.mk.injEq,true_and]
      ring
    rw [he]
    unfold primarySupport
    rw [(scaled_primary_support (R:=R) hκ hη).2]
  · have hδ : delta C.theta T=z := by simpa [tPrimary,htd] using hsource.symm
    simp only [btOwner,tdOwner,btWeight,tdWeight,↓reduceIte]
    rw [SecondaryEStress.force_T_td_primary,hδ]
    have he : (c s.family t z*Real.sin z,c s.family t z*Real.cos z-mWeight s.family t z)=
        (c s.family t z*Real.sin z,-(c s.family t z*Real.sin z)*eta t) := by
      simp only [mWeight,Prod.mk.injEq,true_and]
      ring
    rw [he]
    unfold primarySupport
    rw [(scaled_primary_support (R:=R) hκ hη).1]

theorem fixedWork_le {C : SignedCycle} {ab : Fin 4} (s : ScalarCase) {R t z : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (hsource : z=tPrimary C s.td) (hs : (C.point T).Sorted)
    (hc : ∀ i,(C.point i).Contained (R^2)) (hn : C.NormalAnchors) :
    fixedWork C ab s.family s.td t z (x s t z) (SoleTScalarModel.e s t z)≤
      anchorSupport C ab s R t z+primarySupport R (c s.family t z) (eta t) z := by
  obtain ⟨F,hF⟩ : ∃ F,F=faceForces C ab s t z := ⟨_,rfl⟩
  have hH : work (F H) (C.point H) ≤ SecondaryEStress.signedSupport R 1 (F H) :=
    work_le_signed_support hR (hc H) (Or.inl rfl) (by simp [abs_of_nonneg hn.H_nonneg]) (F H)
  have hA : work (F A) (C.point A) ≤ SecondaryEStress.signedSupport R 1 (F A) :=
    work_le_signed_support hR (hc A) (Or.inl rfl) (by simp [abs_of_nonneg hn.A_nonneg]) (F A)
  have hB : work (F B) (C.point B) ≤ SecondaryEStress.signedSupport R (-1) (F B) :=
    work_le_signed_support hR (hc B) (Or.inr rfl) (by simp [abs_of_nonpos hn.B_nonpos]) (F B)
  have hD : work (F D) (C.point D) ≤ SecondaryEStress.signedSupport R (-1) (F D) :=
    work_le_signed_support hR (hc D) (Or.inr rfl) (by simp [abs_of_nonpos hn.D_nonpos]) (F D)
  have hT := work_le_circleSupport hR hs (hc T) (F T)
  rw [hF,T_support ab s ht hz hsource,← hF] at hT
  have hsum := SoleEStress.sum_bounds C hab
    (SolePositiveTOriginalBlocks.btOwner_cases s.td) (SolePositiveTOriginalBlocks.tdOwner_cases s.td)
    (deOwner_cases s.family) (ehOwner_cases s.family)
    (n s t z) (k s.family t z) (ell s.family t z)
    (btWeight s.family s.td t z) (tdWeight s.family s.td t z) (p s t z) (lambda s.family) R
  have hsum' : SecondaryEStress.signedSupport R 1 (F H)+circleSupport R (F G)+
      SecondaryEStress.signedSupport R 1 (F A)+SecondaryEStress.signedSupport R (-1) (F B)+
      circleSupport R (F T)+SecondaryEStress.signedSupport R (-1) (F D)+work (F E) (C.point E)=
      anchorSupport C ab s R t z+circleSupport R (F G)+circleSupport R (F T)+
        work (F E) (C.point E) := by
    rw [Fin.sum_univ_seven] at hsum
    rw [hF]
    exact hsum
  have hfix : fixedWork C ab s.family s.td t z (x s t z) (SoleTScalarModel.e s t z)=
      work (F H) (C.point H)+work (F A) (C.point A)+work (F B) (C.point B)+
        work (F T) (C.point T)+work (F D) (C.point D) := by
    rw [hF]
    rfl
  rw [hfix]
  linarith

theorem E_support {C : SignedCycle} (s : ScalarCase) {R M t z : ℝ}
    (hR : 0≤R) (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (hs : (C.point E).Sorted) (hc : (C.point E).Contained (R^2)) :
    eBound C s.family R M t (SoleTScalarModel.e s t z)≤eWork s R M t z := by
  have he := (split_angles s ht hz).2.2
  by_cases htilt : tiltedE s.family=true
  · simp [eBound,eWork,htilt]
  · have htilt' := Bool.eq_false_of_not_eq_true htilt
    by_cases hde : isDE s.family=true
    · simp [eBound,eWork,htilt',hde]
    · have hde' := Bool.eq_false_of_not_eq_true hde
      simp only [eBound,eWork,htilt',hde']
      exact SoleEndpointSupport.folded_work_le hR hs hc he

theorem decomposition {C : SignedCycle} {ab : Fin 4} (s : ScalarCase) (R M : ℝ) {t z : ℝ}
    (hab : ab=0 ∨ ab=2) (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (hsource : z=tPrimary C s.td) (ha : ∀ i,|delta C.theta i|≤frameCap) :
    variableDemand C s.family s.td t z (x s t z) (SoleTScalarModel.e s t z)-anchorSupport C ab s R t z-
      primarySupport R (c s.family t z) (eta t) z-
      k s.family t z*sigma R (g s.family t)*Real.sin (x s t z)-eWork s R M t z=
    baseline s R (M+1/2) t z+SolePositiveTOriginalBlocks.increment C ab s R t z := by
  obtain ⟨hz',hx,he⟩ := split_angles s ht hz
  have hWx := edgeWidth_positive_formula hx
  have hWe := edgeWidth_positive_formula he
  have hWz := edgeWidth_positive_formula hz'
  have hψz := psi_positive hz'
  have hW0 : edgeWidth (0:ℝ)=1 := by simp [edgeWidth,pairWidth]
  cases htd : s.td
  · have hδ : delta C.theta B=z := by simpa [tPrimary,htd] using hsource.symm
    rcases hab with rfl | rfl <;> cases hf : s.family <;>
      simp [variableDemand,anchorSupport,baseline,SolePositiveTOriginalBlocks.increment,
        SoleEStress.increment,SoleEStress.anchorNorms,SoleEStress.halfShift,SoleEStress.zeroNorms,
        eWork,eTerm,primaryCoefficient,primarySupport,sigma,SoleEndpointSupport.highWork,
        first,second,Fin.sum_univ_succ,btOwner,tdOwner,deOwner,ehOwner,btWeight,tdWeight,
        ordinaryDE,ordinaryEH,nWeight,n,mWeight,m,deWeight,ehWeight,p,lambda,tiltedE,isDE,hf,htd,
        hδ,hWx,hWe,hWz,width_eq (ha H),width_eq (ha A),width_eq (ha T),
        width_eq (ha D),width_eq (ha E),PositiveAngularEnvelope.phi,psi_zero] <;> ring
  · have hδ : delta C.theta T=z := by simpa [tPrimary,htd] using hsource.symm
    rcases hab with rfl | rfl <;> cases hf : s.family <;>
      simp [variableDemand,anchorSupport,baseline,SolePositiveTOriginalBlocks.increment,
        SoleEStress.increment,SoleEStress.anchorNorms,SoleEStress.halfShift,SoleEStress.zeroNorms,
        eWork,eTerm,primaryCoefficient,primarySupport,sigma,SoleEndpointSupport.highWork,
        first,second,Fin.sum_univ_succ,btOwner,tdOwner,deOwner,ehOwner,btWeight,tdWeight,
        ordinaryDE,ordinaryEH,nWeight,n,mWeight,m,deWeight,ehWeight,p,lambda,tiltedE,isDE,hf,htd,
        hδ,hWx,hWe,hWz,width_eq (ha H),width_eq (ha A),width_eq (ha B),
        width_eq (ha D),width_eq (ha E),PositiveAngularEnvelope.phi,psi_zero] <;> ring

theorem value_lower {C : SignedCycle} {ab : Fin 4} (s : ScalarCase) {R M t z : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (hsource : z=tPrimary C s.td) (hs : ∀ i,(C.point i).Sorted)
    (hc : ∀ i,(C.point i).Contained (R^2)) (hn : C.NormalAnchors)
    (ha : ∀ i,|delta C.theta i|≤frameCap) :
    baseline s R (M+1/2) t z+SolePositiveTOriginalBlocks.increment C ab s R t z≤
      SolePositiveTSplitModel.value C ab s.family s.td R M t z (x s t z) := by
  have hx : x s t z∈Icc 0 (t-z) := by
    unfold x
    split_ifs
    · exact ⟨by linarith [hz.2],le_rfl⟩
    · exact ⟨le_rfl,by linarith [hz.2]⟩
  have he : t-z-x s t z=SoleTScalarModel.e s t z := by
    unfold x SoleTScalarModel.e
    split_ifs <;> ring
  have hfixed := fixedWork_le s hab hR ht hz hsource (hs T) hc hn
  have hE := E_support (C := C) s (M := M) hR ht hz (hs E) (hc E)
  have hid := decomposition s R M hab ht hz hsource ha
  rw [value_eq_stress s.td R M hab ht hz hx hn,he]
  simp only [stress]
  linarith

theorem endpoint_positive {C : SignedCycle} {ab : Fin 4} (s : ScalarCase) {q t z : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qTrial)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (hsource : z=tPrimary C s.td)
    (hC : C.Necessary q) (hn : C.NormalAnchors) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤ePrimary C s.family) (hT : 0≤tPrimary C s.td)
    (htotal : delta C.theta G+ePrimary C s.family+tPrimary C s.td=t) :
    0<SolePositiveTSplitModel.value C ab s.family s.td (Real.sqrt q) (axisCoordinate q) t z (x s t z) := by
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hR2 := Real.sq_sqrt hq0
  have hR := Real.sqrt_nonneg q
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  have hRL : qLow≤(Real.sqrt q)^2 := by simpa only [hR2] using hQL
  have hRU : (Real.sqrt q)^2≤qCap := by simpa only [hR2] using hcap
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by simpa only [hR2] using hC.contained
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hpure (i : Fin 4) : 1/10000-baseline s (Real.sqrt q) (Real.sqrt (q-1/4)) t z≤
      SingleAngleConcavity.pure (single s i) (Real.sqrt q) (small s t z i) (large s t z i)
        (actualNu s t z i) t := by
    have hs := SolePositiveTScalar.actual_radius_positive {s with negative:=i} hQU ht hz
    have hl := pure_scalar_lower s (R:=Real.sqrt q) (M:=Real.sqrt (q-1/4)) ht hz i
    linarith
  have hi := SolePositiveTOriginalBlocks.original_increment s hab hR hRL hRU ht hz
    ha hvar hG hE hT htotal hpure
  have hl := value_lower s hab hR ht hz hsource hC.sorted hc hn ha
    (M:=axisCoordinate q)
  have haxis : axisCoordinate q+1/2=Real.sqrt (q-1/4) := by simp [axisCoordinate]
  rw [haxis] at hl
  linarith

end SquaresInCircles.Eight.SolePositiveTEndpoint
end
end
end

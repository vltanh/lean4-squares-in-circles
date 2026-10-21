module

public import SquaresInCircles.Eight.TableFree.FlatPrimaryParameters
public import SquaresInCircles.Eight.TableFree.CoreENegativeStress

/-!
# The original four anchor blocks with negative E secants

Uncompiled source. Only the two E stress multipliers change. Every
signed angle, owner, and source point remains the original one. The
positive and negative budgets below are exact sums of those angles.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.FlatEBlocks
open Candidate PositiveAngularEnvelope PositivePrimaryBaselines PositiveStressCoefficients
open ActualOrdinaryBlocks ActualCoreEBlocks OrdinaryAngleConcavity
open FlatPrimaryConcentration FlatPrimaryEnvelope NegativeEOneAngle

def deAngle (C : SignedCycle) (de : Fin 4) : ℝ := -primaryDE C de
def ehAngle (C : SignedCycle) (eh : Fin 4) : ℝ := -primaryEH C eh
def deWeight (C : SignedCycle) (de : Fin 4) : ℝ := 1/Real.cos (deAngle C de)
def ehWeight (C : SignedCycle) (eh : Fin 4) : ℝ := 1/Real.cos (ehAngle C eh)

def blocks (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t : ℝ) : Fin 4 → Block :=
  ![⟨n,ehWeight C eh,delta C.theta H,ordinaryEH C eh⟩,
    ⟨l,k,if ab=0 then 0 else delta C.theta A,0⟩,
    ⟨l,b,if ab=0 then delta C.theta A else 0,if bt=2 then delta C.theta B else 0⟩,
    ⟨deWeight C de,t,ordinaryDE C de,if td=0 then delta C.theta T else 0⟩]

def modified (de eh : Fin 4) : Fin 4 → Bool := ![decide (eh=1),false,false,decide (de=3)]

def positiveRemoved (C : SignedCycle) (bt td : Fin 4) : ℝ :=
  positivePart (delta C.theta G)+(if bt=3 then positivePart (delta C.theta B) else 0)+
    (if td=2 then positivePart (delta C.theta T) else 0)

def negativeRemoved (C : SignedCycle) (bt td de eh : Fin 4) : ℝ :=
  negativePart (delta C.theta G)+(if bt=3 then negativePart (delta C.theta B) else 0)+
    (if td=2 then negativePart (delta C.theta T) else 0)+deAngle C de+ehAngle C eh

theorem unchanged_masses (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t : ℝ) (i : Fin 4) :
    (blocks C ab bt td de eh n k l b t i).P=
      (ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).P ∧
    (blocks C ab bt td de eh n k l b t i).N=
      (ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).N := by
  fin_cases i <;> simp [blocks,ActualCoreEBlocks.blocks,Block.P,Block.N]

theorem sum_parts (C : SignedCycle) {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (n k l b t : ℝ) (f : ℝ → ℝ) (hf0 : f 0=0) :
    (∑ i,f (blocks C ab bt td de eh n k l b t i).u+
      f (blocks C ab bt td de eh n k l b t i).v)=
      (∑ j,f (delta C.theta j))-f (delta C.theta G)-
        (if bt=3 then f (delta C.theta B) else 0)-
        (if td=2 then f (delta C.theta T) else 0)-
        f (primaryDE C de)-f (primaryEH C eh) := by
  have he (i : Fin 4) :
      f (blocks C ab bt td de eh n k l b t i).u+f (blocks C ab bt td de eh n k l b t i).v=
      f (ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).u+
        f (ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).v := by
    fin_cases i <;> simp [blocks,ActualCoreEBlocks.blocks]
  simp_rw [he]
  exact ActualCoreEBlocks.sum_parts C hab hbt htd hde heh n k l b t f hf0

theorem removed_nonneg {C : SignedCycle} {bt td de eh : Fin 4}
    (hd : primaryDE C de≤0) (he : primaryEH C eh≤0) :
    0≤positiveRemoved C bt td ∧ 0≤negativeRemoved C bt td de eh ∧
      deAngle C de∈Icc 0 (negativeRemoved C bt td de eh) ∧
      ehAngle C eh∈Icc 0 (negativeRemoved C bt td de eh) := by
  have hPB : 0≤(if bt=3 then positivePart (delta C.theta B) else 0) := by split_ifs <;> positivity
  have hPT : 0≤(if td=2 then positivePart (delta C.theta T) else 0) := by split_ifs <;> positivity
  have hNB : 0≤(if bt=3 then negativePart (delta C.theta B) else 0) := by split_ifs <;> positivity
  have hNT : 0≤(if td=2 then negativePart (delta C.theta T) else 0) := by split_ifs <;> positivity
  have hPG := positivePart_nonneg (delta C.theta G)
  have hNG := negativePart_nonneg (delta C.theta G)
  dsimp [positiveRemoved,negativeRemoved,deAngle,ehAngle]
  exact ⟨by linarith,by linarith,⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

theorem budgets {C : SignedCycle} {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (n k l b t : ℝ) (hvar : positiveVariation C.theta≤frameCap)
    (hd : primaryDE C de≤0) (he : primaryEH C eh≤0) :
    positiveRemoved C bt td∈Icc 0 frameCap ∧
    negativeRemoved C bt td de eh∈Icc 0 frameCap ∧
    (∑ i,(blocks C ab bt td de eh n k l b t i).P)≤frameCap-positiveRemoved C bt td ∧
    (∑ i,(blocks C ab bt td de eh n k l b t i).N)=
      positiveRemoved C bt td-negativeRemoved C bt td de eh+
        ∑ i,(blocks C ab bt td de eh n k l b t i).P := by
  have hp := sum_parts C hab hbt htd hde heh n k l b t positivePart positivePart_zero
  have hn := sum_parts C hab hbt htd hde heh n k l b t negativePart negativePart_zero
  have hPd : positivePart (primaryDE C de)=0 := max_eq_right hd
  have hPe : positivePart (primaryEH C eh)=0 := max_eq_right he
  have hNd : negativePart (primaryDE C de)=deAngle C de := max_eq_left (neg_nonneg.mpr hd)
  have hNe : negativePart (primaryEH C eh)=ehAngle C eh := max_eq_left (neg_nonneg.mpr he)
  have hp' : (∑ i,(blocks C ab bt td de eh n k l b t i).P)=
      positiveVariation C.theta-positiveRemoved C bt td := by
    change (∑ i,positivePart (blocks C ab bt td de eh n k l b t i).u+
      positivePart (blocks C ab bt td de eh n k l b t i).v)=_
    rw [hp,hPd,hPe]
    dsimp [positiveVariation,positiveRemoved]
    ring
  have hn' : (∑ i,(blocks C ab bt td de eh n k l b t i).N)=
      negativeVariation C.theta-negativeRemoved C bt td de eh := by
    change (∑ i,negativePart (blocks C ab bt td de eh n k l b t i).u+
      negativePart (blocks C ab bt td de eh n k l b t i).v)=_
    rw [hn,hNd,hNe]
    dsimp [negativeVariation,negativeRemoved]
    ring
  have hP0 := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => (blocks C ab bt td de eh n k l b t i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => (blocks C ab bt td de eh n k l b t i).N_nonneg)
  have hn0 := removed_nonneg (bt := bt) (td := td) hd he
  have hv := variations_equal C.theta
  exact ⟨⟨hn0.1,by linarith⟩,⟨hn0.2.1,by linarith⟩,by linarith,by linarith⟩

theorem block_minorant {C : SignedCycle} {ab bt td de eh : Fin 4}
    {n l b t s : ℝ} {p q : Fin 4 → ℝ}
    (htd : td=0 ∨ td=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hn : k≤n ∧ n≤2069/2000) (ht : k≤t ∧ (td=0 → t≤2069/2000))
    (hs : s∈Icc 0 frameCap)
    (hd : deAngle C de∈Icc 0 s) (he : ehAngle C eh∈Icc 0 s)
    (hp : ∀ i,0<p i)
    (hcoeff : ∀ i,(ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).p=p i ∧
      (ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).q=q i)
    (hP : ∀ i,(blocks C ab bt td de eh n k l b t i).P≤frameCap)
    (hN : ∀ i,(blocks C ab bt td de eh n k l b t i).N≤frameCap-s)
    (i : Fin 4) :
    F (modified de eh i) (p i) (q i) s
      (blocks C ab bt td de eh n k l b t i).P
      (blocks C ab bt td de eh n k l b t i).N≤
        (blocks C ab bt td de eh n k l b t i).increment (Real.sqrt qCap) := by
  have hordinary (j : Fin 4)
      (hb : blocks C ab bt td de eh n k l b t j=
        ActualCoreEBlocks.blocks C ab bt td de eh n k l b t j)
      (hm : modified de eh j=false) :
      F (modified de eh j) (p j) (q j) s
        (blocks C ab bt td de eh n k l b t j).P
        (blocks C ab bt td de eh n k l b t j).N≤
          (blocks C ab bt td de eh n k l b t j).increment (Real.sqrt qCap) := by
    have hc := hcoeff j
    have hpos : 0≤(blocks C ab bt td de eh n k l b t j).p := by rw [hb,hc.1]; exact (hp j).le
    have hh := (blocks C ab bt td de eh n k l b t j).minorant (Real.sqrt qCap)
      hpos (hP j) (by linarith [hN j,hs.1])
    simpa [hm,F,hb,hc.1,hc.2] using hh
  fin_cases i
  · rcases heh with rfl | rfl
    · apply hordinary 0
      · simp [blocks,ActualCoreEBlocks.blocks,ehWeight,ehAngle,primaryEH]
      · simp [modified]
    · have hbud : negativePart (delta C.theta H)≤frameCap-s := by
        simpa [blocks,Block.N,ordinaryEH] using hN 0
      have hh := actual_minorant hn hs he (hsmall H) hbud
      simpa [blocks,Block.P,Block.N,Block.increment,modified,F,ordinaryEH,
        ehWeight,NegativeEOneAngle.increment] using hh
  · apply hordinary 1 <;> simp [blocks,ActualCoreEBlocks.blocks,modified]
  · apply hordinary 2 <;> simp [blocks,ActualCoreEBlocks.blocks,modified]
  · rcases hde with rfl | rfl
    · apply hordinary 3
      · simp [blocks,ActualCoreEBlocks.blocks,deWeight,deAngle,primaryDE]
      · simp [modified]
    · rcases htd with rfl | rfl
      · have hbud : negativePart (delta C.theta T)≤frameCap-s := by
          simpa [blocks,Block.N,ordinaryDE] using hN 3
        have hh := actual_minorant ⟨ht.1,ht.2 rfl⟩ hs hd (hsmall T) hbud
        simpa [blocks,Block.P,Block.N,Block.increment,modified,F,ordinaryDE,
          deWeight,NegativeEOneAngle.increment,pairNorm_symm] using hh
      · simp [blocks,Block.P,Block.N,Block.increment,modified,F,ordinaryDE]

theorem actual_lower {C : SignedCycle} {ab bt td de eh : Fin 4} {n l b t λ : ℝ}
    {p q : Fin 4 → ℝ}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hvar : positiveVariation C.theta≤frameCap)
    (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hn : k≤n ∧ n≤2069/2000) (ht : k≤t ∧ (td=0 → t≤2069/2000))
    (hdom : Domain (positiveRemoved C bt td) (negativeRemoved C bt td de eh) l p q)
    (hcoeff : ∀ i,(ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).p=p i ∧
      (ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).q=q i)
    (hλ : 369/500≤λ) :
    min (V (Real.sqrt qCap) l k (positiveRemoved C bt td)) (λ*positiveRemoved C bt td)≤
      λ*negativeRemoved C bt td de eh+
        ∑ i,(blocks C ab bt td de eh n k l b t i).increment (Real.sqrt qCap) := by
  let bs := blocks C ab bt td de eh n k l b t
  have hb := budgets hab hbt htd hde heh n k l b t hvar hd he
  have hremoved := removed_nonneg (bt := bt) (td := td) hd he
  have hPsum : (∑ i,(bs i).P)≤frameCap := by linarith [hb.2.2.1,hb.1.1]
  have hNsum : (∑ i,(bs i).N)≤frameCap-negativeRemoved C bt td de eh := by
    rw [hb.2.2.2]
    linarith [hb.2.2.1]
  have hP (i : Fin 4) : (bs i).P≤frameCap :=
    (Finset.single_le_sum (fun j _ => (bs j).P_nonneg) (Finset.mem_univ i)).trans hPsum
  have hN (i : Fin 4) : (bs i).N≤frameCap-negativeRemoved C bt td de eh :=
    (Finset.single_le_sum (fun j _ => (bs j).N_nonneg) (Finset.mem_univ i)).trans hNsum
  have hminor := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    block_minorant htd hde heh hsmall hn ht hb.2.1 hremoved.2.2.1 hremoved.2.2.2
      hdom.positive hcoeff hP hN i)
  have hangular := mixed_sum_lower hdom hλ (modified de eh) (fun i => (bs i).P)
    (fun i => (bs i).N) (fun i => (bs i).P_nonneg) (fun i => (bs i).N_nonneg)
    hb.2.2.1 hb.2.2.2
  exact hangular.trans (add_le_add_left hminor _)

end SquaresInCircles.Eight.TableFree.FlatEBlocks

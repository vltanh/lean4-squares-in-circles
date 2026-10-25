module

public import SquaresInCircles.Eight.TableFree.SoleNegativeTEnvelope
public import SquaresInCircles.Eight.TableFree.SoleNegativeTDSupport
public import SquaresInCircles.Eight.TableFree.SolePositiveTOriginalBlocks

/-!
# The original ordinary blocks for a genuine negative T primary

Uncompiled source. The negative primary removes exactly its original
negative variation. The other ordinary angles, and the weak AB owner,
remain unchanged. D is charged against its sorted support at the actual
q; the other three anchors retain their original circle supports.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleNegativeTOriginalBlocks
open Candidate SoleTScalarModel SolePositiveTSplitModel
open SoleNegativeTCoefficients SoleNegativeTOrdinaryData
open ActualCoreEBlocks ActualOrdinaryBlocks PositiveAngularEnvelope
open OrdinaryAngleConcavity SingleAngleConcavity

def blocks (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool) (t s : ℝ) :
    Fin 4 → Block :=
  SoleEStress.blocks C ab (btOwner td) (tdOwner td) (deOwner f) (ehOwner f)
    (n (face f atG) t 0) (k f t 0) (ell f t 0)
    (SoleNegativeTSplit.btWeight f td t s) (SoleNegativeTSplit.tdWeight f td t s)
    (p (face f atG) t 0) (lambda f)

def contribution (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool)
    (q t s : ℝ) (i : Fin 4) : ℝ :=
  if i=3 then SoleNegativeTDSupport.increment q (p (face f atG) t 0)
    (dCoefficient f td t s) (ordinaryDE C (deOwner f))
  else (blocks C ab f atG td t s i).increment (Real.sqrt q)

def ordinary (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool) (q t s : ℝ) : ℝ :=
  ∑ i,contribution C ab f atG td q t s i

theorem sum_parts (C : SignedCycle) {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (f : Family) (atG td : Bool) (t s : ℝ) (F : ℝ → ℝ) (hF : F 0=0) :
    (∑ i,(F (blocks C ab f atG td t s i).u+F (blocks C ab f atG td t s i).v))=
      (∑ j,F (delta C.theta j))-F (delta C.theta G)-F (ePrimary C f)-F (tPrimary C td) := by
  have hh := ActualCoreEBlocks.sum_parts C hab
    (SolePositiveTOriginalBlocks.btOwner_cases td) (SolePositiveTOriginalBlocks.tdOwner_cases td)
    (SolePositiveTSplitSupport.deOwner_cases f) (SolePositiveTSplitSupport.ehOwner_cases f)
    (n (face f atG) t 0) (k f t 0) (ell f t 0)
    (SoleNegativeTSplit.btWeight f td t s) (SoleNegativeTSplit.tdWeight f td t s) F hF
  have he : (∑ i,(F (blocks C ab f atG td t s i).u+F (blocks C ab f atG td t s i).v))=
      ∑ i,(F (ActualCoreEBlocks.blocks C ab (btOwner td) (tdOwner td) (deOwner f) (ehOwner f)
        (n (face f atG) t 0) (k f t 0) (ell f t 0)
        (SoleNegativeTSplit.btWeight f td t s) (SoleNegativeTSplit.tdWeight f td t s) i).u+
      F (ActualCoreEBlocks.blocks C ab (btOwner td) (tdOwner td) (deOwner f) (ehOwner f)
        (n (face f atG) t 0) (k f t 0) (ell f t 0)
        (SoleNegativeTSplit.btWeight f td t s) (SoleNegativeTSplit.tdWeight f td t s) i).v) := by
    apply Finset.sum_congr rfl
    intro i _
    fin_cases i <;> rfl
  rw [he,hh]
  cases f <;> cases td <;>
    simp [btOwner,tdOwner,deOwner,ehOwner,ePrimary,tPrimary,primaryDE,primaryEH,isDE,hF] <;> ring

theorem original_budgets {C : SignedCycle} {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (f : Family) (atG td : Bool) {t s : ℝ}
    (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤ePrimary C f) (hs : 0≤ s)
    (hsource : tPrimary C td= -s) (htotal : delta C.theta G+ePrimary C f=t) :
    0≤t ∧ (∑i,(blocks C ab f atG td t s i).P)≤frameCap-t ∧
      (∑i,(blocks C ab f atG td t s i).N)=t-s+∑i,(blocks C ab f atG td t s i).P := by
  have hp := sum_parts C hab f atG td t s positivePart positivePart_zero
  have hn := sum_parts C hab f atG td t s negativePart negativePart_zero
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hG
  have hPE : positivePart (ePrimary C f)=ePrimary C f := max_eq_left hE
  have hPT : positivePart (tPrimary C td)=0 := by
    rw [hsource]
    exact max_eq_right (by linarith)
  have hNG : negativePart (delta C.theta G)=0 := max_eq_right (by linarith)
  have hNE : negativePart (ePrimary C f)=0 := max_eq_right (by linarith)
  have hNT : negativePart (tPrimary C td)=s := by
    simp [hsource,negativePart,max_eq_left hs]
  change (∑ i,(blocks C ab f atG td t s i).P)=
    positiveVariation C.theta-positivePart (delta C.theta G)-positivePart (ePrimary C f)-
      positivePart (tPrimary C td) at hp
  change (∑ i,(blocks C ab f atG td t s i).N)=
    negativeVariation C.theta-negativePart (delta C.theta G)-negativePart (ePrimary C f)-
      negativePart (tPrimary C td) at hn
  rw [hPG,hPE,hPT] at hp
  rw [hNG,hNE,hNT] at hn
  have hv := variations_equal C.theta
  refine ⟨by linarith,by linarith,by linarith⟩

theorem individual_budgets {C : SignedCycle} {ab : Fin 4} {f : Family} {atG td : Bool}
    {t s : ℝ} (ht : 0≤t) (hs : 0≤ s)
    (hP : (∑i,(blocks C ab f atG td t s i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab f atG td t s i).N)=t-s+∑i,(blocks C ab f atG td t s i).P)
    (i : Fin 4) :
    (blocks C ab f atG td t s i).P≤frameCap ∧ (blocks C ab f atG td t s i).N≤frameCap := by
  have hp := Finset.single_le_sum (fun j _ => (blocks C ab f atG td t s j).P_nonneg)
    (Finset.mem_univ i)
  have hn := Finset.single_le_sum (fun j _ => (blocks C ab f atG td t s j).N_nonneg)
    (Finset.mem_univ i)
  constructor <;> linarith

theorem single_data {C : SignedCycle} (ab : Fin 4) (f : Family) (atG td : Bool) (t s : ℝ)
    (hflat : td=false → delta C.theta T=0) (i : Fin 4) (hi : single f td i=true) :
    (blocks C ab f atG td t s i).v=0 := by
  fin_cases i <;> cases f <;> cases td <;>
    simp_all [single,blocks,SoleEStress.blocks,btOwner,tdOwner,deOwner,ehOwner,
      ordinaryDE,ordinaryEH,isDE]

theorem single_parts {C : SignedCycle} (ab : Fin 4) (f : Family) (atG td : Bool) (t s : ℝ)
    (hflat : td=false → delta C.theta T=0) (i : Fin 4) (hi : single f td i=true) :
    (blocks C ab f atG td t s i).P=0 ∨ (blocks C ab f atG td t s i).N=0 := by
  have hv := single_data ab f atG td t s hflat i hi
  by_cases hu : 0≤(blocks C ab f atG td t s i).u
  · right
    simp [Block.N,hv,negativePart,max_eq_right (show -(blocks C ab f atG td t s i).u≤0 by linarith)]
  · left
    simp [Block.P,hv,positivePart,max_eq_right (le_of_lt (lt_of_not_ge hu))]

theorem angles_small {C : SignedCycle} (ab : Fin 4) (f : Family) (atG td : Bool) (t s : ℝ)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (i : Fin 4) :
    |(blocks C ab f atG td t s i).u|≤frameCap ∧ |(blocks C ab f atG td t s i).v|≤frameCap := by
  have hz : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hite (P : Prop) [Decidable P] (j : Vertex) :
      |(if P then delta C.theta j else 0)|≤frameCap := by
    split_ifs
    · exact ha j
    · exact hz
  have hite' (P : Prop) [Decidable P] (j : Vertex) :
      |(if P then 0 else delta C.theta j)|≤frameCap := by
    split_ifs
    · exact hz
    · exact ha j
  fin_cases i
  · exact ⟨ha H,hite _ _⟩
  · exact ⟨hite' _ _,hz⟩
  · exact ⟨hite _ _,hite _ _⟩
  · exact ⟨hite _ _,hite _ _⟩

theorem Vnu_min_max (R a b nu v : ℝ) :
    Vnu R (min a b) (max a b) nu v=Vnu R a b nu v := by
  rcases le_total a b with hab | hba
  · simp [min_eq_left hab,max_eq_right hab]
  · simp [min_eq_right hba,max_eq_left hba,Vnu,pairNorm_symm]

theorem old_A (f : Family) (atG : Bool) (R t v : ℝ) :
    oldV f atG R t v 1=Vnu R (ell f t 0) (k f t 0) (ell f t 0) v := by
  change Vnu R (min (k f t 0) (ell f t 0)) (max (k f t 0) (ell f t 0))
    (ell f t 0) v=_
  rw [Vnu_min_max]
  simp [Vnu,pairNorm_symm]

theorem old_B (f : Family) (atG : Bool) (R t v : ℝ) :
    oldV f atG R t v 2=Vnu R (ell f t 0) (c f t 0) (c f t 0) v := by
  simp only [oldV,small,large,SoleNegativeTCoefficients.first,SoleNegativeTCoefficients.second,
    face,SoleTScalarModel.first,SoleTScalarModel.second,m,Real.cos_zero,Real.sin_zero,mul_one,
    mul_zero,add_zero,↓reduceIte,SoleNegativeTCoefficients.nu,Matrix.cons_val]
  rw [Vnu_min_max]

theorem old_D (f : Family) (atG : Bool) (R t v : ℝ) :
    oldV f atG R t v 3=Vnu R (p (face f atG) t 0) (c f t 0)
      (max (p (face f atG) t 0) (c f t 0)) v := by
  simp only [oldV,small,large,SoleNegativeTCoefficients.first,SoleNegativeTCoefficients.second,
    face,SoleTScalarModel.first,SoleTScalarModel.second,m,Real.cos_zero,Real.sin_zero,mul_one,
    mul_zero,add_zero,↓reduceIte,SoleNegativeTCoefficients.nu,Matrix.cons_val]
  rw [Vnu_min_max]

theorem changed_B_negative {f : Family} (atG : Bool) {R t s v : ℝ}
    (hR : 0≤R) (ht : t∈domain f) (hs : s∈Icc 0 (9/100:ℝ)) (hv : v∈Icc 0 frameCap) :
    oldV f atG R t v 2≤Vnu R (ell f t 0) (c f t 0/Real.cos s) (ell f t 0) v := by
  have hb := changed_B_domain atG ht hs
  have hc := c_ge_ell atG ht
  have hcpos := (coefficient_positive ht (zero_mem ht)).2.2.1
  have hsec := SoleNegativeTSplit.secant_nonneg
    (show s∈Icc 0 frameCap from ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩)
  have hcg : c f t 0≤c f t 0/Real.cos s := by
    have hh := mul_nonneg hcpos.le hsec.2
    have he : c f t 0/Real.cos s=c f t 0*(1/Real.cos s) := by ring
    nlinarith
  have hgain := HalfRatioNormGain.larger_monotone hR hb.1 hc hcg hb.2.2 hv
  have hcos := mul_le_mul_of_nonpos_right hc (show Real.cos v-1≤0 by linarith [Real.cos_le_one v])
  rw [old_B]
  dsimp only [Vnu,SoleNormGain.normGain] at *
  linarith

theorem unchanged_coefficients (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool)
    (t s : ℝ) (i : Fin 4) (hD : i≠3) (hB : ¬(i=2 ∧ td=false)) :
    (blocks C ab f atG td t s i).p=small f atG t i ∧
      (blocks C ab f atG td t s i).q=large f atG t i := by
  fin_cases i <;> cases td <;>
    simp_all [blocks,SoleEStress.blocks,Block.p,Block.q,small,large,
      SoleNegativeTCoefficients.first,SoleNegativeTCoefficients.second,face,
      SoleTScalarModel.first,SoleTScalarModel.second,SoleNegativeTSplit.btWeight,
      SoleNegativeTSplit.tdWeight,m,min_comm,max_comm]

theorem unchanged_nu (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool)
    (t s : ℝ) (i : Fin 4) (hD : i≠3) (hB : ¬(i=2 ∧ td=false))
    (hi : single f td i=true) : (blocks C ab f atG td t s i).alpha=nu f atG t i := by
  fin_cases i <;> cases hf : isDE f <;> cases td <;>
    simp_all [single,blocks,SoleEStress.blocks,SoleNegativeTCoefficients.nu]

theorem D_minorant {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) {q t s : ℝ}
    (hQL : qLow≤q) (hQU : q≤qCap) (ht : t∈domain f) (hs : s∈shortDomain td)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hflat : td=false → delta C.theta T=0) :
    block f atG td (Real.sqrt q) t s (blocks C ab f atG td t s 3).P
      (blocks C ab f atG td t s 3).N 3≤contribution C ab f atG td q t s 3 := by
  have hv := single_data ab f atG td t s hflat 3 (by simp [single])
  have hu : (blocks C ab f atG td t s 3).u=ordinaryDE C (deOwner f) := rfl
  have hd := (ordinary_small (de:=deOwner f) (eh:=ehOwner f) ha).1
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hp := p_ge_one atG ht
  have hcoeff := coefficient_positive ht (zero_mem ht)
  have hcg := d_coefficient_ge td ht hs
  have hpc := p_half_c atG ht
  have hc3 : contribution C ab f atG td q t s 3=SoleNegativeTDSupport.increment q
      (p (face f atG) t 0) (dCoefficient f td t s) (ordinaryDE C (deOwner f)) := by
    simp [contribution]
  rw [hc3]
  by_cases hde : isDE f=true
  · have hd0 : ordinaryDE C (deOwner f)=0 := by simp [deOwner,ordinaryDE,hde]
    have hP : (blocks C ab f atG td t s 3).P=0 := by
      simp [Block.P,hv,hu,hd0,positivePart]
    have hN : (blocks C ab f atG td t s 3).N=0 := by
      simp [Block.N,hv,hu,hd0,negativePart]
    rw [hP,hN,hd0,block_right,positive_zero]
    simp [SoleNegativeTDSupport.increment]
  · have heh := Bool.eq_false_of_not_eq_true hde
    have hAb := EH_A_bounds heh ht
    by_cases hsign : 0≤ordinaryDE C (deOwner f)
    · have hd' : ordinaryDE C (deOwner f)∈Icc 0 frameCap :=
        ⟨hsign,by simpa [abs_of_nonneg hsign] using hd⟩
      have hP : (blocks C ab f atG td t s 3).P=ordinaryDE C (deOwner f) := by
        simp [Block.P,hv,hu,positivePart,max_eq_left hsign]
      have hN : (blocks C ab f atG td t s 3).N=0 := by
        simp [Block.N,hv,hu,negativePart,
          max_eq_right (show -ordinaryDE C (deOwner f)≤0 by linarith)]
      rw [hP,hN,block_right]
      simp only [SoleNegativeTOrdinaryData.positive,↓reduceIte,heh,Bool.false_eq_true]
      split_ifs with hdiag
      · exact SoleNegativeTDSupport.positive_diagonal_lower hQL hQU (by linarith) hdiag hd'
      · exact SoleNegativeTDSupport.positive_full_lower hq0 (by linarith)
          (lt_of_not_ge hdiag) (by linarith) hd'
    · have hsign' : ordinaryDE C (deOwner f)≤0 := (lt_of_not_ge hsign).le
      have hd' : -ordinaryDE C (deOwner f)∈Icc 0 frameCap :=
        ⟨by linarith,by simpa [abs_of_nonpos hsign'] using hd⟩
      have hP : (blocks C ab f atG td t s 3).P=0 := by
        simp [Block.P,hv,hu,positivePart,max_eq_right hsign']
      have hN : (blocks C ab f atG td t s 3).N= -ordinaryDE C (deOwner f) := by
        simp [Block.N,hv,hu,negativePart,
          max_eq_left (show 0≤-ordinaryDE C (deOwner f) by linarith)]
      have hh := SoleNegativeTDSupport.negative_min hQL hp hcoeff.2.2.1 hcg hpc
        hcoeff.1 hcoeff.2.1 hAb.1 hAb.2 hd'
      rw [hP,hN,block_left atG td (Real.sqrt q) ht]
      simp only [negative,↓reduceIte,heh,Bool.false_eq_true]
      rw [old_D,old_A]
      simpa only [neg_neg] using hh

theorem block_minorant {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) {q t s : ℝ}
    (hQL : qLow≤q) (hQU : q≤qCap) (ht : t∈domain f) (hs : s∈shortDomain td)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hflat : td=false → delta C.theta T=0)
    (hP : (∑i,(blocks C ab f atG td t s i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab f atG td t s i).N)=t-s+∑i,(blocks C ab f atG td t s i).P)
    (i : Fin 4) :
    block f atG td (Real.sqrt q) t s (blocks C ab f atG td t s i).P
      (blocks C ab f atG td t s i).N i≤contribution C ab f atG td q t s i := by
  by_cases hD : i=3
  · subst i
    exact D_minorant atG td hQL hQU ht hs ha hflat
  have hb := individual_budgets (angle ht).1 (short_small hs).1 hP hN i
  by_cases hB : i=2 ∧ td=false
  · rcases hB with ⟨rfl,rfl⟩
    have hs' : s∈Icc 0 (9/100:ℝ) := by simpa [shortDomain] using hs
    have hpair := changed_B_domain atG ht hs'
    have hv := single_data ab f atG false t s hflat 2 (by simp [single])
    have hraw := SoleOriginalBlocks.one_angle_minorant (blocks C ab f atG false t s 2)
      (Real.sqrt q) hv (angles_small ab f atG false t s ha 2).1
    have hneg := changed_B_negative atG (Real.sqrt_nonneg q) ht hs'
      (show (blocks C ab f atG false t s 2).N∈Icc 0 frameCap from
        ⟨(blocks C ab f atG false t s 2).N_nonneg,hb.2⟩)
    have hpairdata : (blocks C ab f atG false t s 2).p=ell f t 0 ∧
        (blocks C ab f atG false t s 2).q=c f t 0/Real.cos s ∧
        (blocks C ab f atG false t s 2).alpha=ell f t 0 := by
      simp [blocks,SoleEStress.blocks,Block.p,Block.q,SoleNegativeTSplit.btWeight,
        min_eq_left hpair.2.1,max_eq_right hpair.2.1]
    rw [hpairdata.1,hpairdata.2.1,hpairdata.2.2] at hraw
    simp only [F,↓reduceIte] at hraw
    have hc2 : contribution C ab f atG false q t s 2=
        (blocks C ab f atG false t s 2).increment (Real.sqrt q) := by
      simp [contribution]
    have hblock : block f atG false (Real.sqrt q) t s (blocks C ab f atG false t s 2).P
        (blocks C ab f atG false t s 2).N 2=
        U (Real.sqrt q) (ell f t 0) (c f t 0/Real.cos s) (blocks C ab f atG false t s 2).P+
          oldV f atG (Real.sqrt q) t (blocks C ab f atG false t s 2).N 2 := by
      simp [block,single,SoleNegativeTOrdinaryData.positive,negative]
    rw [hc2,hblock]
    linarith
  · obtain ⟨hp,hq⟩ := unchanged_coefficients C ab f atG td t s i hD hB
    have hci : contribution C ab f atG td q t s i=
        (blocks C ab f atG td t s i).increment (Real.sqrt q) := by
      simp [contribution,hD]
    rw [hci]
    cases hi : single f td i
    · have hh := (blocks C ab f atG td t s i).minorant (Real.sqrt q)
        (by rw [hp]; exact (SoleNegativeTCoefficients.positive atG ht i).2.2.le) hb.1 hb.2
      simpa only [block,hi,Bool.false_eq_true,↓reduceIte,hp,hq] using hh
    · have hv := single_data ab f atG td t s hflat i hi
      have hnu := unchanged_nu C ab f atG td t s i hD hB hi
      have hh := SoleOriginalBlocks.one_angle_minorant (blocks C ab f atG td t s i)
        (Real.sqrt q) hv (angles_small ab f atG td t s ha i).1
      have hpos : positive f atG td (Real.sqrt q) t s (blocks C ab f atG td t s i).P i=
          U (Real.sqrt q) (small f atG t i) (large f atG t i)
            (blocks C ab f atG td t s i).P := by
        simp [SoleNegativeTOrdinaryData.positive,hD,hB]
      have hnegv : negative f atG (Real.sqrt q) t (blocks C ab f atG td t s i).N i=
          oldV f atG (Real.sqrt q) t (blocks C ab f atG td t s i).N i := by
        simp [negative,hD]
      simp only [block,hi,↓reduceIte,hpos,hnegv]
      simpa only [F,↓reduceIte,hp,hq,hnu,oldV] using hh

theorem negative_original {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) {q t s L : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qCap)
    (ht : t∈domain f) (hs : s∈shortDomain td) (hst : s≤t)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hflat : td=false → delta C.theta T=0)
    (hvar : positiveVariation C.theta≤frameCap) (hG : 0≤delta C.theta G)
    (hE : 0≤ePrimary C f) (hsource : tPrimary C td= -s)
    (htotal : delta C.theta G+ePrimary C f=t)
    (hpure : ∀ i,Used f i → L≤oldV f atG (Real.sqrt q) t (t-s) i) :
    L≤ordinary C ab f atG td q t s := by
  obtain ⟨ht0,hP,hN⟩ := original_budgets hab f atG td hvar hG hE (short_small hs).1 hsource htotal
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hsquare := Real.sq_sqrt hq0
  have he := SoleNegativeTEnvelope.negative_balance atG td
    (fun i => (blocks C ab f atG td t s i).P) (fun i => (blocks C ab f atG td t s i).N)
    (Real.sqrt_nonneg q) (by simpa only [hsquare] using hQL)
    (by simpa only [hsquare] using hQU) ht hs hst
    (fun i => (blocks C ab f atG td t s i).P_nonneg)
    (fun i => (blocks C ab f atG td t s i).N_nonneg) hP hN
    (single_parts ab f atG td t s hflat) hpure
  exact he.trans (Finset.sum_le_sum fun i _ => block_minorant atG td hQL hQU ht hs ha hflat hP hN i)

theorem positive_original {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) {q t s : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qCap)
    (ht : t∈domain f) (hs : s∈shortDomain td) (hts : t≤ s)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hflat : td=false → delta C.theta T=0)
    (hvar : positiveVariation C.theta≤frameCap) (hG : 0≤delta C.theta G)
    (hE : 0≤ePrimary C f) (hsource : tPrimary C td= -s)
    (htotal : delta C.theta G+ePrimary C f=t) :
    -gamma f*(s-t)≤ordinary C ab f atG td q t s := by
  obtain ⟨ht0,hP,hN⟩ := original_budgets hab f atG td hvar hG hE (short_small hs).1 hsource htotal
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hsquare := Real.sq_sqrt hq0
  have he := SoleNegativeTEnvelope.positive_balance atG td
    (fun i => (blocks C ab f atG td t s i).P) (fun i => (blocks C ab f atG td t s i).N)
    (Real.sqrt_nonneg q) (by simpa only [hsquare] using hQL)
    (by simpa only [hsquare] using hQU) ht hs hts
    (fun i => (blocks C ab f atG td t s i).P_nonneg)
    (fun i => (blocks C ab f atG td t s i).N_nonneg) hP hN
    (single_parts ab f atG td t s hflat)
  exact he.trans (Finset.sum_le_sum fun i _ => block_minorant atG td hQL hQU ht hs ha hflat hP hN i)

end SquaresInCircles.Eight.TableFree.SoleNegativeTOriginalBlocks

module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD0SourceData
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3Scalar

/-!
# Actual four-block stress for core DE3, BT2 and arbitrary TD0

The secant-D minorant is taken at the actual negative DE3 angle.
B still owns BT2, including its independent signed error. The two
positive A arguments are only removed through their exact signed
primary total. No T support bound or nonexistent TD2 owner is used.
Uncompiled Sections 3–6 of the negative-DE3/TD0 hand proof, reusing
the whole-domain zero-tilt scalar certificate of the BT3 companion.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDETD0
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

abbrev Family := NegativeDEPositiveBT.Family

lemma source_pair_coefficients {C : SignedCycle} {hg : Fin 4}
    (ga ab : Bool) {k l m : ℝ} (hk : k≤1) (hl : k≤l)
    (i : Fin 3) :
    (blocks C hg ga ab k l m i.castSucc).p=
      (![k,k,min l m] : Fin 3→ℝ) i ∧
    (blocks C hg ga ab k l m i.castSucc).q=
      (![1,l,max l m] : Fin 3→ℝ) i :=
  block_coefficients ga ab hk hl i

/-- The same scalar baseline at BT3 zero tilt, without selecting BT3. -/
theorem baseline_identity {C : SignedCycle} {a s : ℝ}
    (hs : s=magnitude C) (hsm : s∈Icc 0 frameCap)
    (k l m : ℝ) :
    base C k l m+l*TwoPositive.ASupport.charge a =
      k+2*l+2*m+(1/Real.cos s)+1-fullSupport 1 k-
        fullSupport k l-fullSupport l m-
        PositiveBT3.sortedSupport (1/Real.cos s) m+
        (13/12)*Real.tan s-((1/Real.cos s)-1)/2+
        l*TwoPositive.ASupport.charge a := by
  subst hs
  have hid := NegativeDEPositiveTD.Source.deCorrection_identity hsm
  have he : Real.cos (delta C.theta D)=Real.cos (magnitude C) := by
    simp [magnitude,NegativeDEPositiveBT.Source.magnitude,NegativeDEPositiveTD.Source.magnitude]
  simp only [base,deCorrection,NegativeDEPositiveBT.Source.deCorrection]
  rw [hid,he]
  simp only [NegativeDEPositiveTD.Explicit.K,NegativeDEPositiveTD.Explicit.secant,
    magnitude,NegativeDEPositiveBT.Source.magnitude]
  ring

lemma high_scalar_baseline {C : SignedCycle} (ga ab : Bool)
    (hs : magnitude C∈Icc 0 frameCap) :
    base C (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab))+
      NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab)*
        TwoPositive.ASupport.charge (aTotal C ga ab)=
    NegativeDEPositiveBT.Explicit.baseline .high (aTotal C ga ab) 0 (magnitude C) := by
  rw [baseline_identity (a:=aTotal C ga ab) (s:=magnitude C) rfl hs]
  simp only [NegativeDEPositiveBT.Explicit.baseline,NegativeDEPositiveBT.Explicit.c,
    NegativeDEPositiveBT.Explicit.sec,NegativeELargeA.secant,NegativeDEPositiveBT.Explicit.K,
    Real.cos_zero,Real.sin_zero,mul_zero,add_zero,mul_one,sub_zero,edgeWidth_zero]
  ring

/-- Three ordinary blocks are protected by circle support; the fourth
retains the actual secant-D inequality across its sorted support switch. -/
theorem high_blocks_lower {Q : ℝ} {C : SignedCycle}
    (hg : Fin 4) (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hs : delta C.theta D≤0)
    (hθ : aTotal C ga ab∈Icc (1/6:ℝ) frameCap)
    (i : Fin 4) :
    NegativeDEPositiveBT.Blocks.block .high (aTotal C ga ab) 0 (magnitude C)
      (blocks C hg ga ab
        (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
        (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
        (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) i).P
      (blocks C hg ga ab
        (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
        (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
        (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) i).N i≤
    actualBlocks C hg ga ab
      (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) i := by
  have hz : (0:ℝ)∈Icc 0 (aTotal C ga ab) := ⟨le_rfl,ha⟩
  obtain ⟨hk,hkl,hl,hm,hc,hkc⟩ :=
    NegativeDEPositiveBT.Explicit.source_coefficients .high hθ hz
  have hb := budgets hg ga ab (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) hvar ha hs
  have hordinary (j : Fin 3) {P : SignedPoint}
      (hy : 0≤P.y) (hP : P.Contained Q) :
      NegativeDEPositiveBT.Blocks.block .high (aTotal C ga ab) 0 (magnitude C)
        (blocks C hg ga ab
          (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) j.castSucc).P
        (blocks C hg ga ab
          (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) j.castSucc).N j.castSucc≤
      PositiveTD.actualPairIncrement (blocks C hg ga ab
          (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) j.castSucc) P := by
    have hpair := source_pair_coefficients (C:=C) (hg:=hg) ga ab
      (m:=NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) (by linarith [hk.2]) hkl j
    have hp' : NegativeDEPositiveBT.Explicit.p .high (aTotal C ga ab) j=
        (blocks C hg ga ab
          (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) j.castSucc).p :=
      hpair.1.symm
    have hq' : NegativeDEPositiveBT.Explicit.q .high (aTotal C ga ab) j=
        (blocks C hg ga ab
          (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) j.castSucc).q :=
      hpair.2.symm
    have hpn := (NegativeDEPositiveBT.Explicit.family_pairs .high hθ j).1.le
    rw [hp'] at hpn
    rw [NegativeDEPositiveBT.Blocks.block_ordinary,hp',hq']
    exact PositiveTD.actual_block_minorant hy hP hQ hpn
      (block_budgets hg ga ab _ _ _ hvar ha hs j.castSucc).1
      (block_budgets hg ga ab _ _ _ hvar ha hs j.castSucc).2
  fin_cases i
  · exact hordinary 0 hHy (hcontained H)
  · exact hordinary 1
      (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hcontained G)
  · exact hordinary 2
      (P:=(C.point B).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hcontained B)
  · have hn : negativeVariation C.theta≤frameCap := by
      rw [←variations_equal]; exact hvar
    have ht : |delta C.theta T|≤frameCap := original_error_bound hvar hn T
    have hD := NegativeDEPositiveBT.Source.actual_D_minorant
      (hsorted D) hDy (hcontained D) hQ hk hc hkc hb.de_domain ht
    have hc0 : NegativeDEPositiveBT.Explicit.c .high (aTotal C ga ab) 0=
        NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab) := by
      simp [NegativeDEPositiveBT.Explicit.c]
    have hsec : NegativeDEPositiveBT.Explicit.sec (magnitude C)=
        1/Real.cos (delta C.theta D) := by
      simp [NegativeELargeA.secant,magnitude,NegativeDEPositiveBT.Source.magnitude,
        NegativeDEPositiveTD.Source.magnitude]
    have hV : NegativeDEPositiveBT.Explicit.V .high (aTotal C ga ab) 0
        (negativePart (delta C.theta T))=
        V R (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab)) 1
          (negativePart (delta C.theta T)) := rfl
    change NegativeDEPositiveBT.Blocks.block .high (aTotal C ga ab) 0 (magnitude C)
        (positivePart (delta C.theta T)+positivePart 0)
        (negativePart (delta C.theta T)+negativePart 0) 3≤
      SecantD.actualIncrement (1/Real.cos (delta C.theta D))
        (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) (delta C.theta T) (C.point D)
    rw [NegativeDEPositiveBT.Blocks.block_D,NegativeDEPositiveBT.Blocks.positive_D,
      NegativeDEPositiveBT.Blocks.negative_D,positivePart_zero,negativePart_zero,add_zero,
      add_zero,hV,NegativeDEPositiveBT.Explicit.gamma,hc0,hsec]
    rw [hc0,hsec] at hD
    linarith

theorem stress_nonpositive {C : SignedCycle} (hg : Fin 4)
    (ga ab : Bool) {k l m : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hm : 0≤ m)
    (hs : magnitude C∈Icc 0 frameCap)
    (hf : ∀i,C.Feasible i (owners hg ga ab i)) :
    stress C hg ga ab k l m≤0 := by
  have hcos : 0<Real.cos (delta C.theta D) := by
    simpa [magnitude,NegativeDEPositiveTD.Source.magnitude] using
      (show 0<Real.cos (magnitude C) by linarith [(transport_trig hs).1])
  have hw (i : Vertex) : 0≤weights C k l m i := by
    fin_cases i <;> simp [weights] <;> positivity
  apply Finset.sum_nonpos
  intro i _
  have hi : edgeWidth (delta C.theta i)≤C.edge i (owners hg ga ab i) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,sub_nonneg] using hf i
  exact mul_nonpos_of_nonneg_of_nonpos (hw i) (sub_nonpos.mpr hi)

/-- Original signed BT2/TD0 force yields the scalar nonpositive bound. -/
theorem high_scalar_nonpositive {Q : ℝ} {C : SignedCycle}
    (hg : Fin 4) (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : aTotal C ga ab∈Icc (1/6:ℝ) frameCap)
    (hs : delta C.theta D≤0) (hflat : (C.point E).a=7/12)
    (hhg : hg=0∨hg=2)
    (hf : ∀i,C.Feasible i (owners hg ga ab i)) :
    NegativeDEPositiveBT.Explicit.baseline .high (aTotal C ga ab) 0 (magnitude C)+
      ∑i,NegativeDEPositiveBT.Blocks.block .high (aTotal C ga ab) 0 (magnitude C)
        (blocks C hg ga ab
          (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) i).P
        (blocks C hg ga ab
          (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) i).N i≤0 := by
  have ha0 : 0≤aTotal C ga ab := by linarith [ha.1]
  have hbud := budgets hg ga ab (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) hvar ha0 hs
  have hcos : Real.cos (delta C.theta D)≠0 := by
    have he := (transport_trig hbud.de_domain).1
    have hpos : 0<Real.cos (magnitude C) := by linarith [he]
    simpa [magnitude,NegativeDEPositiveBT.Source.magnitude,
      NegativeDEPositiveTD.Source.magnitude] using hpos.ne'
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    high_blocks_lower hg ga ab hsorted hcontained hQ
      hHy hGy hBy hDy hvar ha0 hs ha i)
  have hn : negativeVariation C.theta≤frameCap := by
    rw [←variations_equal]; exact hvar
  have hA : TwoPositive.ASupport.charge (aTotal C ga ab)≤
      PairedE.primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A) :=
    PairedE.selected_charge ga ab (hsorted A) (hcontained A) hQ
      (original_error_bound hvar hn G) (original_error_bound hvar hn A) hbud.a_domain
  have hcoef := NegativeDEPositiveBT.Explicit.source_coefficients .high ha
    (show (0:ℝ)∈Icc 0 (aTotal C ga ab) from ⟨le_rfl,ha0⟩)
  have hAl := mul_le_mul_of_nonneg_left hA hcoef.2.2.1.le
  have hi := high_scalar_baseline ga ab hbud.de_domain
  have hd := decomposition C ga ab hhg
    (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) hflat hcos
  have hst := stress_nonpositive hg ga ab
    (k:=NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
    (l:=NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
    (m:=NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab))
    (by linarith [hcoef.1.1]) hcoef.2.2.1.le hcoef.2.2.2.1.le hbud.de_domain hf
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDETD0

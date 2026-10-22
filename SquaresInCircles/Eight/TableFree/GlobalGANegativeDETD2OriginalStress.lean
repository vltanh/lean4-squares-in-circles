module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2SourceData
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3DEnvelopeGeometry

/-!
# The negative-DE / positive-TD2 scalar inequality at the original cycle

Uncompiled transcription of Sections 1--3 of the angle-concentration
companion. The selected A arguments may have opposite signs. Their
signed total is used only after the actual primary gains have been
bounded. The DE secant stays in the original D support, and every
ordinary block retains its original positive and negative masses.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks PairedE SignedStress PositiveBT3

/-- The width identity at the actual negative DE error, including zero. -/
theorem deCorrection_identity {C : SignedCycle}
    (hs : magnitude C∈Icc 0 frameCap) :
    deCorrection C=Explicit.K*Real.tan (magnitude C)-
      (Explicit.secant (magnitude C)-1)/2 := by
  have hcos : Real.cos (magnitude C)≠0 :=
    (show 0<Real.cos (magnitude C) by linarith [(transport_trig hs).1]).ne'
  have hd : delta C.theta D= -magnitude C := by simp [magnitude]
  rw [deCorrection,hd,edgeWidth_negative_formula hs,Real.sin_neg,Real.cos_neg]
  dsimp [Explicit.K,Explicit.secant]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos]
  ring

/-- This is an identity, not a change of the actual A/TD split. -/
theorem baseline_identity {C : SignedCycle} (ga ab : Bool) (f : Family)
    (hs : magnitude C∈Icc 0 frameCap) :
    base C (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
        (Explicit.c f (total C ga ab))+
      Explicit.l f (total C ga ab)*TwoPositive.ASupport.charge (aTotal C ga ab)=
      Explicit.baseline f (aTotal C ga ab) (delta C.theta T) (magnitude C) := by
  have hd : Real.cos (delta C.theta D)=Real.cos (magnitude C) := by
    simp [magnitude]
  rw [base,deCorrection_identity hs,hd]
  dsimp [Explicit.baseline,total,Explicit.m,Explicit.eta,Explicit.sigma,
    Explicit.secant,PositiveTD.tilted,PositiveTD.eta,PositiveTD.sigma]
  ring

/-- The full-circle high baseline is a lower bound for the actual sorted D baseline. -/
theorem fullBaseline_le (f : Family) (a z s : ℝ) :
    Explicit.fullBaseline f a z s≤Explicit.baseline f a z s := by
  have hclip : clippedSupport (Explicit.secant s) (Explicit.c f (a+z))≤
      fullSupport (Explicit.secant s) (Explicit.c f (a+z)) := by
    by_cases h : Explicit.secant s≤Explicit.c f (a+z)
    · rw [clippedSupport,if_pos h]
      have hh := raw_full_support (a:=diagonal) (b:=diagonal)
        (f:=Explicit.secant s) (g:=Explicit.c f (a+z))
        (show (diagonal+1/2)^2+(diagonal+1/2)^2≤qCap by nlinarith [diagonal_circle])
      simpa [diagonalSupport,add_mul] using hh
    · simp [clippedSupport,h]
  dsimp [Explicit.fullBaseline]
  linarith

theorem dReserve_nonnegative {Q c : ℝ} {C : SignedCycle}
    (hsorted : (C.point D).Sorted) (hy : (C.point D).y≤0)
    (hcontained : (C.point D).Contained Q) (hQ : Q≤qCap)
    (hc : 0≤c) (hs : magnitude C∈Icc 0 frameCap) : 0≤dReserve C c := by
  have hcos : 0<Real.cos (delta C.theta D) := by
    simpa [magnitude] using (show 0<Real.cos (magnitude C) by
      linarith [(transport_trig hs).1])
  have hcircle : ((C.point D).a+1/2)^2+(-(C.point D).y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hy]
      using hcontained.trans hQ
  have horder : -(C.point D).y≤(C.point D).a := by
    simpa [abs_of_nonpos hy] using hsorted.2
  have hh := raw_clipped_support (f:=1/Real.cos (delta C.theta D)) (g:=c)
    hcircle horder (by linarith [hsorted.1])
    (add_nonneg (div_nonneg (by norm_num) hcos.le) hc)
  dsimp [dReserve]
  have he : (C.point D).a/Real.cos (delta C.theta D)=
      (1/Real.cos (delta C.theta D))*(C.point D).a := by ring
  rw [he]
  linarith

theorem tReserve_nonnegative {Q c : ℝ} {C : SignedCycle}
    (hsorted : (C.point T).Sorted) (hcontained : (C.point T).Contained Q)
    (hQ : Q≤qCap) (hc : 0≤c) (hz : delta C.theta T∈Icc 0 frameCap) :
    0≤PositiveTD.tReserve C c := by
  have hcircle : (C.point T).Contained (R^2) := by
    rw [radius_sq]
    exact hcontained.trans hQ
  have hsupp := work_le_circleSupport (Real.sqrt_nonneg qCap) hsorted hcircle
    (1,PositiveTD.eta)
  have heta : 0≤PositiveTD.eta := by norm_num [PositiveTD.eta]
  have hbound : (C.point T).a+PositiveTD.eta*(C.point T).y≤PositiveTD.sigma := by
    simpa [work,circleSupport,PositiveTD.sigma,fullSupport,abs_of_nonneg heta] using hsupp
  have hsin := (transport_trig hz).2.2.1
  dsimp [PositiveTD.tReserve]
  exact mul_nonneg (mul_nonneg hc hsin) (sub_nonneg.mpr hbound)

theorem actual_blocks_lower {Q : ℝ} {C : SignedCycle}
    (hg ga ab : Bool) (f : Family)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0)
    (hθ : total C ga ab∈Icc (Explicit.left f) (Explicit.right f)) (i : Fin 3) :
    mixedBlock R (Explicit.p f (total C ga ab) (delta C.theta T) i)
      (Explicit.q f (total C ga ab) (delta C.theta T) i)
      (blocks C hg ga ab (Explicit.k f (total C ga ab))
        (Explicit.l f (total C ga ab)) (Explicit.c f (total C ga ab)) i).P
      (blocks C hg ga ab (Explicit.k f (total C ga ab))
        (Explicit.l f (total C ga ab)) (Explicit.c f (total C ga ab)) i).N≤
      actualBlocks C hg ga ab (Explicit.k f (total C ga ab))
        (Explicit.l f (total C ga ab)) (Explicit.c f (total C ga ab)) i := by
  let k := Explicit.k f (total C ga ab)
  let l := Explicit.l f (total C ga ab)
  let c := Explicit.c f (total C ga ab)
  have hb := budgets hg ga ab k l c hvar ha hz hs
  have hp := family_coefficients f hθ hb.td_domain
  have hcoef := family_block_coefficients hg ga ab f hθ hb.td_domain i
  have hP := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l c j).P_nonneg) (Finset.mem_univ i)
  have hN := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l c j).N_nonneg) (Finset.mem_univ i)
  have hPb : (blocks C hg ga ab k l c i).P≤frameCap := by
    linarith [hb.positive_bound,hb.total_domain.1]
  have hNb : (blocks C hg ga ab k l c i).N≤frameCap := by
    linarith [hb.negative_bound,hb.de_domain.1]
  have hsmall : 0≤(blocks C hg ga ab k l c i).p := by
    rw [hcoef.1]
    exact (hp.2.2 i).1.le
  have hminor {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained Q) :=
    PositiveTD.actual_block_minorant hy hP hQ hsmall hPb hNb
  rw [←hcoef.1,←hcoef.2]
  fin_cases i
  · simpa [actualBlocks,k,l,c] using hminor hHy (hcontained H)
  · simpa [actualBlocks,k,l,c] using hminor (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hcontained G)
  · simpa [actualBlocks,k,l,c] using hminor (P:=(C.point B).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hcontained B)

theorem stress_nonpositive {C : SignedCycle} (hg ga ab : Bool) {k l c : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c)
    (hz : delta C.theta T∈Icc 0 frameCap) (hs : magnitude C∈Icc 0 frameCap)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : stress C hg ga ab k l c≤0 := by
  have hm := PositiveTD.tilted_pos hc hz
  have hcos : 0<Real.cos (delta C.theta D) := by
    simpa [magnitude] using (show 0<Real.cos (magnitude C) by
      linarith [(transport_trig hs).1])
  have hw (i : Vertex) : 0≤weights C k l c i := by
    fin_cases i <;> simp only [weights,Matrix.cons_val_succ,Matrix.cons_val_zero] <;> positivity
  apply Finset.sum_nonpos
  intro i _
  have hi : edgeWidth (delta C.theta i)≤C.edge i (owners hg ga ab i) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,sub_nonneg] using hfeasible i
  exact mul_nonpos_of_nonneg_of_nonpos (hw i) (sub_nonpos.mpr hi)

/-- The complete scalar necessary inequality, with no substituted angles
or new feasibility assumptions. Its remaining task is scalar positivity. -/
theorem scalar_nonpositive {Q : ℝ} {C : SignedCycle}
    (hg ga ab : Bool) (f : Family)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12)
    (hθ : total C ga ab∈Icc (Explicit.left f) (Explicit.right f))
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) :
    Explicit.baseline f (aTotal C ga ab) (delta C.theta T) (magnitude C)+
      ∑i,mixedBlock R (Explicit.p f (total C ga ab) (delta C.theta T) i)
        (Explicit.q f (total C ga ab) (delta C.theta T) i)
        (blocks C hg ga ab (Explicit.k f (total C ga ab))
          (Explicit.l f (total C ga ab)) (Explicit.c f (total C ga ab)) i).P
        (blocks C hg ga ab (Explicit.k f (total C ga ab))
          (Explicit.l f (total C ga ab)) (Explicit.c f (total C ga ab)) i).N≤0 := by
  let k := Explicit.k f (total C ga ab)
  let l := Explicit.l f (total C ga ab)
  let c := Explicit.c f (total C ga ab)
  have hb := budgets hg ga ab k l c hvar ha hz hs
  have hp := Explicit.family_positive f hθ hb.td_domain
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hA := PairedE.selected_charge ga ab (hsorted A) (hcontained A) hQ
    (original_error_bound hvar hn G) (original_error_bound hvar hn A)
    (show aTotal C ga ab∈Icc 0 frameCap from
      ⟨ha,hb.a_domain.2.trans hb.total_domain.2⟩)
  change TwoPositive.ASupport.charge (aTotal C ga ab)≤
    primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A) at hA
  have hAg := mul_le_mul_of_nonneg_left hA hp.2.1.le
  have hzframe : delta C.theta T∈Icc 0 frameCap :=
    ⟨hz,hb.td_domain.2.trans hb.total_domain.2⟩
  have hT := tReserve_nonnegative (hsorted T) (hcontained T) hQ hp.2.2.1.le hzframe
  have hD := dReserve_nonnegative (hsorted D) hDy (hcontained D) hQ hp.2.2.1.le hb.de_domain
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    actual_blocks_lower hg ga ab f hsorted hcontained hQ hHy hGy hBy hvar ha hz hs hθ i)
  have hcos : Real.cos (delta C.theta D)≠0 := by
    have hh := (transport_trig hb.de_domain).1
    simpa [magnitude] using (show Real.cos (magnitude C)≠0 by linarith)
  have hidentity := decomposition C hg ga ab k l c hflat hcos
  have hbase := baseline_identity (C:=C) ga ab f hb.de_domain
  have hupper := stress_nonpositive hg ga ab hp.1.le hp.2.1.le hp.2.2.1
    hzframe hb.de_domain hfeasible
  change Explicit.baseline f (aTotal C ga ab) (delta C.theta T) (magnitude C)+_≤0
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Source

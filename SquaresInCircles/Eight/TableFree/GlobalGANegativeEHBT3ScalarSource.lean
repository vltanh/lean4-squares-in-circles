module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3SourceCoefficients

/-!
# Original-source transfer for all four genuine EH1 / positive BT3 families

Uncompiled source join. The scalar coefficients and the original signed
mass budgets refer to the identical, unchanged cycle. In the small-low
family D keeps its sorted two-sign support. In all other families the
four actual ordinary blocks, including original TD0 and DE2, are retained.
This imports the independently committed original-source files rather
than replacing their Fin-4 HG owner interface.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

def familyRegime (f : Family) : Regime := if far f then .far else .small

private theorem full_scalar_identity (f : Family) (hf : f≠.smallLow)
    (θ a z s : ℝ) (P N : Fin 4→ℝ) :
    baseline f θ a z+charge f s+
      (∑i,Scalar.block f θ z (P i) (N i) i)=
    PositiveBT3.Analytic.fullBaseline (Explicit.k f θ) (Explicit.l f θ)
      (Explicit.m f θ) z+
    Explicit.l f θ*TwoPositive.ASupport.charge a+
    ehLower (familyRegime f) s+
      (∑i,fullBlock (familyRegime f) (Explicit.k f θ) (Explicit.l f θ)
        (Explicit.m f θ) z i (P i) (N i)) := by
  cases f with
  | smallLow => exact (hf rfl).elim
  | smallHigh =>
      simp [familyRegime,baseline,charge,Scalar.block,Blocks.block,
        ChargedOrdinaryConcentration.block,fullBlock,epsilon,far,errorCharge,
        NegativeEHPositiveTD.Explicit.errorCharge,
        NegativeEHPositiveTD.Explicit.gain,SmallLow.gain_eq]
  | farLow =>
      simp [familyRegime,baseline,charge,Scalar.block,Blocks.block,
        ChargedOrdinaryConcentration.block,fullBlock,epsilon,far,errorCharge,
        NegativeEHPositiveTD.Explicit.errorCharge,NegativeEH.epsilon,
        NegativeEHPositiveTD.Explicit.gain,NegativeEH.G,SmallLow.gain_eq]
  | farHigh =>
      simp [familyRegime,baseline,charge,Scalar.block,Blocks.block,
        ChargedOrdinaryConcentration.block,fullBlock,epsilon,far,errorCharge,
        NegativeEHPositiveTD.Explicit.errorCharge,NegativeEH.epsilon,
        NegativeEHPositiveTD.Explicit.gain,NegativeEH.G,SmallLow.gain_eq]

/-- The exact scalar is nonpositive at the *original* selected weak edges.
Neither the G/T endpoint normalization nor an inequality on a transported
packing appears here. The two genuine signed caps are passed unchanged. -/
theorem scalar_nonpositive {Q : ℝ} {C : SignedCycle} (f : Family) {hg : Fin 4}
    (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B)
    (hs : delta C.theta E≤0)
    (hflat : (C.point E).a=7/12) (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (hθ : total C ga ab∈Icc (Scalar.left f) (Scalar.right f))
    (he : magnitude C∈Icc (Scalar.eLeft f) (Scalar.eRight f))
    (hhg : hg=0∨hg=2)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) :
    baseline f (total C ga ab) (aTotal C ga ab) (delta C.theta B)+
      charge f (magnitude C)+
      (∑i,Scalar.block f (total C ga ab) (delta C.theta B)
        (blocks C hg ga ab (Explicit.k f (total C ga ab))
          (Explicit.l f (total C ga ab)) (Explicit.m f (total C ga ab)) i).P
        (blocks C hg ga ab (Explicit.k f (total C ga ab))
          (Explicit.l f (total C ga ab)) (Explicit.m f (total C ga ab)) i).N i)≤0 := by
  let θ := total C ga ab
  let k := Explicit.k f θ
  let l := Explicit.l f θ
  let m := Explicit.m f θ
  have hbud := budgets hg ga ab k l m hvar ha hz hs
  by_cases hlow : f=.smallLow
  · subst f
    have hactual := low_scalar_nonpositive (hg:=hg) ga ab hsorted hcontained hQ
      hHy hGy hBy hDy hvar ha hz hs hθ hflat hb he hhg hfeasible
    simpa [θ,k,l,m,baseline,Scalar.block,SmallLow.block,lowBlock,
      SmallLow.dCost,PositiveBT3.slope,charge,far,SmallLow.gain_eq,
      Explicit.k,Explicit.l,Explicit.m] using hactual
  · have hc := coefficients f hθ hbud.bt_domain
    have he' : magnitude C∈Icc
        (NegativeEHPositiveTD.Explicit.eLeft (familyRegime f))
        (NegativeEHPositiveTD.Explicit.eRight (familyRegime f)) := by
      cases f <;> simp_all [familyRegime,Scalar.eLeft,Scalar.eRight,far,
        NegativeEHPositiveTD.Explicit.eLeft,NegativeEHPositiveTD.Explicit.eRight]
    have hkfar : familyRegime f=.far→k∈Icc (3/5:ℝ) (4/5) := by
      intro hh
      have hf : far f=true := by
        cases f <;> simp_all [familyRegime,far]
      exact far_k f hθ hf
    have hactual := full_scalar_nonpositive (k:=k) (l:=l) (m:=m)
      (hg:=hg) (familyRegime f) ga ab hsorted hcontained hQ
      hHy hGy hBy hDy hvar ha hz hs hc.1 hc.2.2.2 hc.2.2.1
      hkfar hflat hb he' hhg hfeasible
    have hid := full_scalar_identity f hlow θ (aTotal C ga ab)
      (delta C.theta B) (magnitude C)
      (fun i => (blocks C hg ga ab k l m i).P)
      (fun i => (blocks C hg ga ab k l m i).N)
    change _≤0 at hactual
    rw [hid]
    exact hactual

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source

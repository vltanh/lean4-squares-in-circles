module

public import SquaresInCircles.Eight.TableFree.PositiveOrdinaryEnvelope
public import SquaresInCircles.Eight.TableFree.PositiveScalarTransfer
public import SquaresInCircles.Eight.TableFree.PositiveSplitConcavity

/-!
# Actual positive-GA exclusion with both E separators secondary

Uncompiled source draft. These theorems connect the original weak SAT
contacts, exact seven-angle budgets, whole-angle ordinary envelope,
positive-primary split, and the proved strict scalar inequalities.

All three nonnegative-T regimes are covered, with both actual AB owners.
The E point has no sign or radial assumption. The selected physical
contacts are used exactly as supplied, and the original radius is only
bounded above by the analytic cap.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PositiveSecondaryEExclusion
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity
open SecondaryEStress PositivePrimaryBaselines PositiveStressCoefficients
open PositiveOrdinaryParameters PositiveOrdinaryEnvelope ActualOrdinaryBlocks

theorem scalar_V_eq (l d : ℝ) :
    PositiveScalarTransfer.V l d=V (Real.sqrt qCap) l k d := by
  simp [PositiveScalarTransfer.V,PositiveScalarData.K,k,V,pairNorm,Real.sin_neg]
  ring_nf

/-- Secondary BT2/TD0 leaves both original T angles in the ordinary
budget. No hypothesis is made on either angle's sign. -/
theorem secondary_T_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hf : ∀ i,C.Feasible i (owners ab 2 0 i)) : False := by
  let d : ℝ := delta C.theta G
  have hbud := block_budgets hab (Or.inl rfl) (Or.inl rfl) 0 0 0 0 0
    hvar hG (by intro h; norm_num at h) (by intro h; norm_num at h)
  have hd : d∈Icc 0 frameCap := by simpa [removed,d] using hbud.1
  have hp := familyN hd
  have hinc := increment_lower hab (Or.inl rfl) (Or.inl rfl) hvar hG
    (by intro h; norm_num at h) (by intro h; norm_num at h)
    (by simpa [removed,d] using hp)
  have hinc' : V (Real.sqrt qCap) (lN d) k d≤
      secondaryIncrement C ab (Real.sqrt qCap) k (lN d) (cN d) (19/50) := by
    rw [secondary_increment_eq C hab]
    simpa [removed,d] using hinc
  have hcoeff := coefficient_bounds hd
  have hnec := secondary_necessary (k := k) (l := lN d) (c := cN d) (η := 19/50)
    hq hC hnormal hab
    (by norm_num [k]) (by linarith [hcoeff.2.2.1])
    (by norm_num [k] at hcoeff; linarith [hcoeff.2.2.2.2.1])
    (by norm_num : (0:ℝ)≤19/50) hG hf
  have hstrict := (PositiveScalarTransfer.seven_scalar_bounds hd).2.2.2.1
  rw [scalar_V_eq] at hstrict
  have hbase : PositiveScalarTransfer.BN d=
      secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d := by
    rfl
  rw [hbase] at hstrict
  dsimp [d] at hinc' hstrict
  linarith

/-- Positive TD2 uses its actual nonnegative angle as the second primary
angle; the original BT2 angle remains in the B block. -/
theorem positive_TD_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hT : 0≤delta C.theta T)
    (hf : ∀ i,C.Feasible i (owners ab 2 2 i)) : False := by
  let x : ℝ := delta C.theta G
  let z : ℝ := delta C.theta T
  let d : ℝ := x+z
  have hbud := block_budgets hab (Or.inl rfl) (Or.inr rfl) 0 0 0 0 0
    hvar hG (by intro h; norm_num at h) (by intro _; exact hT)
  have hd : d∈Icc 0 frameCap := by simpa [removed,d,x,z] using hbud.1
  have hx : x∈Icc 0 d := ⟨hG,by dsimp [d,x,z]; linarith⟩
  have hz : z∈Icc 0 d := ⟨hT,by dsimp [d,x,z]; linarith⟩
  have hp := familyP_td hd hx hz
  have hinc := increment_lower hab (Or.inl rfl) (Or.inr rfl) hvar hG
    (by intro h; norm_num at h) (by intro _; exact hT)
    (by simpa [removed,d,x,z] using hp)
  have hinc' : V (Real.sqrt qCap) (lP d) k d≤
      tdIncrement C ab (Real.sqrt qCap) k (lP d) (etaP d) := by
    rw [td_increment_eq C hab]
    simpa [removed,d,x,z] using hinc
  have hcoeff := coefficient_bounds hd
  have hnec := td_necessary (k := k) (l := lP d) (η := etaP d)
    hq hC hnormal hab (by norm_num [k])
    (by linarith [hcoeff.1]) (by linarith [hcoeff.2.2.2.2.2.2.1]) hG hT hf
  have hbase := PositiveSplitConcavity.tdBaseline_ge_familyP hd hG hT
    (show delta C.theta G+delta C.theta T=d by rfl)
  have hstrict := (PositiveScalarTransfer.seven_scalar_bounds hd).1
  rw [scalar_V_eq] at hstrict
  linarith

/-- Positive BT3 is the other physical T primary. Its actual TD0 angle
remains in the D block; AB0 and AB2 are both retained. -/
theorem positive_BT_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hB : 0≤delta C.theta B)
    (hf : ∀ i,C.Feasible i (owners ab 3 0 i)) : False := by
  let x : ℝ := delta C.theta G
  let z : ℝ := delta C.theta B
  let d : ℝ := x+z
  have hbud := block_budgets hab (Or.inr rfl) (Or.inl rfl) 0 0 0 0 0
    hvar hG (by intro _; exact hB) (by intro h; norm_num at h)
  have hd : d∈Icc 0 frameCap := by simpa [removed,d,x,z] using hbud.1
  have hx : x∈Icc 0 d := ⟨hG,by dsimp [d,x,z]; linarith⟩
  have hz : z∈Icc 0 d := ⟨hB,by dsimp [d,x,z]; linarith⟩
  have hp := familyP_bt hd hx hz
  have hinc := increment_lower hab (Or.inr rfl) (Or.inl rfl) hvar hG
    (by intro _; exact hB) (by intro h; norm_num at h)
    (by simpa [removed,d,x,z] using hp)
  have hinc' : V (Real.sqrt qCap) (lP d) k d≤
      btIncrement C ab (Real.sqrt qCap) k (lP d) (etaP d) := by
    rw [bt_increment_eq C hab]
    simpa [removed,d,x,z] using hinc
  have hcoeff := coefficient_bounds hd
  have hnec := bt_necessary (k := k) (l := lP d) (η := etaP d)
    hq hC hnormal hab (by norm_num [k])
    (by linarith [hcoeff.1]) (by linarith [hcoeff.2.2.2.2.2.2.1]) hG hB hf
  have hbase := PositiveSplitConcavity.btBaseline_ge_familyP hd hG hB
    (show delta C.theta G+delta C.theta B=d by rfl)
  have hstrict := (PositiveScalarTransfer.seven_scalar_bounds hd).1
  rw [scalar_V_eq] at hstrict
  linarith

theorem nonnegative_T_false {C : SignedCycle} {q : ℝ} {ab bt td : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hT : (bt=2 ∧ td=0) ∨ (bt=2 ∧ td=2 ∧ 0≤delta C.theta T) ∨
      (bt=3 ∧ td=0 ∧ 0≤delta C.theta B))
    (hf : ∀ i,C.Feasible i (owners ab bt td i)) : False := by
  rcases hT with ⟨rfl,rfl⟩ | ⟨rfl,rfl,hT⟩ | ⟨rfl,rfl,hB⟩
  · exact secondary_T_false hq hC hnormal hvar hab hG hf
  · exact positive_TD_false hq hC hnormal hvar hab hG hT hf
  · exact positive_BT_false hq hC hnormal hvar hab hG hB hf

end SquaresInCircles.Eight.TableFree.PositiveSecondaryEExclusion

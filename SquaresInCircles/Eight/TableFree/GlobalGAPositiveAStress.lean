module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveASource

/-!
# The positive-A stress inequalities before imposing the original axes

Uncompiled source. These are the same three stress arguments already used
for a single A primary. Exposing their strict inequalities permits the
paired-primary comparison of the hand proof, where the two lost arguments
are analytic zeros and no new individual separator is asserted.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

namespace PositiveATD0.Source
open OrdinaryAngleConcentration
open TwoPositive.Source (aError aReserve a_reserve_nonneg)

theorem exists_positive_stress {q : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aError C atG)
    (hhg : hg=0 ∨ hg=2) :
    ∃k l c : ℝ,0≤k ∧ 0≤l ∧ 0≤c ∧ 0<actualStress C hg atG k l c := by
  by_cases hlow : aError C atG≤1/6
  · refine ⟨lowK,lowL,lowC,by norm_num [lowK],by norm_num [lowL],
      by norm_num [lowC],?_⟩
    have hb := Finset.sum_nonneg (s:=Finset.univ)
      (fun i _ => actual_blocks_nonneg atG hs hc hq hHy hGy hBy hDy hvar ha i (hg:=hg))
    have hA := a_reserve_nonneg (l:=lowL) atG (hs A) (hc A) hq (by norm_num [lowL])
      ⟨ha,hlow.trans (by norm_num [frameCap])⟩
    have hp := low_scalar_positive ⟨ha,hlow⟩
    have he := decomposition C atG hhg
    linarith
  · have hab := (original_budgets hg atG 1 1 1 hvar ha).1
    have hai : aError C atG∈Icc (1/6:ℝ) frameCap :=
      ⟨(lt_of_not_ge hlow).le,hab.2⟩
    let a := aError C atG
    let k := TwoPositive.highK a
    let l := TwoPositive.highL a
    let c := TwoPositive.highC a
    have hr := TwoPositive.high_ranges hai
    have hd := high_coefficient_ranges hai
    have hb := original_budgets hg atG k l c hvar ha
    have hcoefK : k≤1 := by dsimp [k,a]; linarith [hr.2.1]
    have hcoefL : k≤l := by dsimp [k,l,a]; linarith [hr.2.1,hr.2.2.1]
    have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
      full_blocks_lower atG hc hq hHy hGy hBy hDy hvar ha hcoefK hcoefL hd.1 i (hg:=hg))
    obtain ⟨i,j,hij⟩ := ordinary_concentration R (pWeights k l c) (qWeights k l c)
      (fun i => (blocks C hg atG k l c i).P) (fun i => (blocks C hg atG k l c i).N)
      (Real.sqrt_nonneg qCap) radius_sq.le hd.1 hd.2.1
      (fun i => by linarith [hd.2.2.1 i])
      (fun i => (blocks C hg atG k l c i).P_nonneg)
      (fun i => (blocks C hg atG k l c i).N_nonneg) hb.1 hb.2.1 hb.2.2
    have hend := high_endpoint_lower hai i j
    change endpoint k l c a i j≤_ at hij
    have henv : envelope k l c a≤∑i,actualFullBlocks C hg atG k l c i :=
      hend.trans (hij.trans hsum)
    have hA := a_reserve_nonneg (l:=l) atG (hs A) (hc A) hq
      (show 0≤l by dsimp [l,a]; linarith [hr.2.2.1]) hb.1
    have hdecomp := full_decomposition C atG hhg k l c
    have hscalar := high_scalar_positive hai
    change 0<fullBaseline k l c+l*TwoPositive.ASupport.charge a+envelope k l c a at hscalar
    exact ⟨k,l,c,by dsimp [k,a]; linarith [hr.1],
      by dsimp [l,a]; linarith [hr.2.2.1],
      by dsimp [c,a]; linarith [hr.2.2.2.2.1],by linarith⟩

end PositiveATD0.Source

namespace TwoPositive.Source
open PositiveTD

theorem exists_positive_stress {q : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aError C atG) (hz : 0≤delta C.theta T) (hhg : hg=0 ∨ hg=2) :
    ∃k l c : ℝ,0≤k ∧ 0≤l ∧ 0<c ∧ 0<actualStress C hg atG k l c := by
  have hb₀ := original_budgets hg atG 1 1 1 hvar ha hz
  obtain ⟨k,l,c,hk,hl,hcoef,hratio,hpositive⟩ := explicit_split_positive hb₀.1 hb₀.2.1
  have hsplit : total C atG-aError C atG=delta C.theta T := by dsimp [total]; ring
  rw [hsplit] at hratio
  have hb := original_budgets hg atG k l c hvar ha hz
  have hw := coefficient_domain hk hl hcoef hb.2.2.1 hratio
  obtain ⟨i,j,he⟩ := Hybrid.concentrate R (diagonal-1/2)
    (pWeights k l (tilted c (delta C.theta T)))
    (qWeights k l (tilted c (delta C.theta T)))
    (fun i => (blocks C hg atG k l c i).P)
    (fun i => (blocks C hg atG k l c i).N) (3:Fin 4)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hw i).1) (fun i => (hw i).2.1) (fun i => (hw i).2.2)
    (fun i => (blocks C hg atG k l c i).P_nonneg)
    (fun i => (blocks C hg atG k l c i).N_nonneg)
    hb.1 hb.2.2.2.1 hb.2.2.2.2
  have hsum := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => block_family_lower atG hs hc hq hHy hGy hBy hDy hvar ha hz
      hk hl hcoef hratio i)
  have hT := tReserve_nonneg (hs T) (hc T) hq
    (show 0≤c by linarith [hk.1,hcoef.1]) hb.2.2.1
  have hA := a_reserve_nonneg atG (hs A) (hc A) hq
    (show 0≤l by linarith [hk.1,hl.1]) ⟨ha,hb.2.1.2.trans hb.1.2⟩
  have hd := decomposition C atG hhg k l c
  change TwoPositive.endpoint k l (tilted c (delta C.theta T)) (total C atG) i j≤_ at he
  have hp := hpositive i j
  simp only [splitScalar,splitBase,hsplit] at hp
  exact ⟨k,l,c,by linarith [hk.1],by linarith [hk.1,hl.1],
    by linarith [hk.1,hcoef.1],by linarith⟩

end TwoPositive.Source

namespace PositiveANegativeTD.Source
open TwoPositive.Source (aError aReserve a_reserve_nonneg)

theorem exists_positive_stress {q : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aError C atG) (hz : delta C.theta T≤0) (hhg : hg=0 ∨ hg=2) :
    ∃k l c : ℝ,0≤k ∧ 0≤l ∧ 0≤c ∧ 0<actualStress C hg atG k l c := by
  have hb₀ := original_budgets hg atG 1 1 1 hvar ha hz
  have hcos : Real.cos (delta C.theta T)≠0 := by
    have hh := (transport_trig hb₀.2.1).1
    simpa [sError] using (ne_of_gt (show 0<Real.cos (sError C) by linarith))
  by_cases hlow : aError C atG≤1/6
  · refine ⟨PositiveATD0.lowK,PositiveATD0.lowL,PositiveATD0.lowC,
      by norm_num [PositiveATD0.lowK],by norm_num [PositiveATD0.lowL],
      by norm_num [PositiveATD0.lowC],?_⟩
    have hb := Finset.sum_nonneg (s:=Finset.univ)
      (fun i _ => actual_low_blocks_nonneg atG hs hc hq hHy hGy hBy hDy hvar ha hz i (hg:=hg))
    have hA := a_reserve_nonneg (l:=PositiveATD0.lowL) atG (hs A) (hc A) hq
      (by norm_num [PositiveATD0.lowL]) hb₀.1
    have hgain := actual_gain_lower (hs T) hcoreT (hc T) (hs D) hDy (hc D) hq
      (show 0≤PositiveATD0.lowC by norm_num [PositiveATD0.lowC]) hb₀.2.1
    have hp := PositiveATD0.low_scalar_positive ⟨ha,hlow⟩
    have he := low_decomposition C atG hhg hcos
    have hcharge : 0≤((9/10)*PositiveATD0.lowC-PositiveATD0.charge)*sError C := by
      apply mul_nonneg _ hb₀.2.1.1
      norm_num [PositiveATD0.lowC,PositiveATD0.charge]
    linarith
  · refine ⟨Fixed.k,Fixed.l,Fixed.c,by norm_num [Fixed.k],by norm_num [Fixed.l],
      by norm_num [Fixed.c],?_⟩
    have hai : aError C atG∈Icc Fixed.L frameCap :=
      ⟨(lt_of_not_ge hlow).le,hb₀.1.2⟩
    have hb := original_budgets hg atG Fixed.k Fixed.l Fixed.c hvar ha hz
    have hsum := Finset.sum_le_sum (s:=Finset.univ)
      (fun i _ => high_blocks_lower atG hs hc hq hHy hGy hBy hDy hvar ha hz i (hg:=hg))
    have hscalar := Fixed.sum_scalar_positive
      (fun i => (blocks C hg atG Fixed.k Fixed.l Fixed.c i).P)
      (fun i => (blocks C hg atG Fixed.k Fixed.l Fixed.c i).N) hai hb.2.1
      (fun i => (blocks C hg atG Fixed.k Fixed.l Fixed.c i).P_nonneg)
      (fun i => (blocks C hg atG Fixed.k Fixed.l Fixed.c i).N_nonneg)
      hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2
    have hA := a_reserve_nonneg (l:=Fixed.l) atG (hs A) (hc A) hq
      (by norm_num [Fixed.l]) hb.1
    have hgain := actual_gain_lower (hs T) hcoreT (hc T) (hs D) hDy (hc D) hq
      (show 0≤Fixed.c by norm_num [Fixed.c]) hb.2.1
    have hdecomp := high_decomposition C atG hhg hcos
    dsimp [Fixed.speed] at hscalar
    linarith

end PositiveANegativeTD.Source
end SquaresInCircles.Eight.TableFree.GlobalGA

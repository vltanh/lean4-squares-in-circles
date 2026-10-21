module

public import SquaresInCircles.Eight.TableFree.GlobalGAHybridConcentration
public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTD

/-!
# Original positive-TD data and exact remaining sign budgets

Uncompiled source.  The tilted BT multiplier depends on the actual TD
error.  Its only coefficient premises are the numerical ratio domain
needed for the proved ordinary concavity.  Removing the TD argument from
the analytic blocks preserves the exact two signed budgets.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

abbrev eta : ℝ := 293/1000
def tilted (c z : ℝ) : ℝ := c*(Real.cos z+eta*Real.sin z)
def sigma : ℝ := fullSupport 1 eta

def weights (k l c z : ℝ) : Vertex → ℝ := ![k,l,l,tilted c z,c,1,1]

def baseline (k l c z : ℝ) : ℝ :=
  k+2*l+tilted c z+c*edgeWidth z+2-c*sigma*Real.sin z-
    fullSupport 1 k-fullSupport l k-fullSupport (tilted c z) l-clippedSupport 1 c

def pWeights (k l m : ℝ) : Fin 4 → ℝ := ![k,k,min l m,k]
def qWeights (k l m : ℝ) : Fin 4 → ℝ := ![1,l,max l m,1]

def blocks (C : SignedCycle) (hg : Fin 4) (k l c : ℝ) : Fin 4 → Block :=
  ![⟨k,1,if hg=0 then 0 else delta C.theta H,delta C.theta E⟩,
    ⟨k,l,if hg=0 then delta C.theta H else 0,delta C.theta G⟩,
    ⟨l,tilted c (delta C.theta T),delta C.theta A,delta C.theta B⟩,
    ⟨k,1,delta C.theta D,0⟩]

def actualPairIncrement (B : Block) (P : SignedPoint) : ℝ :=
  B.alpha*(edgeWidth B.u-1)+B.beta*(edgeWidth B.v-1)-
    (pairF B.alpha B.beta B.u B.v*P.a+pairG B.alpha B.beta B.u B.v*P.y)+
    fullSupport B.beta B.alpha

theorem tilted_pos {c z : ℝ} (hc : 0<c) (hz : z∈Icc 0 frameCap) :
    0<tilted c z := by
  have ht := transport_trig hz
  have hs := mul_nonneg (show (0:ℝ)≤eta by norm_num [eta]) ht.2.2.1
  exact mul_pos hc (by linarith [ht.1])

theorem weights_nonneg {k l c z : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c) (hz : z∈Icc 0 frameCap) (i : Vertex) :
    0≤weights k l c z i := by
  have hm := (tilted_pos hc hz).le
  fin_cases i <;> simp [weights] <;> positivity

theorem coefficient_domain {k l c z : ℝ}
    (hk : k∈Icc (1/2) (17/20)) (hl : l∈Icc k (2*k))
    (hc : c∈Icc k 2) (hz : z∈Icc 0 frameCap)
    (hratio : l≤2*tilted c z ∧ tilted c z≤2*l) (i : Fin 4) :
    0<pWeights k l (tilted c z) i ∧
      pWeights k l (tilted c z) i≤qWeights k l (tilted c z) i ∧
      qWeights k l (tilted c z) i≤2*pWeights k l (tilted c z) i := by
  have hk0 : 0<k := by linarith [hk.1]
  have hl0 : 0<l := hk0.trans_le hl.1
  have hm0 := tilted_pos (hk0.trans_le hc.1) hz
  fin_cases i
  · simp only [pWeights,qWeights,Matrix.cons_val_zero]
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1]⟩
  · simp [pWeights,qWeights]
    exact ⟨hk0,hl.1,hl.2⟩
  · change 0<min l (tilted c z) ∧ min l (tilted c z)≤max l (tilted c z) ∧
      max l (tilted c z)≤2*min l (tilted c z)
    refine ⟨lt_min hl0 hm0,min_le_max,?_⟩
    rcases le_total l (tilted c z) with h | h
    · simpa [min_eq_left h,max_eq_right h] using hratio.2
    · simpa [min_eq_right h,max_eq_left h] using hratio.1
  · simp only [pWeights,qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero]
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1]⟩

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} {k l c : ℝ}
    (hk : k≤1) (hl : k≤l) (i : Fin 4) :
    (blocks C hg k l c i).p=pWeights k l (tilted c (delta C.theta T)) i ∧
      (blocks C hg k l c i).q=qWeights k l (tilted c (delta C.theta T)) i := by
  fin_cases i <;>
    simp [blocks,Block.p,Block.q,pWeights,qWeights,min_eq_left hk,max_eq_right hk,
      min_eq_left hl,max_eq_right hl]

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (k l c : ℝ)
    (f : ℝ → ℝ) (hf : f 0=0) :
    (∑ i,f (blocks C hg k l c i).u+f (blocks C hg k l c i).v)=
      (∑ j,f (delta C.theta j))-f (delta C.theta T) := by
  by_cases h : hg=0 <;>
    simp [blocks,h,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

theorem original_budgets {C : SignedCycle} (hg : Fin 4) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta T) :
    delta C.theta T∈Icc 0 frameCap ∧
      (∑ i,(blocks C hg k l c i).P)≤frameCap-delta C.theta T ∧
      (∑ i,(blocks C hg k l c i).N)=
        delta C.theta T+∑ i,(blocks C hg k l c i).P := by
  have hp := sum_parts C hg k l c positivePart positivePart_zero
  have hn := sum_parts C hg k l c negativePart negativePart_zero
  have hpz : positivePart (delta C.theta T)=delta C.theta T := max_eq_left hz
  have hnz : negativePart (delta C.theta T)=0 :=
    max_eq_right (by linarith : -delta C.theta T≤0)
  have hp' : (∑ i,(blocks C hg k l c i).P)=
      positiveVariation C.theta-delta C.theta T := by
    change (∑ i,positivePart (blocks C hg k l c i).u+
      positivePart (blocks C hg k l c i).v)=_
    simpa only [hpz,positiveVariation] using hp
  have hn' : (∑ i,(blocks C hg k l c i).N)=negativeVariation C.theta := by
    change (∑ i,negativePart (blocks C hg k l c i).u+
      negativePart (blocks C hg k l c i).v)=_
    simpa only [hnz,negativeVariation,sub_zero] using hn
  have hp0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg k l c i).P_nonneg)
  have heq := variations_equal C.theta
  exact ⟨⟨hz,by linarith⟩,by linarith,by linarith⟩

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta T)
    (i : Fin 4) :
    (blocks C hg k l c i).P≤frameCap ∧ (blocks C hg k l c i).N≤frameCap := by
  have h := original_budgets hg k l c hvar hz
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg k l c j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg k l c j).N_nonneg) (Finset.mem_univ i)
  constructor <;> linarith [h.1.1,h.2.1,h.2.2]

theorem actual_block_increment_lower {q : ℝ} {B : Block} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap)
    (hP : B.P≤frameCap) (hN : B.N≤frameCap) :
    B.increment R≤actualPairIncrement B P := by
  have hb := pair_error_bounds hP hN
  have h := actual_pair_lower (p:=B.alpha) (q:=B.beta) hy hc hq hb.1 hb.2.1
  dsimp [chargedPair,pairIncrement,actualPairIncrement,Block.increment] at *
  linarith

theorem actual_block_minorant {q : ℝ} {B : Block} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap)
    (hp : 0≤B.p) (hP : B.P≤frameCap) (hN : B.N≤frameCap) :
    mixedBlock R B.p B.q B.P B.N≤actualPairIncrement B P :=
  (B.minorant R hp hP hN).trans (actual_block_increment_lower hy hc hq hP hN)

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD

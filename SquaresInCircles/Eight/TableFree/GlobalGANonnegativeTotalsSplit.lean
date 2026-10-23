module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsEndpoints
public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveSplit

/-!
# The actual fixed-theta split with the independent E total

Uncompiled transcription of equations (17)--(19). The coefficient norm
retains negative angle delta = theta + e, while the tilted multiplier
moves with theta - a. These two angles are not identified. The existing
concavity theorem admits exactly these independent arguments and keeps
the min/max coefficient transition and the original A support join.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Analytic
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def fixedPart (k l c theta e : ℝ) (i : Fin 3) : ℝ :=
  k+(5/2)*l+2-fullSupport 1 k-fullSupport l k-fullSupport 1 c+
    TwoPositive.ASupport.charge e+(![V R k 1 (theta+e),V R k l (theta+e),0] i)
def coefficientAngle (t : ℝ) (i : Fin 3) : ℝ := if i=2 then t else 0
def coefficientCosine (t : ℝ) (i : Fin 3) : ℝ := if i=2 then Real.cos t-1 else 0

theorem split_form {k l c theta e a : ℝ} (i : Fin 3)
    (hθ : theta∈Icc 0 frameCap) (ha : a∈Icc 0 theta) :
    largeScalar k l c theta e a i=fixedPart k l c theta e i+
      (TwoPositive.Coefficient.H l (-coefficientAngle (theta+e) i) 0
        (coefficientCosine (theta+e) i) (PositiveTD.tilted c (theta-a))+
          TwoPositive.Split.rest c l theta a) := by
  have hz := (TwoPositive.Split.split_domain hθ ha).2
  have hsmooth := TwoPositive.Split.smooth_actual (c:=c) hz
  rw [largeScalar,fullBaseline,fullSupport_pair l (PositiveTD.tilted c (theta-a))]
  fin_cases i <;>
    simp only [negative,fixedPart,coefficientAngle,coefficientCosine,
      Fin.reduceFinMk,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_succ,
      TwoPositive.Coefficient.H,zero_mul,add_zero,neg_zero,TwoPositive.Split.rest,
      hsmooth]
  · ring
  · ring
  · rw [V,pairNorm_min_max,pairNorm_min_max]
    ring

theorem coefficient_angle_domain {t : ℝ} (ht : t∈Icc 0 frameCap) (i : Fin 3) :
    coefficientAngle t i∈Icc 0 frameCap ∧
    coefficientCosine t i≤0 ∧ Real.cos (coefficientAngle t i)-1≤coefficientCosine t i := by
  by_cases hi : i=2
  · simp only [coefficientAngle,coefficientCosine,if_pos hi]
    exact ⟨ht,by linarith [Real.cos_le_one t],le_rfl⟩
  · simp [coefficientAngle,coefficientCosine,hi,frameCap]

theorem largeScalar_concave (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) :
    ConcaveOn ℝ (Icc 0 (Explicit.theta r x y))
      (fun a => largeScalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
        (Explicit.theta r x y) (Explicit.e r x y) a i) := by
  have hb := Explicit.base_bounds r hd
  have hθ := (Explicit.domains hd).1
  have hδ : Explicit.delta r x y∈Icc 0 frameCap :=
    ⟨by linarith [(Explicit.domains hd).2.2.1],(Explicit.domains hd).2.2.2⟩
  have hs := coefficient_angle_domain hδ i
  have hm (a : ℝ) (ha : a∈Icc 0 (Explicit.theta r x y)) :
      PositiveTD.tilted (Explicit.c r x y) (Explicit.theta r x y-a)∈
        Icc ((2/3)*Explicit.l r x y) ((23/20)*Explicit.l r x y) := by
    have hh := Explicit.tilted_ratio r hd
      (show Explicit.theta r x y-a∈Icc 0 (Explicit.theta r x y) from
        ⟨by linarith [ha.2],by linarith [ha.1]⟩)
    exact ⟨hh.1.le,hh.2.le⟩
  have hc := TwoPositive.Split.high_scalar_concave
    hb.l_positive hb.c_lower_ratio hb.c_upper_ratio hθ hs.1
    (show 0<(2/3)*Explicit.l r x y by positivity) le_rfl
    hs.2.1 hs.2.2 hm
  refine ⟨hc.1,?_⟩
  intro a ha b hb' u v hu hv huv
  have hcomb := hc.1 ha hb' hu hv huv
  have hh := hc.2 ha hb' hu hv huv
  rw [split_form i hθ ha,split_form i hθ hb',split_form i hθ hcomb]
  simp only [smul_eq_mul] at hh ⊢
  have hconst := congrArg (fun t : ℝ => t*fixedPart
    (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
    (Explicit.theta r x y) (Explicit.e r x y) i) huv
  change u*fixedPart _ _ _ _ _ i+v*fixedPart _ _ _ _ _ i=fixedPart _ _ _ _ _ i at hconst
  nlinarith only [hh,hconst]

theorem large_scalar_positive (r : Region) (i : Fin 3) {x y a : ℝ}
    (hd : Explicit.Domain r x y) (ha : a∈Icc 0 (Explicit.theta r x y)) :
    0<largeScalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
      (Explicit.theta r x y) (Explicit.e r x y) a i := by
  have hleft : 0<largeScalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
      (Explicit.theta r x y) (Explicit.e r x y) 0 i := by
    simpa only [endpoint,aAt] using endpoint_positive r .atT i hd
  have hright : 0<largeScalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
      (Explicit.theta r x y) (Explicit.e r x y) (Explicit.theta r x y) i := by
    simpa only [endpoint,aAt] using endpoint_positive r .atA i hd
  exact concave_gt_of_endpoints (largeScalar_concave r i hd) ha hleft hright

def concentrationScalar (k l c theta e a : ℝ) (i j : Fin 4) : ℝ :=
  fullBaseline k l c (theta-a)+l*TwoPositive.ASupport.charge a+
    TwoPositive.ASupport.charge e+
      TwoPositive.endpoint k l (PositiveTD.tilted c (theta-a)) (theta+e) i j

theorem large_concentration_positive (r : Region) {x y a : ℝ}
    (hd : Explicit.Domain r x y) (ha : a∈Icc 0 (Explicit.theta r x y)) (i j : Fin 4) :
    0<concentrationScalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
      (Explicit.theta r x y) (Explicit.e r x y) a i j := by
  have h0 := large_scalar_positive r 0 hd ha
  have h1 := large_scalar_positive r 1 hd ha
  have h2 := large_scalar_positive r 2 hd ha
  have hmin : 0<fullBaseline (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
      (Explicit.theta r x y-a)+
      Explicit.l r x y*TwoPositive.ASupport.charge a+TwoPositive.ASupport.charge (Explicit.e r x y)+
      TwoPositive.balancedEnvelope (Explicit.k r x y) (Explicit.l r x y)
        (PositiveTD.tilted (Explicit.c r x y) (Explicit.theta r x y-a)) (Explicit.delta r x y) := by
    unfold TwoPositive.balancedEnvelope
    rw [add_min,add_min]
    exact lt_min h0 (lt_min h1 h2)
  have hh := Explicit.balanced_endpoint r hd
    (show Explicit.theta r x y-a∈Icc 0 (Explicit.theta r x y) from
      ⟨by linarith [ha.2],by linarith [ha.1]⟩) i j
  dsimp [concentrationScalar,Explicit.delta]
  exact hmin.trans_le (add_le_add_left hh _)

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Analytic

import SquaresInCircles.Six.Classification.CommonDomain
import SquaresInCircles.Six.Stress.StrictSupport

/-!
# One actual stress for every canonical central-bit pattern

The four central multipliers are chosen independently on the two adjacent
pairs. Their resultants are (-1,1) and (1,-1), so the central force vanishes
exactly. All selected adjacent axes remain genuine consequences of the pin
orientation theorem; the surviving diagonal axes come from the completed
fixed-stress classification.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization Classification

/-- Actual canonical central separator direction, including cardinal tie preference. -/
def balancedCenterAxis {R : ℝ} (P : NormalizedPacking R) (i : Fin 5) : Point :=
  if P.ownBits i then primary (P.phase i) else primary (cardinalCenter (matchingCardinal i))

def balancedAlpha {R : ℝ} (P : NormalizedPacking R) : ℝ :=
  pairAlpha (P.ownBits 1) (P.ownBits 2) (P.helperAngle 1) (P.helperAngle 2)
def balancedGamma {R : ℝ} (P : NormalizedPacking R) : ℝ :=
  pairGamma (P.ownBits 1) (P.ownBits 2) (P.helperAngle 1) (P.helperAngle 2)
def balancedBeta {R : ℝ} (P : NormalizedPacking R) : ℝ :=
  pairAlpha (P.ownBits 0) (P.ownBits 4) (-P.helperAngle 0) (-P.helperAngle 4)
def balancedDelta {R : ℝ} (P : NormalizedPacking R) : ℝ :=
  pairGamma (P.ownBits 0) (P.ownBits 4) (-P.helperAngle 0) (-P.helperAngle 4)

def balancedNWAxis {R : ℝ} (P : NormalizedPacking R) (u : Fin 4) : Point :=
  preferredPairAxis NWsigns (P.square 2) (P.square 1) u

def balancedESAxis {R : ℝ} (P : NormalizedPacking R) (v : Fin 4) : Point :=
  preferredPairAxis ESsigns (P.square 4) (P.square 0) v

def BalancedSelected {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) : Prop :=
  Seven.SAT.threshold (P.square 2) (P.square 1)≤
    dot (balancedNWAxis P u) (sub (P.square 1).center (P.square 2).center) ∧
  Seven.SAT.threshold (P.square 4) (P.square 0)≤
    dot (balancedESAxis P v) (sub (P.square 0).center (P.square 4).center)

lemma exists_balanced_selection {R : ℝ} (P : NormalizedPacking R) :
    ∃ u v : Fin 4, BalancedSelected P u v := by
  obtain ⟨u,hu⟩ := P.NW_source
  obtain ⟨v,hv⟩ := P.ES_source
  exact ⟨u,v,hu,hv⟩

/-- Model order C,E,N,W,D,S; edge order CN,CE,CW,CS,WN,SE,WD,DS. -/
def balancedSystem {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) : System 6 8 where
  source := ![0,0,0,0,3,5,3,4]
  target := ![2,1,3,5,2,1,4,5]
  normal := ![balancedCenterAxis P 1,balancedCenterAxis P 0,
    balancedCenterAxis P 2,balancedCenterAxis P 4,balancedNWAxis P u,balancedESAxis P v,
    normalY (P.square 2),normalY (P.square 4)]
  weight := ![balancedAlpha P,balancedBeta P,balancedGamma P,balancedDelta P,rStar,rStar,mStar,mStar]
  threshold := fun e => Seven.SAT.threshold
    (P.model (![0,0,0,0,3,5,3,4] e)) (P.model (![2,1,3,5,2,1,4,5] e))

lemma balanced_weights_pos {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) (e : Fin 8) :
    0<(balancedSystem P u v).weight e := by
  obtain ⟨hn,hw,he,hs⟩ := common_pair_domains P
  have hnw := pair_weights_pos (P.ownBits 1) (P.ownBits 2) hn
    (show -2/3≤P.helperAngle 2 ∧ P.helperAngle 2≤5/8 by constructor <;> linarith [hw.1,hw.2])
  have hes := pair_weights_pos (P.ownBits 0) (P.ownBits 4) he
    (show -2/3≤-P.helperAngle 4 ∧ -P.helperAngle 4≤5/8 by constructor <;> linarith [hs.1,hs.2])
  fin_cases e
  · exact hnw.1
  · exact hes.1
  · exact hnw.2
  · exact hes.2
  · exact rStar_pos
  · exact rStar_pos
  · exact mStar_pos
  · exact mStar_pos

lemma balanced_weights_nonnegative {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    (balancedSystem P u v).Nonnegative := fun e => (balanced_weights_pos P u v e).le

lemma balanced_threshold_pos {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    0<(balancedSystem P u v).thresholdSum := by
  have he (e : Fin 8) : 0<(balancedSystem P u v).weight e*(balancedSystem P u v).threshold e :=
    mul_pos (balanced_weights_pos P u v e) (threshold_pos _ _)
  have hs := Finset.single_le_sum
    (fun e (_ : e ∈ Finset.univ) => (he e).le) (Finset.mem_univ (0:Fin 8))
  exact (he 0).trans_le hs

lemma balanced_selected_center {R : ℝ} (P : NormalizedPacking R) (i : Fin 5) :
    Seven.SAT.threshold (P.model 0) (P.model i.succ)≤
      dot (balancedCenterAxis P i) (sub (P.model i.succ).center (P.model 0).center) := by
  change Seven.SAT.threshold (axisSquare P.center) (P.square i)≤
    dot (balancedCenterAxis P i) (sub (P.square i).center P.center)
  rw [P.square_def,central_threshold]
  cases hbit : P.ownBits i
  · have hm := P.cardinal_separator i hbit
    fin_cases i
    all_goals simp only [balancedCenterAxis,hbit,Bool.false_eq_true,if_false,
      matchingCardinal,cardinalCenter,primary,Real.cos_zero,Real.sin_zero,
      Real.cos_pi,Real.sin_pi,Real.cos_pi_div_two,Real.sin_pi_div_two,south_cos,south_sin]
    all_goals dsimp [centralMargin,centerX,centerY,dot,sub,orientedSquare] at hm ⊢
    all_goals linarith
  · have hm := P.own_separator i hbit
    simp only [balancedCenterAxis,hbit,if_true]
    change 1/2+angularWidth (P.phase i)≤
      frameX (orientedSquare (P.phase i) (P.radial i) (P.transverse i))
        (sub (orientedSquare (P.phase i) (P.radial i) (P.transverse i)).center P.center)
    rw [primary_difference]
    dsimp [centralMargin] at hm
    linarith

/-- All eight inequalities are supplied by actual canonical or selected axes. -/
theorem balanced_separates {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4)
    (hsel : BalancedSelected P u v) : (balancedSystem P u v).Separates P.model := by
  have hg := candidate_diagonal_edges P
  intro e
  fin_cases e
  · exact balanced_selected_center P 1
  · exact balanced_selected_center P 0
  · exact balanced_selected_center P 2
  · exact balanced_selected_center P 4
  · exact hsel.1
  · exact hsel.2
  · simpa only [Stress.pairNormal] using hg.1
  · simpa only [Stress.pairNormal] using hg.2.1

lemma pair_vector_balance (no wo : Bool) {n w : ℝ}
    (hn : -3/10≤n ∧ n≤5/12) (hw : -2/3≤w ∧ w≤5/8) :
    add (scale (pairAlpha no wo n w) (if no then (-Real.sin n,Real.cos n) else (0,1)))
      (scale (pairGamma no wo n w) (if wo then (-Real.cos w,-Real.sin w) else (-1,0)))=(-1,1) := by
  have ht := pair_trig_signs hn hw
  have hb := pair_balance no wo (ne_of_gt ht.1) (ne_of_gt ht.2.1) (ne_of_gt ht.2.2.1)
  cases no <;> cases wo
  all_goals apply Prod.ext
  all_goals simp only [Bool.false_eq_true,if_false,if_true,add,scale] at hb ⊢
  all_goals linarith [hb.1,hb.2]

lemma balanced_center_axes {R : ℝ} (P : NormalizedPacking R) :
    balancedCenterAxis P 0=(if P.ownBits 0 then (Real.cos (P.helperAngle 0),Real.sin (P.helperAngle 0)) else (1,0)) ∧
    balancedCenterAxis P 1=(if P.ownBits 1 then (-Real.sin (P.helperAngle 1),Real.cos (P.helperAngle 1)) else (0,1)) ∧
    balancedCenterAxis P 2=(if P.ownBits 2 then (-Real.cos (P.helperAngle 2),-Real.sin (P.helperAngle 2)) else (-1,0)) ∧
    balancedCenterAxis P 4=(if P.ownBits 4 then (Real.sin (P.helperAngle 4),-Real.cos (P.helperAngle 4)) else (0,-1)) := by
  have he := P.phase_from_deviation 0
  have hn := P.phase_from_deviation 1
  have hw := P.phase_from_deviation 2
  have hs := P.phase_from_deviation 4
  simp only [matchingCardinal,cardinalCenter,zero_add] at he hn hw hs
  simp [balancedCenterAxis,matchingCardinal,cardinalCenter,he,hn,hw,hs,primary,
    Real.cos_add,Real.sin_add,south_cos,south_sin]

lemma balanced_pair_resultants {R : ℝ} (P : NormalizedPacking R) :
    add (scale (balancedAlpha P) (balancedCenterAxis P 1))
      (scale (balancedGamma P) (balancedCenterAxis P 2))=(-1,1) ∧
    add (scale (balancedBeta P) (balancedCenterAxis P 0))
      (scale (balancedDelta P) (balancedCenterAxis P 4))=(1,-1) := by
  obtain ⟨hn,hw,he,hs⟩ := common_pair_domains P
  have hnw := pair_vector_balance (P.ownBits 1) (P.ownBits 2) hn
    (show -2/3≤P.helperAngle 2 ∧ P.helperAngle 2≤5/8 by constructor <;> linarith [hw.1,hw.2])
  have hes := pair_vector_balance (P.ownBits 0) (P.ownBits 4) he
    (show -2/3≤-P.helperAngle 4 ∧ -P.helperAngle 4≤5/8 by constructor <;> linarith [hs.1,hs.2])
  have hv := balanced_center_axes P
  constructor
  · rw [hv.2.1,hv.2.2.1]
    exact hnw
  · have href := congrArg diagonalPoint hes
    rw [hv.1,hv.2.2.2]
    cases hE : P.ownBits 0 <;> cases hS : P.ownBits 4
    all_goals simpa [hE,hS,diagonalPoint,add,scale,Real.sin_neg,Real.cos_neg,
      balancedBeta,balancedDelta] using href

/-- The force on the central square vanishes for every source and every bit
choice; no central box support is needed in this common stress. -/
theorem balanced_central_force_zero {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    (balancedSystem P u v).force 0=(0,0) := by
  have hp := balanced_pair_resultants P
  have hnwx := congrArg Prod.fst hp.1
  have hnwy := congrArg Prod.snd hp.1
  have hesx := congrArg Prod.fst hp.2
  have hesy := congrArg Prod.snd hp.2
  dsimp [add,scale] at hnwx hnwy hesx hesy
  apply Prod.ext
  all_goals simp [System.force,balancedSystem,Fin.sum_univ_succ]
  all_goals linarith

end SquaresInCircles.Six.Stress

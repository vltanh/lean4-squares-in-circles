import SquaresInCircles.Six.Analytic.CandidateWestTail.Support
import SquaresInCircles.Six.Analytic.CanonicalSouthSign

/-!
# The candidate D graph supplies the OWN-W outer tail

The scalar stress consumes four actual separators: CW, CS, WD and DS. CD is
not weighted. For two OWN wings the already proved shared-center budget gives
s-w<1, so a putative -w>=11/25 has s<14/25<3/5. Cardinal S instead has |s|<2/5.
These are consequences, not additional assumptions on NormalizedPacking.

The result is conditional only on the two candidate D separators. It removes
the need to prove the west tail independently of the mixed-source exclusion;
it does not silently supply those still-unproved candidate separators.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.CandidateWestTail
open Normalization

/-- Four genuine scalar separators contradict the positive whole-domain stress. -/
theorem scalar_impossible (k : Fin 3) {v x d aw bw ad bd asouth bsouth cx cy : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hx : 0 ≤ x ∧ x ≤ xMax k)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hS : ContainedChart asouth |bsouth|) (hcx : cx ≤ c0) (hcy : 0 ≤ cy)
    (hCW : 1/2+angularWidth v ≤ aw+cx*Real.cos v-cy*Real.sin v)
    (hCS : 1/2+angularWidth (side k*x) ≤
      if k=0 then asouth-cx*Real.sin (side k*x)+cy*Real.cos (side k*x)
      else asouth*Real.cos (side k*x)-bsouth*Real.sin (side k*x)+cy)
    (hWD : 1/2+angularWidth (v+d) ≤
      ad*Real.sin (v+d)+bd*Real.cos (v+d)-bw)
    (hDS : 1/2+angularWidth (d-side k*x) ≤
      bsouth+ad*Real.cos (d-side k*x)-bd*Real.sin (d-side k*x)) : False := by
  have hsum : totalThreshold v (side k*x) d ≤
      (beta*aw-mu*bw)+
      (diagonalU v (side k*x) d*ad+diagonalV v (side k*x) d*bd)+
      southWork k (side k*x) asouth bsouth+centerWork k v (side k*x) cx cy := by
    by_cases hk : k=0
    · simp only [if_pos hk] at hCS
      simp only [totalThreshold,diagonalU,diagonalV,southWork,centerWork,if_pos hk]
      dsimp [beta,gamma,mu,nu]
      linear_combination (109/200)*hCW+(47/250)*hCS+(169/1000)*hWD+(49/500)*hDS
    · simp only [if_neg hk] at hCS
      simp only [totalThreshold,diagonalU,diagonalV,southWork,centerWork,if_neg hk]
      dsimp [beta,gamma,mu,nu]
      linear_combination (109/200)*hCW+(47/250)*hCS+(169/1000)*hWD+(49/500)*hDS
  have hw := west_support hW
  have hs := south_support k (s := side k*x) hS
  have hd' := diagonal_support (v := v) (s := side k*x) (d := d) hD
  have hc := center_support k hv hx hcx hcy
  have hnonpos : defect k v (side k*x) d ≤ 0 := by
    dsimp [defect]
    linarith only [hsum,hw,hs,hd',hc]
  have hpositive := (positive k hv hx hd).trans_le (minorant_le_defect k v x d)
  linarith

/-- The OWN-W lower tail follows from the actual candidate graph at Q0.
There is no additional pair-domain or tail assumption. -/
theorem normalized_own_west_tail_of_edges {R : ℝ} (P : NormalizedPacking R)
    (hedges : FixedPair.CandidateDSeparators P) (hW : P.ownBits 2=true) :
    -11/25 < P.helperAngle 2 := by
  by_contra! htail
  let v := -P.helperAngle 2
  let s := P.helperAngle 4
  let d := P.diagonalAngle
  have hv : 11/25 ≤ v ∧ v ≤ 2/3 := by
    dsimp [v]
    constructor <;> linarith [P.helper_windows.2.2.1.1]
  have hd : 1/2 ≤ d ∧ d ≤ 11/14 := by
    have hlo := normalized_diagonal_gt_half P
    have hhi := P.diagonal_angle_range.2
    constructor <;> linarith [Real.pi_lt_d4]
  have hWphase : P.phase 2=Real.pi-v := by
    rw [P.phase_from_deviation 2]
    dsimp [v]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+s := P.phase_from_deviation 4
  have hDphase : P.phase 3=Real.pi+d := by dsimp [d,NormalizedPacking.diagonalAngle]; ring
  have hCW : 1/2+angularWidth v ≤
      P.radial 2+P.center.1*Real.cos v-P.center.2*Real.sin v := by
    have h := P.own_separator 2 hW
    rw [hWphase] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hWD : 1/2+angularWidth (v+d) ≤
      P.radial 3*Real.sin (v+d)+P.transverse 3*Real.cos (v+d)-P.transverse 2 := by
    have h := hedges.1
    change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      frameY (P.square 2) (sub (P.square 3).center (P.square 2).center) at h
    rw [P.square_def 2,P.square_def 3,hWphase,hDphase,oriented_pair_threshold,pair_frameY_left,
      show (Real.pi+d)-(Real.pi-v)=v+d by ring] at h
    exact h
  have hDS : 1/2+angularWidth (d-s) ≤
      P.transverse 4+P.radial 3*Real.cos (d-s)-P.transverse 3*Real.sin (d-s) := by
    have h := hedges.2
    change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      frameY (P.square 4) (sub (P.square 4).center (P.square 3).center) at h
    rw [P.square_def 3,P.square_def 4,hDphase,hSphase,oriented_pair_threshold,pair_frameY_right,
      show (3*Real.pi/2+s)-(Real.pi+d)=Real.pi/2-(d-s) by ring,
      FixedPair.width_half_pi_sub,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub] at h
    linarith only [h]
  have finish (k : Fin 3) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ xMax k)
      (hxid : s=side k*x)
      (hCS : 1/2+angularWidth s ≤
        if k=0 then P.radial 4-P.center.1*Real.sin s+P.center.2*Real.cos s
        else P.radial 4*Real.cos s-P.transverse 4*Real.sin s+P.center.2) : False := by
    apply scalar_impossible k hv hx hd (P.contained 2) (P.contained 3) (P.contained 4)
      P.box.1.2 P.box.2.1 hCW
    · simpa only [← hxid] using hCS
    · exact hWD
    · simpa only [← hxid] using hDS
  cases hS : P.ownBits 4
  · have hs : -2/5 < s ∧ s < 2/5 := abs_lt.mp (P.cardinal_angle 4 hS)
    have hCS : 1/2+angularWidth s ≤
        P.radial 4*Real.cos s-P.transverse 4*Real.sin s+P.center.2 := by
      have h := P.cardinal_separator 4 hS
      change 0 ≤ centralMargin .south (P.phase 4) (P.radial 4) (P.transverse 4)
        P.center.1 P.center.2 at h
      rw [hSphase] at h
      simp only [centralMargin,centerY,angularWidth,Real.cos_add,Real.sin_add,
        south_cos,south_sin,zero_mul,one_mul,neg_one_mul,zero_add,add_zero,abs_neg] at h
      dsimp [angularWidth]
      nlinarith only [h]
    by_cases hs0 : 0 ≤ s
    · apply finish 1 s
      · norm_num [xMax]
        exact ⟨hs0,by linarith [hs.2]⟩
      · norm_num [side]
      · simpa using hCS
    · apply finish 2 (-s)
      · norm_num [xMax]
        constructor <;> linarith [hs.1]
      · norm_num [side]
      · simpa using hCS
  · have hs0 : 0 < s := canonical_own_south_positive P hS
    have hsum := normalized_own_wing_angle_sum P hW hS
    have hs1 : s ≤ 3/5 := by dsimp [v,s] at *; linarith
    have hCS : 1/2+angularWidth s ≤
        P.radial 4-P.center.1*Real.sin s+P.center.2*Real.cos s := by
      have h := P.own_separator 4 hS
      rw [hSphase] at h
      simp only [centralMargin,centralNormal,angularWidth,Real.cos_add,Real.sin_add,
        south_cos,south_sin,zero_mul,one_mul,neg_one_mul,zero_add,add_zero,abs_neg] at h
      dsimp [angularWidth]
      nlinarith only [h]
    apply finish 0 s
    · simpa [xMax] using And.intro hs0.le hs1
    · norm_num [side]
    · simpa using hCS

end SquaresInCircles.Six.Analytic.CandidateWestTail

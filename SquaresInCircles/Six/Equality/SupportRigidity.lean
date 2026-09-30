module
public import SquaresInCircles.Six.Equality.LocalCenters

@[expose] public section

/-!
# Actual support equality determines all exterior coordinates

The support and separator equalities come from the same selected nonnegative
stress used in the radius proof. No equality case of a numerical checker is
assumed. The center-coordinate uniqueness lemmas are then applied to the
original contained squares in their actual frames.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization

lemma balanced_support_tight {R : ℝ} (P : NormalizedPacking R) (hR : R^2≤Six.qStar)
    (u v : Fin 4) (hsel : BalancedSelected P u v) (hzero : balancedDefect P u v=0) (i : Fin 6) :
    dot ((balancedSystem P u v).force i) (P.model i).center=balancedUpper P u v i := by
  have heq : (balancedSystem P u v).thresholdSum=∑ j,balancedUpper P u v j :=
    sub_eq_zero.mp hzero
  exact (balancedSystem P u v).support_tight P.model (balancedUpper P u v)
    (balanced_weights_nonnegative P u v) (balanced_separates P u v hsel)
    (balanced_upper_bounds P hR u v) heq i

lemma balanced_separator_tight {R : ℝ} (P : NormalizedPacking R) (hR : R^2≤Six.qStar)
    (u v : Fin 4) (hsel : BalancedSelected P u v) (hzero : balancedDefect P u v=0) (e : Fin 8) :
    dot ((balancedSystem P u v).normal e)
      (sub (P.model ((balancedSystem P u v).target e)).center
        (P.model ((balancedSystem P u v).source e)).center)=
      (balancedSystem P u v).threshold e := by
  have heq : (balancedSystem P u v).thresholdSum=∑ j,balancedUpper P u v j :=
    sub_eq_zero.mp hzero
  exact (balancedSystem P u v).separator_tight P.model (balancedUpper P u v)
    (balanced_weights_nonnegative P u v) (balanced_separates P u v hsel)
    (balanced_upper_bounds P hR u v) heq e (balanced_weights_pos P u v e)

end SquaresInCircles.Six.Stress

namespace SquaresInCircles.Six.Equality
open Stress Normalization

lemma candidate_phases {R : ℝ} (P : NormalizedPacking R) (ha : CandidateAngles P) :
    P.phase 0=0 ∧ P.phase 1=Real.pi/2 ∧ P.phase 2=Real.pi ∧
      P.phase 3=5*Real.pi/4 ∧ P.phase 4=3*Real.pi/2 := by
  obtain ⟨he,hn,hw,hs,hd⟩ := ha
  have hE := P.phase_from_deviation 0
  have hN := P.phase_from_deviation 1
  have hW := P.phase_from_deviation 2
  have hS := P.phase_from_deviation 4
  simp only [matchingCardinal,cardinalCenter,he,hn,hw,hs,add_zero] at hE hN hW hS
  have hD : P.phase 3=5*Real.pi/4 := by
    dsimp [NormalizedPacking.diagonalAngle] at hd
    linarith
  exact ⟨hE,hN,hW,hD,hS⟩

lemma candidate_local_forces {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4)
    (ha : CandidateAngles P) (hsrc : CandidateSources u v) :
    projectAt (P.phase 0) ((balancedSystem P u v).force 1)=(1,rStar) ∧
    projectAt (P.phase 1) ((balancedSystem P u v).force 2)=(1,-rStar) ∧
    projectAt (P.phase 2) ((balancedSystem P u v).force 3)=(1+rStar,-mStar) ∧
    projectAt (P.phase 4) ((balancedSystem P u v).force 5)=(1+rStar,mStar) ∧
    projectAt (P.phase 3) ((balancedSystem P u v).force 4)=(diagonalK,0) := by
  obtain ⟨he,hn,hw,hs,hd⟩ := ha
  have hNW := pair_candidate_forces (P.ownBits 1) (P.ownBits 2) hsrc.1
  have hES := pair_candidate_forces (P.ownBits 0) (P.ownBits 4) hsrc.2
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [balanced_local_east,he,hs,neg_zero,hES.1]
    simp [reflectLocal]
  · rw [balanced_local_north,hn,hw,hNW.1]
  · rw [balanced_local_west,hn,hw,hNW.2]
  · rw [balanced_local_south,he,hs,neg_zero,hES.2]
    simp [reflectLocal]
  · rw [balanced_local_diagonal,hw,hs,hd]
    simp [diagonalLocalForce,diagonalK,Six.hStar,halfDiagonal]
    ring

lemma local_support_equality {t a b R : ℝ} {g : Point}
    (h : dot g (orientedSquare t a b).center=exactSupport R (orientedSquare t a b) g) :
    (projectAt t g).1*a+(projectAt t g).2*b=
      scalarSupport R (projectAt t g).1 (projectAt t g).2 := by
  have hx : frameX (orientedSquare t a b) (orientedSquare t a b).center=a := by
    simpa [sub] using oriented_frame_centerX t a b
  have hy : frameY (orientedSquare t a b) (orientedSquare t a b).center=b := by
    simpa [sub] using oriented_frame_centerY t a b
  rw [← frame_dot] at h
  change frameX (orientedSquare t a b) g*frameX (orientedSquare t a b) (orientedSquare t a b).center+
    frameY (orientedSquare t a b) g*frameY (orientedSquare t a b) (orientedSquare t a b).center=
    scalarSupport R (frameX (orientedSquare t a b) g) (frameY (orientedSquare t a b) g) at h
  rw [hx,hy] at h
  exact h

structure CandidateCenterCoordinates {R : ℝ} (P : NormalizedPacking R) : Prop where
  east_radial : P.radial 0=1+Six.sStar
  east_transverse : P.transverse 0=Six.sStar
  north_radial : P.radial 1=1+Six.sStar
  north_transverse : P.transverse 1= -Six.sStar
  west_radial : P.radial 2=1-Six.sStar
  west_transverse : P.transverse 2= -Six.tStar
  south_radial : P.radial 4=1-Six.sStar
  south_transverse : P.transverse 4=Six.tStar
  diagonal_radial : P.radial 3=rhoStar
  diagonal_transverse : P.transverse 3=0

/-- All ten exterior chart coordinates are forced by the active supports. -/
theorem candidate_center_coordinates {R : ℝ} (P : NormalizedPacking R) (hR : R^2≤Six.qStar)
    (u v : Fin 4) (hsel : BalancedSelected P u v) (ha : CandidateAngles P)
    (hsrc : CandidateSources u v) (hzero : balancedDefect P u v=0) :
    CandidateCenterCoordinates P := by
  have hbox (i : Fin 5) :
      (|P.radial i|+1/2)^2+(|P.transverse i|+1/2)^2≤Six.radius^2 := by
    have hc := (P.packing.phi_le i.succ).trans hR
    simpa only [pinModel_succ,orientedSquare_alpha,orientedSquare_beta,phi,Six.radius_sq] using hc
  have hlocal (i : Fin 5) :
      (projectAt (P.phase i) ((balancedSystem P u v).force i.succ)).1*P.radial i+
      (projectAt (P.phase i) ((balancedSystem P u v).force i.succ)).2*P.transverse i=
      scalarSupport Six.radius
        (projectAt (P.phase i) ((balancedSystem P u v).force i.succ)).1
        (projectAt (P.phase i) ((balancedSystem P u v).force i.succ)).2 := by
    have hs := balanced_support_tight P hR u v hsel hzero i.succ
    have hi : i.succ≠0 := by intro he; have hv := congrArg Fin.val he; simp at hv
    rw [balancedUpper,if_neg hi] at hs
    exact local_support_equality hs
  obtain ⟨hfE,hfN,hfW,hfS,hfD⟩ := candidate_local_forces P u v ha hsrc
  have he := hlocal 0
  have hn := hlocal 1
  have hw := hlocal 2
  have hs := hlocal 4
  have hd := hlocal 3
  rw [hfE] at he
  rw [hfN] at hn
  rw [hfW] at hw
  rw [hfS] at hs
  rw [hfD] at hd
  have ce := north_center_unique (sgn := (1:ℝ)) (Or.inl rfl) (hbox 0)
    (by simpa only [one_mul] using he)
  have cn := north_center_unique (sgn := (-1:ℝ)) (Or.inr rfl) (hbox 1)
    (by simpa only [one_mul,neg_one_mul] using hn)
  have cw := west_center_unique (sgn := (-1:ℝ)) (Or.inr rfl) (hbox 2)
    (by simpa only [neg_one_mul] using hw)
  have cs := west_center_unique (sgn := (1:ℝ)) (Or.inl rfl) (hbox 4)
    (by simpa only [one_mul] using hs)
  have cd := diagonal_center_unique (hbox 3) (by simpa only [zero_mul,add_zero] using hd)
  exact ⟨ce.1,by simpa using ce.2,cn.1,by simpa using cn.2,
    cw.1,by simpa using cw.2,cs.1,by simpa using cs.2,cd.1,cd.2⟩

end SquaresInCircles.Six.Equality

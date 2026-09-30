module
public import SquaresInCircles.Six.Stress.BalancedSystem

@[expose] public section

/-!
# Exact local-force identities

The N/W and E/S source indices are the actual four pin-oriented axes. E/S is
identified with the same pair formula at (-e,-s), with its local transverse
force reversed. That reversal is harmless only after the exact support's sign
symmetry is invoked; it is not a global reflection of the packing.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization Classification

def projectAt (t : ℝ) (g : Point) : Point :=
  (Real.cos t*g.1+Real.sin t*g.2,-Real.sin t*g.1+Real.cos t*g.2)

def reflectLocal (g : Point) : Point := (g.1,-g.2)

lemma projectAt_add (t : ℝ) (p q : Point) : projectAt t (add p q)=add (projectAt t p) (projectAt t q) := by
  apply Prod.ext <;> dsimp [projectAt,add] <;> ring

lemma projectAt_scale (t l : ℝ) (p : Point) : projectAt t (scale l p)=scale l (projectAt t p) := by
  apply Prod.ext <;> dsimp [projectAt,scale] <;> ring

lemma projectAt_primary (t z : ℝ) : projectAt t (primary z)=(Real.cos (z-t),Real.sin (z-t)) := by
  apply Prod.ext <;> dsimp [projectAt,primary] <;> rw [Real.cos_sub,Real.sin_sub] <;> ring

lemma projectAt_secondary (t z : ℝ) : projectAt t (secondary z)=(-Real.sin (z-t),Real.cos (z-t)) := by
  apply Prod.ext <;> dsimp [projectAt,secondary] <;> rw [Real.cos_sub,Real.sin_sub] <;> ring

@[simp] lemma projectAt_primary_self (t : ℝ) : projectAt t (primary t)=(1,0) := by
  simp [projectAt_primary]

@[simp] lemma projectAt_secondary_self (t : ℝ) : projectAt t (secondary t)=(0,1) := by
  simp [projectAt_secondary]

lemma reflectLocal_add (p q : Point) : reflectLocal (add p q)=add (reflectLocal p) (reflectLocal q) := by
  apply Prod.ext <;> dsimp [reflectLocal,add] <;> ring

lemma reflectLocal_scale (l : ℝ) (p : Point) : reflectLocal (scale l p)=scale l (reflectLocal p) := by
  apply Prod.ext <;> dsimp [reflectLocal,scale] <;> ring

lemma scalarSupport_reflectLocal (R : ℝ) (p : Point) :
    scalarSupport R (reflectLocal p).1 (reflectLocal p).2=scalarSupport R p.1 p.2 := by
  exact scalarSupport_neg_second

/-- Explicit lists used solely to simplify the already selected geometric axes. -/
def nwAxisAt (n w : ℝ) : Fin 4 → Point :=
  ![scale (-1) (primary (Real.pi+w)),scale (-1) (secondary (Real.pi+w)),
    primary (Real.pi/2+n),scale (-1) (secondary (Real.pi/2+n))]

def esAxisAt (e s : ℝ) : Fin 4 → Point :=
  ![scale (-1) (primary (3*Real.pi/2+s)),secondary (3*Real.pi/2+s),
    primary e,secondary e]

lemma balancedNWAxis_at {R : ℝ} (P : NormalizedPacking R) (u : Fin 4) :
    balancedNWAxis P u=nwAxisAt (P.helperAngle 1) (P.helperAngle 2) u := by
  have hn := P.phase_from_deviation 1
  have hw := P.phase_from_deviation 2
  simp only [matchingCardinal,cardinalCenter] at hn hw
  fin_cases u <;> simp [balancedNWAxis,nwAxisAt,preferredPairAxis,unsignedPairAxis,NWsigns,
    P.square_def,hn,hw,normalX,normalY,orientedSquare,primary,secondary]

lemma balancedESAxis_at {R : ℝ} (P : NormalizedPacking R) (v : Fin 4) :
    balancedESAxis P v=esAxisAt (P.helperAngle 0) (P.helperAngle 4) v := by
  have he := P.phase_from_deviation 0
  have hs := P.phase_from_deviation 4
  simp only [matchingCardinal,cardinalCenter,zero_add] at he hs
  fin_cases v <;> simp [balancedESAxis,esAxisAt,preferredPairAxis,unsignedPairAxis,ESsigns,
    P.square_def,he,hs,normalX,normalY,orientedSquare,primary,secondary]

lemma nw_north_projection (u : Fin 4) (n w : ℝ) :
    projectAt (Real.pi/2+n) (nwAxisAt n w u)=pairNorthSource u (n-w) := by
  fin_cases u <;> apply Prod.ext <;>
    simp [projectAt,nwAxisAt,pairNorthSource,primary,secondary,scale,
      Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub] <;>
    nlinarith [Real.sin_sq_add_cos_sq n,Real.sin_sq_add_cos_sq w]

lemma nw_west_projection (u : Fin 4) (n w : ℝ) :
    projectAt (Real.pi+w) (scale (-1) (nwAxisAt n w u))=pairWestSource u (n-w) := by
  fin_cases u <;> apply Prod.ext <;>
    simp [projectAt,nwAxisAt,pairWestSource,primary,secondary,scale,
      Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub] <;>
    nlinarith [Real.sin_sq_add_cos_sq n,Real.sin_sq_add_cos_sq w]

lemma es_east_projection (v : Fin 4) (e s : ℝ) :
    projectAt e (esAxisAt e s v)=reflectLocal (pairNorthSource v ((-e)-(-s))) := by
  fin_cases v <;> apply Prod.ext <;>
    simp [projectAt,esAxisAt,pairNorthSource,reflectLocal,primary,secondary,scale,
      Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,Real.cos_neg,Real.sin_neg,
      south_cos,south_sin] <;>
    nlinarith [Real.sin_sq_add_cos_sq e,Real.sin_sq_add_cos_sq s]

lemma es_south_projection (v : Fin 4) (e s : ℝ) :
    projectAt (3*Real.pi/2+s) (scale (-1) (esAxisAt e s v))=
      reflectLocal (pairWestSource v ((-e)-(-s))) := by
  fin_cases v <;> apply Prod.ext <;>
    simp [projectAt,esAxisAt,pairWestSource,reflectLocal,primary,secondary,scale,
      Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,Real.cos_neg,Real.sin_neg,
      south_cos,south_sin] <;>
    nlinarith [Real.sin_sq_add_cos_sq e,Real.sin_sq_add_cos_sq s]

lemma balanced_center_projection {R : ℝ} (P : NormalizedPacking R) (i : Fin 5) :
    projectAt (P.phase i) (balancedCenterAxis P i)=
      if P.ownBits i then (1,0) else (Real.cos (P.helperAngle i),-Real.sin (P.helperAngle i)) := by
  unfold balancedCenterAxis
  split_ifs
  · exact projectAt_primary_self _
  · rw [projectAt_primary]
    have he : cardinalCenter (matchingCardinal i)-P.phase i= -P.helperAngle i := by
      dsimp [NormalizedPacking.helperAngle]
      ring
    rw [he,Real.cos_neg,Real.sin_neg]

/-- Exact incidence forces before taking any frame projection. -/
def balancedForceArray {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) : Fin 6 → Point :=
  ![(0,0),
    add (scale (balancedBeta P) (balancedCenterAxis P 0)) (scale rStar (balancedESAxis P v)),
    add (scale (balancedAlpha P) (balancedCenterAxis P 1)) (scale rStar (balancedNWAxis P u)),
    add (scale (balancedGamma P) (balancedCenterAxis P 2))
      (add (scale rStar (scale (-1) (balancedNWAxis P u))) (scale (-mStar) (normalY (P.square 2)))),
    add (scale mStar (normalY (P.square 2))) (scale (-mStar) (normalY (P.square 4))),
    add (scale (balancedDelta P) (balancedCenterAxis P 4))
      (add (scale rStar (scale (-1) (balancedESAxis P v))) (scale mStar (normalY (P.square 4))))]

lemma balanced_force_array {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) (i : Fin 6) :
    (balancedSystem P u v).force i=balancedForceArray P u v i := by
  fin_cases i
  · exact balanced_central_force_zero P u v
  all_goals apply Prod.ext
  all_goals simp [System.force,balancedSystem,balancedForceArray,Fin.sum_univ_succ,add,scale]
  all_goals ring

lemma balanced_local_north {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    projectAt (P.phase 1) ((balancedSystem P u v).force 2)=
      pairNorthForce (P.ownBits 1) (P.ownBits 2) u (P.helperAngle 1) (P.helperAngle 2) := by
  rw [balanced_force_array]
  change projectAt (P.phase 1)
    (add (scale (balancedAlpha P) (balancedCenterAxis P 1)) (scale rStar (balancedNWAxis P u)))=_
  rw [projectAt_add,projectAt_scale,projectAt_scale,balanced_center_projection,balancedNWAxis_at]
  have hn : P.phase 1=Real.pi/2+P.helperAngle 1 := P.phase_from_deviation 1
  rw [hn,nw_north_projection]
  cases hb : P.ownBits 1 <;>
    simp [pairNorthForce,pairNorthBase,balancedAlpha,hb,add,scale]

lemma balanced_local_west {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    projectAt (P.phase 2) ((balancedSystem P u v).force 3)=
      pairWestForce (P.ownBits 1) (P.ownBits 2) u (P.helperAngle 1) (P.helperAngle 2) := by
  rw [balanced_force_array]
  change projectAt (P.phase 2)
    (add (scale (balancedGamma P) (balancedCenterAxis P 2))
      (add (scale rStar (scale (-1) (balancedNWAxis P u))) (scale (-mStar) (normalY (P.square 2)))))=_
  rw [projectAt_add,projectAt_scale,projectAt_add,projectAt_scale,projectAt_scale,
    balanced_center_projection,balancedNWAxis_at]
  have hy : normalY (P.square 2)=secondary (P.phase 2) := rfl
  rw [hy,projectAt_secondary_self]
  have hw : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  rw [hw,nw_west_projection]
  cases hb : P.ownBits 2 <;>
    simp [pairWestForce,pairWestBase,balancedGamma,hb,add,scale] <;> ring

lemma balanced_local_east {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    projectAt (P.phase 0) ((balancedSystem P u v).force 1)=
      reflectLocal (pairNorthForce (P.ownBits 0) (P.ownBits 4) v (-P.helperAngle 0) (-P.helperAngle 4)) := by
  rw [balanced_force_array]
  change projectAt (P.phase 0)
    (add (scale (balancedBeta P) (balancedCenterAxis P 0)) (scale rStar (balancedESAxis P v)))=_
  rw [projectAt_add,projectAt_scale,projectAt_scale,balanced_center_projection,balancedESAxis_at]
  have he : P.phase 0=P.helperAngle 0 := by
    simpa [matchingCardinal,cardinalCenter] using P.phase_from_deviation 0
  rw [he,es_east_projection]
  cases hb : P.ownBits 0 <;>
    simp [pairNorthForce,pairNorthBase,balancedBeta,hb,reflectLocal,add,scale,
      Real.cos_neg,Real.sin_neg] <;> ring

lemma balanced_local_south {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    projectAt (P.phase 4) ((balancedSystem P u v).force 5)=
      reflectLocal (pairWestForce (P.ownBits 0) (P.ownBits 4) v (-P.helperAngle 0) (-P.helperAngle 4)) := by
  rw [balanced_force_array]
  change projectAt (P.phase 4)
    (add (scale (balancedDelta P) (balancedCenterAxis P 4))
      (add (scale rStar (scale (-1) (balancedESAxis P v))) (scale mStar (normalY (P.square 4)))))=_
  rw [projectAt_add,projectAt_scale,projectAt_add,projectAt_scale,projectAt_scale,
    balanced_center_projection,balancedESAxis_at]
  have hy : normalY (P.square 4)=secondary (P.phase 4) := rfl
  rw [hy,projectAt_secondary_self]
  have hs : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  rw [hs,es_south_projection]
  cases hb : P.ownBits 4 <;>
    simp [pairWestForce,pairWestBase,balancedDelta,hb,reflectLocal,add,scale,
      Real.cos_neg,Real.sin_neg] <;> ring

lemma balanced_local_diagonal {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    projectAt (P.phase 3) ((balancedSystem P u v).force 4)=
      diagonalLocalForce (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle := by
  rw [balanced_force_array]
  change projectAt (P.phase 3)
    (add (scale mStar (normalY (P.square 2))) (scale (-mStar) (normalY (P.square 4))))=_
  have hW : normalY (P.square 2)=secondary (P.phase 2) := rfl
  have hS : normalY (P.square 4)=secondary (P.phase 4) := rfl
  rw [projectAt_add,projectAt_scale,projectAt_scale,hW,hS,projectAt_secondary,projectAt_secondary]
  have hw : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hs : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have hd : P.phase 3=Real.pi+P.diagonalAngle := by dsimp [NormalizedPacking.diagonalAngle]; ring
  rw [hw,hs,hd]
  apply Prod.ext <;>
    simp [add,scale,diagonalLocalForce,Real.sin_sub,Real.cos_sub,Real.sin_add,Real.cos_add,
      south_cos,south_sin] <;> ring

end SquaresInCircles.Six.Stress

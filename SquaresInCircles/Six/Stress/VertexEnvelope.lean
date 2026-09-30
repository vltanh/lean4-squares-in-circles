import SquaresInCircles.Six.Stress.BalancedPair
import SquaresInCircles.Six.Equality.SupportMaximizers

/-!
# A smooth lower bound near the candidate and its exact base value

The signed far-vertex expression is an upper support in every direction; no
unproved sign or cap-branch selection is used to replace the exact support.
At the candidate it agrees with the exact support, by explicit feasible
supporting centers and the active-radius identities.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress

lemma orderedSupport_le_vertex {R U V : ℝ} (hR : 1≤R) (hU : 0≤U) (hV : 0≤V) :
    orderedSupport R U V ≤ R*Real.sqrt (U^2+V^2)-(U+V)/2 := by
  have hrad : 0≤R^2-1/4 := by nlinarith [sq_nonneg (R-1)]
  have hid := Real.sq_sqrt hrad
  have hround := dot_le_radius (v := (U,V))
    (p := (Real.sqrt (R^2-1/4),(1:ℝ)/2)) (by linarith)
    (by dsimp [normSq]; nlinarith [hid])
  dsimp [dot,vectorLength,normSq] at hround
  unfold orderedSupport
  split_ifs
  · dsimp [rhoAt]
    nlinarith
  · exact le_rfl

lemma scalarSupport_le_vertex {R x y : ℝ} (hR : 1≤R) :
    scalarSupport R x y ≤ R*Real.sqrt (x^2+y^2)-(|x|+|y|)/2 := by
  unfold scalarSupport
  split_ifs
  · simpa only [sq_abs] using orderedSupport_le_vertex hR (abs_nonneg x) (abs_nonneg y)
  · have h := orderedSupport_le_vertex hR (abs_nonneg y) (abs_nonneg x)
    simpa only [sq_abs,add_comm] using h

def northVertex (x y : ℝ) : ℝ := Six.radius*Real.sqrt (x^2+y^2)-(x-y)/2

/-- The smooth expression used in the local pair proof is always an upper
support, whether or not the force currently has the candidate signs. -/
lemma scalarSupport_le_northVertex (x y : ℝ) :
    scalarSupport Six.radius x y ≤ northVertex x y := by
  have h := scalarSupport_le_vertex (x := x) (y := y)
    (show 1≤Six.radius by linarith [radius_gt_three_halves])
  dsimp [northVertex]
  linarith [le_abs_self x,neg_le_abs y]

@[simp] lemma scalarSupport_neg_first (R x y : ℝ) : scalarSupport R (-x) y=scalarSupport R x y := by
  simp [scalarSupport,abs_neg]

@[simp] lemma scalarSupport_neg_second (R x y : ℝ) : scalarSupport R x (-y)=scalarSupport R x y := by
  simp [scalarSupport,abs_neg]

lemma length_of_scaled_radius {p : Point} {l R : ℝ}
    (hl : 0≤l) (hR : 0≤R) (hp : normSq p=R^2) :
    vectorLength (scale l p)=l*R := by
  have hn : normSq (scale l p)=(l*R)^2 := by
    calc
      normSq (scale l p)=l^2*normSq p := by dsimp [normSq,scale]; ring
      _=(l*R)^2 := by rw [hp]; ring
  rw [vectorLength,hn,Real.sqrt_sq (mul_nonneg hl hR)]

lemma radius_length_eq_dot_of_ray {g p : Point} {l R : ℝ}
    (hl : 0≤l) (hR : 0≤R) (hp : normSq p=R^2) (hg : g=scale l p) :
    R*vectorLength g=dot g p := by
  rw [hg,length_of_scaled_radius hl hR hp]
  calc
    R*(l*R)=l*R^2 := by ring
    _=l*normSq p := by rw [hp]
    _=dot (scale l p) p := by dsimp [dot,scale,normSq]; ring

lemma northVertex_candidate_north : northVertex 1 (-rStar)=1+Six.sStar+rStar*Six.sStar := by
  let p : Point := (Six.sStar+3/2,-(Six.sStar+1/2))
  have hp : normSq p=Six.radius^2 := by
    dsimp [p,normSq]
    nlinarith [Six.east_radius_identity,Six.radius_sq]
  have hg : (1,-rStar)=scale (1/(Six.sStar+3/2)) p := by
    apply Prod.ext
    · dsimp [scale,p]
      field_simp [ne_of_gt rStar_den_pos]
    · dsimp [scale,p,rStar]
      ring
  have hd := radius_length_eq_dot_of_ray
    (show 0≤1/(Six.sStar+3/2) by positivity) Six.radius_pos.le hp hg
  dsimp [vectorLength,normSq,dot,p] at hd
  dsimp [northVertex]
  nlinarith

lemma northVertex_candidate_west :
    northVertex (1+rStar) (-mStar)=(1+rStar)*(1-Six.sStar)+mStar*Six.tStar := by
  let p : Point := (3/2-Six.sStar,-(Six.tStar+1/2))
  let l : ℝ := (1+rStar)/(3/2-Six.sStar)
  have hl : 0≤l := (div_pos one_add_rStar_pos kStar_den_pos).le
  have hp : normSq p=Six.radius^2 := by
    dsimp [p,normSq]
    nlinarith [Six.west_radius_identity,Six.radius_sq]
  have hg : (1+rStar,-mStar)=scale l p := by
    apply Prod.ext
    · dsimp [scale,l,p]
      field_simp [ne_of_gt kStar_den_pos]
    · dsimp [scale,l,p,mStar,kStar]
      ring
  have hd := radius_length_eq_dot_of_ray hl Six.radius_pos.le hp hg
  dsimp [vectorLength,normSq,dot,p] at hd
  dsimp [northVertex]
  nlinarith

lemma candidate_north_exact_support :
    scalarSupport Six.radius 1 (-rStar)=northVertex 1 (-rStar) := by
  have hc : (|1+Six.sStar|+1/2)^2+(|-Six.sStar|+1/2)^2≤Six.radius^2 := by
    rw [abs_of_pos (by linarith [Six.sStar_pos]),abs_neg,abs_of_pos Six.sStar_pos]
    nlinarith [Six.east_radius_identity,Six.radius_sq]
  have hl := scalar_center_support (x := (1:ℝ)) (y := -rStar) radius_gt_half hc
  have hu := scalarSupport_le_northVertex 1 (-rStar)
  rw [northVertex_candidate_north] at hu ⊢
  nlinarith

lemma candidate_west_exact_support :
    scalarSupport Six.radius (1+rStar) (-mStar)=northVertex (1+rStar) (-mStar) := by
  have hs : 0<1-Six.sStar := by linarith [Six.sStar_lt_fifth]
  have ht : 0<Six.tStar := by linarith [Six.tStar_bounds.1]
  have hc : (|1-Six.sStar|+1/2)^2+(|-Six.tStar|+1/2)^2≤Six.radius^2 := by
    rw [abs_of_pos hs,abs_neg,abs_of_pos ht]
    nlinarith [Six.west_radius_identity,Six.radius_sq]
  have hl := scalar_center_support (x := 1+rStar) (y := -mStar) radius_gt_half hc
  have hu := scalarSupport_le_northVertex (1+rStar) (-mStar)
  rw [northVertex_candidate_west] at hu ⊢
  nlinarith

lemma pairBase_vertex_identity :
    2+rStar+mStar/2-northVertex 1 (-rStar)-northVertex (1+rStar) (-mStar)=pairBase := by
  rw [northVertex_candidate_north,northVertex_candidate_west]
  dsimp [pairBase]
  ring

lemma pairValue_candidate (no wo : Bool) {u : Fin 4} (hu : u=0 ∨ u=3) :
    pairValue no wo u 0 0=pairBase := by
  have hf := pair_candidate_forces no wo hu
  rw [pairValue,pairThreshold_zero,hf.1,hf.2,
    candidate_north_exact_support,candidate_west_exact_support]
  exact pairBase_vertex_identity

/-- This identity anchors all scalar lower bounds at the exact candidate. -/
lemma pairBase_diagonal_identity :
    2*pairBase+(2*Six.hStar*mStar)*(1-rhoStar)=0 := by
  rw [rhoStar_eq_two_h_d]
  dsimp [pairBase,Six.dStar]
  linear_combination (-4*mStar*(1/2+Six.hStar-Six.tStar))*Six.hStar_sq

lemma pairBase_pos : 0<pairBase := by
  dsimp [pairBase]
  exact mul_pos mStar_pos (by linarith [Six.tStar_bounds.2])

end SquaresInCircles.Six.Stress

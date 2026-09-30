module
public import SquaresInCircles.Six.Stress.StrictSupport

@[expose] public section

/-!
# Unique support maximizers needed for equality reconstruction

A far-vertex support equality forces that vertex to the unique support point of
the disk. The axial cap equality forces the transverse center coordinate to
zero. These are statements about the original contained square, not properties
assumed of a normalized or optimal configuration.
-/

noncomputable section
namespace SquaresInCircles.Six.Equality
open Stress

lemma disk_support_point_unique {g p : Point} {R : ℝ}
    (hR : 0 ≤ R) (hg : g≠(0,0)) (hp : normSq p≤R^2)
    (he : dot g p=R*vectorLength g) : p=scale (R/vectorLength g) g := by
  let L := vectorLength g
  have hL0 : 0<L := Real.sqrt_pos.mpr (normSq_pos_of_ne hg)
  have hL : L^2=normSq g := vectorLength_sq g
  have hmult := mul_le_mul_of_nonneg_left hp (sq_nonneg L)
  have hidentity : normSq (sub (scale L p) (scale R g)) =
      L^2*normSq p+R^2*normSq g-2*L*R*dot g p := by
    dsimp [normSq,sub,scale,dot]
    ring
  have hzero : normSq (sub (scale L p) (scale R g))≤0 := by
    rw [hidentity,← hL,he]
    change L^2*normSq p+R^2*L^2-2*L*R*(R*L)≤0
    nlinarith only [hmult]
  have hvec : sub (scale L p) (scale R g)=(0,0) := by
    by_contra hn
    exact (not_lt_of_ge hzero) (normSq_pos_of_ne hn)
  have hx := congrArg Prod.fst hvec
  have hy := congrArg Prod.snd hvec
  dsimp [sub,scale] at hx hy
  apply Prod.ext
  · change p.1=(R/L)*g.1
    field_simp [ne_of_gt hL0]
    nlinarith only [hx]
  · change p.2=(R/L)*g.2
    field_simp [ne_of_gt hL0]
    nlinarith only [hy]

/-- Choose the supporting corner by its two local signs. The hypotheses allow
zero projections, but active candidate vertex forces have both projections
nonzero, so the sign choice is then unique as well. -/
theorem center_eq_of_vertex_support {S : UnitSquare} {g : Point} {R sx sy : ℝ}
    (hR : 0≤R) (hg : g≠(0,0))
    (hcontain : ∀ p, closedSquare S p → inDisk (0,0) R p)
    (hsx : |sx|=1) (hsy : |sy|=1)
    (hx : sx*frameX S g=|frameX S g|)
    (hy : sy*frameY S g=|frameY S g|)
    (he : dot g S.center=vertexSupport R S g) :
    S.center=sub (scale (R/vectorLength g) g) (rotate S (sx/2,sy/2)) := by
  let p : Point := add S.center (rotate S (sx/2,sy/2))
  have hp : closedSquare S p := by
    constructor
    · rw [show localX S p=sx/2 from localX_rotated S (sx/2) (sy/2)]
      simp [abs_div,hsx]
    · rw [show localY S p=sy/2 from localY_rotated S (sx/2) (sy/2)]
      simp [abs_div,hsy]
  have hproj := projection_local S g p
  rw [dot_sub_right] at hproj
  have hlocx : localX S p=sx/2 := localX_rotated S (sx/2) (sy/2)
  have hlocy : localY S p=sy/2 := localY_rotated S (sx/2) (sy/2)
  rw [hlocx,hlocy] at hproj
  have hdot : dot g p=R*vectorLength g := by
    dsimp [vertexSupport,width] at he
    nlinarith [hx,hy]
  have hnorm : normSq p≤R^2 := by simpa [inDisk,sub] using hcontain p hp
  have hpoint := disk_support_point_unique hR hg hnorm hdot
  have hpx := congrArg Prod.fst hpoint
  have hpy := congrArg Prod.snd hpoint
  apply Prod.ext
  · dsimp [p,add,scale] at hpx
    dsimp [sub,scale]
    linarith
  · dsimp [p,add,scale] at hpy
    dsimp [sub,scale]
    linarith

lemma rotate_frame_coordinates (S : UnitSquare) (p : Point) :
    rotate S (frameX S p,frameY S p)=p := by
  apply Prod.ext
  · dsimp [rotate,frameX,frameY]
    linear_combination p.1*S.unit
  · dsimp [rotate,frameX,frameY]
    linear_combination p.2*S.unit

lemma rhoAt_identity {R : ℝ} (hR : 1≤R) : (rhoAt R+1/2)^2+1/4=R^2 := by
  have hs := Real.sq_sqrt (show 0≤R^2-1/4 by nlinarith [sq_nonneg (R-1)])
  dsimp [rhoAt]
  nlinarith

lemma rhoAt_pos {R : ℝ} (hR : 1≤R) : 0<rhoAt R := by
  have hs := Real.sqrt_lt_sqrt (show (0:ℝ)≤(1/2)^2 by norm_num)
    (show (1/2:ℝ)^2<R^2-1/4 by nlinarith [sq_nonneg (R-1)])
  rw [Real.sqrt_sq (by norm_num)] at hs
  dsimp [rhoAt]
  linarith

/-- On the axial cap, the active primary bound leaves no transverse slack. -/
theorem center_eq_of_primary_cap {S : UnitSquare} {R : ℝ}
    (hR : 1≤R) (hcontain : ∀ p, closedSquare S p → inDisk (0,0) R p)
    (ha : frameX S S.center=rhoAt R) : S.center=rotate S (rhoAt R,0) := by
  have hc := phi_le_of_contained S (0,0) R hcontain
  rw [alpha_frame_center,beta_frame_center,ha,abs_of_pos (rhoAt_pos hR)] at hc
  have hid := rhoAt_identity hR
  have hbabs : |frameY S S.center|=0 := by
    dsimp [phi] at hc
    nlinarith [abs_nonneg (frameY S S.center),sq_nonneg |frameY S S.center|]
  have hb := abs_eq_zero.mp hbabs
  calc
    S.center=rotate S (frameX S S.center,frameY S S.center) :=
      (rotate_frame_coordinates S S.center).symm
    _=rotate S (rhoAt R,0) := by rw [ha,hb]

lemma scalarSupport_positive_axis {R l : ℝ} (hl : 0≤l) :
    scalarSupport R l 0=rhoAt R*l := by
  unfold scalarSupport orderedSupport
  simp only [abs_zero,abs_of_nonneg hl,if_pos hl,zero_pow (by decide : (2:ℕ)≠0),
    add_zero,Real.sqrt_sq hl,mul_zero,if_pos hl]

lemma primary_force_components (S : UnitSquare) (l : ℝ) :
    frameX S (scale l (normalX S))=l ∧ frameY S (scale l (normalX S))=0 := by
  constructor
  · dsimp [frameX,scale,normalX]
    linear_combination l*S.unit
  · dsimp [frameY,scale,normalX]
    ring

/-- Equality of exact support for a positive primary force determines the
whole center, not just its primary projection. -/
theorem center_eq_of_axial_support {S : UnitSquare} {R l : ℝ}
    (hR : 1≤R) (hl : 0<l)
    (hcontain : ∀ p, closedSquare S p → inDisk (0,0) R p)
    (he : dot (scale l (normalX S)) S.center =
      exactSupport R S (scale l (normalX S))) :
    S.center=rotate S (rhoAt R,0) := by
  have hcomponents := primary_force_components S l
  rw [exactSupport,hcomponents.1,hcomponents.2,scalarSupport_positive_axis hl.le] at he
  have hproj : dot (scale l (normalX S)) S.center=l*frameX S S.center := by
    dsimp [dot,scale,normalX,frameX]
    ring
  rw [hproj] at he
  have ha : frameX S S.center=rhoAt R := by nlinarith [hl]
  exact center_eq_of_primary_cap hR hcontain ha

end SquaresInCircles.Six.Equality

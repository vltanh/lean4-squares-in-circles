import SquaresInCircles.Six.Stress.StrictSupport

/-!
# Equality in the support bounds

For `g ≠ 0`, a point of the disk of radius `R` at which the linear form
`⟨g, ·⟩` reaches `R |g|` is the point `(R/|g|) g`. So if the far-vertex
support of a contained square is attained, its far vertex is that point, and
the centre of the square is determined. On a positive axis the support of the
force `(l, 0)` is `rhoAt R * l`.
-/

noncomputable section
namespace SquaresInCircles.Six.Equality
open Stress

/-- For `g ≠ 0`, a point `p` of the disk of radius `R` with `⟨g, p⟩ = R |g|`
is `(R/|g|) g`. -/
lemma disk_support_point_unique {g p : Point} {R : ℝ}
    (hg : g≠(0,0)) (hp : normSq p≤R^2)
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

/-- If the far-vertex support of a contained square is attained, then with the
signs `sx`, `sy` of the force in the frame of the square, the centre is
`(R/|g|) g` minus the half-diagonal to the vertex of those signs. -/
theorem center_eq_of_vertex_support {S : UnitSquare} {g : Point} {R sx sy : ℝ}
    (hg : g≠(0,0))
    (hcontain : ∀ p, closedSquare S p → inDisk (0,0) R p)
    (hsx : |sx|=1) (hsy : |sy|=1)
    (hx : sx*frameX S g=|frameX S g|)
    (hy : sy*frameY S g=|frameY S g|)
    (he : dot g S.center=vertexSupport R S g) :
    S.center=sub (scale (R/vectorLength g) g) (rotate S (sx/2,sy/2)) := by
  let p : Point := add S.center (rotate S (sx/2,sy/2))
  have hp : closedSquare S p := by
    constructor
    · rw [show localX S p=sx/2 from localX_rotated S (sx/2,sy/2)]
      simp [abs_div,hsx]
    · rw [show localY S p=sy/2 from localY_rotated S (sx/2,sy/2)]
      simp [abs_div,hsy]
  have hproj := projection_local S g p
  rw [dot_sub_right] at hproj
  have hlocx : localX S p=sx/2 := localX_rotated S (sx/2,sy/2)
  have hlocy : localY S p=sy/2 := localY_rotated S (sx/2,sy/2)
  rw [hlocx,hlocy] at hproj
  have hdot : dot g p=R*vectorLength g := by
    dsimp [vertexSupport,width] at he
    nlinarith [hx,hy]
  have hnorm : normSq p≤R^2 := by simpa [inDisk,sub] using hcontain p hp
  have hpoint := disk_support_point_unique hg hnorm hdot
  have hpx := congrArg Prod.fst hpoint
  have hpy := congrArg Prod.snd hpoint
  apply Prod.ext
  · dsimp [p,add,scale] at hpx
    dsimp [sub,scale]
    linarith
  · dsimp [p,add,scale] at hpy
    dsimp [sub,scale]
    linarith

/-- On a positive axis the support of `(l, 0)` is `rhoAt R * l`. -/
lemma scalarSupport_positive_axis {R l : ℝ} (hl : 0≤l) :
    scalarSupport R l 0=rhoAt R*l := by
  unfold scalarSupport orderedSupport
  simp only [abs_zero,abs_of_nonneg hl,zero_pow (by decide : (2:ℕ)≠0),
    add_zero,Real.sqrt_sq hl,mul_zero,ite_eq_left hl]

end SquaresInCircles.Six.Equality

module

public import SquaresInCircles.Eight.GeometricModel.Basic
public import SquaresInCircles.Eight.ExactFamily.Coordinates

/-!
# The exact two-height form of the five-corner model

Uncompiled source draft. The upper chord has horizontal length three. Its
two circle equations eliminate the radius and both upper square roots.
Only the lower right and lower left circle roots remain.

The domain below uses nonnegative heights and squared-radius inequalities.
It has no decimal coordinate window and no auxiliary radius bracket. The
strict upper bound two specifies the geometric branch on which the two
upper corners are above the horizontal axis.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GeometricModel

theorem upperRight_add_upperLeft (u v : ℝ) :
    upperRightFromHeights u v + upperLeftFromHeights u v = 3 := by
  dsimp [upperRightFromHeights, upperLeftFromHeights]
  ring

theorem upperRight_circle (u v : ℝ) :
    upperRightFromHeights u v ^ 2 + (2-u) ^ 2 = twoHeightRadiusSq u v := by
  dsimp [upperRightFromHeights, twoHeightRadiusSq]
  ring

theorem upperLeft_circle (u v : ℝ) :
    upperLeftFromHeights u v ^ 2 + (2-v) ^ 2 = twoHeightRadiusSq u v := by
  dsimp [upperLeftFromHeights, twoHeightRadiusSq]
  ring

theorem twoHeightRadiusSq_ge_nine_quarters (u v : ℝ) :
    9/4 ≤ twoHeightRadiusSq u v := by
  have hprod := mul_nonneg (sq_nonneg (u-v)) (sq_nonneg (4-u-v))
  dsimp [twoHeightRadiusSq]
  nlinarith [sq_nonneg (u-v), sq_nonneg (4-u-v)]

theorem twoHeightRadiusSq_pos (u v : ℝ) : 0 < twoHeightRadiusSq u v := by
  linarith [twoHeightRadiusSq_ge_nine_quarters u v]

/-- The formula follows from just the two upper circles and their span.
No critical-point equation is used. -/
theorem twoHeight_of_upper_circles {q u v U V : ℝ}
    (hU : U^2+(2-u)^2=q) (hV : V^2+(2-v)^2=q) (hspan : U+V=3) :
    U=upperRightFromHeights u v ∧ V=upperLeftFromHeights u v ∧
      q=twoHeightRadiusSq u v := by
  have hV' : V=3-U := by linarith
  rw [hV'] at hV
  have hU' : U=upperRightFromHeights u v := by
    dsimp [upperRightFromHeights]
    nlinarith [hU, hV]
  have hV'' : V=upperLeftFromHeights u v := by
    linarith [upperRight_add_upperLeft u v]
  refine ⟨hU', hV'', ?_⟩
  rw [← upperRight_circle u v, ← hU']
  exact hU.symm

/-- Two lower heights and the actual angle, rather than nested roots or a
half-angle variable. -/
structure TwoHeights where
  u : ℝ
  v : ℝ
  angle : ℝ

namespace TwoHeights

def radiusSq (p : TwoHeights) : ℝ := twoHeightRadiusSq p.u p.v
def radius (p : TwoHeights) : ℝ := Real.sqrt p.radiusSq
def r (p : TwoHeights) : ℝ := Real.sqrt (p.radiusSq-p.u^2)
def w (p : TwoHeights) : ℝ := Real.sqrt (p.radiusSq-p.v^2)
def U (p : TwoHeights) : ℝ := upperRightFromHeights p.u p.v
def V (p : TwoHeights) : ℝ := upperLeftFromHeights p.u p.v
def K₁ (p : TwoHeights) : ℝ :=
  2-Real.cos p.angle*(p.r-1)+Real.sin p.angle*p.u
def K₂ (p : TwoHeights) : ℝ :=
  1+Real.cos p.angle*p.v-Real.sin p.angle*(p.w-1)
def defect (p : TwoHeights) : ℝ := p.K₁^2+p.K₂^2-p.radiusSq

structure InDomain (p : TwoHeights) : Prop where
  u_nonneg : 0 ≤ p.u
  v_nonneg : 0 ≤ p.v
  u_sq_le : p.u^2 ≤ p.radiusSq
  v_sq_le : p.v^2 ≤ p.radiusSq
  radiusSq_lt_four : p.radiusSq < 4
  angle_lower : 0 ≤ p.angle
  angle_upper : p.angle ≤ Real.pi/4

theorem radiusSq_pos (p : TwoHeights) : 0 < p.radiusSq :=
  twoHeightRadiusSq_pos p.u p.v

theorem radius_pos (p : TwoHeights) : 0 < p.radius :=
  Real.sqrt_pos.mpr p.radiusSq_pos

@[simp] theorem radius_sq (p : TwoHeights) : p.radius^2=p.radiusSq :=
  Real.sq_sqrt p.radiusSq_pos.le

theorem InDomain.heights_lt_two {p : TwoHeights} (h : p.InDomain) :
    p.u < 2 ∧ p.v < 2 := by
  constructor <;> nlinarith [h.u_sq_le, h.v_sq_le, h.radiusSq_lt_four]

theorem InDomain.radius_lt_two {p : TwoHeights} (h : p.InDomain) :
    p.radius < 2 := by
  nlinarith [p.radius_sq, h.radiusSq_lt_four]

theorem InDomain.sqrt_domain {p : TwoHeights} (h : p.InDomain) :
    0 ≤ p.u ∧ p.u ≤ p.radius ∧ 0 ≤ p.v ∧ p.v ≤ p.radius ∧
      p.radius < 2 ∧ 0 ≤ p.angle ∧ p.angle ≤ Real.pi/4 := by
  refine ⟨h.u_nonneg, ?_, h.v_nonneg, ?_, h.radius_lt_two,
    h.angle_lower, h.angle_upper⟩ <;>
    nlinarith [p.radius_pos, p.radius_sq, h.u_sq_le, h.v_sq_le]

theorem inDomain_iff (p : TwoHeights) : p.InDomain ↔
    0 ≤ p.u ∧ p.u ≤ p.radius ∧ 0 ≤ p.v ∧ p.v ≤ p.radius ∧
      p.radius < 2 ∧ 0 ≤ p.angle ∧ p.angle ≤ Real.pi/4 := by
  refine ⟨fun h => h.sqrt_domain, ?_⟩
  rintro ⟨hu, hur, hv, hvr, hr, ht, ht'⟩
  refine ⟨hu, hv, ?_, ?_, ?_, ht, ht'⟩ <;>
    nlinarith [p.radius_pos, p.radius_sq]

theorem InDomain.lower_circles {p : TwoHeights} (h : p.InDomain) :
    p.r^2+p.u^2=p.radiusSq ∧ p.w^2+p.v^2=p.radiusSq := by
  constructor
  · have hs := Real.sq_sqrt (sub_nonneg.mpr h.u_sq_le)
    dsimp only [r]
    linarith
  · have hs := Real.sq_sqrt (sub_nonneg.mpr h.v_sq_le)
    dsimp only [w]
    linarith

theorem upper_circles (p : TwoHeights) :
    p.U^2+(2-p.u)^2=p.radiusSq ∧ p.V^2+(2-p.v)^2=p.radiusSq ∧ p.U+p.V=3 :=
  ⟨upperRight_circle p.u p.v, upperLeft_circle p.u p.v,
    upperRight_add_upperLeft p.u p.v⟩

/-- Positive upper coordinates are consequences of the natural domain.
Their sum is three, while each has absolute value less than two. -/
theorem InDomain.upper_coordinates {p : TwoHeights} (h : p.InDomain) :
    1 < p.U ∧ p.U < 2 ∧ 1 < p.V ∧ p.V < 2 ∧
      0 < 2-p.u ∧ 0 < 2-p.v := by
  obtain ⟨hU, hV, hsum⟩ := p.upper_circles
  have hU' : p.U < 2 := by
    nlinarith [h.radiusSq_lt_four, sq_nonneg (2-p.u)]
  have hV' : p.V < 2 := by
    nlinarith [h.radiusSq_lt_four, sq_nonneg (2-p.v)]
  obtain ⟨hu, hv⟩ := h.heights_lt_two
  exact ⟨by linarith, hU', by linarith, hV', by linarith, by linarith⟩

def framePoint (t a b : ℝ) : Point :=
  (Real.cos t*a-Real.sin t*b, Real.sin t*a+Real.cos t*b)

theorem framePoint_norm (t a b : ℝ) : normSq (framePoint t a b)=a^2+b^2 := by
  dsimp [normSq, framePoint]
  linear_combination (a^2+b^2) * Real.sin_sq_add_cos_sq t

theorem framePoint_e (t a b : ℝ) : projection (e t) (framePoint t a b)=a := by
  dsimp [projection, e, framePoint]
  linear_combination a * Real.sin_sq_add_cos_sq t

theorem framePoint_f (t a b : ℝ) : projection (f t) (framePoint t a b)=b := by
  dsimp [projection, f, framePoint]
  linear_combination b * Real.sin_sq_add_cos_sq t

def chain (p : TwoHeights) : FiveCorner where
  angle := p.angle
  point := ![(p.r,-p.u), (p.U,2-p.u), (-p.V,2-p.v), (-p.w,-p.v),
    framePoint p.angle (-p.K₁) (-p.K₂)]

theorem chain_spans {p : TwoHeights} (h : p.InDomain) : p.chain.spans := by
  have hsum := p.upper_circles.2.2
  have he := framePoint_e p.angle (-p.K₁) (-p.K₂)
  have hf := framePoint_f p.angle (-p.K₁) (-p.K₂)
  refine ⟨h.angle_lower, h.angle_upper, ?_, ?_, ?_, ?_, ?_⟩
  · change 2 ≤ (2-p.u)-(-p.u)
    linarith
  · change 3 ≤ p.U-(-p.V)
    linarith
  · change 2 ≤ (2-p.v)-(-p.v)
    linarith
  · change 1+Real.sin p.angle ≤
      projection (f p.angle)
        (sub (-p.w,-p.v) (framePoint p.angle (-p.K₁) (-p.K₂)))
    dsimp [projection, f, sub] at hf ⊢
    dsimp only [K₂] at hf
    nlinarith
  · change 2+Real.cos p.angle ≤
      projection (e p.angle)
        (sub (p.r,-p.u) (framePoint p.angle (-p.K₁) (-p.K₂)))
    dsimp [projection, e, sub] at he ⊢
    dsimp only [K₁] at he
    nlinarith

theorem chain_first_four_on_circle {p : TwoHeights} (h : p.InDomain)
    (i : Fin 4) : normSq (p.chain.point i.castSucc)=p.radiusSq := by
  obtain ⟨hr, hw⟩ := h.lower_circles
  obtain ⟨hU, hV, hspan⟩ := p.upper_circles
  fin_cases i <;> simp [chain, normSq] <;> nlinarith

theorem chain_fifth_norm (p : TwoHeights) :
    normSq (p.chain.point 4)=p.K₁^2+p.K₂^2 := by
  simp [chain, framePoint_norm]

/-- The entire fifth-circle condition is one scalar inequality. -/
theorem chain_fits_iff {p : TwoHeights} (h : p.InDomain) :
    p.chain.fits p.radius ↔ p.defect ≤ 0 := by
  constructor
  · intro hfit
    have hlast := hfit.2 4
    rw [chain_fifth_norm, radius_sq] at hlast
    exact sub_nonpos.mpr hlast
  · intro hdef
    refine ⟨p.radius_pos.le, ?_⟩
    intro i
    rw [radius_sq]
    fin_cases i
    · exact (chain_first_four_on_circle h 0).le
    · exact (chain_first_four_on_circle h 1).le
    · exact (chain_first_four_on_circle h 2).le
    · exact (chain_first_four_on_circle h 3).le
    · rw [chain_fifth_norm]
      exact sub_nonpos.mp hdef

theorem feasible_radius {p : TwoHeights} (h : p.InDomain) (hdef : p.defect ≤ 0) :
    p.radius ∈ FiveCorner.feasibleRadii :=
  ⟨p.chain, chain_spans h, (chain_fits_iff h).mpr hdef⟩

end TwoHeights

/-- The older coordinate chain has the same polynomial radius. This
identity is valid for every chain, before stationarity or localization. -/
theorem coordinate_chain_two_heights {d : ExactFamily.Coordinates} (hd : d.IsChain) :
    d.x₂=upperRightFromHeights (-d.y) (-d.y₄) ∧
      -d.x₃=upperLeftFromHeights (-d.y) (-d.y₄) ∧
      d.q=twoHeightRadiusSq (-d.y) (-d.y₄) := by
  apply twoHeight_of_upper_circles
  · simpa only [sub_neg_eq_add, add_comm] using hd.second_circle
  · have h := hd.third_circle
    dsimp only [ExactFamily.Coordinates.y₄]
    nlinarith
  · dsimp [ExactFamily.Coordinates.x₃]
    ring

end SquaresInCircles.Eight.GeometricModel

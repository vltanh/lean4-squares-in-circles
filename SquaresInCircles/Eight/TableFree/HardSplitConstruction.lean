module

public import SquaresInCircles.Eight.TableFree.HardSplitCap

/-!
# Realizing the hard-quarter endpoint split

Uncompiled draft.  Original weak hard-quarter witnesses and the separate
actual circles imply the cap comparison.  The construction changes only
the two middle centers and their common frame.  Its neighboring G and T
centers are the original centers, and its two hard projections are exact
equalities for the original owner axes 0 and 2.

The concrete theorem below preserves each original middle corner radius,
so a strict loss at either middle anchor is preserved.  An interior split
gives strict slack on the actual aligned AB separator.  This module makes
no assertion about nonneighbor packing or about the global front end that
produces these signs and aligned zero edges.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HardSplitCap

theorem primary_lower_of_contact {D θ X Z : ℝ}
    (hD : 3/5 ≤ D) (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hZ : 0 ≤ Z)
    (hcontact : D ≤ (X-1)*Real.cos θ-Z*Real.sin θ) : D+1 ≤ X := by
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc0 : 0 < Real.cos θ := by linarith
  have hZs := mul_nonneg hZ hs
  have hX : 0 ≤ X-1 := by
    by_contra! hn
    have hp := mul_neg_of_neg_of_pos hn hc0
    linarith
  have hp := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hX
  nlinarith

/-- Feasibility of the scalar cap is a consequence of the original
contact and corner inequality, including when that inequality is slack. -/
theorem feasible_of_weak_contact {q D θ X Z : ℝ}
    (hQ : q ≤ qCap) (hD : 3/5 ≤ D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hZ : 1/2 ≤ Z)
    (hcontact : D ≤ (X-1)*Real.cos θ-Z*Real.sin θ)
    (hcircle : X^2+Z^2 ≤ q) : Feasible q D := by
  have hX := primary_lower_of_contact hD hθ (by linarith) hcontact
  have hXs := pow_le_pow_left₀ (by linarith : 0 ≤ D+1) hX 2
  have hZs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hZ 2
  exact ⟨hQ,hD,by nlinarith⟩

/-- Rotate the original corner, retain its weak contact, and use its own
circle.  The perpendicular coordinate is bounded by the actual-q root. -/
theorem cap_majorizes_weak_contact {q D θ X Z : ℝ}
    (h : Feasible q D) (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hZ : 0 ≤ Z)
    (hcontact : D ≤ (X-1)*Real.cos θ-Z*Real.sin θ)
    (hcircle : X^2+Z^2 ≤ q) : Z ≤ cap q D θ := by
  let P := X*Real.cos θ-Z*Real.sin θ
  let R := X*Real.sin θ+Z*Real.cos θ
  have hX := primary_lower_of_contact h.transverse hθ hZ hcontact
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc0 : 0 ≤ Real.cos θ := by linarith
  have hP : contact D θ ≤ P := by dsimp [P,contact]; nlinarith
  have hP2 := pow_le_pow_left₀ (contact_pos h hθ).le hP 2
  have hR0 : 0 ≤ R := by
    exact add_nonneg (mul_nonneg (by linarith [h.transverse]) hs)
      (mul_nonneg hZ hc0)
  have hrotation : P^2+R^2=X^2+Z^2 := by
    dsimp [P,R]
    calc
      (X*Real.cos θ-Z*Real.sin θ)^2+(X*Real.sin θ+Z*Real.cos θ)^2 =
          (X^2+Z^2)*((Real.sin θ)^2+(Real.cos θ)^2) := by ring
      _ = X^2+Z^2 := by rw [Real.sin_sq_add_cos_sq,mul_one]
  have hR : R ≤ root q D θ := by
    have hw := root_pos h hθ
    have hw2 := root_sq h hθ
    nlinarith
  have hback : Real.cos θ*R-Real.sin θ*P=Z := by
    dsimp [P,R]
    linear_combination Z*(Real.sin_sq_add_cos_sq θ)
  have hR' := mul_le_mul_of_nonneg_left hR hc0
  have hP' := mul_le_mul_of_nonneg_left hP hs
  dsimp [cap]
  linarith

/-- Original own-frame coordinates and the actual hard-quarter width. -/
theorem actual_cap_bound {q bG a b θ : ℝ}
    (hQ : q ≤ qCap) (hG : 1/10 ≤ bG) (hb : 0 ≤ b)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ))
    (hcontact : edgeWidth θ+bG ≤ a*Real.cos θ-b*Real.sin θ)
    (hcircle : (a+1/2)^2+(b+1/2)^2 ≤ q) :
    Feasible q (bG+1/2) ∧ b+1/2 ≤ cap q (bG+1/2) θ := by
  have hD : (3/5 : ℝ) ≤ bG+1/2 := by linarith
  have hc : bG+1/2 ≤ (a+1/2-1)*Real.cos θ-(b+1/2)*Real.sin θ := by
    rw [edgeWidth_positive_formula hθ] at hcontact
    nlinarith
  have hf := feasible_of_weak_contact hQ hD hθ (by linarith : 1/2 ≤ b+1/2)
    hc hcircle
  exact ⟨hf,cap_majorizes_weak_contact hf hθ (by linarith) hc hcircle⟩

theorem cap_upper {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : cap q D θ < 233/200 := by
  have hzero : (0:ℝ) ∈ Icc 0 (7/10 : ℝ) := by norm_num
  have hle : cap q D θ ≤ cap q D 0 := (cap_strictAnti h).antitoneOn hzero hθ hθ.1
  have hz : cap q D 0=root q D 0 := by simp [cap]
  have hsq := root_sq h hzero
  have hD : (8/5 : ℝ) ≤ D+1 := by linarith [h.transverse]
  have hD2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8/5) hD 2
  have hq := h.ceiling
  dsimp [qCap] at hq
  simp only [contact,Real.cos_zero] at hsq
  rw [hz] at hle
  have hw := root_pos h hzero
  nlinarith

theorem corner_contact (q D θ : ℝ) :
    (cornerX q D θ-1)*Real.cos θ-cap q D θ*Real.sin θ=D := by
  dsimp [cornerX,cap,contact]
  linear_combination (D+Real.cos θ)*(Real.sin_sq_add_cos_sq θ)

theorem corner_norm {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    (cornerX q D θ)^2+(cap q D θ)^2=q := by
  calc
    (cornerX q D θ)^2+(cap q D θ)^2 =
        ((Real.sin θ)^2+(Real.cos θ)^2)*
          ((contact D θ)^2+(root q D θ)^2) := by unfold cornerX cap; ring
    _ = q := by rw [Real.sin_sq_add_cos_sq,one_mul,root_sq h hθ]; ring

def positivePoint (q D θ : ℝ) : SignedPoint :=
  ⟨cornerX q D θ-1/2,cap q D θ-1/2⟩

theorem positivePoint_hard {q D θ : ℝ} (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    (positivePoint q D θ).a*Real.cos θ-(positivePoint q D θ).y*Real.sin θ=
      edgeWidth θ+D-1/2 := by
  rw [edgeWidth_positive_formula hθ]
  dsimp [positivePoint]
  nlinarith [corner_contact q D θ]

/-- A cap selected with total room at least two has a genuine sorted,
positive center outside the core, on its own actual corner circle. -/
theorem positivePoint_properties {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hL : 167/200 < cap q D θ) :
    (67/200 < (positivePoint q D θ).y ∧ (positivePoint q D θ).y < 133/200) ∧
    11/10 ≤ (positivePoint q D θ).a ∧
    (positivePoint q D θ).Sorted ∧ (positivePoint q D θ).AvoidsCore ∧
    (positivePoint q D θ).circle=q := by
  have hU := cap_upper h hθ
  have hX := primary_lower_of_contact h.transverse hθ (by linarith : 0 ≤ cap q D θ)
    (corner_contact q D θ).ge
  have hy : 0 ≤ (positivePoint q D θ).y := by dsimp [positivePoint]; linarith
  have ha : 11/10 ≤ (positivePoint q D θ).a := by
    dsimp [positivePoint]
    linarith [h.transverse]
  refine ⟨⟨?_,?_⟩,ha,?_,?_,?_⟩
  · dsimp [positivePoint]; linarith
  · dsimp [positivePoint]; linarith
  · refine ⟨by linarith,?_⟩
    rw [abs_of_nonneg hy]
    dsimp [positivePoint] at *
    linarith
  · dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
    rw [max_eq_left (by linarith : 0 ≤ (positivePoint q D θ).a-1/2)]
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/5)
      (show 3/5 ≤ (positivePoint q D θ).a-1/2 by linarith) 2
    nlinarith [sq_nonneg (max (|(positivePoint q D θ).y|-1/2) 0)]
  · dsimp [SignedPoint.circle]
    rw [abs_of_nonneg hy]
    simpa [positivePoint] using corner_norm h hθ

private theorem choose_endpoint (qA DA qB DB t u : ℝ) :
    ∃ v w : ℝ, ((v=0 ∧ w=t+u) ∨ (v=t+u ∧ w=0)) ∧
      cap qA DA v+cap qB DB w=
        max (cap qA DA 0+cap qB DB (t+u))
          (cap qA DA (t+u)+cap qB DB 0) := by
  rcases le_total (cap qA DA 0+cap qB DB (t+u))
    (cap qA DA (t+u)+cap qB DB 0) with h | h
  · exact ⟨t+u,0,Or.inr ⟨rfl,rfl⟩,(max_eq_right h).symm⟩
  · exact ⟨0,t+u,Or.inl ⟨rfl,rfl⟩,(max_eq_left h).symm⟩

/-- Output of the explicit two-center construction.  Its hypotheses occur
only in `actual_pair_endpoint`; no output property is assumed there. -/
structure PairEndpoint (G A B T : SignedPoint) (t u : ℝ) where
  angleA : ℝ
  angleB : ℝ
  pointA : SignedPoint
  pointB : SignedPoint
  endpoint : (angleA=0 ∧ angleB=t+u) ∨ (angleA=t+u ∧ angleB=0)
  span : angleA+angleB=t+u
  angleA_mem : angleA ∈ Icc 0 (7/10 : ℝ)
  angleB_mem : angleB ∈ Icc 0 (7/10 : ℝ)
  sorted_A : pointA.Sorted
  sorted_B : pointB.Sorted
  avoids_A : pointA.AvoidsCore
  avoids_B : pointB.AvoidsCore
  normal_A : 0 < pointA.y
  normal_B : pointB.y < 0
  primary_A : 11/10 ≤ pointA.a
  primary_B : 11/10 ≤ pointB.a
  transverse_A : 67/200 < pointA.y ∧ pointA.y < 133/200
  transverse_B : 67/200 < -pointB.y ∧ -pointB.y < 133/200
  circle_A : pointA.circle=A.circle
  circle_B : pointB.circle=B.circle
  GA_exact : quarterProjection G pointA (-angleA) 0=edgeWidth (-angleA)
  BT_exact : quarterProjection pointB T (-angleB) 2=edgeWidth (-angleB)
  AB_zero : zeroFeasible pointA pointB 0 0
  AB_two : zeroFeasible pointA pointB 0 2
  strict_if_interior : 0 < t → 0 < u → 1 < pointA.y-pointB.y

/-- The actual original signed pair invokes cap convexity.  Each new
corner circle equals that original point's circle separately, so inherited
strict loss is retained without changing G or T or their coordinates. -/
theorem actual_pair_endpoint {G A B T : SignedPoint} {t u : ℝ}
    (hA : A.circle ≤ qCap) (hB : B.circle ≤ qCap)
    (hyA : 0 ≤ A.y) (hyB : B.y ≤ 0)
    (hyG : G.y ≤ -(1/10 : ℝ)) (hyT : (1/10 : ℝ) ≤ T.y)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hspan : t+u ≤ 7/10)
    (hGA : quarterFeasible G A (-t) 0)
    (hBT : quarterFeasible B T (-u) 2)
    (hAB : zeroFeasible A B 0 0) : Nonempty (PairEndpoint G A B T t u) := by
  have ht' : t ∈ Icc 0 (7/10 : ℝ) := ⟨ht,by linarith⟩
  have hu' : u ∈ Icc 0 (7/10 : ℝ) := ⟨hu,by linarith⟩
  have hAcircle : (A.a+1/2)^2+(A.y+1/2)^2 ≤ A.circle := by
    simp [SignedPoint.circle,abs_of_nonneg hyA]
  have hBcircle : (B.a+1/2)^2+(-B.y+1/2)^2 ≤ B.circle := by
    simp [SignedPoint.circle,abs_of_nonpos hyB]
  have hAhard : edgeWidth t+(-G.y) ≤ A.a*Real.cos t-A.y*Real.sin t := by
    have hh := hGA
    simp [quarterFeasible,quarterProjection] at hh
    linarith
  have hBhard : edgeWidth u+T.y ≤ B.a*Real.cos u-(-B.y)*Real.sin u := by
    have hh := hBT
    simp [quarterFeasible,quarterProjection] at hh
    nlinarith
  obtain ⟨hfA,hcapA⟩ := actual_cap_bound hA (by linarith : 1/10 ≤ -G.y) hyA ht'
    hAhard hAcircle
  obtain ⟨hfB,hcapB⟩ := actual_cap_bound hB hyT (by linarith : 0 ≤ -B.y) hu'
    hBhard hBcircle
  have hsource : 2 ≤ cap A.circle (-G.y+1/2) t+cap B.circle (T.y+1/2) u := by
    have hab : 1 ≤ A.y-B.y := by simpa [zeroFeasible,zeroProjection] using hAB
    linarith
  obtain ⟨v,w,hend,hmax⟩ := choose_endpoint A.circle (-G.y+1/2)
    B.circle (T.y+1/2) t u
  have hv : v ∈ Icc 0 (7/10 : ℝ) := by
    rcases hend with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> constructor <;> linarith
  have hw : w ∈ Icc 0 (7/10 : ℝ) := by
    rcases hend with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> constructor <;> linarith
  have hroom : 2 ≤ cap A.circle (-G.y+1/2) v+cap B.circle (T.y+1/2) w := by
    rw [hmax]
    exact hsource.trans (split_endpoint hfA hfB ht hu hspan)
  have hLA : 167/200 < cap A.circle (-G.y+1/2) v := by
    linarith [cap_upper hfB hw]
  have hLB : 167/200 < cap B.circle (T.y+1/2) w := by
    linarith [cap_upper hfA hv]
  obtain ⟨hAy,hAa,hAs,hAc,hAq⟩ := positivePoint_properties hfA hv hLA
  obtain ⟨hBy,hBa,hBs,hBc,hBq⟩ := positivePoint_properties hfB hw hLB
  let A' := positivePoint A.circle (-G.y+1/2) v
  let B' := (positivePoint B.circle (T.y+1/2) w).reflect
  have hnormalA : 0 < A'.y := by dsimp [A']; linarith [hAy.1]
  have hnormalB : B'.y < 0 := by dsimp [B',SignedPoint.reflect]; linarith [hBy.1]
  have hAB' : 1 ≤ A'.y-B'.y := by
    dsimp [A',B',positivePoint,SignedPoint.reflect]
    linarith
  refine ⟨{
    angleA := v
    angleB := w
    pointA := A'
    pointB := B'
    endpoint := hend
    span := ?_
    angleA_mem := hv
    angleB_mem := hw
    sorted_A := hAs
    sorted_B := by simpa [B'] using hBs
    avoids_A := hAc
    avoids_B := by simpa [B'] using hBc
    normal_A := hnormalA
    normal_B := hnormalB
    primary_A := hAa
    primary_B := by simpa [B',SignedPoint.reflect] using hBa
    transverse_A := hAy
    transverse_B := by simpa [B',SignedPoint.reflect] using hBy
    circle_A := hAq
    circle_B := by simpa [B'] using hBq
    GA_exact := ?_
    BT_exact := ?_
    AB_zero := by simpa [zeroFeasible,zeroProjection] using hAB'
    AB_two := by simpa [zeroFeasible,zeroProjection] using hAB'
    strict_if_interior := ?_
  }⟩
  · rcases hend with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> ring
  · have hh := positivePoint_hard (q := A.circle) (D := -G.y+1/2) hv
    change G.y+A'.a*Real.cos (-v)+A'.y*Real.sin (-v)=edgeWidth (-v)
    rw [Real.cos_neg,Real.sin_neg,edgeWidth_neg]
    dsimp [A']
    linarith
  · have hh := positivePoint_hard (q := B.circle) (D := T.y+1/2) hw
    change B'.a*Real.cos (-w)-B'.y*Real.sin (-w)-T.y=edgeWidth (-w)
    rw [Real.cos_neg,Real.sin_neg,edgeWidth_neg]
    dsimp [B',SignedPoint.reflect]
    nlinarith
  · intro hti hui
    have hstrict := split_endpoint_strict hfA hfB hti hui hspan
    rw [← hmax] at hstrict
    dsimp [A',B',positivePoint,SignedPoint.reflect]
    linarith

end SquaresInCircles.Eight.TableFree.HardSplitCap

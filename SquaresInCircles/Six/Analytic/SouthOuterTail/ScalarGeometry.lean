import SquaresInCircles.Six.Analytic.SouthOuterTail.Support

/-!
# The south tail is empty

Let W, S and D lie in the disk, S at an angle `s ∈ [11/25, 2/3]` and D at an
angle `d ∈ [1/2, 11/14]`. Let W be separated from C along its own axis or the
west side of C, S along its own axis, and W–D and D–S along the second axes of
W and of S, as in the model. The sum of the four separating inequalities with
the weights `5/8` (W on its own axis) or `3/5` (W on the west side of C), `1`,
`2/5` and `3/10`, together with the support bounds of W, S and D, makes the
stress of the south tail nonpositive, while it is positive.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.SouthOuterTail
open Normalization

/-- The south tail with W on its own axis is empty. -/
theorem own_impossible {v s d aw bw asouth bsouth ad bd cx cy : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 11/25) (hs : 11/25 ≤ s ∧ s ≤ 2/3)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hW : ContainedChart aw |bw|) (hS : ContainedChart asouth |bsouth|)
    (hD : ContainedChart ad |bd|) (hb : |bd| ≤ 23/100)
    (hx : 0 ≤ cx ∧ cx ≤ coreUpper) (hy : cy ≤ coreUpper)
    (hCW : 1/2+angularWidth v ≤ aw+cx*Real.cos v-cy*Real.sin v)
    (hCS : 1/2+angularWidth s ≤ asouth-cx*Real.sin s+cy*Real.cos s)
    (hWD : 1/2+angularWidth (d+v) ≤ ad*Real.sin (d+v)+bd*Real.cos (d+v)-bw)
    (hDS : 1/2+angularWidth (d-s) ≤ bsouth+ad*Real.cos (d-s)-bd*Real.sin (d-s)) : False := by
  have hvSin := (Real.sin_le hv.1).trans hv.2
  have hcos := south_cos_lower hs
  have hfy : 0 ≤ Real.cos s-Own.weightW*Real.sin v := by
    dsimp [Own.weightW]
    linarith
  obtain ⟨upper,hcenter⟩ := center_face
    (fx := Own.weightW*Real.cos v-Real.sin s)
    (fy := Real.cos s-Own.weightW*Real.sin v) hx hy hfy
  have hsum : Own.weightW*(1/2+angularWidth v)+(1/2+angularWidth s)+
      mu*(1/2+angularWidth (d+v))+nu*(1/2+angularWidth (d-s)) ≤
      (Own.weightW*aw-mu*bw)+(asouth+nu*bsouth)+
      diagonalU v s d*ad+diagonalV v s d*bd+
      (Own.weightW*Real.cos v-Real.sin s)*cx+
      (Real.cos s-Own.weightW*Real.sin v)*cy := by
    dsimp [Own.weightW,mu,nu,diagonalU,diagonalV]
    linear_combination (5/8)*hCW+hCS+(2/5)*hWD+(3/10)*hDS
  have hw := west_own_support hW
  have hsu := south_support hS
  have wv := width_lower v
  have ws := width_lower s
  have wq := width_lower (d+v)
  have wr := width_lower (d-s)
  have hn : Own.raw upper v s d ad bd ≤ 0 := by
    cases upper <;>
      dsimp [Own.raw,Own.constant,Own.weightW,diagonalU,diagonalV,mu,nu,A,B,coreUpper,face]
        at hsum hw hsu hcenter ⊢ <;>
      nlinarith only [hsum,hw,hsu,hcenter,wv,ws,wq,wr]
  exact (not_lt_of_ge hn) (Own.positive_raw upper hv hs hd hD hb)

def cardinalSign (negative : Bool) : ℝ := if negative then -1 else 1

/-- The south tail with W on the west side of C, at an angle of either sign, is
empty. -/
theorem cardinal_impossible (negative : Bool) {x s d aw bw asouth bsouth ad bd cx cy : ℝ}
    (hxangle : 0 ≤ x ∧ x ≤ 2/5) (hs : 11/25 ≤ s ∧ s ≤ 2/3)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hW : ContainedChart aw |bw|) (hS : ContainedChart asouth |bsouth|)
    (hD : ContainedChart ad |bd|)
    (hx : 0 ≤ cx ∧ cx ≤ coreUpper) (hy : cy ≤ coreUpper)
    (hCW : 1/2+angularWidth (cardinalSign negative*x) ≤
      aw*Real.cos (cardinalSign negative*x)+bw*Real.sin (cardinalSign negative*x)+cx)
    (hCS : 1/2+angularWidth s ≤ asouth-cx*Real.sin s+cy*Real.cos s)
    (hWD : 1/2+angularWidth (d+cardinalSign negative*x) ≤
      ad*Real.sin (d+cardinalSign negative*x)+bd*Real.cos (d+cardinalSign negative*x)-bw)
    (hDS : 1/2+angularWidth (d-s) ≤ bsouth+ad*Real.cos (d-s)-bd*Real.sin (d-s)) : False := by
  let v := cardinalSign negative*x
  have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi hxangle.1
    (by linarith [hxangle.2,Real.pi_gt_d2])
  have hsin1 := (Real.sin_le hxangle.1).trans hxangle.2
  have hcosx := Real.cos_nonneg_of_mem_Icc
    (show x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hxangle.1,hxangle.2,Real.pi_gt_d2])
  have hvSin : -(2/5) ≤ Real.sin v ∧ Real.sin v ≤ 2/5 := by
    cases negative <;> simp [v,cardinalSign] <;> constructor <;> linarith
  have wv : angularWidth v=(Real.cos x+Real.sin x)/2 := by
    cases negative <;>
      simp [v,cardinalSign,angularWidth,abs_of_nonneg hcosx,abs_of_nonneg hsin0]
  have hfy : 0 ≤ Real.cos s := by linarith [south_cos_lower hs]
  obtain ⟨upper,hcenter⟩ := center_face
    (fx := beta-Real.sin s) (fy := Real.cos s) hx hy hfy
  have hsum : beta*(1/2+angularWidth v)+(1/2+angularWidth s)+
      mu*(1/2+angularWidth (d+v))+nu*(1/2+angularWidth (d-s)) ≤
      (beta*Real.cos v*aw+(beta*Real.sin v-mu)*bw)+(asouth+nu*bsouth)+
      diagonalU v s d*ad+diagonalV v s d*bd+
      (beta-Real.sin s)*cx+Real.cos s*cy := by
    dsimp [beta,mu,nu,diagonalU,diagonalV,v]
    linear_combination (3/5)*hCW+hCS+(2/5)*hWD+(3/10)*hDS
  rw [wv] at hsum
  have hw := west_cardinal_support hW hvSin
  have hsu := south_support hS
  have hdu := diagonal_vertex_support hD v s d
  have ws := width_lower s
  have wq := width_lower (d+v)
  have wr := width_lower (d-s)
  have hn : profile (if negative then 2 else 1) upper x s d ≤ 0 := by
    cases negative <;> cases upper <;>
      simp [v,cardinalSign,profile,constantTerm,cosineCoefficient,sineCoefficient,
        westRoot,side,face,beta,mu,nu,A,B,kappa,coreUpper,diagonalU,diagonalV]
        at hsum hw hsu hdu hcenter ws wq wr ⊢ <;>
      nlinarith only [hsum,hw,hsu,hdu,hcenter,ws,wq,wr]
  exact (not_lt_of_ge hn) (positive_cardinal negative upper hxangle hs hd)

end SquaresInCircles.Six.Analytic.SouthOuterTail

import SquaresInCircles.Six.Analytic.WestGapReserve.Geometry

/-!
# Bounds for W and D: the profile

The profile of a stress with weights `b`, `z` and `1` on the separators of C and
W, of C and D, and of W and D along the secondary axis of D is a constant plus
`b (A cos v + (1/2 + y) sin v)`, `z (A cos d + (1/2 - y) sin d)` and
`cos (v + d)/2 - B sin (v + d)`. For fixed `d` it is `k + a cos v + e sin v`
with `a, e ≥ 0`, since `sin x/2 + B cos x ≤ 4/5` by Pythagoras, and on an
interval inside `[0, π/2]` such a harmonic is positive when it is positive at
the ends. The same holds in `d` for fixed `v`, and in `d` along the line
`v + d = 53/50`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.WestCoreBounds

def A : ℝ := 19359/50000
def B : ℝ := 30641/50000
def face (upper : Bool) : ℝ := if upper then 5641/50000 else 0

def profile (b z y K v d : ℝ) : ℝ := K+
  b*(A*Real.cos v+(1/2+y)*Real.sin v)+
  z*(A*Real.cos d+(1/2-y)*Real.sin d)+
  (1/2)*Real.cos (v+d)-B*Real.sin (v+d)

structure Coefficients (b z y : ℝ) : Prop where
  b_nonneg : 0 ≤ b
  z_nonneg : 0 ≤ z
  y_nonneg : 0 ≤ y
  y_half : y ≤ 1/2
  b_cos : B ≤ b*A
  b_sin : 4/5 ≤ b*(1/2+y)
  z_cos : B ≤ z*A
  z_sin : 4/5 ≤ z*(1/2-y)

lemma adverse_harmonic (x : ℝ) :
    (1/2)*Real.sin x+B*Real.cos x ≤ 4/5 := by
  have hid : ((1/2)*Real.sin x+B*Real.cos x)^2+
      ((1/2)*Real.cos x-B*Real.sin x)^2=(1/2:ℝ)^2+B^2 := by
    linear_combination ((1/2:ℝ)^2+B^2)*(Real.sin_sq_add_cos_sq x)
  have hB : (1/2:ℝ)^2+B^2 < (4/5)^2 := by norm_num [B]
  by_contra! h
  have hp := mul_pos (sub_pos.mpr h)
    (show 0 < (1/2)*Real.sin x+B*Real.cos x+4/5 by linarith)
  nlinarith [sq_nonneg ((1/2)*Real.cos x-B*Real.sin x)]

private lemma trig_nonnegative {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
    0 ≤ Real.cos x ∧ 0 ≤ Real.sin x := by
  exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩,
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_pos])⟩

lemma extend_west {b z y K l u v d : ℝ} (hc : Coefficients b z y)
    (hd : 0 ≤ d ∧ d ≤ Real.pi/2) (hl : 0 ≤ l) (hu : u ≤ Real.pi/2)
    (hv : l ≤ v ∧ v ≤ u)
    (hleft : 0 < profile b z y K l d) (hright : 0 < profile b z y K u d) :
    0 < profile b z y K v d := by
  let a := b*A+(1/2)*Real.cos d-B*Real.sin d
  let e := b*(1/2+y)-(1/2)*Real.sin d-B*Real.cos d
  let k := K+z*(A*Real.cos d+(1/2-y)*Real.sin d)
  have ident (x : ℝ) : profile b z y K x d=k+a*Real.cos x+e*Real.sin x := by
    dsimp [profile,k,a,e]
    rw [Real.cos_add,Real.sin_add]
    ring
  have ht := trig_nonnegative hd
  have hA : 0 ≤ a := by
    have hp := mul_nonneg (by norm_num [B] : 0 ≤ B)
      (show 0 ≤ 1-Real.sin d by linarith [Real.sin_le_one d])
    dsimp [a]
    nlinarith only [hc.b_cos,ht.1,hp]
  have hE : 0 ≤ e := by
    dsimp [e]
    linarith [hc.b_sin,adverse_harmonic d]
  rw [ident] at hleft hright ⊢
  have h := trig_lower_of_endpoints hA hE hl hu hv
    (C := -k) (by linarith) (by linarith)
  linarith

lemma extend_diagonal {b z y K l u v d : ℝ} (hc : Coefficients b z y)
    (hv : 0 ≤ v ∧ v ≤ Real.pi/2) (hl : 0 ≤ l) (hu : u ≤ Real.pi/2)
    (hd : l ≤ d ∧ d ≤ u)
    (hleft : 0 < profile b z y K v l) (hright : 0 < profile b z y K v u) :
    0 < profile b z y K v d := by
  let a := z*A+(1/2)*Real.cos v-B*Real.sin v
  let e := z*(1/2-y)-(1/2)*Real.sin v-B*Real.cos v
  let k := K+b*(A*Real.cos v+(1/2+y)*Real.sin v)
  have ident (x : ℝ) : profile b z y K v x=k+a*Real.cos x+e*Real.sin x := by
    dsimp [profile,k,a,e]
    rw [Real.cos_add,Real.sin_add]
    ring
  have ht := trig_nonnegative hv
  have hA : 0 ≤ a := by
    have hp := mul_nonneg (by norm_num [B] : 0 ≤ B)
      (show 0 ≤ 1-Real.sin v by linarith [Real.sin_le_one v])
    dsimp [a]
    nlinarith only [hc.z_cos,ht.1,hp]
  have hE : 0 ≤ e := by dsimp [e]; linarith [hc.z_sin,adverse_harmonic v]
  rw [ident] at hleft hright ⊢
  have h := trig_lower_of_endpoints hA hE hl hu hd
    (C := -k) (by linarith) (by linarith)
  linarith

lemma extend_gap_wall {b z y K l u d : ℝ} (hc : Coefficients b z y)
    (hbalance : b*(1/2+y)/2 ≤ z*(1/2-y))
    (hl : 0 ≤ l) (hu : u ≤ Real.pi/2) (hd : l ≤ d ∧ d ≤ u)
    (hleft : 0 < profile b z y K (53/50-l) l)
    (hright : 0 < profile b z y K (53/50-u) u) :
    0 < profile b z y K (53/50-d) d := by
  let a := z*A+b*(A*Real.cos (53/50)+(1/2+y)*Real.sin (53/50))
  let e := z*(1/2-y)+b*(A*Real.sin (53/50)-(1/2+y)*Real.cos (53/50))
  let k := K+(1/2)*Real.cos (53/50)-B*Real.sin (53/50)
  have ident (x : ℝ) : profile b z y K (53/50-x) x=k+a*Real.cos x+e*Real.sin x := by
    dsimp [profile,k,a,e]
    rw [show (53:ℝ)/50-x+x=53/50 by ring,Real.cos_sub,Real.sin_sub]
    ring
  have ht := trig_nonnegative (x := (53:ℝ)/50)
    ⟨by norm_num,by linarith [Real.pi_gt_d2]⟩
  have hcos : Real.cos ((53:ℝ)/50) ≤ 1/2 := by
    nlinarith only [Seven.cos_upper_four (x := (53:ℝ)/50) (by norm_num)]
  have hp := mul_le_mul_of_nonneg_left hcos
    (show 0 ≤ b*(1/2+y) from mul_nonneg hc.b_nonneg (by linarith [hc.y_nonneg]))
  have hs := mul_nonneg (mul_nonneg hc.b_nonneg (by norm_num [A] : 0 ≤ A)) ht.2
  have hA : 0 ≤ a := by
    have hAp : (0:ℝ) ≤ A := by norm_num [A]
    have h1 := mul_nonneg hc.z_nonneg hAp
    have h2 := mul_nonneg hc.b_nonneg (add_nonneg (mul_nonneg hAp ht.1)
      (mul_nonneg (show (0:ℝ) ≤ 1/2+y by linarith [hc.y_nonneg]) ht.2))
    dsimp [a]
    linarith
  have hE : 0 ≤ e := by dsimp [e]; nlinarith only [hbalance,hp,hs]
  rw [ident] at hleft hright ⊢
  have h := trig_lower_of_endpoints hA hE hl hu hd
    (C := -k) (by linarith) (by linarith)
  linarith

end SquaresInCircles.Six.Analytic.WestCoreBounds

module
public import SquaresInCircles.Six.Analytic.MixedCardinalSouth.Scalar

@[expose] public section

/-!
# A whole-domain obstruction for the large positive south tail

For the mixed south source use CW, CS, WD, DS with weights 4, 10, 3, 3.
Here W is cardinal, S is OWN, v=-w, and 12/25<=s<=2/3. The support calculation
is kept separate in Geometry.lean. Its rational minorant is `profile` below.

There are no angle cells. The d derivative is negative on the whole domain:
the chord derivative is at most -2067/1000, while the remaining derivative is
at most (1839/1000)*(107/350)+3/2, which is smaller. Thus d=11/14 is worst.
The s slices are positive sine/cosine combinations plus a constant. The v
slices are concave on each side of the geometric sign wall v=0. Six distinct
corners remain: v in {-2/5,0,2/5}, s in {12/25,2/3}, d=11/14. All six
inequalities follow from explicit Taylor bounds and rational arithmetic.

The Boolean only records the sign of v; it is not a certificate selector.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.CardinalSouthTail
open Normalization

def vLower (negative : Bool) : ℝ := if negative then -(2/5) else 0
def vUpper (negative : Bool) : ℝ := if negative then 0 else 2/5
def coefficient (negative : Bool) : ℝ := if negative then 67/1250 else 4

def profile (negative : Bool) (v s d : ℝ) : ℝ :=
  -263/40+(387/100)*Real.cos s+5*Real.sin s+
    4*Real.cos v+coefficient negative*Real.sin v+
    3*Real.sin (d+v)-(5067/500)*Real.sin ((d+v)/2)-
    (1839/1000)*Real.cos (d-s)+(3/2)*Real.sin (d-s)

lemma v_bounds {negative : Bool} {v : ℝ}
    (hv : vLower negative ≤ v ∧ v ≤ vUpper negative) :
    -(2/5) ≤ v ∧ v ≤ 2/5 := by
  cases negative <;> simp only [vLower,vUpper,if_true,if_false] at hv <;>
    constructor <;> linarith [hv.1,hv.2]

private lemma q_bounds {v d : ℝ}
    (hv : -(2/5) ≤ v ∧ v ≤ 2/5) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    0 ≤ d+v ∧ d+v ≤ 6/5 := by
  constructor <;> linarith [hv.1,hv.2,hd.1,hd.2]

private lemma coefficient_sine_lower {negative : Bool} {v : ℝ}
    (hv : vLower negative ≤ v ∧ v ≤ vUpper negative) :
    -(67/3125) ≤ coefficient negative*Real.sin v := by
  cases negative
  · simp only [vLower,vUpper,if_false] at hv
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
      (by linarith [hv.2,Real.pi_gt_d2])
    dsimp [coefficient]
    linarith
  · simp only [vLower,vUpper,if_true] at hv
    have hs := Real.sin_le (show 0 ≤ -v by linarith [hv.2])
    rw [Real.sin_neg] at hs
    dsimp [coefficient]
    linarith [hv.1]

/-- The diagonal derivative is nonpositive everywhere, not only at a mesh. -/
lemma diagonal_derivative_nonpositive {v s d : ℝ}
    (hv : -(2/5) ≤ v ∧ v ≤ 2/5)
    (hs : 12/25 ≤ s ∧ s ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    3*Real.cos (d+v)-(5067/1000)*Real.cos ((d+v)/2)+
      (1839/1000)*Real.sin (d-s)+(3/2)*Real.cos (d-s) ≤ 0 := by
  have hq := q_bounds hv hd
  have hc0 : 0 ≤ Real.cos ((d+v)/2) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hq.1,Real.pi_pos],by linarith [hq.2,Real.pi_gt_d2]⟩
  have hid : Real.cos (d+v)=2*Real.cos ((d+v)/2)^2-1 := by
    have h := Real.cos_two_mul ((d+v)/2)
    rw [show 2*((d+v)/2)=d+v by ring] at h
    nlinarith only [h,Real.sin_sq_add_cos_sq ((d+v)/2)]
  have hp := mul_nonpos_of_nonpos_of_nonneg
    (show Real.cos ((d+v)/2)-1 ≤ 0 by linarith [Real.cos_le_one ((d+v)/2)])
    (show 0 ≤ 6*(Real.cos ((d+v)/2)+1)-5067/1000 by linarith)
  have hchord : 3*Real.cos (d+v)-(5067/1000)*Real.cos ((d+v)/2) ≤
      -(2067/1000) := by nlinarith only [hid,hp]
  have hrlo : -(1/6) ≤ d-s := by linarith [hd.1,hs.2]
  have hrhi : d-s ≤ 107/350 := by linarith [hd.2,hs.1]
  have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ d-s by linarith [Real.pi_gt_d2])
    (show (107:ℝ)/350 ≤ Real.pi/2 by linarith [Real.pi_gt_d2]) hrhi
  have hsin : Real.sin (d-s) ≤ 107/350 :=
    hmono.trans (Real.sin_le (by norm_num))
  linarith [Real.cos_le_one (d-s)]

lemma profile_at_upper_diagonal {negative : Bool} {v s d : ℝ}
    (hv : -(2/5) ≤ v ∧ v ≤ 2/5)
    (hs : 12/25 ≤ s ∧ s ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    profile negative v s (11/14) ≤ profile negative v s d := by
  let D : ℝ → ℝ := fun x =>
    3*Real.cos (x+v)-(5067/1000)*Real.cos ((x+v)/2)+
      (1839/1000)*Real.sin (x-s)+(3/2)*Real.cos (x-s)
  have hf (x : ℝ) : HasDerivAt (profile negative v s) (D x) x := by
    let K := -263/40+(387/100)*Real.cos s+5*Real.sin s+
      4*Real.cos v+coefficient negative*Real.sin v
    convert (((((((hasDerivAt_id x).add_const v).sin).const_mul 3).sub
      (((((hasDerivAt_id x).add_const v).div_const 2).sin).const_mul (5067/500))).sub
      ((((hasDerivAt_id x).sub_const s).cos).const_mul (1839/1000))).add
      ((((hasDerivAt_id x).sub_const s).sin).const_mul (3/2))).const_add K using 1 <;>
      dsimp [profile,D,K] <;> ring
  have hmono : MonotoneOn (fun x => -profile negative v s x) (Set.Icc (1/2) (11/14)) := by
    apply Seven.monoOn_of_hasDeriv_nonneg (by dsimp [profile]; fun_prop)
      (fun x _ => (hf x).neg)
    intro x hx
    exact neg_nonneg.mpr (diagonal_derivative_nonpositive hv hs ⟨hx.1.le,hx.2.le⟩)
  have h := hmono hd (by norm_num : (11:ℝ)/14 ∈ Set.Icc (1/2) (11/14)) hd.2
  linarith

lemma profile_v_concave (negative : Bool) {s d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    ConcaveOn ℝ (Set.Icc (vLower negative) (vUpper negative))
      (fun v => profile negative v s d) := by
  let f' : ℝ → ℝ := fun v => -4*Real.sin v+coefficient negative*Real.cos v+
    3*Real.cos (d+v)-(5067/1000)*Real.cos ((d+v)/2)
  let f'' : ℝ → ℝ := fun v => -4*Real.cos v-coefficient negative*Real.sin v-
    3*Real.sin (d+v)+(5067/2000)*Real.sin ((d+v)/2)
  have hf (v : ℝ) : HasDerivAt (fun x => profile negative x s d) (f' v) v := by
    let K := -263/40+(387/100)*Real.cos s+5*Real.sin s-
      (1839/1000)*Real.cos (d-s)+(3/2)*Real.sin (d-s)
    convert (((((Real.hasDerivAt_cos v).const_mul 4).add
      ((Real.hasDerivAt_sin v).const_mul (coefficient negative))).add
      ((((hasDerivAt_id v).const_add d).sin).const_mul 3)).sub
      (((((hasDerivAt_id v).const_add d).div_const 2).sin).const_mul (5067/500))).const_add K
      using 1 <;> dsimp [profile,f',K] <;> ring
  have hff (v : ℝ) : HasDerivAt f' (f'' v) v := by
    convert ((((Real.hasDerivAt_sin v).const_mul (-4)).add
      ((Real.hasDerivAt_cos v).const_mul (coefficient negative))).add
      ((((hasDerivAt_id v).const_add d).cos).const_mul 3)).sub
      (((((hasDerivAt_id v).const_add d).div_const 2).cos).const_mul (5067/1000))
      using 1 <;> dsimp [f',f''] <;> ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos
    (convex_Icc (vLower negative) (vUpper negative))
    (f' := f') (f'' := f'') (by dsimp [profile]; fun_prop)
  · intro v _
    exact (hf v).hasDerivWithinAt
  · intro v _
    exact (hff v).hasDerivWithinAt
  · intro v hv
    have hmem := interior_subset hv
    have hraw := v_bounds hmem
    have hsq := mul_nonneg (show 0 ≤ 2/5-v by linarith [hraw.2])
      (show 0 ≤ 2/5+v by linarith [hraw.1])
    have hc : 23/25 ≤ Real.cos v := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]
    have hq := q_bounds hraw hd
    have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hq.1
      (by linarith [hq.2,Real.pi_gt_d2])
    have hb := coefficient_sine_lower hmem
    dsimp [f'']
    linarith [Real.sin_le_one ((d+v)/2)]

private lemma extend_s {negative : Bool} {v s d : ℝ}
    (hs : 12/25 ≤ s ∧ s ≤ 2/3)
    (hleft : 0 < profile negative v (12/25) d)
    (hright : 0 < profile negative v (2/3) d) :
    0 < profile negative v s d := by
  let A := 387/100-(1839/1000)*Real.cos d+(3/2)*Real.sin d
  let B := 5-(1839/1000)*Real.sin d-(3/2)*Real.cos d
  let K := -263/40+4*Real.cos v+coefficient negative*Real.sin v+
    3*Real.sin (d+v)-(5067/500)*Real.sin ((d+v)/2)
  have hid (x : ℝ) : profile negative v x d=K+A*Real.cos x+B*Real.sin x := by
    dsimp [profile,K,A,B]
    rw [Real.cos_sub,Real.sin_sub]
    ring
  have hA : 0 ≤ A := by
    dsimp [A]
    linarith [Real.cos_le_one d,Real.neg_one_le_sin d]
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith [Real.sin_le_one d,Real.cos_le_one d]
  rw [hid] at hleft hright ⊢
  have h := trig_lower_of_endpoints hA hB (by norm_num)
    (by linarith [Real.pi_gt_d2]) hs (C := -K) (by linarith) (by linarith)
  linarith

private def cosLower (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720
private def cosUpper (x : ℝ) : ℝ := 1-x^2/2+x^4/24
private def sinFive (x : ℝ) : ℝ := x-x^3/6+x^5/120
private def sinLower (x : ℝ) : ℝ :=
  if 0 ≤ x then x-x^3/6+x^5/120-x^7/5040 else sinFive x

private lemma cos_lower (x : ℝ) : cosLower x ≤ Real.cos x := by
  by_cases hx : 0 ≤ x
  · exact Seven.cos_lower_six hx
  · have h := Seven.cos_lower_six (x := -x) (by linarith)
    simpa [cosLower,Real.cos_neg] using h

private lemma sin_lower (x : ℝ) : sinLower x ≤ Real.sin x := by
  by_cases hx : 0 ≤ x
  · simpa [sinLower,hx] using Seven.sin_lower_seven hx
  · have h := Seven.sin_upper_five (x := -x) (by linarith)
    rw [Real.sin_neg] at h
    simp only [sinLower,if_neg hx,sinFive]
    nlinarith only [h]

private def endpointPolynomial (negative : Bool) (v s : ℝ) : ℝ :=
  -263/40+(387/100)*cosLower s+5*sinLower s+
    4*cosLower v+coefficient negative*sinLower v+
    3*sinLower (11/14+v)-(5067/500)*sinFive ((11/14+v)/2)-
    (1839/1000)*cosUpper (11/14-s)+(3/2)*sinLower (11/14-s)

private lemma endpointPolynomial_le {negative : Bool} {v s : ℝ}
    (hq : 0 ≤ 11/14+v) (hr : 0 ≤ 11/14-s) :
    endpointPolynomial negative v s ≤ profile negative v s (11/14) := by
  have cs := cos_lower s
  have ss := sin_lower s
  have cv := cos_lower v
  have sv := sin_lower v
  have sq := sin_lower (11/14+v)
  have sh := Seven.sin_upper_five (x := (11/14+v)/2) (by linarith)
  have cr := Seven.cos_upper_four hr
  have sr := sin_lower (11/14-s)
  cases negative <;> dsimp [endpointPolynomial,profile,coefficient,cosUpper,sinFive] <;>
    nlinarith only [cs,ss,cv,sv,sq,sh,cr,sr]

/-- These are the physical interval endpoints, with v=0 shared by the two signs. -/
private lemma corner (negative : Bool) (v s : ℝ)
    (hv : v=vLower negative ∨ v=vUpper negative)
    (hs : s=12/25 ∨ s=2/3) : 0 < profile negative v s (11/14) := by
  rcases hv with rfl | rfl <;> rcases hs with rfl | rfl <;> cases negative
  all_goals
    apply lt_of_lt_of_le _ (endpointPolynomial_le
      (by norm_num [vLower,vUpper]) (by norm_num))
    norm_num [endpointPolynomial,coefficient,vLower,vUpper,cosLower,cosUpper,sinLower,sinFive]

/-- The entire large-south rectangle is excluded by one explicit scalar profile. -/
theorem positive (negative : Bool) {v s d : ℝ}
    (hv : vLower negative ≤ v ∧ v ≤ vUpper negative)
    (hs : 12/25 ≤ s ∧ s ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    0 < profile negative v s d := by
  have hside (x : ℝ) (hx : x=12/25 ∨ x=2/3) :
      0 < profile negative v x (11/14) := by
    apply positive_on_concave_interval
      (profile_v_concave negative (s := x) (d := 11/14) ⟨by norm_num,le_rfl⟩) hv
    · exact corner negative (vLower negative) x (Or.inl rfl) hx
    · exact corner negative (vUpper negative) x (Or.inr rfl) hx
  have htop := extend_s hs (hside (12/25) (Or.inl rfl)) (hside (2/3) (Or.inr rfl))
  exact htop.trans_le (profile_at_upper_diagonal (v_bounds hv) hs hd)

end SquaresInCircles.Six.Analytic.CardinalSouthTail

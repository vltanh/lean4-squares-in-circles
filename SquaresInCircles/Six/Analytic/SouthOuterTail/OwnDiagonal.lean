import SquaresInCircles.Six.Analytic.SouthOuterTail.OwnRaw
import SquaresInCircles.Six.Analytic.SouthOuterTail.NarrowSupport

/-!
# The south tail with W on its own axis: the corner `v = s = 11/25`

At the corner `v = s = 11/25` the force on D is `(U(d), V(d))`, linear in `cos d`
and `sin d`. Taylor bounds at `11/25` and the concavity of `cos d + sin d` give
`3/5 ≤ U ≤ 7/10` and `0 ≤ V ≤ 2U/5` for every `d ∈ [1/2, 11/14]`, so the support
of a nearly radial force applies. The term `specialTerm` that remains after it
has a nonpositive derivative, so it is smallest at `d = 11/14`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.SouthOuterTail.Own
open Normalization

def corner : ℝ := 11/25
def forceU (d : ℝ) : ℝ := mu*Real.sin (d+corner)+nu*Real.cos (d-corner)
def forceV (d : ℝ) : ℝ := mu*Real.cos (d+corner)-nu*Real.sin (d-corner)
def rotationA : ℝ := mu*Real.sin corner+nu*Real.cos corner
def rotationB : ℝ := mu*Real.cos corner+nu*Real.sin corner

lemma force_rotation (d : ℝ) :
    forceU d=rotationA*Real.cos d+rotationB*Real.sin d ∧
    forceV d=rotationB*Real.cos d-rotationA*Real.sin d := by
  constructor <;> dsimp [forceU,forceV,rotationA,rotationB] <;>
    simp only [Real.sin_add,Real.cos_add,Real.sin_sub,Real.cos_sub] <;> ring

lemma rotation_bounds :
    11/25 ≤ rotationA ∧ rotationA ≤ 443/1000 ∧
    489/1000 ≤ rotationB ∧ rotationB ≤ 49/100 := by
  have cl := Seven.cos_lower_six (x := (11:ℝ)/25) (by norm_num)
  have cu := Seven.cos_upper_four (x := (11:ℝ)/25) (by norm_num)
  have sl := Seven.sin_lower_seven (x := (11:ℝ)/25) (by norm_num)
  have su := Seven.sin_upper_five (x := (11:ℝ)/25) (by norm_num)
  dsimp [rotationA,rotationB,corner,mu,nu]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [cl,cu,sl,su]

lemma diagonal_trig_bounds {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    (69/100 ≤ Real.cos d ∧ Real.cos d ≤ 879/1000) ∧
    (23/48 ≤ Real.sin d ∧ Real.sin d ≤ 71/100) ∧
    4/3 < Real.cos d+Real.sin d := by
  have hsq := mul_nonneg (sub_nonneg.mpr hd.2)
    (show 0 ≤ 11/14+d by linarith [hd.1])
  have hcl : 69/100 ≤ Real.cos d := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := d)]
  have hcm := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ) ≤ 1/2)
    (show d ≤ Real.pi by linarith [hd.2,Real.pi_gt_d2]) hd.1
  have hcu := Seven.cos_upper_four (x := (1:ℝ)/2) (by norm_num)
  have hslm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (1:ℝ)/2 by linarith [Real.pi_pos])
    (show d ≤ Real.pi/2 by linarith [hd.2,Real.pi_gt_d2]) hd.1
  have hsum := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ d by linarith [hd.1,Real.pi_pos])
    (show (11:ℝ)/14 ≤ Real.pi/2 by linarith [Real.pi_gt_d2]) hd.2
  have hsl := Real.sin_ge_sub_cube (x := (1:ℝ)/2) (by norm_num)
  have hsu := Seven.sin_upper_five (x := (11:ℝ)/14) (by norm_num)
  have hcs : 4/3 < Real.cos d+Real.sin d := by
    have h := trig_lower_of_endpoints (A := 1) (B := 1) (C := 4/3)
      (l := 1/2) (u := 11/14) (by norm_num) (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_d2]) hd
      (by nlinarith only [Seven.cos_lower_six (x := (1:ℝ)/2) (by norm_num),
        Seven.sin_lower_seven (x := (1:ℝ)/2) (by norm_num)])
      (by nlinarith only [Seven.cos_lower_six (x := (11:ℝ)/14) (by norm_num),
        Seven.sin_lower_seven (x := (11:ℝ)/14) (by norm_num)])
    simpa only [one_mul] using h
  exact ⟨⟨hcl,by nlinarith only [hcm,hcu]⟩,
    ⟨by nlinarith only [hslm,hsl],by nlinarith only [hsum,hsu]⟩,hcs⟩

/-- At the corner the force on D is nearly radial, for every
`d ∈ [1/2, 11/14]`. -/
lemma force_cone {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    (3/5 ≤ forceU d ∧ forceU d ≤ 7/10) ∧
    (0 ≤ forceV d ∧ |forceV d| ≤ (2/5)*forceU d) := by
  have ht := diagonal_trig_bounds hd
  have hc : 0 ≤ Real.cos d := by linarith [ht.1.1]
  have hs : 0 ≤ Real.sin d := by linarith [ht.2.1.1]
  have hr := rotation_bounds
  have hi := force_rotation d
  have u1 := mul_nonneg (show 0 ≤ rotationA-11/25 by linarith [hr.1]) hc
  have u2 := mul_nonneg (show 0 ≤ rotationB-489/1000 by linarith [hr.2.2.1]) hs
  have ulo : 3/5 ≤ forceU d := by
    nlinarith only [u1,u2,hi.1,ht.2.1.1,ht.2.2]
  have uhi : forceU d ≤ 7/10 := by
    dsimp [forceU,mu,nu]
    linarith [Real.sin_le_one (d+corner),Real.cos_le_one (d-corner)]
  have v1 := mul_nonneg (show 0 ≤ rotationB-489/1000 by linarith [hr.2.2.1]) hc
  have v2 := mul_nonneg (show 0 ≤ 443/1000-rotationA by linarith [hr.2.1]) hs
  have vlo : 0 ≤ forceV d := by
    nlinarith only [v1,v2,hi.2,ht.1.1,ht.2.1.2]
  have w1 := mul_nonneg
    (show 0 ≤ (2/5)*rotationA-rotationB+157/500 by linarith [hr.1,hr.2.2.2]) hc
  have w2 := mul_nonneg
    (show 0 ≤ (2/5)*rotationB+rotationA-1589/2500 by linarith [hr.1,hr.2.2.1]) hs
  have vhi : forceV d ≤ (2/5)*forceU d := by
    nlinarith only [w1,w2,hi.1,hi.2,ht.1.2,ht.2.1.1]
  exact ⟨⟨ulo,uhi⟩,vlo,by simpa only [abs_of_nonneg vlo] using vhi⟩

lemma corner_support {a b d : ℝ} (hc : ContainedChart a |b|)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    forceU d*a+forceV d*b ≤ CandidateWestTail.rhoBound*forceU d+1/160 := by
  have hcone := force_cone hd
  have h := narrow_support hc hcone.1 hcone.2.2
  have hp := mul_nonneg (sub_nonneg.mpr CandidateWestTail.ceiling_bounds.2.1)
    (show 0 ≤ forceU d by linarith [hcone.1.1])
  nlinarith only [h,hp]

def specialTerm (d : ℝ) : ℝ :=
  (mu/2)*Real.cos (d+corner)-mu*B*Real.sin (d+corner)-
    nu*B*Real.cos (d-corner)+(nu/2)*Real.sin (d-corner)
def specialFirst (d : ℝ) : ℝ :=
  -mu*(B*Real.cos (d+corner)+(1/2)*Real.sin (d+corner))+
    nu*((1/2)*Real.cos (d-corner)+B*Real.sin (d-corner))

lemma special_hasDeriv (d : ℝ) : HasDerivAt specialTerm (specialFirst d) d := by
  convert ((((((hasDerivAt_id d).add_const corner).cos).const_mul (mu/2)).sub
    ((((hasDerivAt_id d).add_const corner).sin).const_mul (mu*B))).sub
    ((((hasDerivAt_id d).sub_const corner).cos).const_mul (nu*B))).add
    ((((hasDerivAt_id d).sub_const corner).sin).const_mul (nu/2)) using 1
  · funext y
    simp only [specialTerm,Pi.add_apply,Pi.sub_apply,id]
  · dsimp [specialFirst]
    ring

lemma special_derivative_nonpositive {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    specialFirst d ≤ 0 := by
  have hq : 47/50 ≤ d+corner ∧ d+corner ≤ 429/350 := by
    dsimp [corner]
    constructor <;> linarith [hd.1,hd.2]
  have hf : 2/3 < B*Real.cos (d+corner)+(1/2)*Real.sin (d+corner) := by
    apply trig_lower_of_endpoints (by norm_num [B]) (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_d2]) hq
    · dsimp [B]
      nlinarith only [Seven.cos_lower_six (x := (47:ℝ)/50) (by norm_num),
        Seven.sin_lower_seven (x := (47:ℝ)/50) (by norm_num)]
    · dsimp [B]
      nlinarith only [Seven.cos_lower_six (x := (429:ℝ)/350) (by norm_num),
        Seven.sin_lower_seven (x := (429:ℝ)/350) (by norm_num)]
  have hr : 0 ≤ d-corner := by dsimp [corner]; linarith [hd.1]
  have hs : Real.sin (d-corner) ≤ 121/350 := by
    have h := Real.sin_le hr
    dsimp [corner] at h ⊢
    linarith [hd.2]
  have hc := Real.cos_le_one (d-corner)
  dsimp [specialFirst,mu,nu,B] at *
  nlinarith only [hf,hs,hc]

lemma special_at_upper_diagonal {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    specialTerm (11/14) ≤ specialTerm d := by
  have hm : MonotoneOn (fun x => -specialTerm x) (Set.Icc (1/2) (11/14)) := by
    refine Seven.monoOn_of_hasDeriv_nonneg (d := fun x => -specialFirst x)
      (fun x _ => (special_hasDeriv x).continuousAt.neg.continuousWithinAt)
      (fun x _ => (special_hasDeriv x).neg) ?_
    intro x hx
    exact neg_nonneg.mpr (special_derivative_nonpositive ⟨hx.1.le,hx.2.le⟩)
  have h := hm hd (by norm_num : (11:ℝ)/14 ∈ Set.Icc (1/2) (11/14)) hd.2
  linarith

end SquaresInCircles.Six.Analytic.SouthOuterTail.Own

import SquaresInCircles.Seven.BoundarySegments
import SquaresInCircles.Seven.Contacts

/-!
# The forward axis, negative target sign

A positive source with any active label, and a negative source with an axial
label. The support of the target is bounded below by Cauchy–Schwarz on the disk
and polynomial certificates, and at medium turns by the tangent of the disk at
the transition state. The sum vanishes only at an axial source and a side
target.
-/
noncomputable section
namespace SquaresInCircles.Seven
open Boundary

/-- The lower bound of the forward sector with target sign `-1`, in the turn `e`
and the signed source label `r`. -/
def rawTarget (A v e r : ℝ) : ℝ :=
  1/2+(4/5)*r-(A-1/2)*Real.cos e-v*Real.sin e+|Real.sin e|/2

lemma forward_negative_target_lower {a u A v : ℝ} (sgn : TransverseSign)
    (h : Admissible a u) (h' : Admissible A v)
    (hsource : sgn=.positive ∨ label a u=axial u) :
    rawTarget A v (sgn.coe*label a u+label A v-Real.pi/6)
      (sgn.coe*label a u) ≤ pairSupport a u A v sgn .negative 1 gap := by
  let e := sgn.coe*label a u+label A v-Real.pi/6
  have hc : 0 ≤ Real.cos e := by
    have ht0 := h.label_nonneg
    have ht1 := h.label_le_quarter
    have hs0 := h'.label_nonneg
    have hs1 := h'.label_le_quarter
    apply Real.cos_nonneg_of_mem_Icc
    cases sgn <;> dsimp [e,TransverseSign.coe] <;> constructor <;> linarith [Real.pi_pos]
  have hsource' : (4/5)*(sgn.coe*label a u) ≤ sgn.coe*u := by
    rcases hsource with rfl | he
    · have hh := h.label_le_axial
      dsimp [TransverseSign.coe,axial] at *
      linarith
    · rw [he]
      dsimp [axial]
      cases sgn <;> norm_num [TransverseSign.coe]
  have hangle : 3*Real.pi/2-gap-sgn.coe*label a u-label A v=Real.pi-e := by
    dsimp [e,gap]
    ring
  rw [pairSupport_one,show TransverseSign.negative.coe = -1 from rfl]
  simp only [neg_one_mul,← sub_eq_add_neg]
  rw [hangle]
  simp only [support,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg,abs_of_nonneg hc]
  change rawTarget A v e (sgn.coe*label a u) ≤ _
  dsimp [rawTarget]
  linarith

/-- An axial target at a turn `-z` with `0 ≤ z ≤ π/2`. For `z ≤ 1/3` the tie
line `9A + 11v ≤ 2π + 7` of the axial label enters as a dual constraint. -/
lemma axial_target_support {A v z : ℝ} (h : Admissible A v) (hA : label A v=axial v)
    (hz : 0 ≤ z ∧ z ≤ Real.pi/2) :
    0 < 1+2*Real.pi/15-(4/5)*z+Real.cos z-(A+1/2)*Real.cos z-(v+1/2)*(1-Real.sin z) := by
  have hs0 : 0 ≤ Real.sin z :=
    Real.sin_nonneg_of_nonneg_of_le_pi hz.1 (by linarith [hz.2,Real.pi_pos])
  have hsL := sin_lower_seven hz.1
  have hcL := cos_lower_six hz.1
  by_cases hsmall : z ≤ 1/3
  · let n := (3/40)*(1-2*Real.sin z)
    let L := Real.cos z-11/40-Real.pi/60-(4/5)*z+(51/20+3*Real.pi/10)*Real.sin z
    let P := 1-z^2/2+z^4/24-z^6/720-55/168-(4/5)*z+
      (873/250)*(z-z^3/6+z^5/120-z^7/5040)
    let U := 1189/800-(27/20)*(1-z^2/2+z^4/24-z^6/720)+
      (27/10)*(1-z^2/2+z^4/24)*(z-z^3/6+z^5/120)+(249/200)*(z^2-z^4/3+2*z^6/45)-
      (319/200)*(z-z^3/6+z^5/120-z^7/5040)
    have hn : 0 ≤ n := by dsimp [n]; linarith [Real.sin_le hz.1]
    have hPL : P ≤ L := by
      have := mul_nonneg (show 0 ≤ 51/20+3*Real.pi/10-873/250 by linarith [Real.pi_gt_d2]) hs0
      dsimp [P,L]
      linarith [pi_lt_22_over_7]
    have hP : 1/2 < P := by
      have hz2 : z^2 ≤ (1/3)^2 := by nlinarith
      have hz3 : z^3 ≤ (1/3)^3 := pow_le_pow_left₀ hz.1 hsmall 3
      have := mul_nonneg (pow_nonneg hz.1 4) (show 0 ≤ 1/24-z^2/720 by linarith)
      have := mul_nonneg (pow_nonneg hz.1 5) (show 0 ≤ 1/120-z^2/5040 by linarith)
      dsimp [P]
      linarith
    have hU : (Real.cos z-9*n)^2+(1-Real.sin z-11*n)^2 ≤ U := by
      have hc0 : 0 ≤ Real.cos z := Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos],hz.2⟩
      have hcU := cos_upper_four hz.1
      have hcs := mul_le_mul hcU (sin_upper_five hz.1) hs0 (hc0.trans hcU)
      have hsin2 : Real.sin z^2 ≤ z^2-z^4/3+2*z^6/45 := by
        linarith [Real.sin_sq_add_cos_sq z,cos_sq_lower_six hz.1]
      dsimp [n,U]
      linarith [Real.sin_sq_add_cos_sq z]
    have hdisc : 0 < P^2-(13/4)*U :=
      bernstein_pos (p := fun z => (1-z^2/2+z^4/24-z^6/720-55/168-(4/5)*z+
          (873/250)*(z-z^3/6+z^5/120-z^7/5040))^2-(13/4)*(1189/800-
          (27/20)*(1-z^2/2+z^4/24-z^6/720)+(27/10)*(1-z^2/2+z^4/24)*(z-z^3/6+z^5/120)+
          (249/200)*(z^2-z^4/3+2*z^6/45)-(319/200)*(z-z^3/6+z^5/120-z^7/5040)))
        ![13553/1411200,72827/7056000,393747163/34398000000,
          2710739309/206388000000,9910498733/638512875000,
          153072314621/8172964800000,47296571468413/2068781715000000,
          3708166534047959/132402029760000000,188854262621881/5516751240000000,
          6257753867831/150456852000000,6998517462046433/139642765762500000,
          48606823214392757/812467000800000000,29832818108969789/421857865800000000,
          34918908326684453/421857865800000000,80964059146525129/843715731600000000]
        (fun i => by fin_cases i <;> norm_num) (by norm_num)
        (fun x => by simp only [bernstein,Fin.sum_univ_succ,Fin.sum_univ_zero]
                     norm_num [Nat.choose]; ring) ⟨hz.1,hsmall⟩
    have hcs := dot_gt (p := -(Real.cos z-9*n)) (r := -(1-Real.sin z-11*n)) (c := L)
      h.phi_le (by linarith) (by unfold targetSq; nlinarith)
    have hline := mul_le_mul_of_nonneg_left
      (show 9*(A+1/2)+11*(v+1/2) ≤ 2*Real.pi+17 by linarith [axial_tie_line h hA]) hn
    dsimp [n,L] at hcs hline
    linarith
  · have hzu : z ≤ 11/7 := by linarith [hz.2,pi_lt_22_over_7]
    have hdiff : 0 ≤ Real.cos (z/2)-Real.sin (z/2) :=
      sub_nonneg.mpr (sin_le_cos_of_small ⟨by linarith,by linarith [hz.2]⟩)
    have hunit : Real.cos z^2+(1-Real.sin z)^2 = 2*(Real.cos (z/2)-Real.sin (z/2))^2 := by
      have hsin : Real.sin z=2*Real.sin (z/2)*Real.cos (z/2) := by
        rw [← Real.sin_two_mul]; ring_nf
      linarith [Real.sin_sq_add_cos_sq z,Real.sin_sq_add_cos_sq (z/2)]
    have hcs := dot_ge (p := -Real.cos z) (r := -(1-Real.sin z))
      (c := (51/20)*(Real.cos (z/2)-Real.sin (z/2))) h.phi_le (by positivity)
      (by unfold targetSq; nlinarith)
    have hp : 0 < 1+157/375-(4/5)*z+(1-z^2/2+z^4/24-z^6/720)-
        (51/20)*((1-(z/2)^2/2+(z/2)^4/24)-((z/2)-(z/2)^3/6+(z/2)^5/120-(z/2)^7/5040)) :=
      bernstein_pos (p := fun z => 1+157/375-(4/5)*z+(1-z^2/2+z^4/24-z^6/720)-
          (51/20)*((1-(z/2)^2/2+(z/2)^4/24)-((z/2)-(z/2)^3/6+(z/2)^5/120-(z/2)^7/5040)))
        ![27834859/5225472000,21646979107/329204736000,85094698273/768144384000,
          83663391929/597445632000,650018406713/4182119424000,224217116981/1394039808000,
          1222825127771/7589772288000,8516973787387/53128406016000]
        (fun i => by fin_cases i <;> norm_num) (by norm_num)
        (fun x => by simp only [bernstein,Fin.sum_univ_succ,Fin.sum_univ_zero]
                     norm_num [Nat.choose]; ring) ⟨(lt_of_not_ge hsmall).le,hzu⟩
    have hch := cos_upper_four (show 0 ≤ z/2 by linarith)
    have hsh := sin_lower_seven (show 0 ≤ z/2 by linarith)
    linarith [Real.pi_gt_d2]

lemma side_transition_trade {A v : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) :
    (12/25)*(v-u0) ≤ a0-A := by
  have hb := side_state_transition_bounds h hT
  have he := transition_circle
  have hc := transition_bounds
  have hp := h.phi_le
  have ht : X0*(A-a0)+Y0*(v-u0) ≤ 0 := by
    dsimp [phi,a0,u0] at hp ⊢
    linarith [sq_nonneg (A+1/2-X0),sq_nonneg (v+1/2-Y0)]
  have hratio : (12/25)*X0 < Y0 := by
    dsimp [a0,u0] at hc
    linarith
  have hm := mul_nonneg (sub_nonneg.mpr hb.1) (sub_nonneg.mpr hratio.le)
  have hXpos : 0 < X0 := by dsimp [a0] at hc; linarith
  by_contra hn
  have hbad := mul_pos
    (show 0 < (12/25)*(v-u0)-(a0-A) by linarith) hXpos
  linarith

def sideTarget (A v e : ℝ) : ℝ :=
  (4/5)*e+(2/15)*remainder A v+(A-1/2)*(1-Real.cos e)
    -v*Real.sin e+|Real.sin e|/2

lemma sideTarget_positive_angle {A v e : ℝ} (h : Admissible A v)
    (he : 0 ≤ e ∧ e ≤ Real.pi/3) :
    (21/40)*e+(2/15)*remainder A v ≤ sideTarget A v e := by
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi he.1
    (by linarith [he.2,Real.pi_pos])
  have hs1 := Real.sin_le he.1
  have hc := mul_nonneg (show 0 ≤ A-1/2 by linarith [h.half_le])
    (sub_nonneg.mpr (Real.cos_le_one e))
  have hv := mul_nonneg (show 0 ≤ 31/40-v by linarith [h.u_lt]) hs0
  have hrem := mul_nonneg (show (0:ℝ) ≤ 11/40 by norm_num) (sub_nonneg.mpr hs1)
  dsimp [sideTarget]
  rw [abs_of_nonneg hs0]
  linarith

lemma sideTarget_negative_pos {A v z : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) (hz : 0 < z ∧ z < 1) :
    0 < sideTarget A v (-z) := by
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le
    (by linarith [hz.2,Real.pi_gt_d2])
  have hexp (a u : ℝ) : sideTarget a u (-z) =
      Real.cos z-2/15-(4/5)*z+(3/5-Real.cos z)*(a+1/2)+(Real.sin z-4/15)*(u+1/2) := by
    dsimp [sideTarget,remainder]
    rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg hs0]
    ring
  rw [hexp]
  by_cases hsmall : z ≤ 1/6
  · have hH : 0 < 26/75-(653/300)*z+(23/45)*z^2+(349/720)*z^3-(47/900)*z^4-
        (1069/21600)*z^5-(13/37800)*z^6 :=
      bernstein_pos (p := fun z => 26/75-(653/300)*z+(23/45)*z^2+(349/720)*z^3-
          (47/900)*z^4-(1069/21600)*z^5-(13/37800)*z^6)
        ![26/75,3091/10800,11017/48600,523261/3110400,3882011/34992000,
          55351163/1007769600,1001149/3527193600]
        (fun i => by fin_cases i <;> norm_num) (by norm_num)
        (fun x => by simp only [bernstein,Fin.sum_univ_succ,Fin.sum_univ_zero]
                     norm_num [Nat.choose]; ring) ⟨hz.1.le,hsmall⟩
    have hL : 0 ≤ Real.cos z-2/15-(4/5)*z := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := z)]
    have hcs := dot_gt (p := 3/5-Real.cos z) (r := Real.sin z-4/15) h.phi_le hL (by
      have := mul_le_mul_of_nonneg_left (cos_upper_four hz.1.le) hz.1.le
      have := cos_sq_lower_six hz.1.le
      have := cos_lower_six hz.1.le
      have := sin_lower_seven hz.1.le
      have := mul_pos hz.1 hH
      unfold targetSq
      nlinarith [Real.sin_sq_add_cos_sq z,pow_nonneg hz.1.le 4])
    linarith
  have hbig : 1/6 ≤ z := (lt_of_not_ge hsmall).le
  have hb := side_state_transition_bounds h hT
  have ht := side_transition_trade h hT
  have hc := transition_coarse
  by_cases hcos : 3/5 ≤ Real.cos z
  · -- compared with the transition state, a positive profile
    have hsin := Real.sin_ge_sub_cube (show 0 ≤ z by linarith)
    have hcosU := cos_upper_four (show 0 ≤ z by linarith)
    have hsinU := Real.sin_le (show 0 ≤ z by linarith)
    have htrans : 0 < Real.cos z-2/15-(4/5)*z+(3/5-Real.cos z)*(a0+1/2)+
        (Real.sin z-4/15)*(u0+1/2) := by
      have hpA := mul_nonneg (show 0 ≤ a0-1/2-3/5 by linarith) (sub_nonneg.mpr (Real.cos_le_one z))
      have hpU := mul_nonneg (show 0 ≤ u0+1/2-79/100 by linarith) hs0
      have hcube := mul_nonneg (pow_nonneg (show 0 ≤ z by linarith) 3)
        (show (0:ℝ) ≤ 4/5-79/100 by norm_num)
      have hz3 : z^3 ≤ z^2 := by nlinarith [mul_nonneg (sq_nonneg z) (show 0 ≤ 1-z by linarith)]
      have hz4 : z^4 ≤ z^2 := by nlinarith [mul_nonneg (sq_nonneg z) (show 0 ≤ 1-z^2 by nlinarith)]
      have hpos := mul_pos (show 0 < z by linarith) (show 0 < -1/100+(17/120)*z by linarith)
      linarith
    by_cases hsin4 : 4/15 ≤ Real.sin z
    · have h1 := mul_nonneg (show 0 ≤ Real.cos z-3/5 by linarith)
        (show 0 ≤ a0-A by linarith [hb.2.1])
      have h2 := mul_nonneg (show 0 ≤ Real.sin z-4/15 by linarith)
        (show 0 ≤ v-u0 by linarith [hb.1])
      linarith
    · have hcos' : 24/25 < Real.cos z := by
        nlinarith [Real.sin_sq_add_cos_sq z]
      have hsin' : (33:ℝ)/200 < Real.sin z := by
        have hm := Real.sin_le_sin_of_le_of_le_pi_div_two (x := 1/6) (y := z)
          (by linarith [Real.pi_gt_d2]) (by linarith [hz.2,Real.pi_gt_d2]) hbig
        have hl := Real.sin_ge_sub_cube (show (0:ℝ) ≤ 1/6 by norm_num)
        linarith
      have h1 := mul_nonneg (show 0 ≤ Real.cos z-3/5 by linarith)
        (show 0 ≤ a0-A-(12/25)*(v-u0) by linarith)
      have h2 := mul_nonneg (show 0 ≤ v-u0 by linarith [hb.1])
        (show 0 ≤ (12/25)*(Real.cos z-3/5)+Real.sin z-4/15 by linarith)
      linarith
  · have hc0 : (1:ℝ)/2 < Real.cos z := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := z)]
    have hsin : 4/5 < Real.sin z := by
      nlinarith [Real.sin_sq_add_cos_sq z]
    have h1 := mul_nonneg (show 0 ≤ 3/5-Real.cos z by linarith) h.a_nonneg
    have h2 := mul_nonneg (show 0 ≤ v-29/100 by linarith [hb.1,hc.2.2.1])
      (show 0 ≤ Real.sin z-4/15 by linarith)
    linarith

lemma negative_target_axial_pos {A v e r : ℝ}
    (h : Admissible A v) (hA : label A v=axial v)
    (he : -Real.pi/2 ≤ e ∧ e ≤ Real.pi/3)
    (hr : e=r+label A v-Real.pi/6) : 0 < rawTarget A v e r := by
  have hv : v ≤ Real.pi/5 := by
    have hh := h.label_le_quarter
    rw [hA] at hh
    dsimp [axial] at hh
    linarith
  have hidentity : rawTarget A v e r =
      1/2+2*Real.pi/15+(4/5)*e-(A-1/2)*Real.cos e-
      v*(1+Real.sin e)+|Real.sin e|/2 := by
    rw [hA] at hr
    dsimp [rawTarget,axial] at *
    linarith
  rw [hidentity]
  by_cases he0 : 0 ≤ e
  · have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi he0
      (by linarith [he.2,Real.pi_pos])
    have hsin := Real.sin_le he0
    have hc := mul_nonneg (show 0 ≤ A-1/2 by linarith [h.half_le])
      (sub_nonneg.mpr (Real.cos_le_one e))
    have hp := mul_nonneg (show 0 ≤ 13/20-v by linarith [pi_lt_22_over_7]) hs0
    have hm := mul_nonneg (show (0:ℝ) ≤ 3/20 by norm_num) (sub_nonneg.mpr hsin)
    rw [abs_of_nonneg hs0]
    have hsum := axial_sum_lt h hA
    linarith [Real.pi_gt_d2]
  · have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ -e by linarith)
      (by linarith [he.1,Real.pi_pos])
    have hp := axial_target_support h hA ⟨show 0 ≤ -e by linarith,by linarith [he.1]⟩
    simp only [Real.cos_neg,Real.sin_neg] at hp hs0
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- The forward axis with target sign `-1`: zero only at an axial source and a
side target. -/
theorem fixed_gap_forward_negative_target {a u A v : ℝ} (sgn : TransverseSign)
    (h : Admissible a u) (h' : Admissible A v)
    (hsource : sgn=.positive ∨ label a u=axial u)
    (htarget : ActiveLabel A v) : PairProperty a u A v sgn .negative 1 := by
  let r := sgn.coe*label a u
  let e := r+label A v-Real.pi/6
  have hlow := forward_negative_target_lower sgn h h' hsource
  change rawTarget A v e r ≤ _ at hlow
  have h0 := h.label_nonneg
  have h1 := h.label_le_quarter
  have he : -Real.pi/2 ≤ e ∧ e ≤ Real.pi/3 := by
    have h2 := h'.label_nonneg
    have h3 := h'.label_le_quarter
    cases sgn <;> dsimp [e,r,TransverseSign.coe] <;> constructor <;> linarith [Real.pi_pos]
  rcases htarget with hA | hT
  · exact .of_pos ((negative_target_axial_pos h' hA he rfl).trans_le hlow)
  have hid : rawTarget A v e r=sideTarget A v e := by
    have hr : e=r+label A v-Real.pi/6 := rfl
    rw [hT,side_identity_radial] at hr
    dsimp [rawTarget,sideTarget]
    linear_combination (-4/5)*hr
  rw [hid] at hlow
  by_cases he0 : 0 ≤ e
  · have hp := sideTarget_positive_angle h' ⟨he0,he.2⟩
    have hW := h'.remainder_nonneg
    refine ⟨by linarith,fun hz => ?_⟩
    have hc := remainder_zero h' (by linarith)
    have ht : label a u=0 := by
      have he' : e=0 := by linarith
      dsimp [e,r] at he'
      rw [hc.1,hc.2,side_label] at he'
      cases sgn <;> dsimp [TransverseSign.coe] at he' <;> linarith
    exact Or.inr (Or.inr ⟨rfl,axial_of_transverse_zero h (h.label_zero_iff.mp ht),hc⟩)
  · have hs := side_selected_label_gt h' hT
    have hp := sideTarget_negative_pos h' hT (z := -e) ⟨by linarith,by
      cases sgn <;> dsimp [e,r,TransverseSign.coe] <;> linarith [pi_lt_22_over_7]⟩
    rw [neg_neg] at hp
    exact .of_pos (hp.trans_le hlow)

end SquaresInCircles.Seven

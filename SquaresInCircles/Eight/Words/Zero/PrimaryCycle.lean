module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import SquaresInCircles.Eight.Frames.Core.MidFullCircle
public import SquaresInCircles.Eight.Words.Common.OneSecondary
public import SquaresInCircles.Eight.Words.Common.QuarterState
public import SquaresInCircles.Eight.Words.Common.Zero

/-!
# Eight squares: the closed-tour exclusion of an original zero-primary witness

The original primary edge has boosted cost greater than `.985`. The
other six original edges each have G1 cost greater than `.8833`.
The closed physical frame tour pays at least the exceptional edge's
frame cost on its return path, so these estimates exceed `2*pi` after
the unchanged original vertex labels cancel.

The continuous G1 pair estimates are the explicit upstream input to
this assembly. The exceptional primary estimate and the closed-tour
return estimate are proved here and in `ZeroPrimarySupport`; neither
wrong-word exclusion is an input.
-/

section
/-!
## What an original zero-quarter primary owner forces

The original physical gap and weak primary inequality force a positive
source tangent, an outer target and a frame deviation greater than `.45`.
The reflection identity retains the same gap for the other primary owner.
No wrong-word conclusion or mismatch assumption is used.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ZeroPrimary

open FramePair

def radialKind (s : State) : RadialKind := if s.branch.type=0 then .coreSide else .outer

theorem semantic_state (s : State) : CommonQuarter.State (radialKind s) s.a s.b := by
  by_cases hc : s.branch.type=0
  · simpa [radialKind,hc,CommonQuarter.State] using FrameCoreArc.state_core_chart s hc
  · have hh : CommonQuarter.OuterState s.a s.b := ⟨s.b_nonneg,s.canonical,s.outer_eq hc⟩
    simpa [radialKind,hc,CommonQuarter.State] using hh

theorem sign_eq (p : Bool) : (WordProblems.sign p:ℝ)=FramePair.sign p := by
  cases p <;> norm_num [WordProblems.sign,FramePair.sign]

theorem primary_lower (s : State) : (447/800:ℝ)<s.a := by
  by_cases hc : s.branch.type=0
  · have hh := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart s hc)).1
    linarith [CoreAngleEndpoint.diagonal_bounds.1]
  · have hh := CommonQuarter.outer_bounds
      (show CommonQuarter.OuterState s.a s.b from ⟨s.b_nonneg,s.canonical,s.outer_eq hc⟩)
    linarith [hh.1,CommonQuarter.outer_endpoint_bounds.2.2.1]

theorem coordinates (s : State) :
    (447/800:ℝ)<s.a ∧ s.a<283/200 ∧ 0≤ s.b ∧ s.b≤ s.a ∧ s.b<9/10 := by
  have hh := CommonQuarter.state_bounds (semantic_state s)
  exact ⟨primary_lower s,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2⟩

/-- Every original target-primary zero contact lies in the same forced
large positive interval and has a strictly positive source tangent. -/
theorem target_primary_domain (s t : State) {d : ℝ} (hd : |d|≤7/10)
    (hg : (19/25:ℝ)<s.gap t d) (hm : s.Feasible t 1 d) :
    d∈Ioc (9/20) (7/10) ∧ s.positive=true ∧ 0<s.b ∧ 1<t.a ∧ t.branch.type≠0 := by
  have hs := semantic_state s
  have ht := semantic_state t
  have hsc := coordinates s
  have htc := coordinates t
  have hm₀ : 0≤forwardMargin 1 s.a s.b t.a t.b
      (WordProblems.sign s.positive) (WordProblems.sign t.positive) d := by
    simpa [State.Feasible,sign_eq] using hm
  have hg₀ : (19/25:ℝ)<d+(WordProblems.sign s.positive:ℝ)*Real.arctan (s.b/s.a)-
      (WordProblems.sign t.positive:ℝ)*Real.arctan (t.b/t.a) := by
    simpa [State.gap,State.offset,sign_eq] using hg
  have hmr : 0≤forwardMargin 3 t.a t.b s.a s.b
      (WordProblems.sign (!t.positive)) (WordProblems.sign (!s.positive)) d := by
    rw [← CommonQuarter.margin_reverse 1 s.positive t.positive s.a s.b t.a t.b d] at hm₀
    simpa using hm₀
  have hgr : (19/25:ℝ)<d+(WordProblems.sign (!t.positive):ℝ)*Real.arctan (t.b/t.a)-
      (WordProblems.sign (!s.positive):ℝ)*Real.arctan (s.b/s.a) := by
    rwa [CommonQuarter.gap_reverse]
  have hpositive : s.positive=true := by
    cases hp : s.positive
    · have hmf : 0≤forwardMargin 3 t.a t.b s.a s.b
          (WordProblems.sign (!t.positive)) 1 d := by
        simpa [hp,WordProblems.sign] using hmr
      have hgf : (19/25:ℝ)<d+(WordProblems.sign (!t.positive):ℝ)*Real.arctan (t.b/t.a)-
          Real.arctan (s.b/s.a) := by simpa [hp,WordProblems.sign] using hgr
      exact (CommonQuarter.zero_primary_positive_target_false ht hs (!t.positive) hd hgf hmf).elim
    · rfl
  have hmr' : 0≤forwardMargin 3 t.a t.b s.a s.b
      (WordProblems.sign (!t.positive)) (-1) d := by
    simpa [hpositive,WordProblems.sign] using hmr
  have hp : 0<d := CommonQuarter.zero_primary_negative_angle ht hs (!t.positive) hd hmr'
  have hdi : d∈Icc 0 (7/10) := ⟨hp.le,(abs_le.mp hd).2⟩
  have tr := CommonQuarter.positive_trig hdi
  have hsin : 0<Real.sin d := by
    linarith [(CommonQuarter.positive_taylor_reserves hdi).1]
  have hcos : 0<Real.cos d := by linarith [tr.1]
  have hdiff : 0<Real.cos d-Real.sin d := by linarith [tr.1,tr.2.2.2.1]
  have hbase : t.a-s.a*Real.cos d<1 := by
    have hh := mul_lt_mul_of_pos_right hsc.1 hcos
    nlinarith [htc.2.1,tr.1]
  have hm' : 0≤t.a-s.a*Real.cos d+s.b*Real.sin d-pairWidth d := by
    simpa [State.Feasible,forwardMargin,hpositive,FramePair.sign] using hm
  have hw := CommonQuarter.width_ge_one d
  have hb : 0<s.b := by
    by_contra! hn
    have hh := mul_nonpos_of_nonpos_of_nonneg hn hsin.le
    linarith
  have hbs := mul_le_mul_of_nonneg_right s.canonical hsin.le
  have hapos : 0<s.a*(Real.cos d-Real.sin d) := mul_pos s.a_pos hdiff
  have htarget : 1<t.a := by nlinarith
  have hlarge : (9/20:ℝ)<d := by
    by_contra! hsmall
    have hA := mul_le_mul_of_nonneg_right hsc.1.le hdiff.le
    have hc := Real.one_sub_sq_div_two_le_cos (x := d)
    have hsine := Real.sin_le hp.le
    have hd2 := pow_le_pow_left₀ hp.le hsmall 2
    rw [CommonQuarter.signed_width hd,abs_of_nonneg hsin.le] at hm'
    nlinarith [htc.2.1]
  have houter : t.branch.type≠0 := by
    intro hc
    have hh := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart t hc)).2.1
    linarith
  exact ⟨⟨hlarge,hdi.2⟩,hpositive,hb,htarget,houter⟩

end SquaresInCircles.Eight.ZeroPrimary
end
end
end

section
/-!
## Whole-chart coarse supports for the unchanged G1 frame marker

The low, middle and high outer labels are bounded on their complete
intrinsic arcs. The middle and high endpoint rules use the original
positive circle branch; the other estimates are full-circle supports.
The same selected label remains attached to each original vertex.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ZeroPrimary

open FramePair FrameCircleArc FrameLowArc FrameMidArc

def unsigned (s : State) : ℝ := FramePair.label s.branch s.a s.b

lemma outer_data (s : State) (hs : s.branch.type≠0) :
    CommonQuarter.OuterState s.a s.b := ⟨s.b_nonneg,s.canonical,s.outer_eq hs⟩

lemma axial_loss (s : State) (hs : s.branch.type≠0) :
    0≤a0-s.a ∧ a0-s.a≤(3/5)*s.b := by
  have hb := CommonQuarter.outer_bounds (outer_data s hs)
  have hau : s.a≤a0 := hb.2.1
  have hid : (a0-s.a)*(a0+s.a+1)=s.b^2+s.b := by
    have hcircle := s.outer_eq hs
    have haxis := CommonQuarter.axial_circle
    change (a0+1/2)^2+(1/2:ℝ)^2=Q0 at haxis
    nlinarith
  have hden : (33/10:ℝ)≤a0+s.a+1 := by
    have ha := hb.1
    change c0≤ s.a at ha
    linarith [a0_bounds.1,c0_bounds.1]
  have hbU : s.b≤9/10 := s.b_upper
  have h₁ := mul_le_mul_of_nonneg_left hden (sub_nonneg.mpr hau)
  have h₂ := mul_le_mul_of_nonneg_left (show s.b+1≤19/10 by linarith) s.b_nonneg
  exact ⟨sub_nonneg.mpr hau,by nlinarith [s.b_nonneg]⟩

lemma low_marker_bounds (s : State) (hs : s.branch=.low) :
    (4/5)*s.b≤unsigned s ∧ unsigned s≤(2/5)*(s.a-a0)+(111/100)*s.b := by
  have ht : s.branch.type≠0 := by simp [hs,Branch.type]
  have hh := axial_loss s ht
  dsimp [unsigned]
  rw [hs]
  dsimp [FramePair.label]
  constructor <;> nlinarith [s.b_nonneg]

lemma middle_marker_lower (s : State) (hs : s.branch=.middle) :
    (4/5)*s.b≤unsigned s := by
  have hb := state_mid_chart s hs
  have hh := linear_endpoint_lower (p := (1489593/1000000:ℝ))
    (q := (780219/1000000:ℝ)) (by norm_num) b1_mem.1 b2_mem.2 hb.2
  have hleft : (85723/40000:ℝ)≤linear (1489593/1000000) (780219/1000000) b1 := by
    rw [linear,A_b1]
    dsimp [b1]
    nlinarith [a1_bounds.1]
  have hright : (85723/40000:ℝ)≤linear (1489593/1000000) (780219/1000000) b2 := by
    rw [linear,A_b2]
    dsimp [b2]
    nlinarith [a2_bounds.1]
  have hlow := (le_min hleft hright).trans hh
  dsimp [unsigned]
  rw [hs]
  dsimp [FramePair.label]
  rw [hb.1]
  dsimp [linear] at hlow
  linarith

lemma middle_marker_upper (s : State) (hs : s.branch=.middle) :
    unsigned s≤(2/5)*(s.a-a0)+(111/100)*s.b := by
  let u : ℝ := 1089593/1000000
  let v : ℝ := 470219/1000000
  have hcircle := CommonQuarter.outer_circle_lower (X := -u) (Y := -v)
    (outer_data s (by simp [hs,Branch.type]))
  have hnorm : Real.sqrt (u^2+v^2)<1187/1000 := by
    have hh := Real.sq_sqrt (show 0≤u^2+v^2 by positivity)
    have hn := Real.sqrt_nonneg (u^2+v^2)
    dsimp [u,v] at *
    nlinarith
  have hR : 0<CommonQuarter.radius := by linarith [CommonQuarter.radius_bounds.1]
  have hprod := (mul_lt_mul_of_pos_left hnorm hR).trans
    (mul_lt_mul_of_pos_right CommonQuarter.radius_bounds.2
      (by norm_num : (0:ℝ)<1187/1000))
  simp only [neg_sq] at hcircle
  dsimp [unsigned]
  rw [hs]
  dsimp [FramePair.label,u,v] at *
  nlinarith [a0_bounds.2]

lemma state_high_chart (s : State) (hs : s.branch=.high) :
    s.a=A s.b ∧ s.b∈Icc b2 c0 := by
  have ht : s.branch.type≠0 := by simp [hs,Branch.type]
  have hh := state_outer_chart s ht
  have hcut : 3*s.a≤7*s.b := by simpa [hs,TypeMem] using s.type_mem
  refine ⟨hh.1,?_,hh.2.2⟩
  by_contra! hn
  have ha := A_antitone hh.2 b2_mem hn.le
  rw [A_b2,← hh.1] at ha
  have hendpoint : 3*a2=7*b2 := by dsimp [b2]; ring
  nlinarith

lemma high_marker_lower (s : State) (hs : s.branch=.high) :
    (4/5)*s.b≤unsigned s := by
  let f : ℝ := 8898/15625
  let r : ℝ := 195443/500000
  have hcircle := CommonQuarter.outer_circle_lower (X := -f) (Y := -(4/5-r))
    (outer_data s (by simp [hs,Branch.type]))
  have hnorm : Real.sqrt (f^2+(4/5-r)^2)<71/100 := by
    have hh := Real.sq_sqrt (show 0≤f^2+(4/5-r)^2 by positivity)
    have hn := Real.sqrt_nonneg (f^2+(4/5-r)^2)
    dsimp [f,r] at *
    nlinarith
  have hR : 0<CommonQuarter.radius := by linarith [CommonQuarter.radius_bounds.1]
  have hprod := (mul_lt_mul_of_pos_left hnorm hR).trans
    (mul_lt_mul_of_pos_right (show CommonQuarter.radius<2 by linarith [CommonQuarter.radius_bounds.2])
      (by norm_num : (0:ℝ)<71/100))
  simp only [neg_sq] at hcircle
  dsimp [unsigned]
  rw [hs]
  dsimp [FramePair.label,f,r] at *
  nlinarith [c0_bounds.1,Arithmetic.pi_hand_enclosure.1]

lemma high_marker_upper (s : State) (hs : s.branch=.high) :
    unsigned s≤(2/5)*(s.a-a0)+(111/100)*s.b := by
  let u : ℝ := 8898/15625+2/5
  let v : ℝ := 111/100-195443/500000
  let C0 : ℝ := Real.pi/4+(8898/15625-195443/500000)*c0+(2/5)*a0
  let Cup : ℝ := 11/14+(8898/15625-195443/500000)*(9/10)+(2/5)*(283/200)
  have hC : C0<Cup := by
    dsimp [C0,Cup]
    nlinarith [pi_lt_22_over_7,c0_bounds.2,a0_bounds.2]
  have hb := state_high_chart s hs
  have hh := linear_endpoint_lower (p := u) (q := v)
    (by norm_num [u]) b2_mem.1 le_rfl hb.2
  have hleft : Cup<linear u v b2 := by
    rw [linear,A_b2]
    dsimp [Cup,u,v,b2]
    nlinarith [a2_bounds.1]
  have hright : Cup<linear u v c0 := by
    rw [linear,A_c0]
    dsimp [Cup,u,v]
    nlinarith [c0_bounds.1]
  have hlow : C0<linear u v s.b := hC.trans_le
    ((lt_min hleft hright).le.trans hh)
  dsimp [unsigned]
  rw [hs]
  dsimp [FramePair.label,C0,u,v,linear] at *
  rw [hb.1]
  nlinarith

/-- Both bounds hold for every original outer chart, including both choices
at either type junction. -/
theorem outer_marker_bounds (s : State) (hs : s.branch.type≠0) :
    (4/5)*s.b≤unsigned s ∧ unsigned s≤(2/5)*(s.a-a0)+(111/100)*s.b := by
  cases hb : s.branch with
  | coreSide | coreCorner => simp [hb,Branch.type] at hs
  | low => exact low_marker_bounds s hb
  | middle => exact ⟨middle_marker_lower s hb,middle_marker_upper s hb⟩
  | high => exact ⟨high_marker_lower s hb,high_marker_upper s hb⟩

theorem core_marker_lower (s : State) (hs : s.branch.type=0) :
    7*(7/12-s.a)+(107/100)*s.b≤unsigned s := by
  have hh := FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart s hs)
  have hA : 0≤7/12-s.a := by linarith [hh.2.1]
  have hB := s.b_nonneg
  cases hb : s.branch <;> simp [hb,Branch.type] at hs
  all_goals dsimp [unsigned]; rw [hb]; dsimp [FramePair.label]; nlinarith

theorem marker_nonneg (s : State) : 0≤unsigned s := by
  by_cases hc : s.branch.type=0
  · have ha := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart s hc)).2.1
    nlinarith [core_marker_lower s hc,s.b_nonneg]
  · nlinarith [(outer_marker_bounds s hc).1,s.b_nonneg]

theorem signed_upper (s : State) : s.signedLabel≤unsigned s := by
  have hh : 0≤FramePair.label s.branch s.a s.b := marker_nonneg s
  cases hp : s.positive
  · simp only [State.signedLabel,unsigned,hp,FramePair.sign,Bool.false_eq_true,ite_false]
    linarith
  · simp [State.signedLabel,unsigned,hp,FramePair.sign]

end SquaresInCircles.Eight.ZeroPrimary
end
end
end

section
/-!
## Two complete polynomial supports for a zero-quarter primary contact

The half-angle substitution produces two degree-eight polynomials. Their
explicit differences from one common polynomial have nonnegative
coefficients after the single shift `x = 3/8-z`. The common polynomial
is positive on the whole interval by three grouped factors.

No angle cover or variable-domain certificate is used. The finite exact
coefficient reductions below are unexecuted proof scripts.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Set

namespace SquaresInCircles.Eight.ZeroPrimaryPolynomial

open Polynomial CommonQuarter Arithmetic

def mass : Bool→ℚ
  | false => 4/5
  | true => 107/100

def anchor : Bool→ℚ
  | false => 899/1000
  | true => 7/12

def B : Bool→ℚ[X]
  | false => C (2399/1250)+C (3863/2500)*X+C (139/25)*X^2+
      C (2963/2500)*X^3+C (4101/1250)*X^4
  | true => C (107/48)+C (2269/1250)*X+C (61/10)*X^2+
      C (1819/1250)*X^3+C (4213/1200)*X^4

def D : ℚ[X] := 1+X^2
def V (core : Bool) : ℚ[X] :=
  (C (mass core)*D+C (4/5)*X)^2+C (4*(111/100)^2)*X^2
def P (core : Bool) : ℚ[X] := (B core)^2-C (9789/2500)*D^2*V core
def J : ℚ[X] := C (1/100)+C 3*X-C 4*X^2-C 16*X^3+
  C 33*X^4-C 56*X^5+C 45*X^6-C 28*X^7+C 7*X^8
def remainder (core : Bool) : ℚ[X] := (P core).comp (C (3/8)-X)-J

/-- The exact coefficients of the two remainders, by evaluation. -/
private def r11_c : Bool → Fin 9 → ℚ
  | false => ![3060651919197/5242880000000, 55171396631/102400000000, 20322758981/20480000000,
      401086219/128000000, 1190115399/3200000000, 19156109/12500000, 20797309/25000000,
      361067/781250, 1965101/1562500]
  | true => ![6649627203349/15099494400000000, 12806316837187/78643200000000,
      41247230469769/19660800000000, 53775643369/245760000000, 4536743663087/1843200000000,
      1303400833/3840000000, 1542517241/4800000000, 286991131/300000000, 758682229/900000000]

private lemma r11_remainder_eq (core : Bool) :
    remainder core=∑j : Fin 9,C (r11_c core j)*X^j.val := by
  apply Polynomial.funext
  intro r
  simp only [remainder,P,D,V,J,eval_sub,eval_add,eval_mul,eval_pow,eval_C,eval_X,
    eval_comp,eval_one,Fin.sum_univ_succ,Fin.sum_univ_zero]
  cases core <;> simp [B,mass,r11_c] <;> ring

private lemma r11_coeff (core : Bool) (j : Fin 9) :
    (remainder core).coeff j.val=r11_c core j := by
  rw [r11_remainder_eq,finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have hne : (j:ℕ)≠b := fun h => hb (Fin.ext h.symm)
    simp [hne]
  · simp

theorem remainder_coeff_nonneg (core : Bool) :
    ∀j : Fin 9,0≤(remainder core).coeff j.val := by
  intro j
  rw [r11_coeff]
  cases core <;> fin_cases j <;> norm_num [r11_c]

theorem remainder_expansion (core : Bool) :
    (P core).comp (C (3/8)-X)=J+
      ∑j : Fin 9,C ((remainder core).coeff j.val)*X^j.val := by
  simp only [r11_coeff]
  rw [← r11_remainder_eq,remainder]
  ring

lemma J_positive {x : ℝ} (hx : x∈Icc 0 (3/20)) : 0<aeval x J := by
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have h₁ : 0≤3-4*x-16*x^2 := by nlinarith
  have h₂ : 0≤33-56*x := by linarith [hx.2]
  have h₃ : 0≤45-28*x := by linarith [hx.2]
  have ht₁ := mul_nonneg hx.1 h₁
  have ht₂ := mul_nonneg (pow_nonneg hx.1 4) h₂
  have ht₃ := mul_nonneg (pow_nonneg hx.1 6) h₃
  have ht₄ := pow_nonneg hx.1 8
  have he : aeval x J=(1/100:ℝ)+x*(3-4*x-16*x^2)+
      x^4*(33-56*x)+x^6*(45-28*x)+7*x^8 := by
    simp [J]
    ring
  rw [he]
  positivity

theorem polynomial_positive (core : Bool) {z : ℝ} (hz : z∈Icc (9/40) (3/8)) :
    0<aeval z (P core) := by
  set x : ℝ := 3/8-z with hxdef
  have hx : x∈Icc 0 (3/20) := ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hh : aeval x ((P core).comp (C (3/8)-X))=
      aeval x (J+∑j : Fin 9,C ((remainder core).coeff j.val)*X^j.val) := by
    rw [remainder_expansion core]
  have he : aeval x (C (3/8:ℚ)-X)=z := by
    simp only [map_sub,aeval_C,aeval_X,eq_ratCast,hxdef]
    push_cast
    ring
  rw [aeval_comp,he] at hh
  simp only [map_add,map_sum,map_mul,aeval_C,map_pow,aeval_X,eq_ratCast] at hh
  have hsum : 0≤∑j : Fin 9,((remainder core).coeff j.val:ℝ)*x^j.val := by
    apply Finset.sum_nonneg
    intro j _
    have hc : (0:ℝ)≤((remainder core).coeff j.val:ℝ) := by
      exact_mod_cast remainder_coeff_nonneg core j
    exact mul_nonneg hc (pow_nonneg hx.1 _)
  linarith [J_positive hx]

theorem numerator_positive (core : Bool) {z : ℝ} (hz : 0≤z) : 0<aeval z (B core) := by
  cases core <;> simp only [B,map_add,map_mul,map_pow,aeval_C,aeval_X] <;>
    norm_num <;> positivity

theorem radical_bound (core : Bool) {z : ℝ} (hz : z∈Icc (9/40) (3/8)) :
    CommonQuarter.radius*(1+z^2)*Real.sqrt (aeval z (V core))<aeval z (B core) := by
  have hV : 0≤aeval z (V core) := by simp [V,D]; positivity
  have hs := Real.sq_sqrt hV
  have hN := Real.sqrt_nonneg (aeval z (V core))
  have hP := polynomial_positive core hz
  have hB := numerator_positive core (z := z) (by linarith [hz.1])
  have hR := radius_sq
  have hR0 : 0≤CommonQuarter.radius := by linarith [radius_bounds.1]
  simp only [P,map_sub,map_pow,map_mul,aeval_C,D,map_add,aeval_one,aeval_X] at hP
  have he : (CommonQuarter.radius*(1+z^2)*Real.sqrt (aeval z (V core)))^2=
      Q0*(1+z^2)^2*aeval z (V core) := by rw [mul_pow,mul_pow,hR,hs]
  norm_num [Q0] at hR hP he
  have hproduct : 0≤CommonQuarter.radius*(1+z^2)*Real.sqrt (aeval z (V core)) := by positivity
  nlinarith

def angleNumerator (d : ℝ) : ℝ :=
  (d-37/1000)*(1+Real.cos d)-(9/5)*Real.sin d
def angleNumeratorD (d : ℝ) : ℝ :=
  1-(4/5)*Real.cos d-(d-37/1000)*Real.sin d
def angleNumeratorDD (d : ℝ) : ℝ :=
  -(1/5)*Real.sin d-(d-37/1000)*Real.cos d

lemma angleNumerator_deriv (d : ℝ) :
    HasDerivAt angleNumerator (angleNumeratorD d) d := by
  have h := (((hasDerivAt_id' d).sub_const (37/1000)).fun_mul
    ((Real.hasDerivAt_cos d).const_add 1)).fun_sub
      ((Real.hasDerivAt_sin d).const_mul (9/5))
  exact h.congr_deriv (by unfold angleNumeratorD; ring)

lemma angleNumeratorD_deriv (d : ℝ) :
    HasDerivAt angleNumeratorD (angleNumeratorDD d) d := by
  have h := (((Real.hasDerivAt_cos d).const_mul (4/5)).const_sub 1).fun_sub
    (((hasDerivAt_id' d).sub_const (37/1000)).fun_mul (Real.hasDerivAt_sin d))
  exact h.congr_deriv (by unfold angleNumeratorDD; ring)

lemma angleNumerator_concave :
    ConcaveOn ℝ (Icc (9/20) (7/10)) angleNumerator := by
  apply concave_of_deriv2 (fun d _ => angleNumerator_deriv d)
    (fun d _ => angleNumeratorD_deriv d)
  intro d hd
  have ht := positive_trig ⟨by linarith [hd.1],hd.2⟩
  have hh := mul_nonneg (show 0≤d-37/1000 by linarith [hd.1])
    (show 0≤Real.cos d by linarith [ht.1])
  dsimp [angleNumeratorDD]
  nlinarith [ht.2.2.1]

lemma angleNumerator_endpoints :
    0<angleNumerator (9/20) ∧ 0<angleNumerator (7/10) := by
  have hs := sin_upper_five (show (0:ℝ)≤9/20 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤9/20 by norm_num)
  norm_num at hs hc
  have ht := cap_trig
  dsimp [angleNumerator]
  constructor <;> linarith [ht.2.1,ht.2.2.1]

/-- A direct concavity argument gives the affine lower angle bound used
by both polynomial numerators. -/
theorem angle_lower {d : ℝ} (hd : d∈Icc (9/20) (7/10)) :
    (9/5)*halfRatio d+37/1000<d := by
  have hm := angleNumerator_concave.min_le_of_mem_Icc
    (by norm_num) (by norm_num) hd
  have hp : 0<angleNumerator d :=
    (lt_min angleNumerator_endpoints.1 angleNumerator_endpoints.2).trans_le hm
  have hd' : 0≤d ∧ d≤4/5 := ⟨by linarith [hd.1],by linarith [hd.2]⟩
  have hden := halfRatio_den_pos hd'
  have hid := (halfRatio_identities hd').1
  have hprod : 0<(d-(9/5)*halfRatio d-37/1000)*(1+Real.cos d) := by
    dsimp [angleNumerator] at hp
    nlinarith
  have hpos := pos_of_mul_pos_left hprod hden.le
  linarith

theorem half_angle_data {d : ℝ} (hd : d∈Icc (9/20) (7/10)) :
    halfRatio d∈Icc (9/40) (3/8) ∧
    (1+(halfRatio d)^2)*Real.sin d=2*halfRatio d ∧
    (1+(halfRatio d)^2)*Real.cos d=1-(halfRatio d)^2 := by
  have hd' : 0≤d ∧ d≤4/5 := ⟨by linarith [hd.1],by linarith [hd.2]⟩
  have hden := halfRatio_den_pos hd'
  have hid := halfRatio_identities hd'
  have ht := positive_trig ⟨hd'.1,hd.2⟩
  have hlow := halfRatio_lower hd'
  have hu : halfRatio d≤3/8 := by
    apply (div_le_iff₀ hden).2
    linarith [ht.1,ht.2.2.2.1]
  have he : (halfRatio d)^2*(1+Real.cos d)=1-Real.cos d := by
    nlinarith [congrArg (fun r : ℝ => halfRatio d*r) hid.1]
  refine ⟨⟨by linarith [hd.1],hu⟩,?_,?_⟩
  · nlinarith [congrArg (fun r : ℝ => halfRatio d*r) he]
  · nlinarith

def support (core : Bool) (d : ℝ) : ℝ :=
  let l : ℝ := (mass core:ℝ)/Real.sin d
  d+(9/50)*frameCost d+l*(oneWidth d+(anchor core:ℝ)*Real.cos d)+
    (2/5)*outerAxial+(l+2/5+111/100)/2-
      CommonQuarter.radius*Real.sqrt ((l+2/5)^2+(111/100)^2)

/-- The complete two-choice primary support on the full forced angle
interval; its only inputs are the intrinsic core/outer choice and angle. -/
theorem support_gt (core : Bool) {d : ℝ} (hd : d∈Icc (9/20) (7/10)) :
    (197/200:ℝ)<support core d := by
  let z : ℝ := halfRatio d
  let D0 : ℝ := 1+z^2
  let l : ℝ := (mass core:ℝ)/Real.sin d
  have hh := half_angle_data hd
  have hz : z∈Icc (9/40) (3/8) := hh.1
  have hz0 : 0<z := by linarith [hz.1]
  have hD : 0<D0 := by dsimp [D0]; positivity
  have ht := positive_trig ⟨by linarith [hd.1],hd.2⟩
  have hsin : 0<Real.sin d := by
    have hh := (positive_taylor_reserves ⟨by linarith [hd.1],hd.2⟩).1
    linarith [hd.1]
  have hs : Real.sin d=2*z/D0 := by
    apply (eq_div_iff hD.ne').2
    simpa [z,D0,mul_comm] using hh.2.1
  have hc : Real.cos d=(1-z^2)/D0 := by
    apply (eq_div_iff hD.ne').2
    simpa [z,D0,mul_comm] using hh.2.2
  have hl : l=(mass core:ℝ)*D0/(2*z) := by
    dsimp [l]
    rw [hs]
    field_simp [hD.ne',hz0.ne']
  have hl0 : 0≤l := by
    dsimp [l]
    apply div_nonneg _ hsin.le
    cases core <;> norm_num [mass]
  have hnorm : Real.sqrt (aeval z (V core))=
      2*z*Real.sqrt ((l+2/5)^2+(111/100)^2) := by
    have hnormsq := Real.sq_sqrt (show 0≤(l+2/5)^2+(111/100:ℝ)^2 by positivity)
    have hV : aeval z (V core)=
        (2*z*Real.sqrt ((l+2/5)^2+(111/100)^2))^2 := by
      simp only [V,D,map_add,map_mul,map_pow,aeval_C,aeval_one,aeval_X,eq_ratCast]
      rw [mul_pow,mul_pow,hnormsq,hl]
      push_cast
      dsimp [D0]
      field_simp [hz0.ne']
      ring
    rw [hV,Real.sqrt_sq (by positivity)]
  have hrad := radical_bound core hz
  have ha : (707/500:ℝ)<outerAxial := by linarith [fine_outer_endpoint_bounds.1]
  have hang : (9/5)*z+37/1000<d := angle_lower hd
  have hpositive : 0<2*z*D0*(d-((9/5)*z+37/1000)+(2/5)*(outerAxial-707/500)) := by
    apply mul_pos (by positivity)
    linarith
  have hid : 2*z*D0*(support core d-197/200)-
      (aeval z (B core)-CommonQuarter.radius*D0*Real.sqrt (aeval z (V core)))=
      2*z*D0*(d-((9/5)*z+37/1000)+(2/5)*(outerAxial-707/500)) := by
    rw [hnorm]
    dsimp [support]
    change 2*z*D0*(d+(9/50)*frameCost d+l*(oneWidth d+
      (anchor core:ℝ)*Real.cos d)+(2/5)*outerAxial+(l+2/5+111/100)/2-
        CommonQuarter.radius*Real.sqrt ((l+2/5)^2+(111/100)^2)-197/200)-
      (aeval z (B core)-CommonQuarter.radius*D0*(2*z*Real.sqrt ((l+2/5)^2+(111/100)^2)))=_
    dsimp [frameCost,oneWidth]
    rw [abs_of_nonneg hsin.le,hs,hc,hl]
    cases core <;> simp only [B,map_add,map_mul,map_pow,aeval_C,aeval_X,mass,anchor,eq_ratCast]
    all_goals push_cast; dsimp [D0]; field_simp [hz0.ne',hD.ne']; ring
  have hproduct : 0<2*z*D0*(support core d-197/200) := by
    change CommonQuarter.radius*D0*Real.sqrt (aeval z (V core))<aeval z (B core) at hrad
    linarith
  exact sub_pos.mp (pos_of_mul_pos_right hproduct (by positivity))

end SquaresInCircles.Eight.ZeroPrimaryPolynomial
end
end
end

section
/-!
## The boosted original zero-primary cost

The original primary inequality determines the allowed angle, tangent sign and radial choice. A
multiplier cancels the source transverse coordinate on the whole core or outer chart
(`source_support`). The target circle support is then one of the two polynomial supports
(`target_primary_boost`, `source_primary_boost`), and `actual_boost` applies this on the cycle.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ZeroPrimary

open FramePair CommonQuarter

lemma source_support (s : FramePair.State) (core : Bool)
    (hcore : core=true ↔ s.branch.type=0) {d : ℝ} (hd : d∈Icc (9/20) (7/10)) :
    ((ZeroPrimaryPolynomial.mass core:ℝ)/Real.sin d)*
        (ZeroPrimaryPolynomial.anchor core:ℝ)*Real.cos d≤
      unsigned s+((ZeroPrimaryPolynomial.mass core:ℝ)/Real.sin d)*s.a*Real.cos d-
        ((ZeroPrimaryPolynomial.mass core:ℝ)/Real.sin d)*s.b*Real.sin d := by
  let l : ℝ := (ZeroPrimaryPolynomial.mass core:ℝ)/Real.sin d
  have tr := positive_trig ⟨by linarith [hd.1],hd.2⟩
  have hsine : (2/5:ℝ)<Real.sin d := by
    have hh := (positive_taylor_reserves ⟨by linarith [hd.1],hd.2⟩).1
    linarith [hd.1]
  have hm : 0<(ZeroPrimaryPolynomial.mass core:ℝ) ∧
      (ZeroPrimaryPolynomial.mass core:ℝ)≤107/100 := by
    cases core <;> norm_num [ZeroPrimaryPolynomial.mass]
  have hl : 0<l := div_pos hm.1 (by linarith)
  have hls : l*Real.sin d=(ZeroPrimaryPolynomial.mass core:ℝ) :=
    div_mul_cancel₀ _ (by linarith)
  have hlU : l<3 := by
    have hh := mul_lt_mul_of_pos_left hsine hl
    nlinarith [hm.2]
  have hlc : l*Real.cos d<7 := by
    have hh := mul_le_mul_of_nonneg_left tr.2.1 hl.le
    linarith
  have hsb : l*s.b*Real.sin d=(ZeroPrimaryPolynomial.mass core:ℝ)*s.b := by
    rw [mul_right_comm,hls]
  change l*(ZeroPrimaryPolynomial.anchor core:ℝ)*Real.cos d≤
    unsigned s+l*s.a*Real.cos d-l*s.b*Real.sin d
  cases core
  · have ho : s.branch.type≠0 := by
      intro hc
      have hh := hcore.mpr hc
      simp at hh
    have hmark := (outer_marker_bounds s ho).1
    have ha := (outer_bounds (outer_data s ho)).1
    have hac : (899/1000:ℝ)≤ s.a := by linarith [fine_outer_endpoint_bounds.2]
    have hmul := mul_le_mul_of_nonneg_right hac
      (mul_nonneg hl.le (by linarith [tr.1] : 0≤Real.cos d))
    norm_num [ZeroPrimaryPolynomial.mass,ZeroPrimaryPolynomial.anchor] at hls hsb ⊢
    nlinarith
  · have hc := hcore.mp rfl
    have hmark := core_marker_lower s hc
    have ha := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart s hc)).2.1
    have hprod := mul_nonneg (show 0≤7-l*Real.cos d by linarith)
      (show 0≤7/12-s.a by linarith)
    norm_num [ZeroPrimaryPolynomial.mass,ZeroPrimaryPolynomial.anchor] at hls hsb ⊢
    nlinarith

/-- A target-primary zero edge has boosted cost above `.985`. The G1 marker chart choices are
the ones supplied in the states. -/
theorem target_primary_boost (s t : FramePair.State) {d : ℝ} (hd : |d|≤7/10)
    (hg : (19/25:ℝ)<s.gap t d) (hm : s.Feasible t 1 d) :
    (197/200:ℝ)<d+s.signedLabel-t.signedLabel+(9/50)*frameCost |d| := by
  have hdom := target_primary_domain s t hd hg hm
  have hdi : d∈Icc (9/20) (7/10) := ⟨hdom.1.1.le,hdom.1.2⟩
  have hpositive : 0<d := by linarith [hdom.1.1]
  have tr := positive_trig ⟨hpositive.le,hdi.2⟩
  have hsin : 0<Real.sin d := by
    have hh := (positive_taylor_reserves ⟨hpositive.le,hdi.2⟩).1
    linarith
  have hslabel : s.signedLabel=unsigned s := by
    simp [FramePair.State.signedLabel,unsigned,hdom.2.1,FramePair.sign]
  have htlabel : t.signedLabel≤(2/5)*(t.a-FramePair.a0)+(111/100)*t.b :=
    (signed_upper t).trans (outer_marker_bounds t hdom.2.2.2.2).2
  have hm' : 0≤t.a-s.a*Real.cos d+s.b*Real.sin d-oneWidth d := by
    simpa [FramePair.State.Feasible,forwardMargin,hdom.2.1,FramePair.sign,
      signed_width hd,oneWidth] using hm
  have hcase (core : Bool) (hcore : core=true ↔ s.branch.type=0) :
      (197/200:ℝ)<d+s.signedLabel-t.signedLabel+(9/50)*frameCost |d| := by
    let l : ℝ := (ZeroPrimaryPolynomial.mass core:ℝ)/Real.sin d
    have hl : 0≤l := by
      dsimp [l]
      apply div_nonneg _ hsin.le
      cases core <;> norm_num [ZeroPrimaryPolynomial.mass]
    have hsource := source_support s core hcore hdi
    have htarget := outer_circle_lower (X := -(l+2/5)) (Y := -(111/100:ℝ))
      (outer_data t hdom.2.2.2.2)
    simp only [neg_sq] at htarget
    have hmargin := mul_nonneg hl hm'
    have hscalar := ZeroPrimaryPolynomial.support_gt core hdi
    change (197/200:ℝ)<d+(9/50)*frameCost d+
      l*(oneWidth d+(ZeroPrimaryPolynomial.anchor core:ℝ)*Real.cos d)+
        (2/5)*outerAxial+(l+2/5+111/100)/2-
          CommonQuarter.radius*Real.sqrt ((l+2/5)^2+(111/100)^2) at hscalar
    change l*(ZeroPrimaryPolynomial.anchor core:ℝ)*Real.cos d≤
      unsigned s+l*s.a*Real.cos d-l*s.b*Real.sin d at hsource
    rw [hslabel,abs_of_pos hpositive]
    change t.signedLabel≤(2/5)*(t.a-outerAxial)+(111/100)*t.b at htlabel
    nlinarith
  by_cases hc : s.branch.type=0
  · exact hcase true (by simp [hc])
  · exact hcase false (by simp [hc])

theorem source_primary_boost (s t : FramePair.State) {d : ℝ} (hd : |d|≤7/10)
    (hg : (19/25:ℝ)<s.gap t d) (hm : s.Feasible t 3 d) :
    (197/200:ℝ)<d+s.signedLabel-t.signedLabel+(9/50)*frameCost |d| := by
  have hrev : t.flip.Feasible s.flip 1 d := by
    simpa [FramePair.State.Feasible,FramePair.State.flip,forwardMargin,FramePair.sign_not,
      sub_eq_add_neg,mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hm
  have hh := target_primary_boost t.flip s.flip hd (by simpa using hg) hrev
  simp only [FramePair.State.flip_label] at hh
  linarith

/-- The original weak owner gives the local boosted estimate on the same cycle, with both
squares in place. -/
theorem actual_boost (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=0) (j : Fin 4) (hj : j=1 ∨ j=3)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (197/200:ℝ)<QuarterWordGeometry.phaseValue F hgap i+
      (stateOf C i).signedLabel-(stateOf C (next i)).signedLabel+
        (9/50)*frameCost |QuarterWordGeometry.difference F i| := by
  have hphase : FramePair.pairAngle C i=QuarterWordGeometry.phaseValue F hgap i := by
    linarith [FramePair.pairAngle_gap C i,QuarterWordGeometry.phase_gap C F hgap i]
  have hz : QuarterWordGeometry.phaseValue F hgap i=QuarterWordGeometry.difference F i := by
    simp [QuarterWordGeometry.phaseValue,hk]
  have hm := stateOf_feasible C i j howner
  have hg : (19/25:ℝ)<(stateOf C i).gap (stateOf C (next i))
      (QuarterWordGeometry.difference F i) := by
    rw [← hz,← hphase,stateOf_gap]
    exact hgap i
  rw [hphase,hz] at hm
  rw [hz]
  rcases hj with rfl | rfl
  · exact target_primary_boost (stateOf C i) (stateOf C (next i))
      (QuarterWordGeometry.difference_small F i).le hg hm
  · exact source_primary_boost (stateOf C i) (stateOf C (next i))
      (QuarterWordGeometry.difference_small F i).le hg hm

end SquaresInCircles.Eight.ZeroPrimary
end
end
end

section
@[expose] public section
noncomputable section
open scoped BigOperators
open Set

namespace SquaresInCircles.Eight.ZeroPrimary

open FramePair QuarterWordGeometry

/-- A metric transform of the actual closed frame tour pays twice any
one edge's cost. No extrema or preferred axis are selected. -/
theorem twice_frame_edge_le_tour {C : BoundaryCycle Q0} (F : QuarterLift C)
    (i : Vertex) :
    2*frameCost |difference F i|≤∑j,frameCost |difference F j| := by
  have hrange (j k : Vertex) : |F.theta k-F.theta j|∈Icc 0 (Real.pi/4) := by
    refine ⟨abs_nonneg _,?_⟩
    linarith [theta_spread F j k,Real.pi_gt_three]
  let r : Vertex → ℝ := fun j => frameCost |F.theta j-F.theta i|
  have hstep (j : Vertex) : |r (next j)-r j|≤frameCost |difference F j| := by
    have h₁ := frameCost_triangle (hrange i j) (hrange j (next j))
      (hrange i (next j)) (by linarith [abs_sub_le (F.theta (next j)) (F.theta j) (F.theta i)])
    have h₂ := frameCost_triangle (hrange i (next j)) (hrange (next j) j)
      (hrange i j) (by linarith [abs_sub_le (F.theta j) (F.theta (next j)) (F.theta i)])
    rw [abs_sub_comm (F.theta j) (F.theta (next j))] at h₂
    apply abs_le.2
    dsimp [r,difference]
    constructor <;> linarith
  have htour := closed_walk_range_bound r i (next i)
  have hzero : r i=0 := by simp [r,frameCost_zero]
  have hnext : r (next i)=frameCost |difference F i| := rfl
  have hnn : 0≤frameCost |difference F i| := frameCost_nonneg (hrange i (next i))
  rw [hzero,hnext,sub_zero,abs_of_nonneg hnn] at htour
  exact htour.trans (Finset.sum_le_sum (fun j _ => hstep j))

/-- The six-edge return path pays the selected edge's actual width. -/
theorem frame_edge_le_return {C : BoundaryCycle Q0} (F : QuarterLift C)
    (i : Vertex) :
    frameCost |difference F i|≤
      ∑j∈(Finset.univ.erase i : Finset Vertex),frameCost |difference F j| := by
  have htour := twice_frame_edge_le_tour F i
  have hsplit := Finset.sum_erase_add (s := Finset.univ)
    (f := fun j => frameCost |difference F j|) (Finset.mem_univ i)
  linarith

lemma frame_pair_cost (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex) :
    (stateOf C i).cost (stateOf C (next i)) (FramePair.pairAngle C i)=
      phaseValue F hgap i+(stateOf C i).signedLabel-
        (stateOf C (next i)).signedLabel-(9/50)*frameCost |difference F i| := by
  have hphase : FramePair.pairAngle C i=phaseValue F hgap i := by
    linarith [FramePair.pairAngle_gap C i,phase_gap C F hgap i]
  have hshort : |difference F i|≤Real.pi/4 := by
    linarith [difference_small F i,Real.pi_gt_three]
  have hperiod : periodicFrameCost (phaseValue F hgap i)=
      frameCost |difference F i| := by
    have hh := periodicFrameCost_int_quarter (difference F i)
      ((F.word hgap pi_lt_22_over_7 i).val:ℤ)
    have hid : phaseValue F hgap i=difference F i+
        (((F.word hgap pi_lt_22_over_7 i).val:ℤ):ℝ)*(Real.pi/2) := by
      simp [phaseValue]
      ring
    rw [hid,hh,periodicFrameCost_of_short hshort]
  simp only [FramePair.State.cost,hphase,hperiod]
  ring

lemma handGamma_lower (i j : Fin 4) : (8833/10000:ℝ)≤handGamma i j := by
  fin_cases i <;> fin_cases j <;> norm_num [handGamma,handGammaNumerator]

/-- The upstream G1 pair theorem is needed only on the other six edges.
Every quantity in this statement is evaluated on the same original
boundary cycle and the same chosen signed representations. -/
theorem no_primary_of_return_pair_costs (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hpair : ∀k, k≠i →
      handGamma (branchOf C k).type (branchOf C (next k)).type<
        (stateOf C k).cost (stateOf C (next k)) (FramePair.pairAngle C k))
    (hk : F.word hgap pi_lt_22_over_7 i=0) (j : Fin 4) (hj : j=1 ∨ j=3)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) : False := by
  let g : Vertex → ℝ := fun k => phaseValue F hgap k+
    (stateOf C k).signedLabel-(stateOf C (next k)).signedLabel
  let v : Vertex → ℝ := fun k => frameCost |difference F k|
  have hboost : (197/200:ℝ)<g i+(9/50)*v i :=
    actual_boost C F hgap i hk j hj howner
  have hother (k : Vertex) (hki : k≠i) : (8833/10000:ℝ)<g k-(9/50)*v k := by
    have hh := (handGamma_lower (branchOf C k).type (branchOf C (next k)).type).trans_lt
      (hpair k hki)
    simpa only [frame_pair_cost C F hgap k,g,v] using hh
  have hsum := Finset.sum_lt_sum_of_nonempty
    (s := (Finset.univ.erase i : Finset Vertex))
    (by
      have hc : (Finset.univ.erase i : Finset Vertex).card=6 := by simp
      exact Finset.card_pos.1 (by omega))
    (fun k hk => hother k (Finset.mem_erase.mp hk).1)
  have hconst : ∑ _k∈(Finset.univ.erase i : Finset Vertex),(8833/10000:ℝ)=26499/5000 := by
    rw [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ i)]
    norm_num
  have hcost : (∑k,g k)=2*Real.pi := marker_budget C F hgap
    (fun k => (stateOf C k).signedLabel)
  have hsplit := Finset.sum_erase_add (s := Finset.univ) (f := g) (Finset.mem_univ i)
  have hreturn : v i≤∑k∈(Finset.univ.erase i : Finset Vertex),v k :=
    frame_edge_le_return F i
  rw [hconst,Finset.sum_sub_distrib,← Finset.mul_sum] at hsum
  rw [hcost] at hsplit
  linarith [Arithmetic.two_pi_lt_710_over_113]

/-- All G1 pairs on the original cycle discharge the only upstream
continuous input of the zero-primary cycle argument. -/
theorem no_primary_of_pair_costs (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hpair : ∀k,handGamma (branchOf C k).type (branchOf C (next k)).type<
      (stateOf C k).cost (stateOf C (next k)) (FramePair.pairAngle C k))
    (i : Vertex) (hk : F.word hgap pi_lt_22_over_7 i=0)
    (j : Fin 4) (hj : j=1 ∨ j=3)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) : False :=
  no_primary_of_return_pair_costs C F hgap i (fun k _ => hpair k) hk j hj howner

/-- Every feasible original zero-edge witness is secondary, including
ties between originally feasible separating axes. -/
theorem original_zero_secondary (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hpair : ∀k,handGamma (branchOf C k).type (branchOf C (next k)).type<
      (stateOf C k).cost (stateOf C (next k)) (FramePair.pairAngle C k))
    (i : Vertex) (hk : F.word hgap pi_lt_22_over_7 i=0)
    (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) : j=0 ∨ j=2 := by
  fin_cases j
  · exact Or.inl rfl
  · exact (no_primary_of_pair_costs C F hgap hpair i hk 1 (Or.inl rfl) howner).elim
  · exact Or.inr rfl
  · exact (no_primary_of_pair_costs C F hgap hpair i hk 3 (Or.inr rfl) howner).elim

end SquaresInCircles.Eight.ZeroPrimary
end
end
end

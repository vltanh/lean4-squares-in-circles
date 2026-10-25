module

public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoFirstOwners
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroData
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroOuter

/-!
# Eight squares: the actual source-zero boundary of a positive outer contact

The
already written mixed-zero circle formulas are reused as formulas for
the very same target point. The source coordinate is zero, not a moved
core square. The original circle and contact equations identify the
rotated coordinates uniquely, including the diagonal entry.
-/

section
/-!
## The six opposite-sign outer zero contacts of the short word

Both angle signs use the literal original source-secondary contact;
reversal restores the original target-secondary owner afterward.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open SecondWord (RoleLabel U W outer_domain outer_zero_mem)

abbrev Row := Fin 6

def c : Row→ℝ := ![-24463/100000,-24463/100000,8753/100000,8753/100000,-45320/100000,-45320/100000]
def p : Row→ℝ := ![0,13422/100000,0,-9133/100000,51554/100000,-19335/100000]
def q : Row→ℝ := ![94766/100000,103828/100000,9994/10000,88074/100000,119909/100000,76744/100000]
def v : Row→ℝ := ![13422/100000,0,-9133/100000,0,-19335/100000,51554/100000]
def t : Row→ℝ := ![103828/100000,94766/100000,88074/100000,9994/10000,76744/100000,119909/100000]

def source (r : Row) : RoleLabel := ⟨0,p r,q r,0,0⟩
def target (r : Row) : RoleLabel := ⟨0,v r,t r,0,0⟩
def l (r : Row) (b : ℝ) : ℝ := q r-p r*ratio b
def h (r : Row) (B : ℝ) : ℝ := t r-v r*ratio B

abbrev plus := SecondWord.OppositeZero.plus
abbrev plusSpeed := SecondWord.OppositeZero.plusSpeed
abbrev plusK := SecondWord.OppositeZero.plusK
abbrev minus := SecondWord.OppositeZero.minus
abbrev minusSpeed := SecondWord.OppositeZero.minusSpeed
abbrev minusK := SecondWord.OppositeZero.minusK
abbrev PlusDomain := SecondWord.OppositeZero.PlusDomain
abbrev MinusDomain := SecondWord.OppositeZero.MinusDomain

def plusCost (r : Row) (B x : ℝ) : ℝ :=
  x+c r+(source r).outer (plus B x)+(target r).outer B
def minusCost (r : Row) (B x : ℝ) : ℝ :=
  -x+c r+(source r).outer (minus B x)+(target r).outer B
def plusAngle (r : Row) (B x : ℝ) : ℝ := 1-l r (plus B x)*plusSpeed B x
def minusAngle (r : Row) (B x : ℝ) : ℝ := -1+l r (minus B x)*minusSpeed B x
def plusTarget (r : Row) (B x : ℝ) : ℝ := h r B-l r (plus B x)*plusK B x
def minusTarget (r : Row) (B x : ℝ) : ℝ := h r B-l r (minus B x)*minusK B x

def plusTargetCurvature (r : Row) (B x : ℝ) : ℝ :=
  -p r*ratioD (plus B x)*(plusK B x)^2+(l r (plus B x)*Real.sin x-v r)*ratioD B
def minusTargetCurvature (r : Row) (B x : ℝ) : ℝ :=
  -p r*ratioD (minus B x)*(minusK B x)^2-(l r (minus B x)*Real.sin x+v r)*ratioD B

def aligned (r : Row) (b : ℝ) : ℝ := c r+(source r).outer b+(target r).outer (1-b)
def alignedFirst (r : Row) (b : ℝ) : ℝ := l r b-h r (1-b)
def alignedSecond (r : Row) (b : ℝ) : ℝ := -p r*ratioD b-v r*ratioD (1-b)
abbrev low : ℝ := 1-outerDiagonal

lemma derivative_source (r : Row) (b : ℝ) : (source r).d1 b=l r b := by
  simp [source,RoleLabel.d1,l]
lemma derivative_target (r : Row) (B : ℝ) : (target r).d1 B=h r B := by
  simp [target,RoleLabel.d1,h]

lemma slope_bounds (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (68355/100000:ℝ)≤l r b ∧ l r b≤6/5 ∧ 0<h r b := by
  have hh := SecondWord.outer_ratio_bounds hb
  have h1 := hh.1
  have h2 := hh.2.1
  fin_cases r <;> norm_num [l,h,p,q,v,t] <;> (try refine ⟨?_,?_,?_⟩) <;> (try refine ⟨?_,?_⟩) <;>
    linarith

lemma source_monotone (r : Row) : MonotoneOn (source r).outer (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => ((source r).outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => (source r).outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by rw [derivative_source]; linarith [(slope_bounds r (Ioo_subset_Icc_self hb)).1])
lemma target_monotone (r : Row) : MonotoneOn (target r).outer (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => ((target r).outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => (target r).outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by rw [derivative_target]; exact (slope_bounds r (Ioo_subset_Icc_self hb)).2.2.le)

lemma l_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (l r) (-p r*ratioD b) b := by
  have hh : HasDerivAt (fun y => q r-p r*ratio y) (-(p r*ratioD b)) b :=
    ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul (p r)).const_sub (q r)
  exact hh.congr_deriv (by ring)
lemma h_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (h r) (-v r*ratioD b) b := by
  have hh : HasDerivAt (fun y => t r-v r*ratio y) (-(v r*ratioD b)) b :=
    ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul (v r)).const_sub (t r)
  exact hh.congr_deriv (by ring)

lemma plusCost_angle_hasDerivAt (r : Row) {B x : ℝ} (hd : PlusDomain B x) :
    HasDerivAt (plusCost r B) (plusAngle r B x) x := by
  have hh := (SecondWord.OppositeZero.plusCost_hasDerivAt (source r) (target r) hd).add_const (c r)
  have he : plusCost r B=fun y => SecondWord.OppositeZero.plusCost (source r) (target r) B y+c r := by
    funext y; simp only [plusCost,SecondWord.OppositeZero.plusCost]; ring
  rw [he]
  exact hh.congr_deriv (by simp only [plusAngle,SecondWord.OppositeZero.plusFirst,derivative_source])

lemma minusCost_angle_hasDerivAt (r : Row) {B x : ℝ} (hd : MinusDomain B x) :
    HasDerivAt (minusCost r B) (minusAngle r B x) x := by
  have hh := (SecondWord.OppositeZero.minusCost_hasDerivAt (source r) (target r) hd).add_const (c r)
  have he : minusCost r B=fun y => SecondWord.OppositeZero.minusCost (source r) (target r) B y+c r := by
    funext y; simp only [minusCost,SecondWord.OppositeZero.minusCost]; ring
  rw [he]
  exact hh.congr_deriv (by simp only [minusAngle,SecondWord.OppositeZero.minusFirst,derivative_source])

lemma plusCost_target_hasDerivAt (r : Row) {B x : ℝ} (hd : PlusDomain B x) :
    HasDerivAt (fun B => plusCost r B x) (plusTarget r B x) B := by
  have hh : HasDerivAt (fun y => x+c r+(source r).outer (plus y x)+(target r).outer y)
      ((source r).d1 (plus B x)*(-plusK B x)+(target r).d1 B) B :=
    ((((source r).outer_hasDerivAt (outer_domain hd.2.2)).comp B
      (SecondWord.OppositeZero.plus_target_hasDerivAt hd.1 x)).const_add (x+c r)).add
        ((target r).outer_hasDerivAt (outer_domain hd.1))
  exact hh.congr_deriv (by simp only [plusTarget,derivative_source,derivative_target]; ring)

lemma minusCost_target_hasDerivAt (r : Row) {B x : ℝ} (hd : MinusDomain B x) :
    HasDerivAt (fun B => minusCost r B x) (minusTarget r B x) B := by
  have hh : HasDerivAt (fun y => -x+c r+(source r).outer (minus y x)+(target r).outer y)
      ((source r).d1 (minus B x)*(-minusK B x)+(target r).d1 B) B :=
    ((((source r).outer_hasDerivAt (outer_domain hd.2.2)).comp B
      (SecondWord.OppositeZero.minus_target_hasDerivAt hd.1 x)).const_add (-x+c r)).add
        ((target r).outer_hasDerivAt (outer_domain hd.1))
  exact hh.congr_deriv (by simp only [minusTarget,derivative_source,derivative_target]; ring)

lemma plusTarget_hasDerivAt (r : Row) {B x : ℝ} (hd : PlusDomain B x) :
    HasDerivAt (fun B => plusTarget r B x) (plusTargetCurvature r B x) B := by
  have hK : HasDerivAt (fun B => plusK B x) (-ratioD B*Real.sin x) B := by
    have hh : HasDerivAt (fun y => Real.cos x-ratio y*Real.sin x) (-(ratioD B*Real.sin x)) B :=
      ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hd.1)).mul_const
        (Real.sin x)).const_sub (Real.cos x)
    exact hh.congr_deriv (by ring)
  have hl : HasDerivAt (l r ∘ fun y => plus y x) (-p r*ratioD (plus B x)*(-plusK B x)) B :=
    (l_hasDerivAt r hd.2.2).comp B (SecondWord.OppositeZero.plus_target_hasDerivAt hd.1 x)
  have hh : HasDerivAt (fun y => h r y-l r (plus y x)*plusK y x)
      (-v r*ratioD B-(-p r*ratioD (plus B x)*(-plusK B x)*plusK B x+
        l r (plus B x)*(-ratioD B*Real.sin x))) B :=
    (h_hasDerivAt r hd.1).fun_sub (hl.fun_mul hK)
  exact hh.congr_deriv (by simp only [plusTargetCurvature]; ring)

lemma minusTarget_hasDerivAt (r : Row) {B x : ℝ} (hd : MinusDomain B x) :
    HasDerivAt (fun B => minusTarget r B x) (minusTargetCurvature r B x) B := by
  have hK : HasDerivAt (fun B => minusK B x) (ratioD B*Real.sin x) B :=
    ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hd.1)).mul_const
      (Real.sin x)).const_add (Real.cos x)
  have hl : HasDerivAt (l r ∘ fun y => minus y x) (-p r*ratioD (minus B x)*(-minusK B x)) B :=
    (l_hasDerivAt r hd.2.2).comp B (SecondWord.OppositeZero.minus_target_hasDerivAt hd.1 x)
  have hh : HasDerivAt (fun y => h r y-l r (minus y x)*minusK y x)
      (-v r*ratioD B-(-p r*ratioD (minus B x)*(-minusK B x)*minusK B x+
        l r (minus B x)*(ratioD B*Real.sin x))) B :=
    (h_hasDerivAt r hd.1).fun_sub (hl.fun_mul hK)
  exact hh.congr_deriv (by simp only [minusTargetCurvature]; ring)

lemma aligned_domains {b : ℝ} (hb : b∈Icc low outerDiagonal) :
    b∈Icc 0 outerDiagonal ∧ 1-b∈Icc 0 outerDiagonal := by
  dsimp [low] at hb
  refine ⟨⟨?_,hb.2⟩,⟨?_,?_⟩⟩ <;>
    linarith [hb.1,hb.2,outer_endpoint_bounds.2.2.1,outer_endpoint_bounds.2.2.2]

lemma aligned_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc low outerDiagonal) :
    HasDerivAt (aligned r) (alignedFirst r b) b := by
  have hh : HasDerivAt (fun y => c r+(source r).outer y+(target r).outer (1-y))
      ((source r).d1 b+(target r).d1 (1-b)*(-1)) b :=
    (((source r).outer_hasDerivAt (outer_domain (aligned_domains hb).1)).const_add (c r)).add
      (((target r).outer_hasDerivAt (outer_domain (aligned_domains hb).2)).comp b
        ((hasDerivAt_id' b).const_sub 1))
  exact hh.congr_deriv (by simp only [alignedFirst,derivative_source,derivative_target]; ring)

lemma alignedFirst_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc low outerDiagonal) :
    HasDerivAt (alignedFirst r) (alignedSecond r b) b := by
  have hh : HasDerivAt (fun y => l r y-h r (1-y)) (-p r*ratioD b-(-v r*ratioD (1-b))*(-1)) b :=
    (l_hasDerivAt r (aligned_domains hb).1).sub
      ((h_hasDerivAt r (aligned_domains hb).2).comp b ((hasDerivAt_id' b).const_sub 1))
  exact hh.congr_deriv (by simp only [alignedSecond]; ring)

end SquaresInCircles.Eight.ShortOuterZero.Opposite
end
end
end

section
/-!
## The entire physical negative-angle contact domain

The final
angle is the exact double-diagonal contact, not an auxiliary search
endpoint. Its half-angle formula, bound .556, original coordinate cuts,
and the two endpoints of each target interval are proved here.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open SecondWord (U W outer_domain outer_zero_mem)

abbrev diagonal_mem : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
def halfRatio : ℝ := (outerDiagonal-1/2)/(outerDiagonal+1/2)
def halfAngle : ℝ := Real.arctan halfRatio
def finalAngle : ℝ := 2*halfAngle

lemma halfRatio_bounds : (0:ℝ)<halfRatio ∧ halfRatio<143/500 := by
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hden : 0<outerDiagonal+1/2 := by linarith
  constructor
  · exact div_pos (by linarith) hden
  · apply (div_lt_iff₀ hden).2
    linarith

lemma halfAngle_bounds : 0<halfAngle ∧ halfAngle<Real.pi/2 ∧ halfAngle<143/500 := by
  have hp : 0<halfAngle := Real.arctan_pos.mpr halfRatio_bounds.1
  have hu : halfAngle<Real.pi/2 := Real.arctan_lt_pi_div_two _
  have hh := Real.arctan_le_self halfRatio_bounds.1.le
  exact ⟨hp,hu,hh.trans_lt halfRatio_bounds.2⟩

lemma final_mem : finalAngle∈Icc 0 (7/10) := by
  have h := halfAngle_bounds
  dsimp [finalAngle]
  constructor <;> linarith [h.1,h.2.2]

lemma final_trig : Real.sin finalAngle=2*halfRatio/(1+halfRatio^2) ∧
    Real.cos finalAngle=(1-halfRatio^2)/(1+halfRatio^2) := by
  have hc : 0<Real.cos halfAngle := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [halfAngle_bounds.1,Real.pi_pos],halfAngle_bounds.2.1⟩
  have ht : Real.sin halfAngle/Real.cos halfAngle=halfRatio := by
    rw [←Real.tan_eq_sin_div_cos]
    exact Real.tan_arctan _
  have hs : Real.sin halfAngle=halfRatio*Real.cos halfAngle := (div_eq_iff hc.ne').1 ht
  have hunit := Real.sin_sq_add_cos_sq halfAngle
  have hden : 0<1+halfRatio^2 := by nlinarith [sq_nonneg halfRatio]
  have hcos2 : (Real.cos halfAngle)^2=1/(1+halfRatio^2) := by
    apply (eq_div_iff hden.ne').2
    rw [hs] at hunit
    nlinarith
  dsimp [finalAngle]
  rw [Real.sin_two_mul,Real.cos_two_mul]
  constructor
  · rw [hs,show 2*(halfRatio*Real.cos halfAngle)*Real.cos halfAngle=
      2*halfRatio*(Real.cos halfAngle)^2 by ring,hcos2]
    ring
  · rw [hcos2]
    field_simp
    ring

lemma double_contact : minus outerDiagonal finalAngle=outerDiagonal := by
  have ht := final_trig
  have hden : outerDiagonal+1/2≠0 := by linarith [outer_endpoint_bounds.2.2.1]
  have hroot : 1+halfRatio^2≠0 := by positivity
  have hr : halfRatio*(outerDiagonal+1/2)=outerDiagonal-1/2 := div_mul_cancel₀ _ hden
  have hinv : (1+halfRatio^2)*(1+halfRatio^2)⁻¹=1 := mul_inv_cancel₀ hroot
  dsimp [minus,SecondWord.OppositeZero.minus]
  rw [ShortOuterOne.SameContact.arc_diagonal,ht.1,ht.2]
  linear_combination (outerDiagonal-1/2)*hinv+2*(1+halfRatio^2)⁻¹*hr

lemma final_exit : outerDiagonal< minus outerDiagonal (139/250) := by
  have hs := HighOrderTaylor.S15_le_sin (show (0:ℝ)≤139/250 by norm_num)
  have hc := HighOrderTaylor.cos_le_C16 (show (0:ℝ)≤139/250 by norm_num)
  have tr := positive_trig (show (139/250:ℝ)∈Icc 0 (7/10) by norm_num)
  have hd := SecondWord.diagonal_fine
  have hp := mul_le_mul
    (show (1399214065109/1000000000000:ℝ)≤outerDiagonal+1/2 by linarith)
    hs (by norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7])
    (by linarith : 0≤outerDiagonal+1/2)
  have hn := mul_le_mul
    (show outerDiagonal-1/2≤(399214065110/1000000000000:ℝ) by linarith)
    hc (by linarith [tr.1] : 0≤Real.cos (139/250)) (by norm_num)
  dsimp [minus,SecondWord.OppositeZero.minus]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7,
    HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,cos10,cos8] at hp hn
  linarith

lemma final_bound : 0<finalAngle ∧ finalAngle<(139/250:ℝ) := by
  constructor
  · dsimp [finalAngle]
    linarith [halfAngle_bounds.1]
  · by_contra! hh
    have hm := SecondWord.OppositeZero.minus_angle_monotone diagonal_mem
      (by norm_num : (139/250:ℝ)∈Icc 0 (7/10)) final_mem hh
    rw [show SecondWord.OppositeZero.minus outerDiagonal finalAngle=outerDiagonal
      from double_contact] at hm
    exact (not_lt_of_ge hm) final_exit

lemma diagonal_speed_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (7/10:ℝ)< minusSpeed outerDiagonal x := by
  have tr := positive_trig hx
  have h1 := mul_le_mul
    (show (1399/1000:ℝ)≤outerDiagonal+1/2 by linarith [ShortMixedZero.fine_diagonal_bounds.1])
    tr.1.le (by norm_num) (by linarith [outer_endpoint_bounds.2.2.1])
  have h2 := mul_nonneg
    (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1]) tr.2.2.1
  norm_num [minusSpeed,SecondWord.OppositeZero.minusSpeed,ShortOuterOne.SameContact.arc_diagonal]
  linarith

lemma diagonal_increase {x y : ℝ} (hx : x∈Icc 0 (7/10)) (hy : y∈Icc 0 (7/10))
    (hxy : x≤y) : (7/10)*(y-x)≤ minus outerDiagonal y-minus outerDiagonal x := by
  have hm : MonotoneOn (fun u => minus outerDiagonal u-(7/10)*u) (Icc 0 (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun u _ => ((SecondWord.OppositeZero.minus_hasDerivAt outerDiagonal u).sub
        ((hasDerivAt_id u).const_mul (7/10))).continuousAt.continuousWithinAt)
      (fun u _ => (SecondWord.OppositeZero.minus_hasDerivAt outerDiagonal u).sub
        ((hasDerivAt_id u).const_mul (7/10)))
      (fun u hu => by linarith [diagonal_speed_lower (Ioo_subset_Icc_self hu)])
  have hh := hm hx hy hxy
  linarith

lemma original_angle {B x : ℝ} (hd : MinusDomain B x) : x≤finalAngle := by
  have ht := SecondWord.OppositeZero.minus_target_antitone hd.2.1 hd.1 diagonal_mem hd.1.2
  have hxbound : minus outerDiagonal x≤outerDiagonal := ht.trans hd.2.2.2
  by_contra! hx
  have hm := diagonal_increase final_mem hd.2.1 hx.le
  rw [double_contact] at hm
  linarith

lemma band_coordinates {B x : ℝ} (hd : MinusDomain B x) :
    B∈Icc low outerDiagonal ∧ minus B x∈Icc low outerDiagonal := by
  have hh := SecondWord.OppositeZero.minus_aligned_le hd.1 hd.2.1
  refine ⟨⟨?_,hd.1.2⟩,⟨?_,hd.2.2.2⟩⟩ <;>
    dsimp [low] <;> linarith [hd.1.2,hd.2.2.2]

lemma target_interval {B x C : ℝ} (hd : MinusDomain B x)
    (hC : C∈Icc B outerDiagonal) : MinusDomain C x := by
  have hCi : C∈Icc 0 outerDiagonal := ⟨hd.1.1.trans hC.1,hC.2⟩
  have hl := SecondWord.OppositeZero.minus_aligned_le hCi hd.2.1
  have hu := SecondWord.OppositeZero.minus_target_antitone hd.2.1 hd.1 hCi hC.1
  exact ⟨hCi,hd.2.1,⟨by linarith [hC.2,outer_endpoint_bounds.2.2.2],hu.trans hd.2.2.2⟩⟩

lemma entry {B x : ℝ} (hd : MinusDomain B x) :
    ∃a, a∈Icc 0 B ∧ minus a x=outerDiagonal ∧
      ∀C∈Icc a outerDiagonal, MinusDomain C x := by
  have hzero : outerDiagonal < minus 0 x := by
    have hh := SecondWord.OppositeZero.minus_aligned_le outer_zero_mem hd.2.1
    linarith [outer_endpoint_bounds.2.2.2]
  have hc : Continuous (fun C => minus C x) := by
    dsimp [minus,SecondWord.OppositeZero.minus,arc]; fun_prop
  obtain ⟨a,ha,he⟩ := intermediate_value_Icc hd.1.1 hc.neg.continuousOn
    (show -outerDiagonal∈Icc (-minus 0 x) (-minus B x) from
      ⟨by linarith,by linarith [hd.2.2.2]⟩)
  have heq : minus a x=outerDiagonal := by
    simp only [Pi.neg_apply] at he
    linarith
  have had : MinusDomain a x :=
    ⟨⟨ha.1,ha.2.trans hd.1.2⟩,hd.2.1,by
      rw [show SecondWord.OppositeZero.minus a x=outerDiagonal from heq]; exact diagonal_mem⟩
  exact ⟨a,ha,heq,fun C hC => target_interval had hC⟩

lemma double_value (r : Row) :
    (131/125:ℝ)< -finalAngle+c r+(p r+q r+v r+t r)*outerDiagonal := by
  have hf := final_bound.2
  have hd := ShortMixedZero.fine_diagonal_bounds
  fin_cases r <;> norm_num [c,p,q,v,t] <;> linarith

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative
end
end
end

section
/-!
## The remaining affine-source interior contact

The original target-stationarity equation identifies the full-circle
support point. Its explicit coordinate curve remains in the physical
contact region near an interior original point. The reduced angular
cost has strict negative curvature by the written N'' >= -N/4 identity.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Norm
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open SecondWord (U W outer_domain U_positive UW_circle)

abbrev R : ℝ := Real.sqrt Q0
def A : ℝ := (v 2)^2+(t 2)^2+(q 2)^2
def C : ℝ := -2*q 2*t 2
def D : ℝ := -2*q 2*v 2
def X (x : ℝ) : ℝ := v 2-q 2*Real.sin x
def Y (x : ℝ) : ℝ := t 2-q 2*Real.cos x
def N (x : ℝ) : ℝ := CircularNorm.norm A C D x
def ND (x : ℝ) : ℝ := CircularNorm.d1 A C D x
def NDD (x : ℝ) : ℝ := CircularNorm.d2 A C D x
def horizontal (x : ℝ) : ℝ := -R*X x/N x
def vertical (x : ℝ) : ℝ := -R*Y x/N x
def height (x : ℝ) : ℝ := vertical x-1/2
def value (x : ℝ) : ℝ :=
  x+c 2+(q 2-v 2-t 2)/2+q 2*(Real.sin x+Real.cos x)-R*N x
def first (x : ℝ) : ℝ := 1+q 2*(Real.cos x-Real.sin x)-R*ND x
def second (x : ℝ) : ℝ := -q 2*(Real.sin x+Real.cos x)-R*NDD x

lemma radius_bounds : 0<R ∧ R<2 ∧ R^2=Q0 := by
  have hp : (0:ℝ)<Q0 := by norm_num [Q0]
  have he := Real.sq_sqrt hp.le
  exact ⟨Real.sqrt_pos.mpr hp,(Real.sqrt_lt' (by norm_num)).2 (by norm_num [Q0]),he⟩

lemma projection_bounds (x : ℝ) :
    -(443/500:ℝ)<v 2*Real.sin x+t 2*Real.cos x ∧
      v 2*Real.sin x+t 2*Real.cos x<443/500 := by
  have hs := sq_nonneg (v 2*Real.cos x-t 2*Real.sin x)
  have hid : (v 2*Real.sin x+t 2*Real.cos x)^2+
      (v 2*Real.cos x-t 2*Real.sin x)^2=(v 2)^2+(t 2)^2 := by
    linear_combination ((v 2)^2+(t 2)^2)*(Real.sin_sq_add_cos_sq x)
  have he : (v 2)^2+(t 2)^2<(443/500:ℝ)^2 := by norm_num [v,t]
  constructor <;> nlinarith

lemma energy_formula (x : ℝ) :
    CircularNorm.energy A C D x=A-2*q 2*(v 2*Real.sin x+t 2*Real.cos x) := by
  dsimp [CircularNorm.energy,C,D]
  ring

lemma energy_positive (x : ℝ) : 0<CircularNorm.energy A C D x := by
  rw [energy_formula]
  have hp := (projection_bounds x).2
  norm_num [A,v,t,q] at *
  linarith

lemma norm_positive (x : ℝ) : 0<N x := CircularNorm.norm_pos (energy_positive x)

lemma norm_square (x : ℝ) : (N x)^2=(X x)^2+(Y x)^2 := by
  rw [N,CircularNorm.norm_sq (energy_positive x).le]
  dsimp [CircularNorm.energy,A,C,D,X,Y]
  linear_combination (-(q 2)^2)*(Real.sin_sq_add_cos_sq x)

lemma norm_upper (x : ℝ) : N x<(943/500:ℝ) := by
  have hs := CircularNorm.norm_sq (energy_positive x).le
  rw [energy_formula] at hs
  have hp := (projection_bounds x).1
  have hsq : (N x)^2<(943/500:ℝ)^2 := by
    show (CircularNorm.norm A C D x)^2<_
    rw [hs]
    norm_num [A,v,t,q] at hp ⊢
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

lemma norm_hasDerivAt (x : ℝ) : HasDerivAt N (ND x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive x)
lemma first_norm_hasDerivAt (x : ℝ) : HasDerivAt ND (NDD x) x :=
  CircularNorm.d1_hasDerivAt (energy_positive x)

lemma value_hasDerivAt (x : ℝ) : HasDerivAt value (first x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y+c 2+(q 2-v 2-t 2)/2) 1 x := by
    simpa using ((hasDerivAt_id x).add_const (c 2)).add_const ((q 2-v 2-t 2)/2)
  have h2 : HasDerivAt (fun y => q 2*(Real.sin y+Real.cos y))
      (q 2*(Real.cos x+-Real.sin x)) x :=
    ((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).const_mul (q 2)
  have h3 : HasDerivAt (fun y => R*N y) (R*ND x) x := (norm_hasDerivAt x).const_mul R
  have h := (h1.fun_add h2).fun_sub h3
  have he : value=fun y => y+c 2+(q 2-v 2-t 2)/2+q 2*(Real.sin y+Real.cos y)-R*N y := rfl
  rw [he]
  convert h using 1
  simp only [first]
  ring

lemma first_hasDerivAt (x : ℝ) : HasDerivAt first (second x) x := by
  have h2 : HasDerivAt (fun y => q 2*(Real.cos y-Real.sin y))
      (q 2*(-Real.sin x-Real.cos x)) x :=
    ((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul (q 2)
  have h3 : HasDerivAt (fun y => R*ND y) (R*NDD x) x := (first_norm_hasDerivAt x).const_mul R
  have h := (h2.const_add 1).fun_sub h3
  have he : first=fun y => 1+q 2*(Real.cos y-Real.sin y)-R*ND y := rfl
  rw [he]
  convert h using 1
  simp only [second]
  ring

lemma second_negative {x : ℝ} (hx : x∈Icc 0 (7/10)) : second x≤-(1/20:ℝ) := by
  have hcoef : C^2+D^2≤A^2 := by norm_num [A,C,D,v,t,q]
  have hcurv : -N x/4≤NDD x := CircularNorm.curvature_lower (energy_positive x) hcoef
  have ht := positive_trig hx
  have hsum : 1≤Real.sin x+Real.cos x := ht.2.2.2.2.2
  have hN := norm_upper x
  have hNp := norm_positive x
  have hR := radius_bounds
  have hproduct : R*N x<2*(943/500:ℝ) :=
    (mul_lt_mul_of_pos_right hR.2.1 hNp).trans
      (mul_lt_mul_of_pos_left hN (by norm_num))
  have hweighted := mul_le_mul_of_nonneg_left hcurv hR.1.le
  have hq : q 2=9994/10000 := by norm_num [q]
  simp only [second]
  rw [hq]
  linarith

lemma X_negative {x : ℝ} (hx : x∈Icc 0 (7/10)) : X x<0 := by
  have hs := (positive_trig hx).2.2.1
  norm_num [X,v,q]
  linarith

lemma original_parallel {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusTarget 2 B x=0) : Y x*U B=X x*W B := by
  have hu := U_positive (outer_domain hd.1)
  dsimp [plusTarget,h,l,plusK,SecondWord.OppositeZero.plusK] at hstat
  norm_num [p] at hstat
  change t 2-v 2*(W B/U B)-q 2*(Real.cos x-(W B/U B)*Real.sin x)=0 at hstat
  field_simp [hu.ne'] at hstat
  dsimp [X,Y]
  nlinarith only [hstat]

lemma original_coordinates {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusTarget 2 B x=0) : horizontal x=U B ∧ vertical x=W B := by
  have hp := original_parallel hd hstat
  have hc := UW_circle (outer_domain hd.1)
  have hn := norm_square x
  have hN := norm_positive x
  have hR := radius_bounds
  have hU := U_positive (outer_domain hd.1)
  have hX := X_negative hd.2.1
  have he : (N x*U B)^2=(R*X x)^2 := by
    linear_combination (U B)^2*hn+(X x)^2*hc+
      (Y x*U B+X x*W B)*hp-(X x)^2*hR.2.2
  have hRX : 0< -R*X x := by
    have hh := mul_pos hR.1 (neg_pos.mpr hX)
    linarith
  have hu : -R*X x=N x*U B :=
    (pow_left_inj₀ hRX.le (mul_pos hN hU).le two_ne_zero).1 (by rw [he]; ring)
  have hhor : horizontal x=U B := by
    unfold horizontal
    apply (div_eq_iff hN.ne').2
    linarith
  have hvert : vertical x=W B := by
    unfold vertical
    apply (div_eq_iff hN.ne').2
    have heq : U B*(-R*Y x-N x*W B)=0 := by linear_combination (-R)*hp+(W B)*hu
    have hz := (mul_eq_zero.mp heq).resolve_left hU.ne'
    linarith
  exact ⟨hhor,hvert⟩

lemma original_height {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusTarget 2 B x=0) : height x=B := by
  rw [height,(original_coordinates hd hstat).2]
  dsimp [W]
  ring

lemma circle (x : ℝ) : (horizontal x)^2+(vertical x)^2=Q0 := by
  have hn := norm_square x
  have hN := norm_positive x
  dsimp [horizontal,vertical]
  field_simp [hN.ne']
  nlinarith [radius_bounds.2.2]

lemma height_continuous : Continuous height := by
  have hN : Continuous N :=
    continuous_iff_continuousAt.2 (fun x => (norm_hasDerivAt x).continuousAt)
  have hY : Continuous Y := by
    show Continuous fun x => t 2-q 2*Real.cos x
    fun_prop
  have he : height=fun x => -R*Y x/N x-1/2 := rfl
  rw [he]
  exact ((continuous_const.mul hY).div hN (fun x => (norm_positive x).ne')).sub continuous_const

lemma curve_state {x : ℝ} (hx : x∈Icc 0 (7/10))
    (hb : height x∈Icc 0 outerDiagonal) :
    OuterState (horizontal x-1/2) (height x) := by
  have hH : 0<horizontal x :=
    div_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos radius_bounds.1) (X_negative hx))
      (norm_positive x)
  have hV : 1/2≤vertical x := by dsimp [height] at hb; linarith [hb.1]
  have hVU : vertical x≤horizontal x := by
    have hvsq := pow_le_pow_left₀ (by linarith : 0≤vertical x)
      (show vertical x≤outerDiagonal+1/2 by dsimp [height] at hb; linarith [hb.2]) 2
    nlinarith [circle x,diagonal_circle]
  refine ⟨hb.1,?_,?_⟩
  · dsimp [height]
    linarith
  · dsimp [height]
    nlinarith [circle x]

lemma curve_value {x : ℝ} (hx : x∈Icc 0 (7/10))
    (hb : height x∈Icc 0 outerDiagonal) : plusCost 2 (height x) x=value x := by
  have hs := curve_state hx hb
  have ha := (ShortOuterOne.SameContact.actual_arc hs).1
  have hsupport : X x*horizontal x+Y x*vertical x= -R*N x := by
    have hN := (norm_positive x).ne'
    have he : X x*horizontal x+Y x*vertical x= -R*((X x)^2+(Y x)^2)/N x := by
      simp only [horizontal,vertical]
      ring
    rw [he,←norm_square x]
    field_simp
  dsimp [plusCost,source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval]
  norm_num [p]
  rw [ha]
  dsimp [plus,SecondWord.OppositeZero.plus]
  rw [ha]
  dsimp [value,height,X,Y] at *
  nlinarith only [hsupport]

/-- A physical stationary target in row 2 has a feasible strictly concave angular curve. -/
theorem interior_not_minimum {B x : ℝ} (hd : PlusDomain B x)
    (hB : B∈Ioo 0 outerDiagonal) (hx : x∈Ioo 0 (7/10))
    (hb : plus B x∈Ioo 0 outerDiagonal) (hstat : plusTarget 2 B x=0)
    (hmin : ∀C y, PlusDomain C y → plusCost 2 B x≤plusCost 2 C y) : False := by
  let O : Set ℝ := Ioo 0 (7/10) ∩ height ⁻¹' Ioo 0 outerDiagonal ∩
    (fun y => plus (height y) y) ⁻¹' Ioo 0 outerDiagonal
  have hplus : Continuous (fun y => plus (height y) y) := by
    have hh := height_continuous
    dsimp [plus,SecondWord.OppositeZero.plus,arc]
    fun_prop
  have hO : IsOpen O :=
    (isOpen_Ioo.inter (isOpen_Ioo.preimage height_continuous)).inter
      (isOpen_Ioo.preimage hplus)
  have hxO : x∈O := by simpa [O,original_height hd hstat] using And.intro (And.intro hx hB) hb
  apply not_minimum_on_strictly_concave_curve
    (s := {p : ℝ×ℝ | PlusDomain p.1 p.2})
    (cost := fun p => plusCost 2 p.1 p.2) (p := (B,x))
    (fun p hp => hmin p.1 p.2 hp)
    (curve := fun y => (height y,y)) (value := value) (dvalue := first) (ddvalue := second)
    hO hxO (by norm_num : (0:ℝ)<1/20)
    (by simp [original_height hd hstat])
  · intro y hy
    exact ⟨Ioo_subset_Icc_self hy.1.2,Ioo_subset_Icc_self hy.1.1,Ioo_subset_Icc_self hy.2⟩
  · intro y hy
    exact curve_value (Ioo_subset_Icc_self hy.1.1) (Ioo_subset_Icc_self hy.1.2)
  · exact fun y _ => value_hasDerivAt y
  · exact fun y _ => first_hasDerivAt y
  · exact fun y hy => second_negative (Ioo_subset_Icc_self hy.1.1)

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Norm
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Zero
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

open SecondWord (U W outer_domain outer_zero_mem U_positive UW_circle)

abbrev start := ShortMixedZero.NegativeContact.start
abbrev horizontal := ShortMixedZero.NegativeContact.U
abbrev vertical := ShortMixedZero.NegativeContact.V
abbrev factor := ShortMixedZero.NegativeContact.speed
abbrev factorD := ShortMixedZero.NegativeContact.speedD

def height (x : ℝ) : ℝ := vertical x-1/2

def Physical (x : ℝ) : Prop := x∈Icc start (7/10) ∧ height x≤outerDiagonal

lemma angle_mem {x : ℝ} (hx : x∈Icc start (7/10)) : x∈Icc 0 (7/10) :=
  ⟨by linarith [hx.1,show (0:ℝ)<start by norm_num [start,ShortMixedZero.NegativeContact.start]],hx.2⟩

lemma state {x : ℝ} (hx : Physical x) : OuterState (horizontal x-1/2) (height x) := by
  have hcoord := ShortMixedZero.NegativeContact.coordinates hx.1
  have hc := ShortMixedZero.NegativeContact.circle hx.1
  have hd := diagonal_circle
  have hV : vertical x≤outerDiagonal+1/2 := by
    have h2 := hx.2
    dsimp only [height] at h2
    linarith
  have hdiag0 : 0<outerDiagonal+1/2 := by linarith [outer_endpoint_bounds.2.2.1]
  have hVsq := pow_le_pow_left₀ (by linarith [hcoord.2.2.1] : 0≤vertical x) hV 2
  have horder : vertical x≤horizontal x := by
    nlinarith [hcoord.1,hcoord.2.2.1]
  refine ⟨?_,?_,?_⟩
  · dsimp only [height]
    linarith [hcoord.2.2.1]
  · dsimp only [height]
    linarith
  · dsimp only [height]
    rw [sub_add_cancel,sub_add_cancel]
    exact hc

lemma target_mem {x : ℝ} (hx : Physical x) : height x∈Icc 0 outerDiagonal :=
  ⟨(state hx).1,hx.2⟩

lemma original_arc {x : ℝ} (hx : Physical x) : arc (height x)=horizontal x-1/2 :=
  (ShortOuterOne.SameContact.actual_arc (state hx)).1

lemma contact {x : ℝ} (hx : Physical x) : plus (height x) x=0 := by
  have he := ShortMixedZero.NegativeContact.contact_equation x
  dsimp [plus,SecondWord.OppositeZero.plus]
  rw [original_arc hx]
  dsimp [height]
  nlinarith

lemma domain {x : ℝ} (hx : Physical x) : PlusDomain (height x) x := by
  refine ⟨target_mem hx,angle_mem hx.1,?_⟩
  have hz : SecondWord.OppositeZero.plus (height x) x=0 := contact hx
  show SecondWord.OppositeZero.plus (height x) x∈Icc 0 outerDiagonal
  rw [hz]
  exact outer_zero_mem

lemma original_angle {B x : ℝ} (hd : PlusDomain B x) (hz : plus B x=0) : start<x := by
  have tr := positive_trig hd.2.1
  have ht := ShortOuterOne.SameContact.arc_state hd.1
  have hproj := outer_diagonal_upper ht tr.2.2.1
    (show Real.sin x≤Real.cos x by linarith [tr.1,tr.2.2.2.1])
  have he : (1+Real.sin x+Real.cos x)/2=arc B*Real.sin x+B*Real.cos x := by
    dsimp [plus,SecondWord.OppositeZero.plus] at hz
    linarith
  have hcut : 0≤ShortMixedZero.NegativeContact.cut x := by
    dsimp [ShortMixedZero.NegativeContact.cut,ShortMixedZero.NegativeContact.m]
    nlinarith
  by_contra! hx
  have hm := ShortMixedZero.NegativeContact.m_monotone hd.2.1
    (by norm_num [start,ShortMixedZero.NegativeContact.start]) hx
  have hh := mul_le_mul_of_nonneg_left hm
    (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1])
  have hs := ShortMixedZero.NegativeContact.cut_start_neg
  dsimp [ShortMixedZero.NegativeContact.cut] at hcut hs
  linarith

lemma original_coordinates {B x : ℝ} (hd : PlusDomain B x) (hz : plus B x=0) :
    Physical x ∧ height x=B := by
  have hx : x∈Icc start (7/10) := ⟨(original_angle hd hz).le,hd.2.1.2⟩
  have ht := ShortOuterOne.SameContact.arc_state hd.1
  have tr := positive_trig hd.2.1
  have hZ : ShortMixedZero.NegativeContact.Z x=U B*Real.sin x+W B*Real.cos x := by
    dsimp [plus,SecondWord.OppositeZero.plus] at hz
    dsimp [ShortMixedZero.NegativeContact.Z,ShortMixedZero.NegativeContact.m,U,W]
    linarith
  have horth : 0<U B*Real.cos x-W B*Real.sin x := by
    have h1 := mul_pos (U_positive (outer_domain hd.1))
      (show 0<Real.cos x-Real.sin x by linarith [tr.1,tr.2.2.2.1])
    have h2 := mul_nonneg (show 0≤U B-W B by dsimp [U,W]; linarith [ht.2.1]) tr.2.2.1
    nlinarith
  have hY : ShortMixedZero.NegativeContact.Y x=U B*Real.cos x-W B*Real.sin x := by
    have hc := UW_circle (outer_domain hd.1)
    have hr := ShortMixedZero.NegativeContact.circle_base hx
    have he : (U B*Real.cos x-W B*Real.sin x)^2+(ShortMixedZero.NegativeContact.Z x)^2=Q0 := by
      rw [hZ]
      linear_combination hc+((U B)^2+(W B)^2)*(Real.sin_sq_add_cos_sq x)
    exact (sq_eq_sq₀ (ShortMixedZero.NegativeContact.Y_pos hx).le horth.le).mp (by linarith)
  have hheight : height x=B := by
    dsimp only [height,vertical,ShortMixedZero.NegativeContact.V]
    rw [hZ,hY]
    dsimp only [W]
    linear_combination (B+1/2)*(Real.sin_sq_add_cos_sq x)
  exact ⟨⟨hx,by rw [hheight]; exact hd.1.2⟩,hheight⟩

lemma height_monotone : AntitoneOn height (Icc start (7/10)) := by
  intro x hx y hy hxy
  exact sub_le_sub_right (ShortMixedZero.NegativeContact.V_antitone hx hy hxy) (1/2)

lemma initial_height : outerDiagonal<height start := by
  by_contra! hh
  have hphysical : Physical start := ⟨by norm_num [start,ShortMixedZero.NegativeContact.start],hh⟩
  have ht := state hphysical
  have tr := positive_trig (angle_mem hphysical.1)
  have hproj := outer_diagonal_upper ht tr.2.2.1
    (show Real.sin start≤Real.cos start by linarith [tr.1,tr.2.2.2.1])
  have hcontact := ShortMixedZero.NegativeContact.contact_equation start
  have hcut : 0≤ShortMixedZero.NegativeContact.cut start := by
    dsimp [ShortMixedZero.NegativeContact.cut,ShortMixedZero.NegativeContact.m,height] at *
    nlinarith
  exact (not_lt_of_ge hcut) ShortMixedZero.NegativeContact.cut_start_neg

lemma entry {x : ℝ} (hx : Physical x) :
    ∃e, e∈Icc start x ∧ height e=outerDiagonal ∧
      ∀y∈Icc e (7/10), Physical y := by
  have hc : ContinuousOn height (Icc start x) := fun y hy =>
    ((ShortMixedZero.NegativeContact.V_hasDerivAt ⟨hy.1,hy.2.trans hx.1.2⟩).sub_const
      (1/2)).continuousAt.continuousWithinAt
  obtain ⟨e,he,heq'⟩ := intermediate_value_Icc' hx.1.1 hc
    (show outerDiagonal∈Icc (height x) (height start) from ⟨hx.2,initial_height.le⟩)
  refine ⟨e,he,heq',?_⟩
  intro y hy
  have hei : e∈Icc start (7/10) := ⟨he.1,he.2.trans hx.1.2⟩
  have hyi : y∈Icc start (7/10) := ⟨he.1.trans hy.1,hy.2⟩
  have hm := height_monotone hei hyi hy.1
  rw [heq'] at hm
  exact ⟨hyi,hm⟩

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Zero
end
end
end

module

public import SquaresInCircles.Eight.Frames.High.HighVaryingScalars
public import SquaresInCircles.Eight.Owners.SplitConcavityTools
public import SquaresInCircles.Eight.Words.Second.Mixed.TransverseSupportWide
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterCorePrimaryPositive

/-!
# Eight squares: the whole negative-core side domain from one norm chord

`J'''` is positive throughout `[0,.7]` (`J3_positive`). The four references and `J''(.4)` give
a positive quadratic lower bound on `[.4,.7]` (`tail_positive`). On `[0,.4]`, the convex first
derivative ends negative, so the minimum is at an endpoint (`early_derivative_convex`,
`J_positive`). The side target then cancels under the positive separator multiplier
(`original_side`, `original`).
-/

section
/-!
## The six original negative-core primary rows and their source circle

The continued primary chart is the original shifted circle, including
its axial endpoint. Its increasing source label also applies below the
physical diagonal when an actual contact requires that continuation.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives Reference

def Remaining (r : Row) : Prop := sourcePositive r=false ∧ targetPositive r=false
def lowerAngle : ℝ := Real.pi/2-7/10
def HeightRange (u : ℝ) : Prop := u∈Icc (33/25) (17/10)
def SourceDomain (a : ℝ) : Prop := a∈Icc (41/50) outerAxial
def v (u : ℝ) : ℝ := Real.sqrt (Q0-u^2)
def M (r : Row) (a : ℝ) : ℝ := ocP r*a-ocQ r*(v (a+1/2)-1/2)
def M1 (r : Row) (a : ℝ) : ℝ := ocP r+ocQ r*(a+1/2)/v (a+1/2)
def M2 (r : Row) (a : ℝ) : ℝ := ocQ r*Q0/(v (a+1/2))^3

theorem remaining_iff (r : Row) : Remaining r↔r=0 ∨ r=4 ∨ r=11 ∨ r=12 ∨ r=19 ∨ r=23 := by
  fin_cases r <;> norm_num [Remaining,sourcePositive,targetPositive]

theorem coefficients (r : Row) (hr : Remaining r) :
    (767/1000:ℝ)<ocQ r ∧ 0<ocG r ∧ ocG r<1139/1000 ∧
      -(263/1000)*ocQ r<ocP r ∧ ocP r<(253/1000)*ocQ r := by
  rcases (remaining_iff r).1 hr with rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [ocP,ocQ,ocG]

theorem primary_cost (r : Row) (hr : Remaining r) (a b A B φ : ℝ) :
    outerCoreCost r a b A B φ=φ+ocC r+ocP r*a-ocQ r*b+ocG r*B := by
  simp [outerCoreCost,sourceSign,targetSign,WordProblems.sign,hr.1,hr.2]
  ring
theorem primary_separator (r : Row) (hr : Remaining r) (a b A B φ : ℝ) :
    sourcePrimary r a b A B φ↔pairWidth φ≤a-A*Real.cos φ+B*Real.sin φ := by
  simp [sourcePrimary,targetSign,WordProblems.sign,hr.2]

theorem source_radicand {a : ℝ} (ha : SourceDomain a) : 1/4≤Q0-(a+1/2)^2 := by
  have hax := axial_circle
  have hprod := mul_nonneg (show 0≤outerAxial-a by linarith [ha.2])
    (show 0≤outerAxial+a+1 by linarith [ha.1,outer_endpoint_bounds.1])
  nlinarith
theorem source_v_positive {a : ℝ} (ha : SourceDomain a) : 0<v (a+1/2) := by
  exact Real.sqrt_pos.mpr (by linarith [source_radicand ha])
theorem source_v_square {a : ℝ} (ha : SourceDomain a) : (v (a+1/2))^2=Q0-(a+1/2)^2 :=
  Real.sq_sqrt (by linarith [source_radicand ha])
theorem source_v_bounds {a : ℝ} (ha : SourceDomain a) :
    1/2≤v (a+1/2) ∧ v (a+1/2)<59/40 ∧ (89/100)*v (a+1/2)<a+1/2 := by
  have hp := source_v_positive ha
  have hsq := source_v_square ha
  have hrad := source_radicand ha
  have hu : (33/25:ℝ)≤a+1/2 := by linarith [ha.1]
  have hu2 := mul_nonneg (show 0≤a+1/2-33/25 by linarith)
    (show 0≤a+1/2+33/25 by linarith)
  norm_num [Q0] at hsq hrad
  refine ⟨?_,?_,?_⟩
  · by_contra! h
    nlinarith [mul_lt_mul'' h h hp.le hp.le]
  · by_contra! h
    nlinarith [mul_le_mul h h (by norm_num) hp.le]
  · by_contra! h
    nlinarith [mul_le_mul h h (by linarith) (by linarith)]

theorem height_source_domain {u : ℝ} (hu : HeightRange u) : SourceDomain (u-1/2) := by
  constructor
  · linarith [hu.1]
  · linarith [hu.2,ShortOuterZero.fine_axial_bounds.1]
theorem height_v_bounds {u : ℝ} (hu : HeightRange u) : (101/100:ℝ)<v u ∧ v u<59/40 := by
  have hd := height_source_domain hu
  have hp := source_v_positive hd
  have he := source_v_square hd
  have hb := source_v_bounds hd
  simp only [sub_add_cancel] at hp he hb
  have hu2 := mul_nonneg (show 0≤17/10-u by linarith [hu.2])
    (show 0≤17/10+u by linarith [hu.1])
  norm_num [Q0] at he
  exact ⟨by nlinarith,hb.2.1⟩

theorem v_hasDerivAt {u : ℝ} (hu : 0<Q0-u^2) : HasDerivAt v (-u/v u) u := by
  convert (((hasDerivAt_const u Q0).sub ((hasDerivAt_id u).pow 2)).sqrt (ne_of_gt hu)) using 1
  · rfl
  · dsimp [v]
    field_simp [(Real.sqrt_pos.mpr hu).ne']
    ring
theorem M_hasDerivAt (r : Row) {a : ℝ} (ha : SourceDomain a) :
    HasDerivAt (M r) (M1 r a) a := by
  have hv : HasDerivAt (fun x => v (x+1/2)) (-(a+1/2)/v (a+1/2)) a :=
    HasDerivAt.comp_add_const a (1/2) (v_hasDerivAt (by linarith [source_radicand ha]))
  have h : HasDerivAt (fun x => ocP r*x-ocQ r*(v (x+1/2)-1/2))
      (ocP r*1-ocQ r*(-(a+1/2)/v (a+1/2))) a :=
    ((hasDerivAt_id' a).const_mul (ocP r)).sub ((hv.sub_const (1/2)).const_mul (ocQ r))
  exact h.congr_deriv (by simp only [M1]; ring)
theorem M1_hasDerivAt (r : Row) {a : ℝ} (ha : SourceDomain a) :
    HasDerivAt (M1 r) (M2 r a) a := by
  have hp := source_v_positive ha
  have he := source_v_square ha
  have hv : HasDerivAt (fun x => v (x+1/2)) (-(a+1/2)/v (a+1/2)) a :=
    HasDerivAt.comp_add_const a (1/2) (v_hasDerivAt (by linarith [source_radicand ha]))
  have h : HasDerivAt (fun x => ocP r+ocQ r*(x+1/2)/v (x+1/2))
      (0+(ocQ r*1*v (a+1/2)-ocQ r*(a+1/2)*(-(a+1/2)/v (a+1/2)))/v (a+1/2)^2) a :=
    (hasDerivAt_const a (ocP r)).add
      ((((hasDerivAt_id' a).add_const (1/2)).const_mul (ocQ r)).div hv hp.ne')
  refine h.congr_deriv ?_
  simp only [M2]
  generalize v (a+1/2) = w at hp he ⊢
  rw [show Q0=w^2+(a+1/2)^2 by linarith]
  field_simp
  ring
theorem M1_positive (r : Row) (hr : Remaining r) {a : ℝ} (ha : SourceDomain a) : 0<M1 r a := by
  have hc := coefficients r hr
  have hv := source_v_positive ha
  have hb := (source_v_bounds ha).2.2
  have hq := mul_lt_mul_of_pos_left hb (show 0<ocQ r by linarith [hc.1])
  have h1 : ocQ r*(89/100)<ocQ r*(a+1/2)/v (a+1/2) := by
    rw [lt_div_iff₀ hv]
    linarith
  simp only [M1]
  linarith [hc.1,hc.2.2.2.1]
theorem M_monotone (r : Row) (hr : Remaining r) : MonotoneOn (M r) (Icc (41/50) outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ha => (M_hasDerivAt r ha).continuousAt.continuousWithinAt)
    (fun _ ha => M_hasDerivAt r (Ioo_subset_Icc_self ha))
    (fun _ ha => (M1_positive r hr (Ioo_subset_Icc_self ha)).le)

theorem source_identity (r : Row) {a b : ℝ} (hs : OuterState a b) :
    M r a=ocP r*a-ocQ r*b := by
  have hb : 0≤b+1/2 := by linarith [hs.1]
  have he : Q0-(a+1/2)^2=(b+1/2)^2 := by linarith [hs.2.2]
  dsimp [M,v]
  rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg hb]
  ring
theorem actual_source_domain {a b : ℝ} (hs : OuterState a b) : SourceDomain a := by
  have hb := outer_bounds hs
  exact ⟨by linarith [hb.1,ShortMixedZero.fine_diagonal_bounds.1],hb.2.1⟩
theorem source_diagonal (r : Row) : M r outerDiagonal=(ocP r-ocQ r)*outerDiagonal := by
  have h := source_identity r (a:=outerDiagonal) (b:=outerDiagonal)
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl,by nlinarith [diagonal_circle]⟩
  nlinarith [h]

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative
end
end
end

section
/-!
## Whole lower-angle geometry of the unchanged core corner

The continued contact height stays between 1.32 and
1.7 on the full early rectangle. The same original circle chart includes
the side join and the diagonal, with no strict-owner convention.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative
open CommonQuarter CorePairGeometry Arithmetic Reference

def lowerAngles : Set ℝ := Icc lowerAngle (Real.pi/2)
def earlyAngles : Set ℝ := Icc lowerAngle (6/5)
def contactPrimary (B φ : ℝ) : ℝ :=
  1/2+(SecondWord.MixedCorner.a B+1/2)*Real.cos φ-(B-1/2)*Real.sin φ
def contactTangent (B φ : ℝ) : ℝ := SecondWord.MixedCorner.w B*Real.cos φ+Real.sin φ
def contactSpeed (B φ : ℝ) : ℝ :=
  (SecondWord.MixedCorner.a B+1/2)*Real.sin φ+(B-1/2)*Real.cos φ

theorem lower_parameter {φ : ℝ} (hφ : φ∈lowerAngles) :
    Real.pi/2-φ∈Icc 0 (7/10) ∧ φ=angle false (Real.pi/2-φ) := by
  constructor
  · constructor <;> dsimp [lowerAngle,lowerAngles] at hφ <;> linarith [hφ.1,hφ.2]
  · dsimp [angle,direction]; ring
theorem lower_trig {φ : ℝ} (hφ : φ∈lowerAngles) :
    (191/250:ℝ)<Real.sin φ ∧ Real.sin φ≤1 ∧ 0≤Real.cos φ ∧ Real.cos φ<129/200 := by
  obtain ⟨hx,he⟩ := lower_parameter hφ
  have ht := positive_trig hx
  rw [he,angle_sin,angle_cos]
  dsimp [direction]
  refine ⟨by linarith [ht.1],Real.cos_le_one _,by linarith [ht.2.2.1],by linarith [ht.2.2.2.1]⟩
theorem early_subset : earlyAngles⊆lowerAngles := by
  intro φ hφ
  exact ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩
theorem early_left : lowerAngle∈earlyAngles := by
  exact ⟨le_rfl,by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2]⟩
theorem early_right : (6/5:ℝ)∈earlyAngles := by
  exact ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],le_rfl⟩

theorem early_cosine {φ : ℝ} (hφ : φ∈earlyAngles) : (181/500:ℝ)<Real.cos φ := by
  have hm : AntitoneOn Real.cos lowerAngles :=
    antiOn_of_hasDeriv_nonpos
      (fun x _ => Real.continuous_cos.continuousAt.continuousWithinAt)
      (fun x _ => Real.hasDerivAt_cos x)
      (fun x hx => by linarith [(lower_trig (Ioo_subset_Icc_self hx)).1])
  have hcmp := hm (early_subset hφ) (early_subset early_right) hφ.2
  have href : (181/500:ℝ)<Real.cos (6/5) := by
    have h := (cosine (by norm_num : (0:ℝ)≤6/5)).mem.1
    have hb : (181/500:ℝ)<(cosine (by norm_num : (0:ℝ)≤6/5)).lo := by mixed_fixed
    exact hb.trans_le h
  linarith

theorem contact_height_range {B φ : ℝ} (hB : B∈SecondWord.MixedCorner.domain) (hφ : φ∈earlyAngles) :
    HeightRange (contactPrimary B φ+1/2) := by
  have ht := lower_trig (early_subset hφ)
  have hc := early_cosine hφ
  have ha := CoreAngleEndpoint.state_bounds (SecondWord.MixedCorner.state hB)
  have hchart := SecondWord.MixedCorner.chart_bounds hB
  have haL : (529/500:ℝ)<SecondWord.MixedCorner.a B+1/2 := by
    dsimp [SecondWord.MixedCorner.a]
    linarith [hchart.1,CoreAngleEndpoint.diagonal_bounds.1]
  have haU : SecondWord.MixedCorner.a B+1/2≤13/12 := by linarith [ha.2.1]
  have hBb : 0≤B-1/2 ∧ B-1/2<59/1000 :=
    ⟨sub_nonneg.mpr hB.1,by linarith [hB.2,CoreAngleEndpoint.diagonal_bounds.2]⟩
  have hAcL := mul_lt_mul_of_pos_right haL (show 0<Real.cos φ by linarith)
  have hAcU := mul_le_mul_of_nonneg_right haU ht.2.2.1
  have hBsL := mul_nonneg hBb.1 (show 0≤Real.sin φ by linarith [ht.1])
  have hBsU := mul_le_mul_of_nonneg_left ht.2.1 hBb.1
  dsimp [HeightRange,contactPrimary]
  constructor <;> nlinarith

theorem contact_domain {B φ : ℝ} (hB : B∈SecondWord.MixedCorner.domain) (hφ : φ∈earlyAngles) :
    SourceDomain (contactPrimary B φ) := by
  have h := height_source_domain (contact_height_range hB hφ)
  simpa using h

theorem contactPrimary_hasDerivAt_B {B φ : ℝ} (hB : B∈SecondWord.MixedCorner.domain) :
    HasDerivAt (fun t => contactPrimary t φ) (-contactTangent B φ) B := by
  have h := ((((SecondWord.MixedCorner.a_hasDerivAt hB).add_const (1/2)).mul_const
    (Real.cos φ)).const_add (1/2)).sub
      (((hasDerivAt_id' B).sub_const (1/2)).mul_const (Real.sin φ))
  exact h.congr_deriv (by simp only [contactTangent]; ring)
theorem contactTangent_hasDerivAt_B {B φ : ℝ} (hB : B∈SecondWord.MixedCorner.domain) :
    HasDerivAt (fun t => contactTangent t φ)
      ((1+(SecondWord.MixedCorner.w B)^2)*Real.cos φ/SecondWord.MixedCorner.z B) B := by
  have h := ((SecondWord.MixedCorner.w_hasDerivAt hB).mul_const (Real.cos φ)).add_const
    (Real.sin φ)
  exact h.congr_deriv (by ring)

theorem actual_height (r : Row) (hr : Remaining r) {a b A B φ : ℝ}
    (_hB : B∈SecondWord.MixedCorner.domain) (hA : A=SecondWord.MixedCorner.a B) (hφ : φ∈earlyAngles)
    (hm : sourcePrimary r a b A B φ) : contactPrimary B φ≤a := by
  have ht := lower_trig (early_subset hφ)
  rw [primary_separator r hr] at hm
  rw [pairWidth,abs_of_nonneg (by linarith [ht.1]),abs_of_nonneg ht.2.2.1,hA] at hm
  dsimp [contactPrimary]
  linarith

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative
end
end
end

section
/-!
## The four negative-core side norms and their endpoint chord

Each norm is convex on the entire cosine interval. Its
endpoint chord is fixed by the aligned and far-angle geometric ends;
no intermediate angle or state subdivision enters the support.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.SideChord
open CommonQuarter CorePairGeometry Arithmetic

def Rows (r : Row) : Prop := r=4 ∨ r=12 ∨ r=19 ∨ r=23
def k0 : ℝ := Real.cos (7/10)
def norm (r : Row) (k : ℝ) : ℝ := Real.sqrt ((ocG r-ocP r*k)^2+(ocQ r*k)^2)
def numerator (r : Row) (k : ℝ) : ℝ := ((ocP r)^2+(ocQ r)^2)*k-ocG r*ocP r
def normD (r : Row) (k : ℝ) : ℝ := numerator r k/norm r k
def normDD (r : Row) (k : ℝ) : ℝ := (ocG r)^2*(ocQ r)^2/(norm r k)^3
def beta (r : Row) : ℝ := (norm r 1-norm r k0)/(1-k0)
def alpha (r : Row) : ℝ := norm r 1-beta r
def K (r : Row) : ℝ := Real.pi/2+ocC r+(-ocP r+ocQ r+ocG r)/2-449/500
def A (r : Row) : ℝ := K r-CommonQuarter.radius*beta r
def B (r : Row) : ℝ := ocG r-CommonQuarter.radius*alpha r
def C (r : Row) : ℝ := 13*ocG r/12
def J (r : Row) (x : ℝ) : ℝ := (A r-x)*Real.cos x+B r+C r*Real.sin x
def J1 (r : Row) (x : ℝ) : ℝ := (C r-1)*Real.cos x-(A r-x)*Real.sin x
def J2 (r : Row) (x : ℝ) : ℝ := (2-C r)*Real.sin x-(A r-x)*Real.cos x
def J3 (r : Row) (x : ℝ) : ℝ := (3-C r)*Real.cos x+(A r-x)*Real.sin x
def reference (r : Row) : ℝ :=
  if r=4 then 52/125 else if r=12 then 1147/2000 else if r=19 then 287/500 else 807/2000
def F (r : Row) (x : ℝ) : ℝ := Real.pi/2-x+ocC r+ocG r/Real.cos x+
  (-ocP r+ocQ r+ocG r)/2+C r*(Real.sin x/Real.cos x)-
    CommonQuarter.radius*Real.sqrt ((ocG r/Real.cos x-ocP r)^2+(ocQ r)^2)

theorem remaining (r : Row) (hr : Rows r) : Remaining r := by
  rcases hr with rfl|rfl|rfl|rfl <;> norm_num [Remaining,sourcePositive,targetPositive]

theorem k0_bounds : (191/250:ℝ)<k0 ∧ k0<153/200 := by
  have hh := (Reference.cosine (by norm_num : (0:ℝ)≤7/10)).mem
  have hl : (191/250:ℝ)<(Reference.cosine (by norm_num : (0:ℝ)≤7/10)).lo := by
    mixed_fixed
  have hu : (Reference.cosine (by norm_num : (0:ℝ)≤7/10)).hi<(153/200:ℝ) := by
    mixed_fixed
  exact ⟨hl.trans_le hh.1,hh.2.trans_lt hu⟩

theorem cosine_mem {x : ℝ} (hx : x∈Icc 0 (7/10)) : Real.cos x∈Icc k0 1 :=
  ⟨cos_anti hx (by norm_num : (7/10:ℝ)∈Icc 0 (7/10)) hx.2,Real.cos_le_one x⟩

theorem norm_positive (r : Row) (hr : Remaining r) {k : ℝ} (hk : 0<k) : 0<norm r k := by
  have hq : 0<ocQ r := by linarith [(coefficients r hr).1]
  have hqk := mul_pos hq hk
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg (ocG r-ocP r*k)]

theorem norm_square (r : Row) (k : ℝ) :
    (norm r k)^2=(ocG r-ocP r*k)^2+(ocQ r*k)^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem norm_hasDerivAt (r : Row) (hr : Remaining r) {k : ℝ} (hk : 0<k) :
    HasDerivAt (norm r) (normD r k) k := by
  have hn := norm_positive r hr hk
  have hh := (((((hasDerivAt_id k).const_mul (ocP r)).const_sub (ocG r)).pow 2).add
    (((hasDerivAt_id k).const_mul (ocQ r)).pow 2)).sqrt (Real.sqrt_pos.mp hn).ne'
  convert hh using 1
  · rfl
  · dsimp [normD,numerator,norm]
    field_simp [hn.ne']
    ring

theorem numerator_identity (r : Row) (k : ℝ) :
    ((ocP r)^2+(ocQ r)^2)*(norm r k)^2-(numerator r k)^2=(ocG r)^2*(ocQ r)^2 := by
  rw [norm_square]
  dsimp [numerator]
  ring

theorem normD_hasDerivAt (r : Row) (hr : Remaining r) {k : ℝ} (hk : 0<k) :
    HasDerivAt (normD r) (normDD r k) k := by
  have hn := (norm_positive r hr hk).ne'
  have hh := (((hasDerivAt_id' k).const_mul ((ocP r)^2+(ocQ r)^2)).sub_const
    (ocG r*ocP r)).div (norm_hasDerivAt r hr hk) hn
  refine hh.congr_deriv ?_
  rw [normDD,←numerator_identity r k]
  simp only [normD,numerator]
  field_simp

theorem norm_convex (r : Row) (hr : Remaining r) : ConvexOn ℝ (Icc k0 1) (norm r) := by
  have hpositive {k : ℝ} (hk : k∈Icc k0 1) : 0<k := by linarith [k0_bounds.1,hk.1]
  have hc : ConcaveOn ℝ (Icc k0 1) (fun k => -norm r k) := concave_of_deriv2
    (fun k hk => (norm_hasDerivAt r hr (hpositive hk)).neg)
    (fun k hk => (normD_hasDerivAt r hr (hpositive hk)).neg)
    (fun k hk => neg_nonpos.mpr (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (pow_nonneg (norm_positive r hr (hpositive hk)).le 3)))
  have h2 := hc.neg
  have he : (-fun k => -norm r k)=norm r := by
    funext k
    simp
  rwa [he] at h2

theorem norm_chord (r : Row) (hr : Remaining r) {k : ℝ} (hk : k∈Icc k0 1) :
    norm r k≤alpha r+beta r*k := by
  have hden : 0<1-k0 := by linarith [k0_bounds.2]
  let t := (k-k0)/(1-k0)
  have ht : 0≤t ∧ t≤1 :=
    ⟨div_nonneg (sub_nonneg.mpr hk.1) hden.le,(div_le_one hden).2 (by linarith [hk.2])⟩
  have hpoint : (1-t) • k0+t • (1:ℝ)=k := by
    simp only [smul_eq_mul]
    dsimp [t]
    field_simp [hden.ne']
    ring
  have hh := (norm_convex r hr).2
    (show k0∈Icc k0 1 from ⟨le_rfl,by linarith⟩)
    (show (1:ℝ)∈Icc k0 1 from ⟨by linarith,le_rfl⟩)
    (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  rw [hpoint] at hh
  simp only [smul_eq_mul] at hh
  have he : (1-t)*norm r k0+t*norm r 1=alpha r+beta r*k := by
    dsimp [t,alpha,beta]
    field_simp [hden.ne']
    ring
  exact hh.trans_eq he

theorem J_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (J r) (J1 r x) x := by
  have h := ((((hasDerivAt_id' x).const_sub (A r)).fun_mul (Real.hasDerivAt_cos x)).add_const
    (B r)).fun_add ((Real.hasDerivAt_sin x).const_mul (C r))
  exact h.congr_deriv (by simp only [J1]; ring)
theorem J1_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (J1 r) (J2 r x) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul (C r-1)).fun_sub
    (((hasDerivAt_id' x).const_sub (A r)).fun_mul (Real.hasDerivAt_sin x))
  exact h.congr_deriv (by simp only [J2]; ring)
theorem J2_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (J2 r) (J3 r x) x := by
  have h := ((Real.hasDerivAt_sin x).const_mul (2-C r)).fun_sub
    (((hasDerivAt_id' x).const_sub (A r)).fun_mul (Real.hasDerivAt_cos x))
  exact h.congr_deriv (by simp only [J3]; ring)

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.SideChord
end
end
end

section
/-!
## Exact endpoint-chord constants and the four references

The fixed norm chord uses `cos(.7)`, the aligned norm, and their exact positive radicals
(`normOneBox`, `normK0Box`). The four intrinsic role references are fixed points
(`reference_mem`, `reference_reserve`). Six positive-square refinements enclose the fixed
radicals; alternating Taylor enclosures supply each fixed sine and cosine.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.SideChord.Reference
open CommonQuarter Arithmetic StationaryPrimitives
open MixedQuarter.Reference

def radiusBox : Interval CommonQuarter.radius :=
  rootSix (Interval.point Q0) 2 (by norm_num) (by norm_num [Interval.point,Q0])
def k0Box : Interval k0 := cosine (by norm_num : (0:ℝ)≤7/10)
def radicandBox (r : Row) {k : ℝ} (Y : Interval k) :
    Interval ((ocG r-ocP r*k)^2+(ocQ r*k)^2) :=
  (((Interval.point (ocG r)).sub ((Interval.point (ocP r)).mul Y)).square).add (((Interval.point (ocQ r)).mul Y).square)
theorem one_radicand (r : Row) (hr : Rows r) :
    0≤(radicandBox r (Interval.point (1:ℝ))).lo := by
  rcases hr with rfl|rfl|rfl|rfl <;> dsimp [radicandBox] <;> mixed_fixed
theorem k0_radicand (r : Row) (hr : Rows r) : 0≤(radicandBox r k0Box).lo := by
  rcases hr with rfl|rfl|rfl|rfl <;> dsimp [radicandBox,k0Box] <;> mixed_fixed
def normOneBox (r : Row) (hr : Rows r) : Interval (norm r 1) :=
  rootSix (radicandBox r (Interval.point (1:ℝ))) 2 (by norm_num) (one_radicand r hr)
def normK0Box (r : Row) (hr : Rows r) : Interval (norm r k0) :=
  rootSix (radicandBox r k0Box) 2 (by norm_num) (k0_radicand r hr)
def denominatorBox : Interval (1-k0) := (Interval.point 1).sub k0Box
theorem denominator_positive : 0<denominatorBox.lo := by
  dsimp [denominatorBox,k0Box]
  mixed_fixed
def betaBox (r : Row) (hr : Rows r) : Interval (beta r) :=
  ((normOneBox r hr).sub (normK0Box r hr)).div denominatorBox denominator_positive
def alphaBox (r : Row) (hr : Rows r) : Interval (alpha r) :=
  (normOneBox r hr).sub (betaBox r hr)
def KBox (r : Row) : Interval (K r) :=
  ((halfPi.add (Interval.point (ocC r))).add
    (Interval.point ((-ocP r+ocQ r+ocG r)/2))).sub (Interval.point (449/500))
def ABox (r : Row) (hr : Rows r) : Interval (A r) :=
  (KBox r).sub (radiusBox.mul (betaBox r hr))
def BBox (r : Row) (hr : Rows r) : Interval (B r) :=
  (Interval.point (ocG r)).sub (radiusBox.mul (alphaBox r hr))
def JBox (r : Row) (hr : Rows r) {x : ℝ} (hx : 0≤x) : Interval (J r x) :=
  ((((ABox r hr).sub (Interval.point x)).mul (cosine hx)).add (BBox r hr)).add ((Interval.point (C r)).mul (sine hx))
def J1Box (r : Row) (hr : Rows r) {x : ℝ} (hx : 0≤x) : Interval (J1 r x) :=
  ((Interval.point (C r-1)).mul (cosine hx)).sub (((ABox r hr).sub (Interval.point x)).mul (sine hx))
def J2Box (r : Row) (hr : Rows r) {x : ℝ} (hx : 0≤x) : Interval (J2 r x) :=
  ((Interval.point (2-C r)).mul (sine hx)).sub (((ABox r hr).sub (Interval.point x)).mul (cosine hx))

macro "side_chord_fixed" : tactic => `(tactic|
  (dsimp [radiusBox,k0Box,radicandBox,normOneBox,normK0Box,denominatorBox,
    betaBox,alphaBox,KBox,ABox,BBox,JBox,J1Box,J2Box,k0,K,C,reference]; mixed_fixed))

theorem coefficient_bounds (r : Row) (hr : Rows r) :
    (479/1000:ℝ)<A r ∧ A r<691/1000 ∧ (129/125:ℝ)<C r ∧ C r<43/40 := by
  have hl : (479/1000:ℝ)<(ABox r hr).lo := by
    rcases hr with rfl|rfl|rfl|rfl <;> side_chord_fixed
  have hu : (ABox r hr).hi<(691/1000:ℝ) := by
    rcases hr with rfl|rfl|rfl|rfl <;> side_chord_fixed
  refine ⟨hl.trans_le (ABox r hr).mem.1,(ABox r hr).mem.2.trans_lt hu,?_⟩
  rcases hr with rfl|rfl|rfl|rfl <;> norm_num [C,ocG]

theorem initial_shape (r : Row) (hr : Rows r) :
    (37/5000:ℝ)<J r 0 ∧ J1 r (2/5)< -(1/1000:ℝ) ∧ (9/100:ℝ)<J2 r (2/5) := by
  have h : (37/5000:ℝ)<(JBox r hr (by norm_num : (0:ℝ)≤0)).lo ∧
      (J1Box r hr (by norm_num : (0:ℝ)≤2/5)).hi< -(1/1000:ℝ) ∧
        (9/100:ℝ)<(J2Box r hr (by norm_num : (0:ℝ)≤2/5)).lo := by
    rcases hr with rfl|rfl|rfl|rfl <;> side_chord_fixed
  exact ⟨h.1.trans_le (JBox r hr _).mem.1,(J1Box r hr _).mem.2.trans_lt h.2.1,
    h.2.2.trans_le (J2Box r hr _).mem.1⟩

theorem reference_mem (r : Row) : reference r∈Icc (2/5:ℝ) (7/10) := by
  dsimp [reference]
  split_ifs <;> norm_num

private lemma r83_reference_eval (r : Row) (hr : Rows r) {x : ℝ} (hx : 0≤x)
    (hv : (r=4 ∧ x=52/125) ∨ (r=12 ∧ x=1147/2000) ∨ (r=19 ∧ x=287/500) ∨ (r=23 ∧ x=807/2000)) :
    (31/50000:ℝ)<(JBox r hr hx).lo ∧ -(1/20000:ℝ)<(J1Box r hr hx).lo ∧
      (J1Box r hr hx).hi<1/20000 := by
  rcases hv with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> side_chord_fixed

theorem reference_reserve (r : Row) (hr : Rows r) :
    (31/50000:ℝ)<J r (reference r) ∧ |J1 r (reference r)|<1/20000 := by
  have hx : 0≤reference r := (by norm_num : (0:ℝ)≤2/5).trans (reference_mem r).1
  have h := r83_reference_eval r hr hx
    (by rcases hr with rfl|rfl|rfl|rfl <;> norm_num [reference])
  exact ⟨h.1.trans_le (JBox r hr hx).mem.1,
    abs_lt.mpr ⟨h.2.1.trans_le (J1Box r hr hx).mem.1,(J1Box r hr hx).mem.2.trans_lt h.2.2⟩⟩

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.SideChord.Reference
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.SideChord
open CommonQuarter CorePairGeometry Arithmetic

theorem J3_positive (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (13/10:ℝ)<J3 r x := by
  have hb := Reference.coefficient_bounds r hr
  have tr := positive_trig hx
  have hfirst := mul_lt_mul''
    (show (77/40:ℝ)<3-C r by linarith [hb.2.2.2]) tr.1
    (by norm_num : (0:ℝ)≤77/40) (by norm_num : (0:ℝ)≤19121/25000)
  have hAx : -(221/1000:ℝ)≤A r-x := by linarith [hb.1,hx.2]
  have hsecond := mul_le_mul_of_nonneg_right hAx tr.2.2.1
  have hnegative := mul_le_mul_of_nonpos_left tr.2.2.2.1.le
    (by norm_num : (-(221/1000):ℝ)≤0)
  dsimp [J3]
  linarith

theorem J2_monotone (r : Row) (hr : Rows r) : MonotoneOn (J2 r) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (J2_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => J2_hasDerivAt r x)
    (fun x hx => by linarith [J3_positive r hr (Ioo_subset_Icc_self hx)])

theorem tail_curvature (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈Icc (2/5:ℝ) (7/10)) :
    (9/100:ℝ)<J2 r x :=
  (Reference.initial_shape r hr).2.2.trans_le
    ((J2_monotone r hr) (by norm_num : (2/5:ℝ)∈Icc 0 (7/10))
      ⟨by linarith [hx.1],hx.2⟩ hx.1)

theorem tail_positive (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈Icc (2/5:ℝ) (7/10)) :
    0<J r x := by
  have href := Reference.reference_mem r
  have hv := Reference.reference_reserve r hr
  have hs := abs_lt.mp hv.2
  have hprod := mul_pos (show 0<1/20000-J1 r (reference r) by linarith [hs.2])
    (show 0<J1 r (reference r)+1/20000 by linarith [hs.1])
  apply positive_of_curvature (κ:=(9/100:ℝ)) (by norm_num) hx href
    (fun y _ => J_hasDerivAt r y) (fun y _ => J1_hasDerivAt r y)
    (fun y hy => (tail_curvature r hr hy).le)
  nlinarith [hv.1]

theorem early_derivative_convex (r : Row) (hr : Rows r) : ConvexOn ℝ (Icc 0 (2/5:ℝ)) (J1 r) := by
  have hc : ConcaveOn ℝ (Icc 0 (2/5:ℝ)) (fun x => -J1 r x) := concave_of_deriv2
    (fun x _ => (J1_hasDerivAt r x).neg)
    (fun x _ => (J2_hasDerivAt r x).neg)
    (fun x hx => neg_nonpos.mpr (by
      linarith [J3_positive r hr ⟨hx.1,hx.2.trans (by norm_num : (2/5:ℝ)≤7/10)⟩]))
  have h2 := hc.neg
  have he : (-fun x => -J1 r x)=J1 r := by
    funext x
    simp
  rwa [he] at h2

theorem J_positive (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<J r x := by
  by_cases ht : (2/5:ℝ)≤x
  · exact tail_positive r hr ⟨ht,hx.2⟩
  have hmin := SplitConcavityTools.minimum_of_convex_derivative
    (fun y _ => J_hasDerivAt r y) (early_derivative_convex r hr)
    (show J1 r (2/5)≤0 by linarith [(Reference.initial_shape r hr).2.1])
    (show x∈Icc 0 (2/5:ℝ) from ⟨hx.1,(lt_of_not_ge ht).le⟩)
  have h0 : 0<J r 0 := by linarith [(Reference.initial_shape r hr).1]
  have hlast := tail_positive r hr (show (2/5:ℝ)∈Icc (2/5:ℝ) (7/10) by norm_num)
  exact (lt_min h0 hlast).trans_le hmin

theorem scaled_norm (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    Real.sqrt ((ocG r/Real.cos x-ocP r)^2+(ocQ r)^2)=norm r (Real.cos x)/Real.cos x := by
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have he : (norm r (Real.cos x)/Real.cos x)^2=
      (ocG r/Real.cos x-ocP r)^2+(ocQ r)^2 := by
    rw [div_pow,norm_square]
    field_simp
  have hn : 0≤norm r (Real.cos x)/Real.cos x := div_nonneg (Real.sqrt_nonneg _) hc.le
  rw [← he,Real.sqrt_sq hn]

theorem scaled_value (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (F r x-449/500)*Real.cos x=
      (K r-x)*Real.cos x+ocG r+C r*Real.sin x-CommonQuarter.radius*norm r (Real.cos x) := by
  have hc : Real.cos x≠0 := by linarith [(positive_trig hx).1]
  rw [F,scaled_norm r hx]
  dsimp [K]
  field_simp [hc]
  ring

theorem J_le_scaled_value (r : Row) (hr : Remaining r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    J r x≤(F r x-449/500)*Real.cos x := by
  have hnorm := norm_chord r hr (cosine_mem hx)
  have hp := mul_le_mul_of_nonneg_left hnorm (show 0≤CommonQuarter.radius by linarith [radius_bounds.1])
  rw [scaled_value r hx]
  dsimp [J,A,B]
  nlinarith only [hp]

theorem F_lower (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) : (449/500:ℝ)<F r x := by
  have hh := (J_positive r hr hx).trans_le (J_le_scaled_value r (remaining r hr) hx)
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hpos : 0<F r x-449/500 := pos_of_mul_pos_left hh hc.le
  linarith

theorem original_ge_F (r : Row) (hr : Remaining r) {a b aC bC x : ℝ}
    (hs : OuterState a b) (hside : aC=7/12) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b aC bC (angle false x)) :
    F r x≤outerCoreCost r a b aC bC (angle false x) := by
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  let w := ocG r/Real.cos x
  have hw : 0<w := div_pos (coefficients r hr).2.1 hc
  have hwk : w*Real.cos x=ocG r := div_mul_cancel₀ _ hc.ne'
  have hsep := (primary_separator r hr a b aC bC (angle false x)).1 hm
  rw [angle_width false hx,angle_cos,angle_sin,hside] at hsep
  dsimp [direction] at hsep
  have hp := mul_le_mul_of_nonneg_left hsep hw.le
  have hcircle := outer_circle_lower (X:=ocP r-w) (Y:=-(ocQ r)) hs
  have hnorm : (ocP r-w)^2+(-(ocQ r))^2=(w-ocP r)^2+(ocQ r)^2 := by ring
  rw [hnorm] at hcircle
  have hB : w*bC*Real.cos x=ocG r*bC := by
    calc
      w*bC*Real.cos x=(w*Real.cos x)*bC := by ring
      _=ocG r*bC := by rw [hwk]
  rw [primary_cost r hr]
  dsimp [F,C,angle,direction]
  change Real.pi/2-x+ocC r+w+(-ocP r+ocQ r+ocG r)/2+
      (13*ocG r/12)*(Real.sin x/Real.cos x)-CommonQuarter.radius*Real.sqrt ((w-ocP r)^2+(ocQ r)^2)≤_
  have hcot : (13*ocG r/12)*(Real.sin x/Real.cos x)=(13/12)*w*Real.sin x := by
    dsimp [w]
    ring
  rw [hcot]
  nlinarith only [hp,hcircle,hwk,hB]

theorem original_side (r : Row) (hr : Remaining r) (hrow : Rows r) {a b aC bC x : ℝ}
    (hs : OuterState a b) (hside : aC=7/12) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b aC bC (angle false x)) :
    (449/500:ℝ)<outerCoreCost r a b aC bC (angle false x) :=
  (F_lower r hrow hx).trans_le (original_ge_F r hr hs hside hx hm)

theorem original (r : Row) (hr : Remaining r) (hrow : Rows r) {a b aC bC x : ℝ}
    (hs : OuterState a b) (_ht : CoreState aC bC) (hside : aC=7/12)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b aC bC (angle false x)) :
    (449/500:ℝ)<outerCoreCost r a b aC bC (angle false x) :=
  original_side r hr hrow hs hside hx hm

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.SideChord
end
end
end

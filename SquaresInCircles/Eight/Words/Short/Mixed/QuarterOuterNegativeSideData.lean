module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterNegativeData

/-!
# Eight squares: the four negative-core side norms and their endpoint chord

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

module

public import SquaresInCircles.Eight.TableFree.FrameLowHighGeometry
public import SquaresInCircles.Eight.TableFree.CircularNorm

/-!
# Both low-source, negative-high-target circle supports

The positive low source uses its proved loss of `1/100000` and the
negative source its exact axial support.  Each resulting norm is an
actual rotating circle force.  Its exact curvature makes the complete
angular interval concave; only the two physical endpoints are used.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowHighSecondaryNegative
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameLowHighGeometry

def lam (i : Bool) : ℝ := if i then 189/200 else 1
def error (i : Bool) : ℝ := if i then 1/100000 else 0
def left (i : Bool) : ℝ := if i then 1/50 else 3/10
def right (i : Bool) : ℝ := if i then 23/50 else 4/5
def normCap (i : Bool) : ℝ := if i then 6/5 else 4/3
def initialNorm (i : Bool) : ℝ := if i then 809/1000 else 26/25
def finalNorm (i : Bool) : ℝ := if i then 11/10 else 4/3
def initialSum (i : Bool) : ℝ := if i then 10197/10000 else 5/4
def finalSum (i : Bool) : ℝ := if i then 133/100 else 7/5
def N (i : Bool) (x : ℝ) : ℝ :=
  CircularNorm.norm (FrameHighArc.u^2+FrameHighArc.v^2+(lam i)^2)
    (-2*lam i*FrameHighArc.v) (2*lam i*FrameHighArc.u) x
def Nd (i : Bool) (x : ℝ) : ℝ :=
  CircularNorm.d1 (FrameHighArc.u^2+FrameHighArc.v^2+(lam i)^2)
    (-2*lam i*FrameHighArc.v) (2*lam i*FrameHighArc.u) x
def Ndd (i : Bool) (x : ℝ) : ℝ :=
  CircularNorm.d2 (FrameHighArc.u^2+FrameHighArc.v^2+(lam i)^2)
    (-2*lam i*FrameHighArc.v) (2*lam i*FrameHighArc.u) x
def K (i : Bool) : ℝ :=
  9/100+lam i/2+FrameHighArc.k+(FrameHighArc.u-FrameHighArc.v)/2-error i
def F (i : Bool) (x : ℝ) : ℝ :=
  x+K i+(lam i-9/100)*(Real.sin x+Real.cos x)-R*N i x
def Fd (i : Bool) (x : ℝ) : ℝ :=
  1+(lam i-9/100)*(Real.cos x-Real.sin x)-R*Nd i x
def Fdd (i : Bool) (x : ℝ) : ℝ :=
  -(lam i-9/100)*(Real.sin x+Real.cos x)-R*Ndd i x

theorem energy_positive (i : Bool) (x : ℝ) :
    0<CircularNorm.energy (FrameHighArc.u^2+FrameHighArc.v^2+(lam i)^2)
      (-2*lam i*FrameHighArc.v) (2*lam i*FrameHighArc.u) x := by
  have hh := FrameCoreArc.projection_lt
    (a := -FrameHighArc.u) (b := FrameHighArc.v)
    (by norm_num : (0:ℝ)<7/10)
    (by norm_num [FrameHighArc.u,FrameHighArc.v]) x
  cases i <;> dsimp [CircularNorm.energy,lam,FrameHighArc.u,FrameHighArc.v] at *
  all_goals linarith

theorem N_positive (i : Bool) (x : ℝ) : 0<N i x := CircularNorm.norm_pos (energy_positive i x)
theorem N_square (i : Bool) (x : ℝ) :
    (N i x)^2=FrameHighArc.u^2+FrameHighArc.v^2+(lam i)^2+
      2*lam i*(FrameHighArc.u*Real.sin x-FrameHighArc.v*Real.cos x) := by
  have hh := CircularNorm.norm_sq (energy_positive i x).le
  convert hh using 1 <;> dsimp [N,CircularNorm.energy] <;> ring
theorem N_deriv (i : Bool) (x : ℝ) : HasDerivAt (N i) (Nd i x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive i x)
theorem Nd_deriv (i : Bool) (x : ℝ) : HasDerivAt (Nd i) (Ndd i x) x :=
  CircularNorm.d1_hasDerivAt (energy_positive i x)

theorem Ndd_lower (i : Bool) (x : ℝ) : -N i x/4≤Ndd i x := by
  exact CircularNorm.curvature_lower (energy_positive i x)
    (by cases i <;> norm_num [lam,FrameHighArc.u,FrameHighArc.v])

theorem N_monotone (i : Bool) : MonotoneOn (N i) (Icc 0 (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (N_deriv i x).continuousAt.continuousWithinAt
  · exact fun x _ => N_deriv i x
  · intro x hx
    have ht := FrameLowPair.quadrant (Ioo_subset_Icc_self hx)
    have hp := N_positive i x
    dsimp [Nd,CircularNorm.d1,CircularNorm.slope]
    apply div_nonneg _ (by positivity)
    cases i <;> dsimp [lam,FrameHighArc.u,FrameHighArc.v] <;> linarith

theorem endpoint_norms (i : Bool) :
    N i (left i)< initialNorm i ∧ N i (right i)<finalNorm i := by
  have he0 := N_square i (left i)
  have he1 := N_square i (right i)
  have hn0 := N_positive i (left i)
  have hn1 := N_positive i (right i)
  have hl0 : 0≤left i := by cases i <;> norm_num [left]
  have hr0 : 0≤right i := by cases i <;> norm_num [right]
  have hs0 := sin_upper_five hl0
  have hc0 := cos_lower_six hl0
  have hs1 := sin_upper_five hr0
  have hc1 := cos_lower_six hr0
  cases i <;> norm_num [left,right,lam,initialNorm,finalNorm,
    FrameHighArc.u,FrameHighArc.v] at *
  all_goals constructor <;> nlinarith

theorem endpoint_sums (i : Bool) :
    initialSum i<Real.sin (left i)+Real.cos (left i) ∧
      finalSum i<Real.sin (right i)+Real.cos (right i) := by
  have hl0 : 0≤left i := by cases i <;> norm_num [left]
  have hr0 : 0≤right i := by cases i <;> norm_num [right]
  have hs0 := sin_lower_seven hl0
  have hc0 := cos_lower_six hl0
  have hs1 := sin_lower_seven hr0
  have hc1 := cos_lower_six hr0
  cases i <;> norm_num [left,right,initialSum,finalSum] at *
  all_goals constructor <;> linarith

theorem quadrant (i : Bool) {x : ℝ} (hx : x∈Icc (left i) (right i)) :
    x∈Icc 0 (Real.pi/2) := by
  cases i <;> dsimp [left,right] at hx <;> constructor <;> linarith [hx.1,hx.2,FrameLowPair.pi_lower]

theorem N_upper (i : Bool) {x : ℝ} (hx : x∈Icc (left i) (right i)) : N i x<normCap i := by
  have hr : right i∈Icc 0 (Real.pi/2) := by
    cases i <;> dsimp [right] <;> constructor <;> linarith [FrameLowPair.pi_lower]
  have hh := N_monotone i (quadrant i hx) hr hx.2
  have he : finalNorm i≤normCap i := by cases i <;> norm_num [finalNorm,normCap]
  exact (hh.trans_lt (endpoint_norms i).2).trans_le he

theorem F_deriv (i : Bool) (x : ℝ) : HasDerivAt (F i) (Fd i x) x := by
  have h := (((hasDerivAt_id' x).add_const (K i)).fun_add
    (((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).const_mul (lam i-9/100))).fun_sub
      ((N_deriv i x).const_mul R)
  refine h.congr_deriv ?_
  simp only [Fd]
  ring
theorem Fd_deriv (i : Bool) (x : ℝ) : HasDerivAt (Fd i) (Fdd i x) x := by
  have h := ((((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul
    (lam i-9/100)).const_add 1).fun_sub ((Nd_deriv i x).const_mul R)
  refine h.congr_deriv ?_
  simp only [Fdd]
  ring

theorem Fdd_negative (i : Bool) {x : ℝ} (hx : x∈Icc (left i) (right i)) : Fdd i x<0 := by
  have hsum : 1≤Real.sin x+Real.cos x := by
    have hw := FrameCoreArc.width_one_le x
    rw [(first_width (quadrant i hx)).1] at hw
    linarith
  have hcurv := mul_le_mul_of_nonneg_left (Ndd_lower i x) R_pos.le
  have hR : R<(99/50:ℝ) := by linarith [radius_precise.2]
  have hn := mul_le_mul hR.le (N_upper i hx).le (N_positive i x).le
    (by norm_num : (0:ℝ)≤99/50)
  cases i <;> dsimp [Fdd,lam,normCap] at * <;> nlinarith

theorem F_concave (i : Bool) : ConcaveOn ℝ (Icc (left i) (right i)) (F i) :=
  concave_of_deriv2 (fun x _ => F_deriv i x) (fun x _ => Fd_deriv i x)
    (fun _ hx => (Fdd_negative i hx).le)

theorem endpoint_lower (i : Bool) :
    (8833/10000:ℝ)<F i (left i) ∧ (8833/10000:ℝ)<F i (right i) := by
  have hn := endpoint_norms i
  have ht := endpoint_sums i
  have hR : R<(99/50:ℝ) := by linarith [radius_precise.2]
  have h0 := mul_le_mul hR.le hn.1.le (N_positive i (left i)).le
    (by norm_num : (0:ℝ)≤99/50)
  have h1 := mul_le_mul hR.le hn.2.le (N_positive i (right i)).le
    (by norm_num : (0:ℝ)≤99/50)
  have hk := high_constant_lower
  cases i <;> dsimp [F,K,lam,error,left,right,initialSum,finalSum,initialNorm,finalNorm,
    FrameHighArc.u,FrameHighArc.v] at *
  all_goals constructor <;> linarith

theorem lower (i : Bool) {x : ℝ} (hx : x∈Icc (left i) (right i)) :
    (8833/10000:ℝ)<F i x :=
  concave_gt_of_endpoints (F_concave i) hx (endpoint_lower i).1 (endpoint_lower i).2

theorem circle_support (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : x∈Icc (left i) (right i))
    (hm : 0≤ secondary i false b B x) : F i x≤lowHighCost i false b B x := by
  have hlam : 0≤lam i := by cases i <;> norm_num [lam]
  have hs : -error i≤ sign i*(L b-lam i*b) := by
    cases i with
    | false => simpa [error,lam,sign] using low_unit_source hb
    | true => simpa [error,lam,sign] using low_positive_source hb
  have hscaled := mul_nonneg hlam hm
  have ht := circle_linear_lower (A_circle ⟨b2_mem.1.trans hB.1,hB.2⟩)
    (-FrameHighArc.u-lam i*Real.sin x) (FrameHighArc.v-lam i*Real.cos x)
  have hn : Real.sqrt ((-FrameHighArc.u-lam i*Real.sin x)^2+
      (FrameHighArc.v-lam i*Real.cos x)^2)=N i x := by
    dsimp [N,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination (lam i)^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  dsimp [secondary,FrameLowMidGeometry.secondary] at hscaled
  rw [(first_width (quadrant i hx)).1] at hscaled
  dsimp [F,K,lowHighCost,H]
  rw [(first_width (quadrant i hx)).2]
  cases i <;> simp only [sign,lam,error,Bool.false_eq_true,↓reduceIte] at hs hscaled ht ⊢ <;> linarith only [hs,hscaled,ht]

theorem weak_separator (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : x∈Icc (left i) (right i))
    (hm : 0≤ secondary i false b B x) : (8833/10000:ℝ)<lowHighCost i false b B x :=
  (lower i hx).trans_le (circle_support i hb hB hx hm)

end SquaresInCircles.Eight.TableFree.FrameLowHighSecondaryNegative

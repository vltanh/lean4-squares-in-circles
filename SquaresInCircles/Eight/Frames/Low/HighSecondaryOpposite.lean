module

public import SquaresInCircles.Eight.Frames.Low.HighGeometry
public import SquaresInCircles.Eight.Frames.Low.HighParallel
public import SquaresInCircles.Eight.Owners.CircularNorm

/-!
# Eight squares: the entire negative-low / positive-high transverse branch

The actual weak owner first forces the angle past `1.35`.  The exact
circle norm is nonzero and increasing on the remaining interval.  Its
curvature makes both physical-quadrant supports concave.  The common
quarter-turn endpoint retains the precise radius bound needed for its
strict reserve.
-/

section
/-!
## Both low-source, negative-high-target circle supports

The positive low source uses its proved loss of `1/100000` and the
negative source its exact axial support.  Each resulting norm is an
actual rotating circle force.  Its exact curvature makes the complete
angular interval concave; only the two physical endpoints are used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighSecondaryNegative
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
  convert hh using 1 <;> dsimp [N,CircularNorm.energy]
  ring
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

end SquaresInCircles.Eight.FrameLowHighSecondaryNegative
end
end
end

section
/-!
## Low-source angle cuts from the original weak margins

The cuts are geometric exclusions on complete angular intervals.
Their endpoint values are controlled by alternating Taylor estimates;
they do not presume an already concentrated frame word.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighCuts
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameLowHighGeometry

theorem trig_sum_short {x : ℝ} (hx : x∈Icc (0:ℝ) (3/10)) :
    Real.sin x+Real.cos x<1251/1000 := by
  have hm : MonotoneOn (fun z => Real.sin z+Real.cos z) (Icc (0:ℝ) (3/10)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z _ => ((Real.hasDerivAt_sin z).add
        (Real.hasDerivAt_cos z)).continuousAt.continuousWithinAt
    · exact fun z _ => (Real.hasDerivAt_sin z).add (Real.hasDerivAt_cos z)
    · intro z hz
      have hs := Real.sin_le hz.1.le
      have hc := Real.one_sub_sq_div_two_le_cos (x := z)
      have hsq := pow_le_pow_left₀ hz.1.le hz.2.le 2
      nlinarith
  have hh := hm hx ⟨by norm_num,le_rfl⟩ hx.2
  have hs := sin_upper_five (show (0:ℝ)≤3/10 by norm_num)
  have hc := cos_upper_four (show (0:ℝ)≤3/10 by norm_num)
  norm_num at hs hc
  linarith

theorem negative_secondary_cut {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤ secondary false false b B x) : (3/10:ℝ)<x := by
  by_contra! hsmall
  by_cases hn : x≤0
  · have hh := nonpositive_secondary_owners false false
      ⟨hb.1,hb.2.trans b1_mem.2⟩ ⟨b2_mem.1.trans hB.1,hB.2⟩ ⟨hx,hn⟩ hm
    cases hh.1
  · have hx0 : 0≤x := (lt_of_not_ge hn).le
    have hxq : x∈Icc 0 (Real.pi/2) :=
      ⟨hx0,by linarith [hsmall,FrameLowPair.pi_lower]⟩
    have ht := FrameLowPair.quadrant hxq
    have hsin := Real.sin_le hx0
    have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
    have hsq := pow_le_pow_left₀ hx0 hsmall 2
    have htarget : MonotoneOn (linear (Real.sin x) (Real.cos x)) (Icc b2 c0) := by
      apply monoOn_of_hasDeriv_nonneg
      · exact fun z hz => (linear_hasDerivAt
          ⟨b2_mem.1.trans hz.1,hz.2⟩ _ _).continuousAt.continuousWithinAt
      · exact fun z hz => linear_hasDerivAt
          ⟨b2_mem.1.trans hz.1.le,hz.2.le⟩ _ _
      · intro z hz
        have hr := slope_high_bounds (Ioo_subset_Icc_self hz)
        have hmul := mul_le_mul_of_nonneg_left hr.2 ht.1
        simp only [Ad,FrameLowArc.slope,neg_div] at hmul ⊢
        nlinarith
    have hp := htarget hB ⟨b2_mem.2,le_rfl⟩ hB.2
    dsimp [linear] at hp
    rw [A_c0] at hp
    have hsum := trig_sum_short ⟨hx0,hsmall⟩
    have hcoef : 0≤c0-1/2 := by linarith [c0_bounds.1]
    have hbound := mul_le_mul
      (show c0-1/2≤399215/1000000 by linarith [diagonal_precise.2]) hsum.le
      (by linarith [ht.1,ht.2.2.1] : 0≤Real.sin x+Real.cos x)
      (by norm_num : (0:ℝ)≤399215/1000000)
    dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hm
    rw [(first_width hxq).1] at hm
    nlinarith [hb.1]

def positiveCut (i : Bool) : ℝ := if i then 11/10 else 27/20

theorem positive_secondary_cut (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤ secondary i true b B x) : positiveCut i<x := by
  by_contra! hsmall
  by_cases hn : x≤0
  · have hh := nonpositive_secondary_owners i true
      ⟨hb.1,hb.2.trans b1_mem.2⟩ ⟨b2_mem.1.trans hB.1,hB.2⟩ ⟨hx,hn⟩ hm
    cases hh.2
  · have hx0 : 0≤x := (lt_of_not_ge hn).le
    have hcap : positiveCut i∈Icc 0 (Real.pi/2) := by
      cases i <;> dsimp [positiveCut] <;> constructor <;> linarith [FrameLowPair.pi_lower]
    have hxq : x∈Icc 0 (Real.pi/2) := ⟨hx0,hsmall.trans hcap.2⟩
    have ht := FrameLowPair.quadrant hxq
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2)≤x) hcap.2 hsmall
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hx0
      (by linarith [hcap.2,Real.pi_pos]) hsmall
    have hsE := sin_upper_five hcap.1
    have hcE := cos_lower_six hcap.1
    have ha := A_high_bounds hB
    have hAs := mul_le_mul_of_nonneg_right
      (show A B-1/2≤7/10 by linarith [ha.2,a2_bounds.2]) ht.1
    have hBc := mul_le_mul_of_nonneg_right
      (show (10139/10000:ℝ)≤B+1/2 by linarith [hB.1,b2_bounds.1]) ht.2.2.1
    dsimp [secondary,FrameLowMidGeometry.secondary] at hm
    rw [(first_width hxq).1] at hm
    cases i <;> norm_num [positiveCut,sign] at *
    all_goals nlinarith [hb.1,hb.2,b1_bounds.2]

theorem negative_primary_cut {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤primary false b B x) : (3/5:ℝ)<x := by
  by_contra! hsmall
  by_cases hn : x≤0
  · exact (not_lt_of_ge hm) (nonpositive_primary_false false
      ⟨hb.1,hb.2.trans b1_mem.2⟩ ⟨b2_mem.1.trans hB.1,hB.2⟩ ⟨hx,hn⟩)
  · have hx0 : 0≤x := (lt_of_not_ge hn).le
    have hxq : x∈Icc 0 (Real.pi/2) :=
      ⟨hx0,by linarith [hsmall,FrameLowPair.pi_lower]⟩
    have ht := FrameLowPair.quadrant hxq
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2)≤x)
      (by linarith [FrameLowPair.pi_lower] : (3/5:ℝ)≤Real.pi/2) hsmall
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hx0
      (by linarith [FrameLowPair.pi_lower] : (3/5:ℝ)≤Real.pi) hsmall
    have hsE := sin_upper_five (show (0:ℝ)≤3/5 by norm_num)
    have hcE := cos_lower_six (show (0:ℝ)≤3/5 by norm_num)
    norm_num at hsE hcE
    have hAc := mul_le_mul_of_nonneg_right
      (show (1399/1000:ℝ)≤A B+1/2 by linarith [(A_high_bounds hB).1,c0_bounds.1]) ht.2.2.1
    have hBs := mul_le_mul_of_nonneg_right
      (show B-1/2≤2/5 by linarith [hB.2,c0_bounds.2]) ht.1
    dsimp [primary,FrameLowMidGeometry.primary,sign] at hm
    rw [(first_width hxq).1] at hm
    nlinarith [(A_low_bounds hb).2,a0_precise.2]

theorem positive_primary_cut {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤primary true b B x) : Real.pi/2<x := by
  by_contra! hsmall
  by_cases hn : x≤0
  · exact (not_lt_of_ge hm) (nonpositive_primary_false true
      ⟨hb.1,hb.2.trans b1_mem.2⟩ ⟨b2_mem.1.trans hB.1,hB.2⟩ ⟨hx,hn⟩)
  · have hxq : x∈Icc 0 (Real.pi/2) := ⟨(lt_of_not_ge hn).le,hsmall⟩
    have ht := FrameLowPair.quadrant hxq
    have hw := FrameCoreArc.width_one_le x
    rw [(first_width hxq).1] at hw
    have hAc := mul_le_mul_of_nonneg_right
      (show (1013/1000:ℝ)≤A B+1/2 by linarith [(A_high_bounds hB).1,c0_bounds.1]) ht.2.2.1
    have hBs := mul_le_mul_of_nonneg_right
      (show (1013/1000:ℝ)≤B+1/2 by linarith [hB.1,b2_bounds.1]) ht.1
    dsimp [primary,FrameLowMidGeometry.primary,sign] at hm
    rw [(first_width hxq).1] at hm
    nlinarith [(A_low_bounds hb).2,a0_precise.2]

/-- One full original sign branch, including every angular tail. -/
theorem negative_negative_secondary {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤ secondary false false b B x) :
    (8833/10000:ℝ)<lowHighCost false false b B x := by
  have hcut := negative_secondary_cut hb hB hx hm
  by_cases htail : (4/5:ℝ)≤x
  · exact low_high_tail false false hb hB (by simpa [lowHighTail] using htail)
  · exact FrameLowHighSecondaryNegative.weak_separator false hb hB
      (by simpa [FrameLowHighSecondaryNegative.left,FrameLowHighSecondaryNegative.right]
        using (show x∈Icc (3/10:ℝ) (4/5) from ⟨hcut.le,(lt_of_not_ge htail).le⟩)) hm

end SquaresInCircles.Eight.FrameLowHighCuts
end
end
end

section
/-!
## The low-positive/high-negative branch at every negative angle

Away from the parallel strip, the original high-target functional
decreases on its whole intrinsic arc.  Its diagonal support gives one
explicit increasing trigonometric function.  The comparison retains
the original weak secondary margin and its low-source loss.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighNegativeAngles
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus

def domain : Set ℝ := Icc (1/50:ℝ) (34/125)
def target (x B : ℝ) : ℝ := H B+(189/200)*A B*Real.sin x-(189/200)*B*Real.cos x
def targetD (x B : ℝ) : ℝ :=
  (FrameHighArc.u-(189/200)*Real.sin x)*slope B+FrameHighArc.v-(189/200)*Real.cos x
def F (x : ℝ) : ℝ :=
  -x+Real.pi/4-1/100000+9/16+
    (153/400-(189/200)*c0)*Real.cos x+(153/400+(189/200)*c0)*Real.sin x
def Fd (x : ℝ) : ℝ :=
  -1-(153/400-(189/200)*c0)*Real.sin x+(153/400+(189/200)*c0)*Real.cos x

theorem trig_bounds {x : ℝ} (hx : x∈domain) :
    0≤Real.sin x ∧ Real.sin x≤34/125 ∧
      (963/1000:ℝ)<Real.cos x ∧ Real.cos x≤1 ∧
        (10197/10000:ℝ)<Real.sin x+Real.cos x := by
  have hx0 : 0≤x := by linarith [hx.1]
  have hxp : x≤Real.pi/2 := by linarith [hx.2,FrameLowPair.pi_lower]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [hxp,Real.pi_pos])
  have hsu := Real.sin_le hx0
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx0 hx.2 2
  have hmono : MonotoneOn (fun z => Real.sin z+Real.cos z) (Icc (0:ℝ) (34/125)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z _ => ((Real.hasDerivAt_sin z).add
        (Real.hasDerivAt_cos z)).continuousAt.continuousWithinAt
    · exact fun z _ => (Real.hasDerivAt_sin z).add (Real.hasDerivAt_cos z)
    · intro z hz
      have hzs := Real.sin_le hz.1.le
      have hzc := Real.one_sub_sq_div_two_le_cos (x := z)
      have hzsq := pow_le_pow_left₀ hz.1.le hz.2.le 2
      nlinarith
  have hsum := hmono (show (1/50:ℝ)∈Icc 0 (34/125) by constructor <;> norm_num)
    ⟨hx0,hx.2⟩ hx.1
  have hs0 := sin_lower_seven (show (0:ℝ)≤1/50 by norm_num)
  have hc0 := cos_lower_six (show (0:ℝ)≤1/50 by norm_num)
  norm_num at hs0 hc0
  exact ⟨hs,by linarith [hx.2],by nlinarith,Real.cos_le_one x,by linarith⟩

theorem target_deriv {x B : ℝ} (hB : B∈Icc b2 c0) :
    HasDerivAt (target x) (targetD x B) B := by
  have he := high_extended hB
  have h := ((extended_H_deriv he).fun_add
    (((extended_A_deriv he).const_mul (189/200)).mul_const (Real.sin x))).fun_sub
      (((hasDerivAt_id' B).const_mul (189/200)).mul_const (Real.cos x))
  refine h.congr_deriv ?_
  simp only [targetD,FrameHighArc.Hd,Ad,FrameLowArc.slope,neg_div]
  ring

theorem targetD_negative {x B : ℝ} (hx : x∈domain) (hB : B∈Icc b2 c0) :
    targetD x B<0 := by
  have ht := trig_bounds hx
  have hr := slope_high_bounds hB
  have hp : 0≤FrameHighArc.u-(189/200)*Real.sin x := by
    dsimp [FrameHighArc.u]
    linarith [ht.2.1]
  have hmul := mul_le_mul_of_nonneg_left hr.2 hp
  dsimp [targetD,FrameHighArc.u,FrameHighArc.v] at *
  linarith [ht.2.2.2.2]

theorem target_antitone {x : ℝ} (hx : x∈domain) : AntitoneOn (target x) (Icc b2 c0) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun B hB => (target_deriv hB).continuousAt.continuousWithinAt
  · exact fun B hB => target_deriv (Ioo_subset_Icc_self hB)
  · exact fun B hB => (targetD_negative hx (Ioo_subset_Icc_self hB)).le

theorem F_deriv (x : ℝ) : HasDerivAt F (Fd x) x := by
  have h := (((((hasDerivAt_id' x).fun_neg.add_const (Real.pi/4)).sub_const (1/100000)).add_const
    (9/16)).fun_add ((Real.hasDerivAt_cos x).const_mul (153/400-(189/200)*c0))).fun_add
      ((Real.hasDerivAt_sin x).const_mul (153/400+(189/200)*c0))
  refine h.congr_deriv ?_
  simp only [Fd]
  ring

theorem Fd_positive {x : ℝ} (hx : x∈domain) : 0<Fd x := by
  have ht := trig_bounds hx
  have hc : 153/400-(189/200)*c0≤0 := by linarith [c0_bounds.1]
  have hs := mul_nonneg (neg_nonneg.mpr hc) ht.1
  have hp : (123/100:ℝ)≤153/400+(189/200)*c0 := by linarith [c0_bounds.1]
  have hm := mul_le_mul hp ht.2.2.1.le (by norm_num : (0:ℝ)≤963/1000)
    (by linarith : 0≤153/400+(189/200)*c0)
  dsimp [Fd]
  nlinarith

theorem F_monotone : MonotoneOn F domain := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (F_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => F_deriv x
  · exact fun x hx => (Fd_positive (Ioo_subset_Icc_self hx)).le

theorem initial_lower : (8833/10000:ℝ)<F (1/50) := by
  have hc : 153/400-(189/200)*c0≤0 := by linarith [c0_bounds.1]
  have hscoef : 0≤153/400+(189/200)*c0 := by linarith [c0_bounds.1]
  have hcos := mul_le_mul_of_nonpos_left (Real.cos_le_one (1/50)) hc
  have hs := sin_lower_seven (show (0:ℝ)≤1/50 by norm_num)
  have hs0 : (19998/1000000:ℝ)≤Real.sin (1/50) := by norm_num at hs; linarith
  have hsin := mul_le_mul
    (show (123225/100000:ℝ)≤153/400+(189/200)*c0 by linarith [diagonal_precise.1]) hs0
    (by norm_num : (0:ℝ)≤19998/1000000) hscoef
  dsimp [F]
  nlinarith [Arithmetic.pi_hand_enclosure.1,diagonal_precise.2]

theorem lower {x : ℝ} (hx : x∈domain) : (8833/10000:ℝ)<F x :=
  initial_lower.trans_le (F_monotone ⟨le_rfl,by norm_num⟩ hx hx.1)

theorem support {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈domain) (hm : 0≤ secondary true false b B (-x)) :
    F x≤lowHighCost true false b B (-x) := by
  have hs := low_positive_source hb
  have ht := target_antitone hx hB ⟨b2_mem.2,le_rfl⟩ hB.2
  have hscaled := mul_nonneg (show (0:ℝ)≤189/200 by norm_num) hm
  have hxn : -x∈Icc (-(54/125:ℝ)) 0 := by constructor <;> linarith [hx.1,hx.2]
  have hw := negative_width hxn
  dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hscaled
  rw [hw.1] at hscaled
  dsimp [target] at ht
  rw [H_c0,A_c0] at ht
  dsimp [F,lowHighCost,sign]
  rw [hw.2]
  simp only [Real.sin_neg,Real.cos_neg] at hscaled ⊢
  nlinarith

theorem weak_separator {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (-(34/125:ℝ)) (-(1/50:ℝ)))
    (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<lowHighCost true false b B x := by
  have hz : -x∈domain := by constructor <;> linarith [hx.1,hx.2]
  have hmargin : 0≤ secondary true false b B (-(-x)) := by simpa using hm
  simpa only [neg_neg] using (lower hz).trans_le (support hb hB hz hmargin)

/-- The complete original positive-low, negative-high secondary branch. -/
theorem positive_negative_secondary {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<lowHighCost true false b B x := by
  by_cases htail : (23/50:ℝ)≤x
  · exact low_high_tail true false hb hB htail
  by_cases hleft : x≤-(1/50:ℝ)
  · exact weak_separator hb hB ⟨hx,hleft⟩ hm
  by_cases hstrip : x≤1/50
  · exact FrameLowHighParallel.low_high_strip hb hB ⟨by linarith,hstrip⟩ hm
  · exact FrameLowHighSecondaryNegative.weak_separator true hb hB
      ⟨by simpa [FrameLowHighSecondaryNegative.left] using le_of_lt (lt_of_not_ge hstrip),
        by simpa [FrameLowHighSecondaryNegative.right] using le_of_lt (lt_of_not_ge htail)⟩ hm

end SquaresInCircles.Eight.FrameLowHighNegativeAngles
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighSecondaryOpposite
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameLowHighGeometry

def lam : ℝ := 51/50
def N (x : ℝ) : ℝ :=
  CircularNorm.norm (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
    (-2*lam*FrameHighArc.v) (-2*lam*FrameHighArc.u) x
def Nd (x : ℝ) : ℝ :=
  CircularNorm.d1 (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
    (-2*lam*FrameHighArc.v) (-2*lam*FrameHighArc.u) x
def Ndd (x : ℝ) : ℝ :=
  CircularNorm.d2 (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
    (-2*lam*FrameHighArc.v) (-2*lam*FrameHighArc.u) x
def K : ℝ := 3/5-FrameHighArc.k-(FrameHighArc.u-FrameHighArc.v)/2
def cosCoefficient (second : Bool) : ℝ := if second then 93/100 else 9/100
def F (second : Bool) (x : ℝ) : ℝ :=
  x+K+(93/100)*Real.sin x-cosCoefficient second*Real.cos x-R*N x
def Fd (second : Bool) (x : ℝ) : ℝ :=
  1+(93/100)*Real.cos x+cosCoefficient second*Real.sin x-R*Nd x
def Fdd (second : Bool) (x : ℝ) : ℝ :=
  -(93/100)*Real.sin x+cosCoefficient second*Real.cos x-R*Ndd x
def left (second : Bool) : ℝ := if second then Real.pi/2 else 27/20
def right (second : Bool) : ℝ := if second then 101/50 else Real.pi/2

theorem energy_positive (x : ℝ) :
    0<CircularNorm.energy (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
      (-2*lam*FrameHighArc.v) (-2*lam*FrameHighArc.u) x := by
  have hh := FrameCoreArc.projection_lt
    (a := FrameHighArc.u) (b := FrameHighArc.v)
    (by norm_num : (0:ℝ)<7/10)
    (by norm_num [FrameHighArc.u,FrameHighArc.v]) x
  dsimp [CircularNorm.energy,lam,FrameHighArc.u,FrameHighArc.v] at *
  linarith

theorem N_positive (x : ℝ) : 0<N x := CircularNorm.norm_pos (energy_positive x)
theorem N_square (x : ℝ) :
    (N x)^2=FrameHighArc.u^2+FrameHighArc.v^2+lam^2-
      2*lam*(FrameHighArc.u*Real.sin x+FrameHighArc.v*Real.cos x) := by
  have hh := CircularNorm.norm_sq (energy_positive x).le
  convert hh using 1 <;> dsimp [N,CircularNorm.energy]
  ring
theorem N_deriv (x : ℝ) : HasDerivAt N (Nd x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive x)
theorem Nd_deriv (x : ℝ) : HasDerivAt Nd (Ndd x) x :=
  CircularNorm.d1_hasDerivAt (energy_positive x)

theorem trig_window {x : ℝ} (hx : x∈Icc (27/20:ℝ) (101/50)) :
    (9/10:ℝ)<Real.sin x ∧ Real.cos x<11/50 := by
  have hs0 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤27/20 by norm_num)
  have hs1 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤101/50 by norm_num)
  have hc0 := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤27/20 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs0 hs1 hc0
  have hs := sin_endpoint_lower (by norm_num : (0:ℝ)≤27/20)
    (by linarith [FrameLowPair.pi_lower] : (101/50:ℝ)≤Real.pi) hx
    (by linarith : (9/10:ℝ)<Real.sin (27/20:ℝ))
    (by linarith : (9/10:ℝ)<Real.sin (101/50:ℝ))
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤27/20) (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1
  exact ⟨hs,by linarith⟩

theorem N_monotone : MonotoneOn N (Icc (27/20:ℝ) (101/50)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (N_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => N_deriv x
  · intro x hx
    have ht := trig_window (Ioo_subset_Icc_self hx)
    have hp := N_positive x
    dsimp [Nd,CircularNorm.d1,CircularNorm.slope]
    apply div_nonneg _ (by positivity)
    dsimp [lam,FrameHighArc.u,FrameHighArc.v]
    linarith

theorem endpoint_norms : N (27/20:ℝ)<229/500 ∧
    N (Real.pi/2)<597/1000 ∧ N (101/50:ℝ)<181/200 := by
  have h0 := N_square (27/20)
  have hm := N_square (Real.pi/2)
  have h1 := N_square (101/50)
  have hp0 := N_positive (27/20)
  have hpm := N_positive (Real.pi/2)
  have hp1 := N_positive (101/50)
  have hs0 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤27/20 by norm_num)
  have hc0 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤27/20 by norm_num)
  have hs1 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤101/50 by norm_num)
  have hc1 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤101/50 by norm_num)
  norm_num [lam,FrameHighArc.u,FrameHighArc.v,
    HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at h0 hm h1 hs0 hc0 hs1 hc1
  refine ⟨lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_,lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_,
    lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_⟩
  · rw [h0]; norm_num; linarith
  · rw [hm]; norm_num
  · rw [h1]; norm_num; linarith

theorem N_upper {x : ℝ} (hx : x∈Icc (27/20:ℝ) (101/50)) : N x<181/200 :=
  (N_monotone hx ⟨by norm_num,le_rfl⟩ hx.2).trans_lt endpoint_norms.2.2

theorem Ndd_lower (x : ℝ) : -N x/4≤Ndd x :=
  CircularNorm.curvature_lower (energy_positive x)
    (by norm_num [lam,FrameHighArc.u,FrameHighArc.v])

theorem F_deriv (second : Bool) (x : ℝ) : HasDerivAt (F second) (Fd second x) x := by
  have h := ((((hasDerivAt_id' x).add_const K).fun_add
    ((Real.hasDerivAt_sin x).const_mul (93/100))).fun_sub
      ((Real.hasDerivAt_cos x).const_mul (cosCoefficient second))).fun_sub ((N_deriv x).const_mul R)
  refine h.congr_deriv ?_
  simp only [Fd]
  ring
theorem Fd_deriv (second : Bool) (x : ℝ) : HasDerivAt (Fd second) (Fdd second x) x := by
  have h := ((((Real.hasDerivAt_cos x).const_mul (93/100)).const_add 1).fun_add
    ((Real.hasDerivAt_sin x).const_mul (cosCoefficient second))).fun_sub ((Nd_deriv x).const_mul R)
  refine h.congr_deriv ?_
  simp only [Fdd]
  ring

theorem quadrant_domain (second : Bool) {x : ℝ}
    (hx : x∈Icc (left second) (right second)) : x∈Icc (27/20:ℝ) (101/50) := by
  have hp := Arithmetic.pi_hand_enclosure
  cases second <;> dsimp [left,right] at hx <;> constructor <;> linarith [hx.1,hx.2]

theorem Fdd_negative (second : Bool) {x : ℝ}
    (hx : x∈Icc (left second) (right second)) : Fdd second x<0 := by
  have hdom := quadrant_domain second hx
  have ht := trig_window hdom
  have hcurv := mul_le_mul_of_nonneg_left (Ndd_lower x) R_pos.le
  have hR : R<(99/50:ℝ) := by linarith [radius_precise.2]
  have hn := mul_le_mul hR.le (N_upper hdom).le (N_positive x).le
    (by norm_num : (0:ℝ)≤99/50)
  cases second <;> dsimp [Fdd,cosCoefficient] <;> nlinarith

theorem F_concave (second : Bool) :
    ConcaveOn ℝ (Icc (left second) (right second)) (F second) :=
  concave_of_deriv2 (fun x _ => F_deriv second x) (fun x _ => Fd_deriv second x)
    (fun _ hx => (Fdd_negative second hx).le)

theorem endpoint_lower (second : Bool) :
    (8833/10000:ℝ)<F second (left second) ∧
      (8833/10000:ℝ)<F second (right second) := by
  have hR := radius_precise.2
  have hn0 := mul_le_mul hR.le endpoint_norms.1.le (N_positive (27/20)).le
    (by norm_num)
  have hnm := mul_le_mul hR.le endpoint_norms.2.1.le (N_positive (Real.pi/2)).le
    (by norm_num)
  have hn1 := mul_le_mul hR.le endpoint_norms.2.2.le (N_positive (101/50)).le
    (by norm_num)
  have hs0 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤27/20 by norm_num)
  have hc0 := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤27/20 by norm_num)
  have hs1 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤101/50 by norm_num)
  have hc1 := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤101/50 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs0 hc0 hs1 hc1
  have hk := k_bounds.2.1
  have hp := Arithmetic.pi_hand_enclosure.1
  cases second <;> norm_num [F,K,left,right,cosCoefficient,FrameHighArc.u,FrameHighArc.v]
  all_goals constructor <;> linarith

theorem lower (second : Bool) {x : ℝ} (hx : x∈Icc (left second) (right second)) :
    (8833/10000:ℝ)<F second x :=
  concave_gt_of_endpoints (F_concave second) hx
    (endpoint_lower second).1 (endpoint_lower second).2

theorem circle_support {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (second : Bool)
    (hx : if second then x∈Icc (Real.pi/2) Real.pi else x∈Icc 0 (Real.pi/2))
    (hm : 0≤ secondary false true b B x) : F second x≤lowHighCost false true b B x := by
  have hs : 0≤-L b+lam*b := by dsimp [lam]; linarith [low_unit_source hb,hb.1]
  have hscaled := mul_nonneg (show (0:ℝ)≤lam by norm_num [lam]) hm
  have ht := circle_linear_lower (A_circle ⟨b2_mem.1.trans hB.1,hB.2⟩)
    (FrameHighArc.u-lam*Real.sin x) (lam*Real.cos x-FrameHighArc.v)
  have hn : Real.sqrt ((FrameHighArc.u-lam*Real.sin x)^2+
      (lam*Real.cos x-FrameHighArc.v)^2)=N x := by
    dsimp [N,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination lam^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  cases second with
  | false =>
      simp only [Bool.false_eq_true,↓reduceIte] at hx
      dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hscaled
      rw [(first_width hx).1] at hscaled
      dsimp [F,K,cosCoefficient,lowHighCost,H,sign]
      rw [(first_width hx).2]
      dsimp [lam] at hs ht hscaled
      nlinarith
  | true =>
      simp only [↓reduceIte] at hx
      dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hscaled
      rw [(second_width hx).1] at hscaled
      dsimp [F,K,cosCoefficient,lowHighCost,H,sign]
      rw [(second_width hx).2]
      dsimp [lam] at hs ht hscaled
      nlinarith

theorem weak_separator {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : -(34/125:ℝ)≤x) (hm : 0≤ secondary false true b B x) :
    (8833/10000:ℝ)<lowHighCost false true b B x := by
  have hcut : (27/20:ℝ)<x := by
    simpa [FrameLowHighCuts.positiveCut] using
      FrameLowHighCuts.positive_secondary_cut false hb hB hx hm
  by_cases htail : (101/50:ℝ)≤x
  · exact low_high_tail false true hb hB (by simpa [lowHighTail] using htail)
  · by_cases hhalf : x≤Real.pi/2
    · exact (lower false (by simpa [left,right] using
        (show x∈Icc (27/20:ℝ) (Real.pi/2) from ⟨hcut.le,hhalf⟩))).trans_le
        (circle_support hb hB false ⟨by linarith,hhalf⟩ hm)
    · exact (lower true (by simpa [left,right] using
        (show x∈Icc (Real.pi/2) (101/50:ℝ) from
          ⟨(lt_of_not_ge hhalf).le,(lt_of_not_ge htail).le⟩))).trans_le
        (circle_support hb hB true
          ⟨(lt_of_not_ge hhalf).le,by linarith [FrameLowPair.pi_lower]⟩ hm)

end SquaresInCircles.Eight.FrameLowHighSecondaryOpposite
end
end
end

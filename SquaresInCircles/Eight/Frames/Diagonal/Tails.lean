module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Frames.High.Arc
public import SquaresInCircles.Eight.Frames.Pair.Shape

/-!
# Eight squares: complete angular tails for M/H and H/H

The quarter-periodic charge is bounded by half the distance to the
quarter turn.  These estimates cover every later angle, with no upper
frame-window hypothesis.
-/

section
/-!
## The exact outer circle in diagonal coordinates

The coordinate change is `(a,b) ↦ (a+b,a-b)`.  It retains both closed
intrinsic cuts.  Its circle, derivatives, endpoint supports and physical
center radii are established before any frame or word concentration.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameDiagonalArc
open FramePair

def R : ℝ := Real.sqrt (2*Q0)
def A (b : ℝ) : ℝ := Real.sqrt (2*Q0-b^2)-1
def Ad (b : ℝ) : ℝ := -b/(A b+1)
def Add (b : ℝ) : ℝ := -(2*Q0)/(A b+1)^3
def slope (b : ℝ) : ℝ := b/(A b+1)
def slopeD (b : ℝ) : ℝ := (2*Q0)/(A b+1)^3
def a0 : ℝ := R-1
def a1 : ℝ := FrameMidArc.a2+FrameMidArc.b2
def b1 : ℝ := FrameMidArc.a2-FrameMidArc.b2
def a2 : ℝ := FrameLowArc.a1+FrameLowArc.b1
def b2 : ℝ := FrameLowArc.a1-FrameLowArc.b1
def linear (p q b : ℝ) : ℝ := p*A b+q*b
def foldTrans (b : ℝ) : ℝ := FrameCircleArc.A b-b

theorem R_pos : 0<R := Real.sqrt_pos.mpr (by norm_num [Q0])
theorem R_sq : R^2=2*Q0 := Real.sq_sqrt (by norm_num [Q0])

theorem R_precise :
    (279842813/100000000:ℝ)<R ∧ R<139921407/50000000 := by
  have hs := R_sq
  have hp := R_pos
  norm_num [Q0] at hs
  constructor <;> nlinarith

theorem R_eq_diagonal : R=2*c0+1 := by
  have hs := R_sq
  have hc := FrameCircleArc.c0_circle
  have hp := R_pos
  have hcpos := FrameCircleArc.c0_bounds.1
  nlinarith

theorem a0_eq_diagonal : a0=2*c0 := by rw [a0,R_eq_diagonal]; ring

theorem a0_precise :
    (179842813/100000000:ℝ)<a0 ∧ a0<89921407/50000000 := by
  dsimp [a0]
  constructor <;> linarith [R_precise.1,R_precise.2]

theorem b1_eq : b1=(2/5)*a1 := by
  dsimp [b1,a1,FrameMidArc.b2]
  ring

theorem b2_eq : b2=(3/5)*a2 := by
  dsimp [b2,a2,FrameLowArc.b1]
  ring

theorem a1_precise :
    (85661147/50000000:ℝ)<a1 ∧ a1<34264459/20000000 := by
  dsimp [a1,FrameMidArc.b2]
  constructor <;> linarith [FrameMidArc.a2_bounds.1,FrameMidArc.a2_bounds.2]

theorem a2_precise :
    (32468681/20000000:ℝ)<a2 ∧ a2<162343407/100000000 := by
  dsimp [a2,FrameLowArc.b1]
  constructor <;> linarith [FrameMidArc.a1_precise.1,FrameMidArc.a1_precise.2]

theorem b1_bounds : (137/200:ℝ)<b1 ∧ b1<343/500 := by
  rw [b1_eq]
  constructor <;> linarith [a1_precise.1,a1_precise.2]

theorem b2_bounds : (487/500:ℝ)<b2 ∧ b2<39/40 := by
  rw [b2_eq]
  constructor <;> linarith [a2_precise.1,a2_precise.2]

theorem b1_lt_b2 : b1<b2 := by linarith [b1_bounds.2,b2_bounds.1]

theorem first_circle : (a1+1)^2+b1^2=2*Q0 := by
  have hc := FrameMidArc.upper_circle
  dsimp [a1,b1]
  nlinarith only [hc]

theorem last_circle : (a2+1)^2+b2^2=2*Q0 := by
  have hc := FrameLowArc.endpoint_circle
  dsimp [a2,b2]
  nlinarith only [hc]

theorem radicand_pos {b : ℝ} (hb : b∈Icc 0 b2) : 0<2*Q0-b^2 := by
  have hsq := pow_le_pow_left₀ hb.1 (hb.2.trans b2_bounds.2.le) 2
  norm_num [Q0] at *
  nlinarith

theorem A_shift_pos {b : ℝ} (hb : b∈Icc 0 b2) : 0<A b+1 := by
  simpa [A] using Real.sqrt_pos.mpr (radicand_pos hb)

theorem A_circle {b : ℝ} (hb : b∈Icc 0 b2) :
    (A b+1)^2+b^2=2*Q0 := by
  have hs := Real.sq_sqrt (radicand_pos hb).le
  dsimp [A]
  nlinarith

theorem A_hasDerivAt {b : ℝ} (hb : b∈Icc 0 b2) : HasDerivAt A (Ad b) b := by
  have hd := ((hasDerivAt_const b (2*Q0)).sub ((hasDerivAt_id b).pow 2)).sqrt
    (radicand_pos hb).ne'
  convert hd.sub_const 1 using 1
  · rfl
  · dsimp [Ad,A]
    ring

theorem Ad_hasDerivAt {b : ℝ} (hb : b∈Icc 0 b2) : HasDerivAt Ad (Add b) b := by
  have hn := (A_shift_pos hb).ne'
  have hc := A_circle hb
  have hd := (hasDerivAt_id b).neg.div ((A_hasDerivAt hb).add_const 1) hn
  convert hd using 1
  · rfl
  · dsimp [Ad,Add]
    field_simp [hn]
    nlinarith only [hc]

theorem slope_hasDerivAt {b : ℝ} (hb : b∈Icc 0 b2) :
    HasDerivAt slope (slopeD b) b := by
  convert (Ad_hasDerivAt hb).fun_neg using 1
  · funext y
    dsimp [Ad,slope]
    ring
  · dsimp [Add,slopeD]
    ring

theorem Ad_nonpos {b : ℝ} (hb : b∈Icc 0 b2) : Ad b≤0 := by
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.1) (A_shift_pos hb).le

theorem Add_negative {b : ℝ} (hb : b∈Icc 0 b2) : Add b<0 := by
  exact div_neg_of_neg_of_pos (by norm_num [Q0]) (pow_pos (A_shift_pos hb) 3)

theorem A_antitone : AntitoneOn A (Icc 0 b2) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun b hb => (A_hasDerivAt hb).continuousAt.continuousWithinAt
  · exact fun b hb => A_hasDerivAt (Ioo_subset_Icc_self hb)
  · exact fun b hb => Ad_nonpos (Ioo_subset_Icc_self hb)

@[simp] theorem A_zero : A 0=a0 := by simp [A,a0,R]

@[simp] theorem A_b1 : A b1=a1 := by
  dsimp [A]
  rw [show 2*Q0-b1^2=(a1+1)^2 by linarith [first_circle],
    Real.sqrt_sq (by linarith [a1_precise.1])]
  ring

@[simp] theorem A_b2 : A b2=a2 := by
  dsimp [A]
  rw [show 2*Q0-b2^2=(a2+1)^2 by linarith [last_circle],
    Real.sqrt_sq (by linarith [a2_precise.1])]
  ring

theorem high_subset {b : ℝ} (hb : b∈Icc 0 b1) : b∈Icc 0 b2 :=
  ⟨hb.1,hb.2.trans b1_lt_b2.le⟩

theorem mid_subset {b : ℝ} (hb : b∈Icc b1 b2) : b∈Icc 0 b2 :=
  ⟨(by linarith [b1_bounds.1,hb.1]),hb.2⟩

theorem A_high_bounds {b : ℝ} (hb : b∈Icc 0 b1) : a1≤A b ∧ A b≤a0 := by
  have hlo := A_antitone (high_subset hb)
    ⟨by linarith [b1_bounds.1],b1_lt_b2.le⟩ hb.2
  have hhi := A_antitone ⟨le_rfl,by linarith [b2_bounds.1]⟩ (high_subset hb) hb.1
  simpa only [A_b1,A_zero] using And.intro hlo hhi

theorem A_mid_bounds {b : ℝ} (hb : b∈Icc b1 b2) : a2≤A b ∧ A b≤a1 := by
  have hlo := A_antitone (mid_subset hb)
    ⟨by linarith [b2_bounds.1],le_rfl⟩ hb.2
  have hhi := A_antitone ⟨by linarith [b1_bounds.1],b1_lt_b2.le⟩
    (mid_subset hb) hb.1
  simpa only [A_b1,A_b2] using And.intro hlo hhi

theorem A_bounds {b : ℝ} (hb : b∈Icc 0 b2) : a2≤A b ∧ A b≤a0 := by
  have hlo := A_antitone hb ⟨by linarith [b2_bounds.1],le_rfl⟩ hb.2
  have hhi := A_antitone ⟨le_rfl,by linarith [b2_bounds.1]⟩ hb hb.1
  simpa only [A_b2,A_zero] using And.intro hlo hhi

theorem slope_high_bounds {b : ℝ} (hb : b∈Icc 0 b1) :
    0≤ slope b ∧ slope b<(253/1000:ℝ) := by
  have hp := A_shift_pos (high_subset hb)
  have ha := A_high_bounds hb
  constructor
  · exact div_nonneg hb.1 hp.le
  · apply (div_lt_iff₀ hp).2
    linarith [hb.2,b1_bounds.2,ha.1,a1_precise.1]

theorem slope_mid_bounds {b : ℝ} (hb : b∈Icc b1 b2) :
    (63/250:ℝ)<slope b ∧ slope b<(93/250:ℝ) := by
  have hp := A_shift_pos (mid_subset hb)
  have ha := A_mid_bounds hb
  constructor
  · apply (lt_div_iff₀ hp).2
    linarith [hb.1,b1_bounds.1,ha.2,a1_precise.2]
  · apply (div_lt_iff₀ hp).2
    linarith [hb.2,b2_bounds.2,ha.1,a2_precise.1]

theorem slope_bounds {b : ℝ} (hb : b∈Icc 0 b2) : 0≤ slope b ∧ slope b<1 := by
  have hp := A_shift_pos hb
  constructor
  · exact div_nonneg hb.1 hp.le
  · apply (div_lt_iff₀ hp).2
    linarith [hb.2,b2_bounds.2,(A_bounds hb).1,a2_precise.1]

theorem linear_hasDerivAt {b : ℝ} (hb : b∈Icc 0 b2) (p q : ℝ) :
    HasDerivAt (linear p q) (p*Ad b+q) b := by
  have hh := ((A_hasDerivAt hb).const_mul p).fun_add ((hasDerivAt_id' b).const_mul q)
  show HasDerivAt (fun y => p*A y+q*y) _ b
  convert hh using 1
  ring

theorem linear_concave {p q l h : ℝ} (hp : 0≤p)
    (hl : 0≤l) (hh : h≤b2) : ConcaveOn ℝ (Icc l h) (linear p q) := by
  apply concave_of_deriv2
    (f' := fun b => p*Ad b+q) (f'' := fun b => p*Add b)
  · exact fun b hb => linear_hasDerivAt ⟨hl.trans hb.1,hb.2.trans hh⟩ p q
  · exact fun b hb =>
      ((Ad_hasDerivAt ⟨hl.trans hb.1,hb.2.trans hh⟩).const_mul p).add_const q
  · exact fun b hb => mul_nonpos_of_nonneg_of_nonpos hp
      (Add_negative ⟨hl.trans hb.1,hb.2.trans hh⟩).le

theorem linear_endpoint_lower {p q l h b : ℝ} (hp : 0≤p)
    (hl : 0≤l) (hh : h≤b2) (hb : b∈Icc l h) :
    min (linear p q l) (linear p q h)≤linear p q b :=
  (linear_concave hp hl hh).min_le_of_mem_Icc
    ⟨le_rfl,hb.1.trans hb.2⟩ ⟨hb.1.trans hb.2,le_rfl⟩ hb

theorem linear_monotone {p q : ℝ} (hp : p≤0) (hq : 0≤q) :
    MonotoneOn (linear p q) (Icc 0 b2) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (linear_hasDerivAt hb p q).continuousAt.continuousWithinAt
  · exact fun b hb => linear_hasDerivAt (Ioo_subset_Icc_self hb) p q
  · exact fun b hb => add_nonneg (mul_nonneg_of_nonpos_of_nonpos hp
      (Ad_nonpos (Ioo_subset_Icc_self hb))) hq

theorem plus_monotone : MonotoneOn (fun b => A b+b) (Icc 0 b2) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb =>
      ((A_hasDerivAt hb).fun_add (hasDerivAt_id' b)).continuousAt.continuousWithinAt
  · exact fun b hb => (A_hasDerivAt (Ioo_subset_Icc_self hb)).fun_add (hasDerivAt_id' b)
  · intro b hb
    have hs := (slope_bounds (Ioo_subset_Icc_self hb)).2
    have he : Ad b=-slope b := by dsimp [Ad,slope]; ring
    linarith

theorem minus_antitone : AntitoneOn (fun b => A b-b) (Icc 0 b2) := by
  intro b hb c hc hbc
  linarith [A_antitone hb hc hbc]

theorem high_coordinates {b : ℝ} (hb : b∈Icc 0 b1) :
    A b+b<(2399/1000:ℝ) ∧ (1027/1000:ℝ)<A b-b := by
  have hp := plus_monotone (high_subset hb)
    ⟨by linarith [b1_bounds.1],b1_lt_b2.le⟩ hb.2
  have hm := minus_antitone (high_subset hb)
    ⟨by linarith [b1_bounds.1],b1_lt_b2.le⟩ hb.2
  dsimp only at hp hm
  rw [A_b1,b1_eq] at hp hm
  constructor <;> linarith [a1_precise.1,a1_precise.2]

theorem mid_coordinates {b : ℝ} (hb : b∈Icc b1 b2) :
    A b+b<(1299/500:ℝ) ∧ (649/1000:ℝ)<A b-b := by
  have hp := plus_monotone (mid_subset hb)
    ⟨by linarith [b2_bounds.1],le_rfl⟩ hb.2
  have hm := minus_antitone (mid_subset hb)
    ⟨by linarith [b2_bounds.1],le_rfl⟩ hb.2
  dsimp only at hp hm
  rw [A_b2,b2_eq] at hp hm
  constructor <;> linarith [a2_precise.1,a2_precise.2]

/-- Unrestricted full-circle support; the coefficients may have either sign. -/
theorem circle_linear_lower {a b : ℝ}
    (hc : (a+1)^2+b^2=2*Q0) (p q : ℝ) :
    -p-R*Real.sqrt (p^2+q^2)≤p*a+q*b := by
  let N : ℝ := Real.sqrt (p^2+q^2)
  have hN : 0≤N := Real.sqrt_nonneg _
  have hN2 : N^2=p^2+q^2 := Real.sq_sqrt (by positivity)
  have hprod : 0≤R*N := mul_nonneg R_pos.le hN
  have he : 2*Q0*(p^2+q^2)-(p*(a+1)+q*b)^2=
      (p*b-q*(a+1))^2 := by rw [← hc]; ring
  have hsq : (p*(a+1)+q*b)^2≤(R*N)^2 := by
    rw [mul_pow,R_sq,hN2]
    nlinarith only [he,sq_nonneg (p*b-q*(a+1))]
  have hlo : -R*N≤p*(a+1)+q*b := by nlinarith
  change -p-R*N≤p*a+q*b
  linarith

theorem folded_circle {a b : ℝ}
    (hc : (a+1/2)^2+(b+1/2)^2=Q0) :
    (a+b+1)^2+(a-b)^2=2*Q0 := by nlinarith only [hc]

theorem A_fold {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hc : (a+1/2)^2+(b+1/2)^2=Q0) : A (a-b)=a+b := by
  have he := folded_circle hc
  dsimp [A]
  rw [show 2*Q0-(a-b)^2=(a+b+1)^2 by linarith,
    Real.sqrt_sq (by linarith)]
  ring

theorem foldTrans_antitone : AntitoneOn foldTrans (Icc 0 c0) := by
  intro b hb c hc hbc
  dsimp [foldTrans]
  linarith [FrameCircleArc.A_antitone hb hc hbc]

@[simp] theorem foldTrans_diagonal : foldTrans c0=0 := by
  simp [foldTrans,FrameCircleArc.A_c0]

@[simp] theorem foldTrans_mid_high : foldTrans FrameMidArc.b2=b1 := by
  simp [foldTrans,b1,FrameMidArc.A_b2]

@[simp] theorem foldTrans_low_mid : foldTrans FrameLowArc.b1=b2 := by
  simp [foldTrans,b2,FrameLowArc.A_b1]

theorem old_high_fold {b : ℝ} (hb : b∈Icc FrameMidArc.b2 c0) :
    foldTrans b∈Icc 0 b1 ∧ A (foldTrans b)=FrameCircleArc.A b+b := by
  have hb' : b∈Icc 0 c0 := ⟨FrameMidArc.b2_mem.1.trans hb.1,hb.2⟩
  have hlo := foldTrans_antitone hb'
    ⟨by linarith [FrameCircleArc.c0_bounds.1],le_rfl⟩ hb.2
  have hhi := foldTrans_antitone FrameMidArc.b2_mem hb' hb.1
  simp only [foldTrans_diagonal,foldTrans_mid_high] at hlo hhi
  refine ⟨⟨hlo,hhi⟩,?_⟩
  exact A_fold (by linarith [(FrameCircleArc.A_bounds hb').1,
    FrameCircleArc.c0_bounds.1]) hb'.1 (FrameCircleArc.A_circle hb')

theorem old_mid_fold {b : ℝ} (hb : b∈Icc FrameLowArc.b1 FrameMidArc.b2) :
    foldTrans b∈Icc b1 b2 ∧ A (foldTrans b)=FrameCircleArc.A b+b := by
  have hb' : b∈Icc 0 c0 :=
    ⟨FrameLowArc.b1_mem.1.trans hb.1,hb.2.trans FrameMidArc.b2_mem.2⟩
  have hlo := foldTrans_antitone hb' FrameMidArc.b2_mem hb.2
  have hhi := foldTrans_antitone FrameLowArc.b1_mem hb' hb.1
  simp only [foldTrans_mid_high,foldTrans_low_mid] at hlo hhi
  refine ⟨⟨hlo,hhi⟩,?_⟩
  exact A_fold (by linarith [(FrameCircleArc.A_bounds hb').1,
    FrameCircleArc.c0_bounds.1]) hb'.1 (FrameCircleArc.A_circle hb')

theorem high_radius_sq {b : ℝ} (hb : b∈Icc FrameMidArc.b2 c0) :
    (FrameCircleArc.A b)^2+b^2<(653/500:ℝ)^2 := by
  have hf := old_high_fold hb
  have ha := (A_high_bounds hf.1).1
  rw [hf.2] at ha
  have hc := FrameCircleArc.A_circle
    (show b∈Icc 0 c0 from ⟨FrameMidArc.b2_mem.1.trans hb.1,hb.2⟩)
  have he := a1_precise.1
  norm_num [Q0] at hc
  nlinarith

theorem state_high_fold (s : FramePair.State) (hs : s.branch=.high) :
    s.a-s.b∈Icc 0 b1 ∧ A (s.a-s.b)=s.a+s.b := by
  have hc := FrameHighArc.state_high_chart s hs
  simpa only [foldTrans,← hc.1] using old_high_fold hc.2

theorem state_mid_fold (s : FramePair.State) (hs : s.branch=.middle) :
    s.a-s.b∈Icc b1 b2 ∧ A (s.a-s.b)=s.a+s.b := by
  have hc := FrameMidArc.state_mid_chart s hs
  simpa only [foldTrans,← hc.1] using old_mid_fold hc.2

end SquaresInCircles.Eight.FrameDiagonalArc
end
end
end

section
/-!
## Explicit moving line/circle contacts in diagonal coordinates

The positive root is written explicitly.  Its circle equation, contact
equation and tangent identity are algebraic; differentiability is derived
from the positive radicand.  Later contact paths therefore need no
existential minimizer or implicit differentiability premise.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameDiagonalContactRoot
open FramePair FrameDiagonalArc

def N (l : ℝ) : ℝ := Real.sqrt (4*Q0-l^2)
def Nd (l : ℝ) : ℝ := -l/N l
def X (c d l : ℝ) : ℝ := (d*l+c*N l)/2-1
def Y (c d l : ℝ) : ℝ := (-c*l+d*N l)/2
def XD (c d l cp dp lp : ℝ) : ℝ :=
  (dp*l+d*lp+cp*N l+c*Nd l*lp)/2
def YD (c d l cp dp lp : ℝ) : ℝ :=
  (-cp*l-c*lp+dp*N l+d*Nd l*lp)/2

theorem N_pos {l : ℝ} (hl : 0<4*Q0-l^2) : 0<N l := Real.sqrt_pos.mpr hl
theorem N_sq {l : ℝ} (hl : 0≤4*Q0-l^2) : (N l)^2=4*Q0-l^2 := Real.sq_sqrt hl

theorem N_deriv {l : ℝ} (hl : 0<4*Q0-l^2) : HasDerivAt N (Nd l) l := by
  have hd := ((hasDerivAt_const l (4*Q0)).fun_sub ((hasDerivAt_id' l).fun_pow 2)).sqrt hl.ne'
  refine hd.congr_deriv ?_
  have hN : Real.sqrt (4*Q0-l^2)≠0 := (N_pos hl).ne'
  dsimp only [Nd,N]
  field_simp
  norm_num

theorem Y_deriv {c d l : ℝ→ℝ} {x cp dp lp : ℝ}
    (hc : HasDerivAt c cp x) (hd : HasDerivAt d dp x) (hl : HasDerivAt l lp x)
    (hp : 0<4*Q0-(l x)^2) :
    HasDerivAt (fun t => Y (c t) (d t) (l t))
      (YD (c x) (d x) (l x) cp dp lp) x := by
  have hn := (N_deriv hp).comp x hl
  convert (((hc.neg.mul hl).add (hd.mul hn)).div_const 2) using 1
  · rfl
  · dsimp [YD]
    ring

theorem contact {c d l : ℝ} (hu : c^2+d^2=2) :
    d*(X c d l+1)-c*Y c d l=l := by
  calc
    d*(X c d l+1)-c*Y c d l=(c^2+d^2)*l/2 := by dsimp [X,Y]; ring
    _=l := by rw [hu]; ring

theorem circle {c d l : ℝ} (hu : c^2+d^2=2) (hl : 0≤4*Q0-l^2) :
    (X c d l+1)^2+(Y c d l)^2=2*Q0 := by
  have he : (X c d l+1)^2+(Y c d l)^2=
      (c^2+d^2)*(l^2+(N l)^2)/4 := by dsimp [X,Y]; ring
  rw [he,hu,N_sq hl]
  ring

theorem radial_tangent {c d l cp dp lp : ℝ}
    (hunit : c*cp+d*dp=0) (hl : 0<4*Q0-l^2) :
    (X c d l+1)*XD c d l cp dp lp+Y c d l*YD c d l cp dp lp=0 := by
  have hn := (N_pos hl).ne'
  have he : (X c d l+1)*XD c d l cp dp lp+Y c d l*YD c d l cp dp lp=
      (c^2+d^2)*(l*lp+N l*Nd l*lp)/4+
        (c*cp+d*dp)*(l^2+(N l)^2)/4 := by dsimp [X,Y,XD,YD]; ring
  rw [he,hunit]
  dsimp [Nd]
  field_simp [hn]
  ring

theorem contact_tangent {c d l cp dp lp : ℝ}
    (hu : c^2+d^2=2) (hunit : c*cp+d*dp=0) :
    d*XD c d l cp dp lp-c*YD c d l cp dp lp+
      dp*(X c d l+1)-cp*Y c d l=lp := by
  have he : d*XD c d l cp dp lp-c*YD c d l cp dp lp+
      dp*(X c d l+1)-cp*Y c d l=
        (c^2+d^2)*lp/2+(c*cp+d*dp)*l := by
    dsimp [X,Y,XD,YD]
    ring
  rw [he,hu,hunit]
  ring

theorem YD_contact {c d l cp dp lp : ℝ}
    (hu : c^2+d^2=2) (hunit : c*cp+d*dp=0)
    (hl : 0<4*Q0-l^2) (hX : X c d l+1≠0) :
    YD c d l cp dp lp*(c+d*(Y c d l/(X c d l+1)))=
      dp*(X c d l+1)-cp*Y c d l-lp := by
  have hr := radial_tangent (lp := lp) hunit hl
  have ht := contact_tangent (l := l) (lp := lp) hu hunit
  apply (mul_right_cancel₀ hX)
  field_simp [hX]
  linear_combination -(X c d l+1)*ht+d*hr

theorem X_eq_chart {c d l : ℝ} (hu : c^2+d^2=2)
    (hl : 0≤4*Q0-l^2) (hX : 0≤X c d l+1) :
    X c d l=A (Y c d l) := by
  have hc := circle hu hl
  dsimp [A]
  rw [show 2*Q0-(Y c d l)^2=(X c d l+1)^2 by linarith,
    Real.sqrt_sq hX]
  ring

theorem target_root_bounds {c d l : ℝ}
    (hc : c∈Icc (4899/5000:ℝ) (51/50))
    (hd : d∈Icc (4899/5000:ℝ) (51/50))
    (hl : l∈Icc (197/100:ℝ) (12/5)) :
    0<4*Q0-l^2 ∧ 0<Y c d l ∧ Y c d l<4/5 ∧ 0<X c d l+1 := by
  have hsqL := pow_le_pow_left₀ (show 0≤l by linarith [hl.1]) hl.2 2
  have hsqU := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤197/100) hl.1 2
  have hrad : 0<4*Q0-l^2 := by norm_num [Q0] at *; nlinarith
  have hs := N_sq hrad.le
  have hn := N_pos hrad
  have hN : (157/50:ℝ)<N l ∧ N l<86/25 := by
    norm_num [Q0] at hs
    constructor <;> nlinarith
  have hc0 : 0≤c := by linarith [hc.1]
  have hd0 : 0≤d := by linarith [hd.1]
  have hl0 : 0≤l := by linarith [hl.1]
  have hclL := mul_le_mul hc.1 hl.1 (by norm_num) hc0
  have hclU := mul_le_mul hc.2 hl.2 hl0 (by norm_num)
  have hdnL := mul_le_mul hd.1 hN.1.le (by norm_num) hd0
  have hdnU := mul_le_mul hd.2 hN.2.le hn.le (by norm_num)
  have hdl := mul_pos (by linarith [hd.1] : 0<d) (by linarith [hl.1] : 0<l)
  have hcn := mul_pos (by linarith [hc.1] : 0<c) hn
  refine ⟨hrad,?_,?_,?_⟩ <;> dsimp [Y,X] <;> nlinarith

theorem source_root_bounds {l : ℝ} (hl : l∈Icc (19/10:ℝ) (243/100)) :
    0<4*Q0-l^2 ∧ 0<Y 1 1 l ∧ Y 1 1 l<4/5 ∧ 0<X 1 1 l+1 := by
  have hl0 : 0≤l := by linarith [hl.1]
  have hsqL := pow_le_pow_left₀ hl0 hl.2 2
  have hsqU := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤19/10) hl.1 2
  have hQ : (4:ℝ)*Q0=9789/625 := by norm_num [Q0]
  have hrad : 0<4*Q0-l^2 := by linarith
  have hs := N_sq hrad.le
  have hn := N_pos hrad
  have hlt : l<N l := by
    by_contra! hbad
    have h2 := pow_le_pow_left₀ hn.le hbad 2
    linarith
  have hut : N l<l+8/5 := by
    by_contra! hbad
    have h2 := pow_le_pow_left₀ (by linarith : 0≤l+8/5) hbad 2
    linarith [hl.1]
  refine ⟨hrad,?_,?_,?_⟩ <;> dsimp [X,Y] <;> linarith

end SquaresInCircles.Eight.FrameDiagonalContactRoot
end
end
end

section
/-!
## The unchanged frame potentials in diagonal coordinates

Both folded markers are exact complements of the original markers.
The identities include the intrinsic endpoints; they do not choose a
new side of a tie.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameDiagonalLabels
open FramePair FrameDiagonalArc

def u : ℝ := 89293/1000000
def v : ℝ := 480179/1000000
def k : ℝ := 767453/500000
def q : ℝ := 45313/1000000
def cM : ℝ := Real.pi/4+85723/40000
def H (b : ℝ) : ℝ := u*(A b-FrameDiagonalArc.a0)+v*b
def M (b : ℝ) : ℝ := cM-k*A b+q*b
def H1 : ℝ := H b1
def M1 : ℝ := M b1
def M2 : ℝ := M b2
def Hd (b : ℝ) : ℝ := v-u*slope b
def Md (b : ℝ) : ℝ := k*slope b+q

/-- `true` denotes the folded middle arc; `false` the folded high arc. -/
def arc (middle : Bool) : Set ℝ := if middle then Icc b1 b2 else Icc 0 b1
def marker (middle : Bool) (b : ℝ) : ℝ := if middle then M b else H b
def constant (middle : Bool) : ℝ := if middle then cM else -u*FrameDiagonalArc.a0
def primary (middle : Bool) : ℝ := if middle then -k else u
def transverse (middle : Bool) : ℝ := if middle then q else v

theorem marker_affine (middle : Bool) (b : ℝ) :
    marker middle b=constant middle+primary middle*A b+transverse middle*b := by
  cases middle <;> dsimp [marker,constant,primary,transverse,H,M] <;> ring

theorem arc_subset {middle : Bool} {b : ℝ} (hb : b∈arc middle) : b∈Icc 0 b2 := by
  cases middle
  · exact high_subset hb
  · exact mid_subset hb

theorem H_deriv {b : ℝ} (hb : b∈Icc 0 b1) : HasDerivAt H (Hd b) b := by
  have hd := (((A_hasDerivAt (high_subset hb)).sub_const FrameDiagonalArc.a0).const_mul u).fun_add
    ((hasDerivAt_id' b).const_mul v)
  have he : Hd b=u*Ad b+v*1 := by
    simp only [Hd,Ad,FrameDiagonalArc.slope]; ring
  rw [he]
  exact hd

theorem Hd_deriv {b : ℝ} (hb : b∈Icc 0 b1) :
    HasDerivAt Hd (-u*slopeD b) b := by
  have hd := ((slope_hasDerivAt (high_subset hb)).const_mul (-u)).const_add v
  have hf : Hd=fun x => v+-u*FrameDiagonalArc.slope x := by
    funext x; simp only [Hd]; ring
  rw [hf]
  exact hd

theorem M_deriv {b : ℝ} (hb : b∈Icc b1 b2) : HasDerivAt M (Md b) b := by
  have hd := (((A_hasDerivAt (mid_subset hb)).const_mul (-k)).const_add cM).fun_add
    ((hasDerivAt_id' b).const_mul q)
  have hf : M=fun y => (cM+-k*A y)+q*y := by
    funext y; simp only [M]; ring
  have he : Md b=-k*Ad b+q*1 := by
    simp only [Md,Ad,FrameDiagonalArc.slope]; ring
  rw [hf,he]
  exact hd

theorem Hd_positive {b : ℝ} (hb : b∈Icc 0 b1) : 0<Hd b := by
  have hr := slope_high_bounds hb
  dsimp [Hd,u,v]
  linarith

theorem Md_positive {b : ℝ} (hb : b∈Icc b1 b2) : 0<Md b := by
  have hr := slope_mid_bounds hb
  dsimp [Md,k,q]
  linarith

theorem H_monotone : MonotoneOn H (Icc 0 b1) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (H_deriv hb).continuousAt.continuousWithinAt
  · exact fun b hb => H_deriv (Ioo_subset_Icc_self hb)
  · exact fun b hb => (Hd_positive (Ioo_subset_Icc_self hb)).le

theorem M_monotone : MonotoneOn M (Icc b1 b2) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (M_deriv hb).continuousAt.continuousWithinAt
  · exact fun b hb => M_deriv (Ioo_subset_Icc_self hb)
  · exact fun b hb => (Md_positive (Ioo_subset_Icc_self hb)).le

@[simp] theorem H_zero : H 0=0 := by simp [H]

theorem H1_bounds : (0:ℝ)<H1 ∧ H1<160727/500000 := by
  have ha := a1_precise
  have h0 := a0_precise
  dsimp [H1,H]
  rw [A_b1,b1_eq]
  dsimp [u,v]
  constructor <;> linarith

theorem M_endpoints :
    (8247/25000:ℝ)<M1 ∧ M2<601/1250 := by
  have ha1 := a1_precise
  have ha2 := a2_precise
  have hp := Arithmetic.pi_hand_enclosure
  dsimp [M1,M2,M]
  rw [A_b1,A_b2,b1_eq,b2_eq]
  dsimp [cM,k,q]
  constructor <;> linarith

theorem H_bounds {b : ℝ} (hb : b∈Icc 0 b1) :
    0≤H b ∧ H b<(160727/500000:ℝ) := by
  have h0 := H_monotone ⟨le_rfl,by linarith [b1_bounds.1]⟩ hb hb.1
  have h1 := H_monotone hb ⟨by linarith [b1_bounds.1],le_rfl⟩ hb.2
  rw [H_zero] at h0
  exact ⟨h0,h1.trans_lt H1_bounds.2⟩

theorem M_bounds {b : ℝ} (hb : b∈Icc b1 b2) :
    (8247/25000:ℝ)<M b ∧ M b<(601/1250:ℝ) := by
  have h1 := M_monotone ⟨le_rfl,b1_lt_b2.le⟩ hb hb.1
  have h2 := M_monotone hb ⟨b1_lt_b2.le,le_rfl⟩ hb.2
  exact ⟨M_endpoints.1.trans_le h1,h2.trans_lt M_endpoints.2⟩

theorem H_concave : ConcaveOn ℝ (Icc 0 b1) H := by
  apply concave_of_deriv2 (fun b hb => H_deriv hb) (fun b hb => Hd_deriv hb)
  intro b hb
  have hp : 0<slopeD b := by
    exact div_pos (by norm_num [Q0]) (pow_pos (A_shift_pos (high_subset hb)) 3)
  exact (mul_neg_of_neg_of_pos (by norm_num [u]) hp).le

theorem H_fold {b : ℝ} (hb : b∈Icc FrameMidArc.b2 c0) :
    H (foldTrans b)=Real.pi/4-FrameHighArc.H b := by
  rw [H,(old_high_fold hb).2,a0_eq_diagonal]
  dsimp [foldTrans,FrameHighArc.H,FrameHighArc.k,
    FrameHighArc.u,FrameHighArc.v,u,v]
  ring

theorem M_fold {b : ℝ} (hb : b∈Icc FrameLowArc.b1 FrameMidArc.b2) :
    M (foldTrans b)=Real.pi/4-FrameMidArc.M b := by
  rw [M,(old_mid_fold hb).2]
  dsimp [foldTrans,FrameMidArc.M,FrameMidArc.cM,FrameMidArc.p,FrameMidArc.q,cM,k,q]
  ring

theorem state_high_label (s : FramePair.State) (hs : s.branch=.high) :
    sign (!s.positive)*H (s.a-s.b)=s.signedLabel-sign s.positive*(Real.pi/4) := by
  have hc := FrameHighArc.state_high_chart s hs
  have he := H_fold hc.2
  rw [foldTrans,← hc.1] at he
  rw [FrameHighArc.state_high_label s hs,he,sign_not]
  ring

theorem state_mid_label (s : FramePair.State) (hs : s.branch=.middle) :
    sign (!s.positive)*M (s.a-s.b)=s.signedLabel-sign s.positive*(Real.pi/4) := by
  have hc := FrameMidArc.state_mid_chart s hs
  have he := M_fold hc.2
  rw [foldTrans,← hc.1] at he
  rw [FrameMidArc.state_mid_label s hs,he,sign_not]
  ring

end SquaresInCircles.Eight.FrameDiagonalLabels
end
end
end

section
/-!
## Original witnesses in the diagonal chart

The chart rotates each original signed frame toward its diagonal.  Its
quarter shift preserves the width and its complementary marker preserves
the actual pair cost.  The identities below carry the original source
axes, including a zero margin, rather than selecting a new separator.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameDiagonalTransport
open FramePair FrameDiagonalArc FrameDiagonalLabels

def kind (middle : Bool) : Branch := if middle then .middle else .high
def angle (i j : Bool) (x : ℝ) : ℝ := x+(sign i-sign j)*(Real.pi/4)
def turn (s : FramePair.State) : ℝ := Real.pi/4-Real.arctan (s.b/s.a)
def offset (s : FramePair.State) : ℝ := s.offset-sign s.positive*(Real.pi/4)
def cap (middle : Bool) : ℝ := if middle then 541/1000 else 381/1000
def cost (m n i j : Bool) (b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*marker m b-sign j*marker n B
def central (i j : Bool) (a b A B x : ℝ) : ℝ :=
  a+sign i*b+(Real.sin x-Real.cos x)*A-
    sign j*(Real.sin x+Real.cos x)*B-2*pairWidth x
def extra (j : Bool) (a b A B x : ℝ) : ℝ :=
  a+b-(Real.sin x+Real.cos x)*A-
    sign j*(Real.sin x-Real.cos x)*B-2*pairWidth x
def centralAxis (i : Bool) : Fin 4 := if i then 0 else 3

@[simp] theorem angle_false_false (x : ℝ) : angle false false x=x := by
  simp [angle,sign]
@[simp] theorem angle_true_true (x : ℝ) : angle true true x=x := by
  simp [angle,sign]
@[simp] theorem angle_false_true (x : ℝ) : angle false true x=x-Real.pi/2 := by
  dsimp [angle,sign]
  ring
@[simp] theorem angle_true_false (x : ℝ) : angle true false x=x+Real.pi/2 := by
  dsimp [angle,sign]
  ring

theorem angle_width (i j : Bool) (x : ℝ) : pairWidth (angle i j x)=pairWidth x := by
  cases i <;> cases j <;> simp [pairWidth,Real.sin_add,Real.cos_add,
    Real.sin_sub,Real.cos_sub,abs_neg,add_comm,add_left_comm,add_assoc]

theorem angle_charge (i j : Bool) (x : ℝ) :
    periodicFrameCost (angle i j x)=periodicFrameCost x := by
  cases i <;> cases j <;> simp [periodicFrameCost,Real.sin_add,Real.cos_add,
    Real.sin_sub,Real.cos_sub,abs_neg,add_comm]

theorem central_identity (i j : Bool) (a b A B x : ℝ) :
    central (!i) (!j) (a+b) (a-b) (A+B) (A-B) (angle i j x)=
      2*forwardMargin (centralAxis i) a b A B (sign i) (sign j) x := by
  dsimp only [central]
  rw [angle_width]
  cases i <;> cases j
  all_goals (simp [centralAxis,sign,forwardMargin,Real.sin_add,Real.cos_add,
    Real.sin_sub,Real.cos_sub]; ring)

theorem extra_identity (j : Bool) (a b A B x : ℝ) :
    extra (!j) (a+b) (a-b) (A+B) (A-B) (angle true j x)=
      2*forwardMargin 3 a b A B 1 (sign j) x := by
  dsimp only [extra]
  rw [angle_width]
  cases j
  all_goals (simp [sign,forwardMargin,Real.sin_add,Real.cos_add]; ring)

theorem offset_turn (s : FramePair.State) : offset s=sign (!s.positive)*turn s := by
  rw [sign_not]
  dsimp [offset,turn,State.offset]
  ring

theorem gap_identity (s t : FramePair.State) (x : ℝ) :
    angle s.positive t.positive x+offset s-offset t=s.gap t x := by
  dsimp [angle,offset,State.gap]
  ring

theorem turn_nonneg (s : FramePair.State) : 0≤turn s := by
  have hr : s.b/s.a≤1 := (div_le_one s.a_pos).2 s.canonical
  have hh : Real.arctan (s.b/s.a)≤Real.pi/4 := by
    simpa [Real.arctan_one] using Real.arctan_mono hr
  exact sub_nonneg.mpr hh

theorem high_turn_upper (s : FramePair.State) (hs : s.branch=.high) :
    turn s<(381/1000:ℝ) := by
  have ht : 3*s.a≤7*s.b := by simpa [hs,TypeMem] using s.type_mem
  have hr : (3/7:ℝ) ≤ s.b/s.a := (le_div_iff₀ s.a_pos).2 (by linarith)
  have hl := Arithmetic.atanLower_le (show (0:ℝ)≤3/7 by norm_num)
  have hn : (1011/2500:ℝ)<Arithmetic.atanLower (3/7:ℝ) := by
    norm_num [Arithmetic.atanLower]
  have ha := hl.trans (Real.arctan_mono hr)
  dsimp [turn]
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem mid_turn_upper (s : FramePair.State) (hs : s.branch=.middle) :
    turn s<(541/1000:ℝ) := by
  have ht : s.a≤4*s.b ∧ 7*s.b≤3*s.a := by simpa [hs,TypeMem] using s.type_mem
  have hr : (1/4:ℝ) ≤ s.b/s.a := (le_div_iff₀ s.a_pos).2 (by linarith [ht.1])
  have hl := Arithmetic.atanLower_le (show (0:ℝ)≤1/4 by norm_num)
  have hn : (489/2000:ℝ)<Arithmetic.atanLower (1/4:ℝ) := by
    norm_num [Arithmetic.atanLower]
  have ha := hl.trans (Real.arctan_mono hr)
  dsimp [turn]
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem turn_bounds (m : Bool) (s : FramePair.State) (hs : s.branch=kind m) :
    0≤turn s ∧ turn s<cap m := by
  refine ⟨turn_nonneg s,?_⟩
  cases m
  · exact high_turn_upper s hs
  · exact mid_turn_upper s hs

theorem offset_bounds (m : Bool) (s : FramePair.State) (hs : s.branch=kind m) :
    -cap m<offset s ∧ offset s<cap m := by
  have ht := turn_bounds m s hs
  rw [offset_turn]
  cases hi : s.positive <;> simp [sign] <;> constructor <;>
    linarith [show 0<cap m by cases m <;> norm_num [cap]]

theorem angle_lower (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) :
    19/25-cap m-cap n<angle s.positive t.positive x := by
  have hso := offset_bounds m s hs
  have hto := offset_bounds n t ht
  have hid := gap_identity s t x
  linarith

/-- A nonpositive folded angle can only have folded signs `(+,-)`. -/
theorem nonpositive_signs (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x)
    (hx : angle s.positive t.positive x≤0) :
    s.positive=false ∧ t.positive=true := by
  have hso := turn_bounds m s hs
  have hto := turn_bounds n t ht
  have hmc : cap m<(19/25:ℝ) := by cases m <;> norm_num [cap]
  have hnc : cap n<(19/25:ℝ) := by cases n <;> norm_num [cap]
  have hid := gap_identity s t x
  rw [offset_turn,offset_turn] at hid
  cases hi : s.positive <;> cases hj : t.positive
  all_goals simp only [hi,hj,Bool.not_false,Bool.not_true,sign,Bool.false_eq_true,
    ↓reduceIte,one_mul,neg_one_mul] at hid hx
  all_goals first | exact ⟨rfl,rfl⟩ | linarith

theorem state_fold (m : Bool) (s : FramePair.State) (hs : s.branch=kind m) :
    s.a-s.b∈arc m ∧ A (s.a-s.b)=s.a+s.b := by
  cases m
  · exact FrameDiagonalArc.state_high_fold s hs
  · exact FrameDiagonalArc.state_mid_fold s hs

theorem state_label (m : Bool) (s : FramePair.State) (hs : s.branch=kind m) :
    sign (!s.positive)*marker m (s.a-s.b)=
      s.signedLabel-sign s.positive*(Real.pi/4) := by
  cases m
  · exact FrameDiagonalLabels.state_high_label s hs
  · exact FrameDiagonalLabels.state_mid_label s hs

theorem state_cost (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n) (x : ℝ) :
    cost m n (!s.positive) (!t.positive) (s.a-s.b) (t.a-t.b)
        (angle s.positive t.positive x)=s.cost t x := by
  rw [cost,angle_charge,state_label m s hs,state_label n t ht]
  dsimp [angle,State.cost]
  ring

theorem state_central (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n) (x : ℝ) :
    central (!s.positive) (!t.positive) (A (s.a-s.b)) (s.a-s.b)
        (A (t.a-t.b)) (t.a-t.b) (angle s.positive t.positive x)=
      2*forwardMargin (centralAxis s.positive) s.a s.b t.a t.b
        (sign s.positive) (sign t.positive) x := by
  rw [(state_fold m s hs).2,(state_fold n t ht).2]
  exact central_identity s.positive t.positive s.a s.b t.a t.b x

theorem state_central_feasible (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n) {x : ℝ}
    (hm : s.Feasible t (centralAxis s.positive) x) :
    0≤central (!s.positive) (!t.positive) (A (s.a-s.b)) (s.a-s.b)
      (A (t.a-t.b)) (t.a-t.b) (angle s.positive t.positive x) := by
  rw [state_central m n s t hs ht]
  exact mul_nonneg (by norm_num) hm

theorem state_extra (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n)
    (hi : s.positive=true) (x : ℝ) :
    extra (!t.positive) (A (s.a-s.b)) (s.a-s.b)
        (A (t.a-t.b)) (t.a-t.b) (angle s.positive t.positive x)=
      2*forwardMargin 3 s.a s.b t.a t.b (sign s.positive) (sign t.positive) x := by
  rw [(state_fold m s hs).2,(state_fold n t ht).2,hi]
  simpa [sign] using extra_identity t.positive s.a s.b t.a t.b x

end SquaresInCircles.Eight.FrameDiagonalTransport
end
end
end

section
/-!
## The initial cuts of the angle on the folded arcs

On the folded arcs `arc m` of the middle and the high ranges, the central margin
`central i j (A b) b (A B) B x` is at most `barrier m n i j x`, its value at given ends of the
source and the target arcs, for every `x` in the first quadrant (`central_upper`): the source
part is largest at `sourceEnd m i` and the target part is monotone along the arc
(`target_positive_antitone`, `target_negative_monotone`). The barrier increases with `x`
(`barrier_monotone`) and is negative at the rational angle `cut m n i j` (`cut_negative`), by one
Taylor comparison, so a weak central margin forces `x > cut m n i j` and excludes the whole initial
interval (`central_cut`). The twelve cases are middle/high, high/middle and high/high with the
signs `i`, `j` of the two ends, ties at the ends of the arcs included.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameDiagonalCuts
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FramePairCalculus

def first (m : Bool) : ℝ := if m then b1 else 0
def last (m : Bool) : ℝ := if m then b2 else b1
def sourceEnd (m i : Bool) : ℝ := if i then last m else first m
def targetEnd (n j : Bool) : ℝ := if j then first n else last n
def sourcePart (i : Bool) (b : ℝ) : ℝ := A b+sign i*b
def targetPart (j : Bool) (x B : ℝ) : ℝ :=
  (Real.sin x-Real.cos x)*A B-sign j*(Real.sin x+Real.cos x)*B
def K (m i : Bool) : ℝ := sourcePart i (sourceEnd m i)-1
def S (n j : Bool) : ℝ := A (targetEnd n j)-sign j*targetEnd n j-1
def C (n j : Bool) : ℝ := A (targetEnd n j)+sign j*targetEnd n j+1
def barrier (m n i j : Bool) (x : ℝ) : ℝ :=
  K m i+S n j*Real.sin x-C n j*Real.cos x
def cut (m n i j : Bool) : ℝ :=
  if m then
    if n then 0 else if i then (if j then 7/10 else 1/10)
      else (if j then 6/5 else 9/10)
  else if n then
    if i then (if j then 11/10 else 1/10) else (if j then 13/10 else 2/5)
  else if i then 7/20 else (if j then 1 else 3/5)

theorem arc_eq (m : Bool) : arc m=Icc (first m) (last m) := by cases m <;> rfl

theorem first_mem (m : Bool) : first m∈arc m := by
  cases m
  · show (0:ℝ)∈Icc 0 b1
    exact ⟨le_rfl,by linarith [b1_bounds.1]⟩
  · show b1∈Icc b1 b2
    exact ⟨le_rfl,b1_lt_b2.le⟩

theorem last_mem (m : Bool) : last m∈arc m := by
  cases m
  · show b1∈Icc 0 b1
    exact ⟨by linarith [b1_bounds.1],le_rfl⟩
  · show b2∈Icc b1 b2
    exact ⟨b1_lt_b2.le,le_rfl⟩

theorem source_upper (m i : Bool) {b : ℝ} (hb : b∈arc m) :
    sourcePart i b≤ sourcePart i (sourceEnd m i) := by
  have hi : b∈Icc (first m) (last m) := by simpa only [arc_eq] using hb
  cases i
  · have h : A b-b≤A (first m)-first m :=
      minus_antitone (arc_subset (first_mem m)) (arc_subset hb) hi.1
    show A b+sign false*b≤A (first m)+sign false*first m
    rw [show sign false=-1 from rfl]
    linarith
  · have h : A b+b≤A (last m)+last m :=
      plus_monotone (arc_subset hb) (arc_subset (last_mem m)) hi.2
    show A b+sign true*b≤A (last m)+sign true*last m
    rw [show sign true=1 from rfl]
    linarith

theorem target_deriv (j : Bool) (x : ℝ) {B : ℝ} (hB : B∈Icc 0 b2) :
    HasDerivAt (targetPart j x)
      (-(Real.sin x-Real.cos x)*slope B-sign j*(Real.sin x+Real.cos x)) B := by
  have hd := ((A_hasDerivAt hB).const_mul (Real.sin x-Real.cos x)).fun_sub
    ((hasDerivAt_id' B).const_mul (sign j*(Real.sin x+Real.cos x)))
  refine hd.congr_deriv ?_
  have hAd : Ad B=-FrameDiagonalArc.slope B := by
    simp only [Ad,FrameDiagonalArc.slope,neg_div]
  rw [hAd]
  ring

theorem quadrant_slope_bounds {x B : ℝ} (hx : x∈Icc 0 (Real.pi/2))
    (hB : B∈Icc 0 b2) :
    -(Real.sin x+Real.cos x)≤(Real.sin x-Real.cos x)*slope B ∧
      (Real.sin x-Real.cos x)*slope B≤Real.sin x+Real.cos x := by
  have ht := FrameLowPair.quadrant hx
  have hr := slope_bounds hB
  have hw := FrameCoreArc.width_one_le x
  rw [(first_width hx).1] at hw
  have hlo := mul_le_mul_of_nonneg_right
    (show -(1:ℝ)≤Real.sin x-Real.cos x by linarith) hr.1
  have hhi := mul_le_mul_of_nonneg_right
    (show Real.sin x-Real.cos x≤1 by linarith) hr.1
  constructor <;> linarith

theorem target_positive_antitone {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    AntitoneOn (targetPart true x) (Icc 0 b2) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun B hB => (target_deriv true x hB).continuousAt.continuousWithinAt
  · exact fun B hB => target_deriv true x (Ioo_subset_Icc_self hB)
  · intro B hB
    have hh := (quadrant_slope_bounds hx (Ioo_subset_Icc_self hB)).1
    norm_num [sign]
    linarith

theorem target_negative_monotone {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    MonotoneOn (targetPart false x) (Icc 0 b2) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun B hB => (target_deriv false x hB).continuousAt.continuousWithinAt
  · exact fun B hB => target_deriv false x (Ioo_subset_Icc_self hB)
  · intro B hB
    have hh := (quadrant_slope_bounds hx (Ioo_subset_Icc_self hB)).2
    norm_num [sign]
    linarith

theorem target_upper (n j : Bool) {B x : ℝ} (hB : B∈arc n)
    (hx : x∈Icc 0 (Real.pi/2)) :
    targetPart j x B≤targetPart j x (targetEnd n j) := by
  have hi : B∈Icc (first n) (last n) := by simpa only [arc_eq] using hB
  cases j
  · exact target_negative_monotone hx (arc_subset hB) (arc_subset (last_mem n)) hi.2
  · exact target_positive_antitone hx (arc_subset (first_mem n)) (arc_subset hB) hi.1

theorem central_upper (m n i j : Bool) {b B x : ℝ}
    (hb : b∈arc m) (hB : B∈arc n) (hx : x∈Icc 0 (Real.pi/2)) :
    central i j (A b) b (A B) B x≤barrier m n i j x := by
  have hs := source_upper m i hb
  have ht := target_upper n j hB hx
  dsimp [sourcePart,targetPart] at hs ht
  dsimp [central,barrier,K,S,C,sourcePart]
  rw [(first_width hx).1]
  nlinarith

theorem coefficients_positive (n j : Bool) : 0<S n j ∧ 0<C n j := by
  have h0 := a0_precise
  have h1 := a1_precise
  have h2 := a2_precise
  have e1 := b1_eq
  have e2 := b2_eq
  cases n <;> cases j <;>
    simp only [S,C,targetEnd,first,last,sign,Bool.false_eq_true,↓reduceIte,
      A_zero,A_b1,A_b2] <;>
    constructor <;> linarith

theorem barrier_deriv (m n i j : Bool) (x : ℝ) :
    HasDerivAt (barrier m n i j)
      (S n j*Real.cos x+C n j*Real.sin x) x := by
  have h := (((Real.hasDerivAt_sin x).const_mul (S n j)).const_add (K m i)).fun_sub
    ((Real.hasDerivAt_cos x).const_mul (C n j))
  refine h.congr_deriv ?_
  ring

theorem barrier_monotone (m n i j : Bool) :
    MonotoneOn (barrier m n i j) (Icc 0 (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (barrier_deriv m n i j x).continuousAt.continuousWithinAt
  · exact fun x _ => barrier_deriv m n i j x
  · intro x hx
    have ht := FrameLowPair.quadrant (Ioo_subset_Icc_self hx)
    have hc := coefficients_positive n j
    exact add_nonneg (mul_nonneg hc.1.le ht.2.2.1) (mul_nonneg hc.2.le ht.1)

theorem cut_quadrant (m n i j : Bool) : cut m n i j∈Icc 0 (Real.pi/2) := by
  cases m <;> cases n <;> cases i <;> cases j <;> norm_num [cut]
  all_goals linarith [Arithmetic.pi_hand_enclosure.1]

theorem cut_negative (m n i j : Bool) (hhigh : m=false ∨ n=false) :
    barrier m n i j (cut m n i j)<0 := by
  have ht := Arithmetic.trig_taylor_bounds (cut_quadrant m n i j).1
  have hc := coefficients_positive n j
  have hs := mul_le_mul_of_nonneg_left ht.2.1 hc.1.le
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.1 hc.2.le
  have hp : K m i+S n j*Arithmetic.sin9 (cut m n i j)-
      C n j*Arithmetic.cos10 (cut m n i j)<0 := by
    have h0 := a0_precise
    have h1 := a1_precise
    have h2 := a2_precise
    have e1 := b1_eq
    have e2 := b2_eq
    cases m
    · cases n <;> cases i <;> cases j <;>
        simp only [cut,K,S,C,sourcePart,sourceEnd,targetEnd,first,last,sign,
          Bool.false_eq_true,↓reduceIte,A_zero,A_b1,A_b2] <;>
        norm_num [e1,e2,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] <;>
        linarith
    · rcases hhigh with h | rfl
      · exact absurd h (by decide)
      · cases i <;> cases j <;>
          simp only [cut,K,S,C,sourcePart,sourceEnd,targetEnd,first,last,sign,
            Bool.false_eq_true,↓reduceIte,A_zero,A_b1,A_b2] <;>
          norm_num [e1,e2,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] <;>
          linarith
  dsimp only [barrier]
  linarith

theorem central_cut (m n i j : Bool) (hhigh : m=false ∨ n=false)
    {b B x : ℝ} (hb : b∈arc m) (hB : B∈arc n) (hx : 0≤x)
    (hm : 0≤central i j (A b) b (A B) B x) : cut m n i j<x := by
  by_contra! hsmall
  have hxq : x∈Icc 0 (Real.pi/2) := ⟨hx,hsmall.trans (cut_quadrant m n i j).2⟩
  have hmax := central_upper m n i j hb hB hxq
  have hmono := barrier_monotone m n i j hxq (cut_quadrant m n i j) hsmall
  linarith [cut_negative m n i j hhigh]

end SquaresInCircles.Eight.FrameDiagonalCuts
end
end
end

section
/-!
## Actual owner reductions for the two remaining outer frame pairs

The original negative transverse axis is excluded by the actual center
radius.  The other extra axis is excluded on the full first quadrant
and on the only relevant continuation after the quarter turn.  The
nonpositive central-angle exclusion uses the original center gap and
the complete folded arcs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameDiagonalGeometry
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FramePairCalculus

def physicalRadius (middle : Bool) : ℝ := if middle then 67/50 else 653/500
def originalTransverse (middle : Bool) : ℝ := if middle then 64937/200000 else 5139/10000

theorem original_transverse_lower (m : Bool) (s : FramePair.State)
    (hs : s.branch=kind m) : originalTransverse m<s.b := by
  cases m with
  | false =>
      have hb := (FrameHighArc.state_high_chart s hs).2.1
      exact FrameMidArc.b2_bounds.1.trans_le hb
  | true =>
      have hb := (FrameMidArc.state_mid_chart s hs).2.1
      exact FrameLowArc.b1_bounds.1.trans_le hb

theorem original_projection_lt (n j : Bool) (t : FramePair.State)
    (ht : t.branch=kind n) (x : ℝ) :
    t.a*Real.sin x-sign j*t.b*Real.cos x<physicalRadius n := by
  cases n with
  | false =>
      have hc := FrameHighArc.state_high_chart t ht
      have hr := high_radius_sq hc.2
      rw [hc.1,show physicalRadius false=653/500 from rfl]
      cases j
      · have h := FrameCoreArc.projection_lt (b := t.b) (by norm_num : (0:ℝ)<653/500) hr x
        rw [show sign false=-1 from rfl]
        linarith
      · have hh : (FrameCircleArc.A t.b)^2+(-t.b)^2<(653/500:ℝ)^2 := by
          rw [neg_sq]
          exact hr
        have h := FrameCoreArc.projection_lt (b := -t.b) (by norm_num : (0:ℝ)<653/500) hh x
        rw [show sign true=1 from rfl]
        linarith
  | true =>
      have hc := FrameMidArc.state_mid_chart t ht
      rw [hc.1]
      exact FrameCoreArc.middle_projection_lt j hc.2 x

/-- At least one endpoint is high; the original weak transverse axis
cannot have a negative original source tangent. -/
theorem original_negative_secondary_false (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n)
    (hhigh : m=false ∨ n=false) (hi : s.positive=false) (x : ℝ) :
    ¬s.Feasible t 0 x := by
  intro hm
  have hp := original_projection_lt n t.positive t ht x
  have hb := original_transverse_lower m s hs
  have hw := FrameCoreArc.width_one_le x
  have hnum : physicalRadius n-originalTransverse m<1 := by
    rcases hhigh with rfl | rfl
    · cases n <;> norm_num [physicalRadius,originalTransverse]
    · cases m <;> norm_num [physicalRadius,originalTransverse]
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero,hi] at hm
  rw [show sign false=-1 from rfl] at hm
  linarith

theorem arc_coordinates (m : Bool) {b : ℝ} (hb : b∈arc m) :
    A b+b<(1299/500:ℝ) ∧ (649/1000:ℝ)<A b-b := by
  cases m
  · have hh := high_coordinates hb
    constructor <;> linarith
  · exact mid_coordinates hb

theorem negative_trig {x : ℝ} (hx : x∈Icc (-(81/500:ℝ)) 0) :
    Real.sin x≤0 ∧ (493/500:ℝ)<Real.cos x := by
  have he : -x∈Icc 0 (81/500:ℝ) := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi he.1
    (by linarith [he.2,Arithmetic.pi_hand_enclosure.1])
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ he.1 he.2 2
  simp only [Real.sin_neg,neg_sq] at hs hsq
  exact ⟨by linarith,by nlinarith⟩

theorem central_nonpositive_false (m n : Bool) {b B x : ℝ}
    (hb : b∈arc m) (hB : B∈arc n) (hx : x∈Icc (-(81/500:ℝ)) 0) :
    central true false (A b) b (A B) B x<0 := by
  have hs := arc_coordinates m hb
  have ht := arc_coordinates n hB
  have htr := negative_trig hx
  have hA := (A_bounds (arc_subset hB)).1
  have hB0 := (arc_subset hB).1
  have hsin := mul_nonpos_of_nonpos_of_nonneg htr.1
    (show 0≤A B+B+1 by linarith [a2_precise.1])
  have hcos := mul_nonneg
    (show 0≤Real.cos x-493/500 by linarith [htr.2])
    (show 0≤A B-B+1-1649/1000 by linarith [ht.2])
  have hw := negative_width
    (show x∈Icc (-(54/125:ℝ)) 0 from ⟨by linarith [hx.1],hx.2⟩)
  dsimp [central,sign]
  rw [hw.1]
  nlinarith

theorem actual_angle_lower (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n)
    (hhigh : m=false ∨ n=false) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    -(81/500:ℝ)<angle s.positive t.positive x := by
  have hh := angle_lower m n s t hs ht hgap
  rcases hhigh with rfl | rfl
  · cases n <;> simp only [cap,Bool.false_eq_true,↓reduceIte] at hh <;> linarith
  · cases m <;> simp only [cap,Bool.false_eq_true,↓reduceIte] at hh <;> linarith

theorem actual_central_positive (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n)
    (hhigh : m=false ∨ n=false) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x)
    (hm : s.Feasible t (centralAxis s.positive) x) :
    0<angle s.positive t.positive x := by
  by_contra! hx
  have hlo := actual_angle_lower m n s t hs ht hhigh hgap
  have hsg := nonpositive_signs m n s t hs ht hgap hx
  have hf := state_central_feasible m n s t hs ht hm
  have hbad := central_nonpositive_false m n
    (state_fold m s hs).1 (state_fold n t ht).1 ⟨hlo.le,hx⟩
  rw [hsg.1,hsg.2] at hf hbad
  simp only [Bool.not_false,Bool.not_true] at hf
  linarith

theorem extra_first_false (m n j : Bool) {b B x : ℝ}
    (hb : b∈arc m) (hB : B∈arc n) (hx : x∈Icc 0 (Real.pi/2)) :
    extra j (A b) b (A B) B x<0 := by
  have hs := arc_coordinates m hb
  have ht := arc_coordinates n hB
  have htr := FrameLowPair.quadrant hx
  have hw := FrameCoreArc.width_one_le x
  have hwf := (first_width hx).1
  have hC : 1≤Real.sin x+Real.cos x := by linarith
  have hA0 : 0≤A B := by linarith [(A_bounds (arc_subset hB)).1,a2_precise.1]
  have hB0 := (arc_subset hB).1
  have hCA := mul_le_mul_of_nonneg_right hC hA0
  have hDlo := mul_le_mul_of_nonneg_right
    (show -(1:ℝ)≤Real.sin x-Real.cos x by linarith) hB0
  have hDhi := mul_le_mul_of_nonneg_right
    (show Real.sin x-Real.cos x≤1 by linarith) hB0
  cases j <;> dsimp [extra,sign] <;> nlinarith

theorem late_sum_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100:ℝ)) :
    (17/20:ℝ)<Real.sin x+Real.cos x := by
  obtain ⟨e,he_def⟩ : ∃ e : ℝ, e=x-Real.pi/2 := ⟨_,rfl⟩
  have he : e∈Icc 0 (7/50:ℝ) := by
    rw [he_def]
    exact ⟨by linarith [hx.1],by linarith [hx.2,Arithmetic.pi_hand_enclosure.1]⟩
  have hs := Real.sin_le he.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := e)
  have hsq := pow_le_pow_left₀ he.1 he.2 2
  have hid : x=Real.pi/2+e := by rw [he_def]; ring
  rw [hid,Real.sin_add,Real.cos_add,Real.sin_pi_div_two,Real.cos_pi_div_two]
  linarith [he.2]

theorem extra_late_false (m n : Bool) {b B x : ℝ}
    (hb : b∈arc m) (hB : B∈arc n) (hx : x∈Icc (Real.pi/2) (171/100:ℝ)) :
    extra true (A b) b (A B) B x<0 := by
  have hs := arc_coordinates m hb
  have hA := (A_bounds (arc_subset hB)).1
  have hB0 := (arc_subset hB).1
  have ht := second_signs
    (show x∈Icc (Real.pi/2) Real.pi from
      ⟨hx.1,by linarith [hx.2,Arithmetic.pi_hand_enclosure.1]⟩)
  have hC := late_sum_lower hx
  have hCA := mul_nonneg (show 0≤Real.sin x+Real.cos x-17/20 by linarith)
    (show 0≤A B-1623/1000 by linarith [a2_precise.1])
  have hDB := mul_nonneg (show 0≤Real.sin x-Real.cos x by linarith) hB0
  have hw := FrameCoreArc.width_one_le x
  dsimp [extra,sign]
  nlinarith

theorem source_first_central (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n)
    (hhigh : m=false ∨ n=false) (j : Fin 4) (hj : j=0 ∨ j=3)
    {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x)
    (hx : angle s.positive t.positive x≤Real.pi/2) (hm : s.Feasible t j x) :
    0<angle s.positive t.positive x ∧ s.Feasible t (centralAxis s.positive) x := by
  cases hi : s.positive with
  | false =>
      have hj3 : j=3 := by
        rcases hj with rfl | hj3
        · exact False.elim ((original_negative_secondary_false m n s t hs ht hhigh hi x) hm)
        · exact hj3
      have hc : s.Feasible t (centralAxis s.positive) x := by
        rw [hi]
        rw [hj3] at hm
        exact hm
      have hp := actual_central_positive m n s t hs ht hhigh hgap hc
      rw [hi] at hp hc
      exact ⟨hp,hc⟩
  | true =>
      have hp : 0<angle s.positive t.positive x := by
        by_contra! hnp
        have hh := (nonpositive_signs m n s t hs ht hgap hnp).1
        rw [hi] at hh
        exact absurd hh (by decide)
      have hj0 : j=0 := by
        rcases hj with hj0 | rfl
        · exact hj0
        · exfalso
          have he := state_extra m n s t hs ht hi x
          have hn := extra_first_false m n (!t.positive)
            (state_fold m s hs).1 (state_fold n t ht).1 ⟨hp.le,hx⟩
          have hm' : 0≤forwardMargin 3 s.a s.b t.a t.b
              (sign s.positive) (sign t.positive) x := hm
          rw [he] at hn
          linarith
      have hc : s.Feasible t (centralAxis s.positive) x := by
        rw [hi]
        rw [hj0] at hm
        exact hm
      rw [hi] at hp hc
      exact ⟨hp,hc⟩

end SquaresInCircles.Eight.FrameDiagonalGeometry
end
end
end

section
/-!
## The supports of the folded pairs on the diagonal circle

For `lam ≥ 0`, the cost of a folded pair less `lam` times the central margin is a base plus a
linear function `source m i lam` of the source state and a linear function `target n j lam x` of
the target state (`exact_identity`); with a nonnegative margin, lower bounds of the two parts give
a lower bound of the cost (`support`). The supports of the whole circle bound the two parts for
coefficients of any signs (`source_circle_lower`, `target_circle_lower`, `both_circle`), and the
derivatives along the arcs locate their minima (`source_deriv`, `target_deriv`); the bounds at the
two ends stay separate inequalities. The base has closed forms before and after the quarter turn
(`base_first`, `base_second`, `fixed_target_first`, `fixed_target_second`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameDiagonalSupport
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FramePairCalculus

def sourceU (m i : Bool) (lam : ℝ) : ℝ := sign i*primary m-lam
def sourceV (m i : Bool) (lam : ℝ) : ℝ := sign i*(transverse m-lam)
def targetU (n j : Bool) (lam x : ℝ) : ℝ :=
  -sign j*primary n-lam*(Real.sin x-Real.cos x)
def targetV (n j : Bool) (lam x : ℝ) : ℝ :=
  sign j*(lam*(Real.sin x+Real.cos x)-transverse n)
def source (m i : Bool) (lam b : ℝ) : ℝ := linear (sourceU m i lam) (sourceV m i lam) b
def target (n j : Bool) (lam x B : ℝ) : ℝ := linear (targetU n j lam x) (targetV n j lam x) B
def base (m n i j : Bool) (lam x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+2*lam*pairWidth x+sign i*constant m-sign j*constant n
def sourceCircle (m i : Bool) (lam : ℝ) : ℝ :=
  -sourceU m i lam-R*Real.sqrt ((sourceU m i lam)^2+(sourceV m i lam)^2)
def targetCircle (n j : Bool) (lam x : ℝ) : ℝ :=
  -targetU n j lam x-R*Real.sqrt ((targetU n j lam x)^2+(targetV n j lam x)^2)

theorem exact_identity (m n i j : Bool) (lam b B x : ℝ) :
    cost m n i j b B x-lam*central i j (A b) b (A B) B x=
      base m n i j lam x+source m i lam b+target n j lam x B := by
  rw [cost,marker_affine,marker_affine]
  dsimp [central,base,source,target,linear,sourceU,sourceV,targetU,targetV]
  ring

theorem support {m n i j : Bool} {lam b B x S T : ℝ}
    (hlam : 0≤lam) (hm : 0≤central i j (A b) b (A B) B x)
    (hs : S≤ source m i lam b) (ht : T≤target n j lam x B) :
    base m n i j lam x+S+T≤cost m n i j b B x := by
  have he := exact_identity m n i j lam b B x
  have hp := mul_nonneg hlam hm
  linarith

theorem source_circle_lower (m i : Bool) (lam : ℝ) {b : ℝ} (hb : b∈arc m) :
    sourceCircle m i lam≤ source m i lam b :=
  circle_linear_lower (A_circle (arc_subset hb)) (sourceU m i lam) (sourceV m i lam)

theorem target_circle_lower (n j : Bool) (lam x : ℝ) {B : ℝ} (hB : B∈arc n) :
    targetCircle n j lam x≤target n j lam x B :=
  circle_linear_lower (A_circle (arc_subset hB)) (targetU n j lam x) (targetV n j lam x)

theorem both_circle {m n i j : Bool} {lam b B x : ℝ}
    (hb : b∈arc m) (hB : B∈arc n) (hlam : 0≤lam)
    (hm : 0≤central i j (A b) b (A B) B x) :
    base m n i j lam x+sourceCircle m i lam+targetCircle n j lam x≤
      cost m n i j b B x :=
  FrameDiagonalSupport.support hlam hm (source_circle_lower m i lam hb) (target_circle_lower n j lam x hB)

theorem source_deriv (m i : Bool) (lam : ℝ) {b : ℝ} (hb : b∈arc m) :
    HasDerivAt (source m i lam)
      (-sourceU m i lam*slope b+sourceV m i lam) b := by
  have h := linear_hasDerivAt (arc_subset hb) (sourceU m i lam) (sourceV m i lam)
  have he : -sourceU m i lam*FrameDiagonalArc.slope b+sourceV m i lam=
      sourceU m i lam*Ad b+sourceV m i lam := by
    simp only [Ad,FrameDiagonalArc.slope]; ring
  rw [he]
  exact h

theorem target_deriv (n j : Bool) (lam x : ℝ) {B : ℝ} (hB : B∈arc n) :
    HasDerivAt (target n j lam x)
      (-targetU n j lam x*slope B+targetV n j lam x) B := by
  have h := linear_hasDerivAt (arc_subset hB) (targetU n j lam x) (targetV n j lam x)
  have he : -targetU n j lam x*FrameDiagonalArc.slope B+targetV n j lam x=
      targetU n j lam x*Ad B+targetV n j lam x := by
    simp only [Ad,FrameDiagonalArc.slope]; ring
  rw [he]
  exact h

theorem base_first (m n i j : Bool) (lam : ℝ) {x : ℝ}
    (hx : x∈Icc 0 (Real.pi/2)) :
    base m n i j lam x=
      x+9/100+lam+(lam-9/100)*(Real.sin x+Real.cos x)+
        sign i*constant m-sign j*constant n := by
  rw [base,(first_width hx).1,(first_width hx).2]
  ring

theorem base_second (m n i j : Bool) (lam : ℝ) {x : ℝ}
    (hx : x∈Icc (Real.pi/2) Real.pi) :
    base m n i j lam x=
      x+9/100+lam+(lam-9/100)*(Real.sin x-Real.cos x)+
        sign i*constant m-sign j*constant n := by
  rw [base,(second_width hx).1,(second_width hx).2]
  ring

theorem fixed_target_first (m n i j : Bool) (lam B S : ℝ) {x : ℝ}
    (hx : x∈Icc 0 (Real.pi/2)) :
    base m n i j lam x+S+target n j lam x B=
      x+9/100+lam+sign i*constant m-sign j*marker n B+S+
        (lam*(1+A B+sign j*B)-9/100)*Real.cos x+
        (lam*(1-A B+sign j*B)-9/100)*Real.sin x := by
  rw [base_first m n i j lam hx,marker_affine]
  dsimp [target,targetU,targetV,linear]
  ring

theorem fixed_target_second (m n i j : Bool) (lam B S : ℝ) {x : ℝ}
    (hx : x∈Icc (Real.pi/2) Real.pi) :
    base m n i j lam x+S+target n j lam x B=
      x+9/100+lam+sign i*constant m-sign j*marker n B+S+
        (lam*(A B+sign j*B-1)+9/100)*Real.cos x+
        (lam*(1-A B+sign j*B)-9/100)*Real.sin x := by
  rw [base_second m n i j lam hx,marker_affine]
  dsimp [target,targetU,targetV,linear]
  ring

end SquaresInCircles.Eight.FrameDiagonalSupport
end
end
end

section
/-!
## Minima at the ends of the folded arcs

The supports `source m i lam` and `target n j lam x` are linear functions of the state along the
closed arcs. A support is least at the first end of the arc when its derivative along the arc is
nonnegative, and at the last end when it is nonpositive (`source_first_of_derivative`,
`source_last_of_derivative`, `target_first_of_derivative`, `target_last_of_derivative`), in
particular for coefficients of suitable signs (`source_first_of_coefficients`,
`target_first_of_coefficients`, `target_last_of_coefficients`). When the coefficient of the
primary coordinate is nonnegative, the support is concave along the arc and is at least the
smaller of its values at the two ends (`source_endpoints`, `target_endpoints`,
`target_endpoints_of_one_coefficient`). The state stays on its arc, the ends included.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameDiagonalSelection
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalSupport
open FrameDiagonalCuts

theorem source_first_of_derivative {m i : Bool} {lam b : ℝ}
    (hb : b∈arc m)
    (hd : ∀ z∈arc m, 0≤-sourceU m i lam*slope z+sourceV m i lam) :
    source m i lam (first m)≤ source m i lam b := by
  have hmono : MonotoneOn (source m i lam) (Icc (first m) (last m)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro z hz
      exact (FrameDiagonalSupport.source_deriv m i lam
        (by simpa only [arc_eq] using hz)).continuousAt.continuousWithinAt
    · intro z hz
      exact FrameDiagonalSupport.source_deriv m i lam
        (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
    · intro z hz
      exact hd z (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
  have hb' : b∈Icc (first m) (last m) := by simpa only [arc_eq] using hb
  exact hmono ⟨le_rfl,hb'.1.trans hb'.2⟩ hb' hb'.1

theorem source_last_of_derivative {m i : Bool} {lam b : ℝ}
    (hb : b∈arc m)
    (hd : ∀ z∈arc m, -sourceU m i lam*slope z+sourceV m i lam≤0) :
    source m i lam (last m)≤ source m i lam b := by
  have hanti : AntitoneOn (source m i lam) (Icc (first m) (last m)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro z hz
      exact (FrameDiagonalSupport.source_deriv m i lam
        (by simpa only [arc_eq] using hz)).continuousAt.continuousWithinAt
    · intro z hz
      exact FrameDiagonalSupport.source_deriv m i lam
        (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
    · intro z hz
      exact hd z (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
  have hb' : b∈Icc (first m) (last m) := by simpa only [arc_eq] using hb
  exact hanti hb' ⟨hb'.1.trans hb'.2,le_rfl⟩ hb'.2

theorem target_first_of_derivative {n j : Bool} {lam x B : ℝ}
    (hB : B∈arc n)
    (hd : ∀ z∈arc n, 0≤-targetU n j lam x*slope z+targetV n j lam x) :
    target n j lam x (first n)≤target n j lam x B := by
  have hmono : MonotoneOn (target n j lam x) (Icc (first n) (last n)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro z hz
      exact (FrameDiagonalSupport.target_deriv n j lam x
        (by simpa only [arc_eq] using hz)).continuousAt.continuousWithinAt
    · intro z hz
      exact FrameDiagonalSupport.target_deriv n j lam x
        (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
    · intro z hz
      exact hd z (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
  have hB' : B∈Icc (first n) (last n) := by simpa only [arc_eq] using hB
  exact hmono ⟨le_rfl,hB'.1.trans hB'.2⟩ hB' hB'.1

theorem target_last_of_derivative {n j : Bool} {lam x B : ℝ}
    (hB : B∈arc n)
    (hd : ∀ z∈arc n, -targetU n j lam x*slope z+targetV n j lam x≤0) :
    target n j lam x (last n)≤target n j lam x B := by
  have hanti : AntitoneOn (target n j lam x) (Icc (first n) (last n)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro z hz
      exact (FrameDiagonalSupport.target_deriv n j lam x
        (by simpa only [arc_eq] using hz)).continuousAt.continuousWithinAt
    · intro z hz
      exact FrameDiagonalSupport.target_deriv n j lam x
        (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
    · intro z hz
      exact hd z (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
  have hB' : B∈Icc (first n) (last n) := by simpa only [arc_eq] using hB
  exact hanti hB' ⟨hB'.1.trans hB'.2,le_rfl⟩ hB'.2

theorem source_endpoints {m i : Bool} {lam b : ℝ} (hb : b∈arc m)
    (hU : 0≤ sourceU m i lam) :
    min (source m i lam (first m)) (source m i lam (last m))≤ source m i lam b := by
  apply linear_endpoint_lower hU
    (arc_subset (first_mem m)).1 (arc_subset (last_mem m)).2
  simpa only [arc_eq] using hb

theorem target_endpoints {n j : Bool} {lam x B : ℝ} (hB : B∈arc n)
    (hU : 0≤targetU n j lam x) :
    min (target n j lam x (first n)) (target n j lam x (last n))≤
      target n j lam x B := by
  apply linear_endpoint_lower hU
    (arc_subset (first_mem n)).1 (arc_subset (last_mem n)).2
  simpa only [arc_eq] using hB

theorem source_first_of_coefficients {m i : Bool} {lam b : ℝ}
    (hb : b∈arc m) (hU : sourceU m i lam≤0) (hV : 0≤ sourceV m i lam) :
    source m i lam (first m)≤ source m i lam b := by
  have hb' : b∈Icc (first m) (last m) := by simpa only [arc_eq] using hb
  exact linear_monotone hU hV (arc_subset (first_mem m)) (arc_subset hb) hb'.1

theorem target_first_of_coefficients {n j : Bool} {lam x B : ℝ}
    (hB : B∈arc n) (hU : targetU n j lam x≤0) (hV : 0≤targetV n j lam x) :
    target n j lam x (first n)≤target n j lam x B := by
  have hB' : B∈Icc (first n) (last n) := by simpa only [arc_eq] using hB
  exact linear_monotone hU hV (arc_subset (first_mem n)) (arc_subset hB) hB'.1

theorem target_last_of_coefficients {n j : Bool} {lam x B : ℝ}
    (hB : B∈arc n) (hU : 0≤targetU n j lam x) (hV : targetV n j lam x≤0) :
    target n j lam x (last n)≤target n j lam x B := by
  apply target_last_of_derivative hB
  intro z hz
  have hp := mul_nonneg hU (slope_bounds (arc_subset hz)).1
  linarith

theorem target_endpoints_of_one_coefficient {n j : Bool} {lam x B : ℝ}
    (hB : B∈arc n) (hUV : 0≤targetU n j lam x ∨ 0≤targetV n j lam x) :
    min (target n j lam x (first n)) (target n j lam x (last n))≤
      target n j lam x B := by
  by_cases hU : 0≤targetU n j lam x
  · exact target_endpoints hB hU
  · have hV := hUV.resolve_left hU
    exact (min_le_left _ _).trans
      (target_first_of_coefficients hB (lt_of_not_ge hU).le hV)

end SquaresInCircles.Eight.FrameDiagonalSelection
end
end
end

section
/-!
## Trigonometric bounds for the folded arcs

The harmonic `p sin x + q cos x` with `p, q ≥ 0` is concave on `[0, π/2]` (`harmonic_concave`), so
a lower bound at the two ends of an interval holds on the whole interval (`harmonic_lower`), and
the Taylor polynomials `sin7` and `cos10` give its values at the ends
(`harmonic_taylor_lower`). The difference `sin x - cos x` increases on `[0, π/2]`
(`difference_monotone`). The bounds of `sin x + cos x` and of `sin x - cos x` on the intervals of
the angle used for the folded pairs follow (`sum_early`, `sum_middle`, `sum_high`,
`sum_target_middle`, `sum_negative`, `weighted_negative`, and `difference_061_negative` to
`difference_100_positive`); only the two ends of each interval are evaluated, by Taylor
inequalities.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameDiagonalTrigonometry
open FramePairCalculus

def harmonic (p q x : ℝ) : ℝ := p*Real.sin x+q*Real.cos x

theorem harmonic_deriv (p q x : ℝ) :
    HasDerivAt (harmonic p q) (p*Real.cos x-q*Real.sin x) x := by
  have h := ((Real.hasDerivAt_sin x).const_mul p).fun_add
    ((Real.hasDerivAt_cos x).const_mul q)
  rw [show p*Real.cos x-q*Real.sin x=p*Real.cos x+q*(-Real.sin x) by ring]
  exact h

theorem harmonic_second (p q x : ℝ) :
    HasDerivAt (fun z => p*Real.cos z-q*Real.sin z) (-harmonic p q x) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul p).fun_sub
    ((Real.hasDerivAt_sin x).const_mul q)
  exact h.congr_deriv (by simp only [harmonic]; ring)

theorem harmonic_concave {p q l h : ℝ} (hp : 0≤p) (hq : 0≤q)
    (hl : 0≤l) (hh : h≤Real.pi/2) :
    ConcaveOn ℝ (Icc l h) (harmonic p q) := by
  apply concave_of_deriv2 (fun x _ => harmonic_deriv p q x)
    (fun x _ => harmonic_second p q x)
  intro x hx
  have ht := FrameLowPair.quadrant ⟨hl.trans hx.1,hx.2.trans hh⟩
  have hs := mul_nonneg hp ht.1
  have hc := mul_nonneg hq ht.2.2.1
  dsimp [harmonic]
  linarith

theorem harmonic_lower {p q l h x c : ℝ} (hp : 0≤p) (hq : 0≤q)
    (hl : 0≤l) (hh : h≤Real.pi/2) (hx : x∈Icc l h)
    (hleft : c<harmonic p q l) (hright : c<harmonic p q h) :
    c<harmonic p q x :=
  concave_gt_of_endpoints (harmonic_concave hp hq hl hh) hx hleft hright

theorem harmonic_taylor_lower {p q x c : ℝ} (hp : 0≤p) (hq : 0≤q)
    (hx : 0≤x) (hpoly : c<p*Arithmetic.sin7 x+q*Arithmetic.cos10 x) :
    c<harmonic p q x := by
  have ht := Arithmetic.trig_taylor_bounds hx
  have hs := mul_le_mul_of_nonneg_left ht.1 hp
  have hc := mul_le_mul_of_nonneg_left ht.2.2.1 hq
  dsimp [harmonic]
  linarith

theorem sine_monotone : MonotoneOn Real.sin (Icc 0 (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (Real.hasDerivAt_sin x).continuousAt.continuousWithinAt
  · exact fun x _ => Real.hasDerivAt_sin x
  · exact fun x hx => (FrameLowPair.quadrant (Ioo_subset_Icc_self hx)).2.2.1

theorem cosine_antitone : AntitoneOn Real.cos (Icc 0 (Real.pi/2)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (Real.hasDerivAt_cos x).continuousAt.continuousWithinAt
  · exact fun x _ => Real.hasDerivAt_cos x
  · exact fun x hx => neg_nonpos.mpr
      (FrameLowPair.quadrant (Ioo_subset_Icc_self hx)).1

theorem difference_deriv (x : ℝ) :
    HasDerivAt (fun z => Real.sin z-Real.cos z) (Real.cos x+Real.sin x) x := by
  exact ((Real.hasDerivAt_sin x).fun_sub (Real.hasDerivAt_cos x)).congr_deriv (by ring)

theorem difference_monotone :
    MonotoneOn (fun x => Real.sin x-Real.cos x) (Icc 0 (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (difference_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => difference_deriv x
  · intro x hx
    have ht := FrameLowPair.quadrant (Ioo_subset_Icc_self hx)
    exact add_nonneg ht.2.2.1 ht.1

theorem rational_quadrant {x : ℝ} (hx : x∈Icc 0 (71/50:ℝ)) :
    x∈Icc 0 (Real.pi/2) :=
  ⟨hx.1,by linarith [hx.2,Arithmetic.pi_hand_enclosure.1]⟩

theorem sum_early {x : ℝ} (hx : x∈Icc (7/20:ℝ) (6/5)) :
    (32/25:ℝ)<Real.sin x+Real.cos x := by
  suffices (32/25:ℝ)<harmonic 1 1 x by simpa [harmonic] using this
  apply harmonic_lower (p := 1) (q := 1) (l := 7/20) (h := 6/5)
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Arithmetic.pi_hand_enclosure.1]) hx
  all_goals apply harmonic_taylor_lower (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem sum_middle {x : ℝ} (hx : x∈Icc (3/5:ℝ) (19/20)) :
    (69/50:ℝ)<Real.sin x+Real.cos x := by
  suffices (69/50:ℝ)<harmonic 1 1 x by simpa [harmonic] using this
  apply harmonic_lower (p := 1) (q := 1) (l := 3/5) (h := 19/20)
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Arithmetic.pi_hand_enclosure.1]) hx
  all_goals apply harmonic_taylor_lower (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem sum_high {x : ℝ} (hx : x∈Icc (1:ℝ) (13/10)) :
    (123/100:ℝ)<Real.sin x+Real.cos x := by
  suffices (123/100:ℝ)<harmonic 1 1 x by simpa [harmonic] using this
  apply harmonic_lower (p := 1) (q := 1) (l := 1) (h := 13/10)
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Arithmetic.pi_hand_enclosure.1]) hx
  all_goals apply harmonic_taylor_lower (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem sum_target_middle {x : ℝ} (hx : x∈Icc (11/10:ℝ) (71/50)) :
    (113/100:ℝ)<Real.sin x+Real.cos x := by
  suffices (113/100:ℝ)<harmonic 1 1 x by simpa [harmonic] using this
  apply harmonic_lower (p := 1) (q := 1) (l := 11/10) (h := 71/50)
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Arithmetic.pi_hand_enclosure.1]) hx
  all_goals apply harmonic_taylor_lower (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem sum_negative {x : ℝ} (hx : x∈Icc (9/10:ℝ) (6/5)) :
    (129/100:ℝ)<Real.sin x+Real.cos x := by
  suffices (129/100:ℝ)<harmonic 1 1 x by simpa [harmonic] using this
  apply harmonic_lower (p := 1) (q := 1) (l := 9/10) (h := 6/5)
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Arithmetic.pi_hand_enclosure.1]) hx
  all_goals apply harmonic_taylor_lower (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem weighted_negative {x : ℝ} (hx : x∈Icc (9/10:ℝ) (6/5)) :
    (23/20:ℝ)<(747/1000)*Real.sin x+(1253/1000)*Real.cos x := by
  change (23/20:ℝ)<harmonic (747/1000) (1253/1000) x
  apply harmonic_lower (p := 747/1000) (q := 1253/1000) (l := 9/10) (h := 6/5)
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Arithmetic.pi_hand_enclosure.1]) hx
  all_goals apply harmonic_taylor_lower (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem difference_061_negative {x : ℝ} (hx : x∈Icc 0 (61/100:ℝ)) :
    Real.sin x-Real.cos x<0 := by
  have hm := difference_monotone
    (rational_quadrant ⟨hx.1,by linarith [hx.2]⟩)
    (rational_quadrant (show (61/100:ℝ)∈Icc 0 (71/50) by norm_num)) hx.2
  have ht := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤61/100 by norm_num)
  simp only at hm
  norm_num [Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at ht
  linarith [ht.2.1,ht.2.2.1]

theorem difference_080_upper {x : ℝ} (hx : x∈Icc 0 (4/5:ℝ)) :
    Real.sin x-Real.cos x<(21/1000:ℝ) := by
  have hm := difference_monotone
    (rational_quadrant ⟨hx.1,by linarith [hx.2]⟩)
    (rational_quadrant (show (4/5:ℝ)∈Icc 0 (71/50) by norm_num)) hx.2
  have ht := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤4/5 by norm_num)
  simp only at hm
  norm_num [Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at ht
  linarith [ht.2.1,ht.2.2.1]

theorem difference_095_upper {x : ℝ} (hx : x∈Icc 0 (19/20:ℝ)) :
    Real.sin x-Real.cos x<(29/125:ℝ) := by
  have hm := difference_monotone
    (rational_quadrant ⟨hx.1,by linarith [hx.2]⟩)
    (rational_quadrant (show (19/20:ℝ)∈Icc 0 (71/50) by norm_num)) hx.2
  have ht := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤19/20 by norm_num)
  simp only at hm
  norm_num [Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at ht
  linarith [ht.2.1,ht.2.2.1]

theorem difference_110_lower {x : ℝ} (hx : x∈Icc (11/10:ℝ) (71/50)) :
    (43/100:ℝ)<Real.sin x-Real.cos x := by
  have hm := difference_monotone
    (rational_quadrant (show (11/10:ℝ)∈Icc 0 (71/50) by norm_num))
    (rational_quadrant ⟨by linarith [hx.1],hx.2⟩) hx.1
  have ht := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤11/10 by norm_num)
  norm_num [Arithmetic.sin7,Arithmetic.cos8] at ht
  linarith [ht.1,ht.2.2.2]

theorem difference_100_positive {x : ℝ} (hx : x∈Icc (1:ℝ) (13/10)) :
    0<Real.sin x-Real.cos x := by
  have hm := difference_monotone
    (rational_quadrant (show (1:ℝ)∈Icc 0 (71/50) by norm_num))
    (rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩) hx.1
  have ht := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤1 by norm_num)
  norm_num [Arithmetic.sin7,Arithmetic.cos8] at ht
  linarith [ht.1,ht.2.2.2]

end SquaresInCircles.Eight.FrameDiagonalTrigonometry
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameDiagonalTails
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport

def mhTail (middleSource i j : Bool) : ℝ :=
  if i then (if j then (if middleSource then 93/100 else 71/50) else 61/100)
  else (if j then 171/100 else (if middleSource then 71/50 else 93/100))
def hhTail (i j : Bool) : ℝ :=
  if i then (if j then Real.pi/2 else 21/20) else (if j then 15543/10000 else 127/100)

theorem quarter_charge_upper (x : ℝ) : periodicFrameCost x≤|x-Real.pi/2|/2 := by
  have hp := periodicFrameCost_pi_half (x-Real.pi/2)
  have he : x-Real.pi/2+Real.pi/2=x := by ring
  rw [he] at hp
  rw [hp]
  have hs := Real.abs_sin_le_abs (x := x-Real.pi/2)
  have hc := Real.abs_cos_le_one (x-Real.pi/2)
  dsimp [periodicFrameCost]
  linarith

theorem angular_after {x : ℝ} (hx : Real.pi/2≤x) :
    (91/100)*x+(9/100)*(Real.pi/2)≤x-(9/50)*periodicFrameCost x := by
  have hh := quarter_charge_upper x
  rw [abs_of_nonneg (sub_nonneg.mpr hx)] at hh
  linarith

theorem angular_from_before {x l : ℝ} (hl : l≤Real.pi/2) (hx : l≤x) :
    (109/100)*l-(9/100)*(Real.pi/2)≤x-(9/50)*periodicFrameCost x := by
  by_cases hxq : x≤Real.pi/2
  · have hh := quarter_charge_upper x
    rw [abs_of_nonpos (sub_nonpos.mpr hxq)] at hh
    linarith
  · have hh := angular_after (lt_of_not_ge hxq).le
    linarith

theorem high_signed_bounds (i : Bool) {b : ℝ} (hb : b∈Icc 0 b1) :
    -(160727/500000:ℝ)<sign i*H b ∧ sign i*H b<160727/500000 := by
  have hh := H_bounds hb
  cases i <;> dsimp [sign] <;> constructor <;> linarith

theorem middle_signed_bounds (i : Bool) {b : ℝ} (hb : b∈Icc b1 b2) :
    -(601/1250:ℝ)<sign i*M b ∧ sign i*M b<601/1250 := by
  have hh := M_bounds hb
  cases i <;> dsimp [sign] <;> constructor <;> linarith

theorem middle_high_late (i j : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (hx : (171/100:ℝ)≤x) :
    (4463/5000:ℝ)<cost true false i j b B x := by
  have hs := middle_signed_bounds i hb
  have ht := high_signed_bounds j hB
  have ha := angular_after (show Real.pi/2≤x by linarith [Arithmetic.pi_hand_enclosure.2])
  dsimp [cost,marker]
  linarith [Arithmetic.pi_hand_enclosure.1]

theorem high_middle_late (i j : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2) (hx : (171/100:ℝ)≤x) :
    (4463/5000:ℝ)<cost false true i j b B x := by
  have hs := high_signed_bounds i hb
  have ht := middle_signed_bounds j hB
  have ha := angular_after (show Real.pi/2≤x by linarith [Arithmetic.pi_hand_enclosure.2])
  dsimp [cost,marker]
  linarith [Arithmetic.pi_hand_enclosure.1]

theorem middle_high (i j : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (hx : mhTail true i j≤x) :
    (4463/5000:ℝ)<cost true false i j b B x := by
  have hs := M_bounds hb
  have ht := H_bounds hB
  have hch := CorePairGeometry.charge_upper x
  cases i <;> cases j
  · dsimp [mhTail,cost,marker,sign] at *
    linarith
  · exact middle_high_late false true hb hB hx
  · dsimp [mhTail,cost,marker,sign] at *
    linarith
  · dsimp [mhTail,cost,marker,sign] at *
    linarith

theorem high_middle (i j : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2) (hx : mhTail false i j≤x) :
    (4463/5000:ℝ)<cost false true i j b B x := by
  have hs := H_bounds hb
  have ht := M_bounds hB
  have hch := CorePairGeometry.charge_upper x
  cases i <;> cases j
  · dsimp [mhTail,cost,marker,sign] at *
    linarith
  · exact high_middle_late false true hb hB hx
  · dsimp [mhTail,cost,marker,sign] at *
    linarith
  · dsimp [mhTail,cost,marker,sign] at *
    linarith

theorem high_high_late (i j : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1) (hx : Real.pi/2≤x) :
    (9099/10000:ℝ)<cost false false i j b B x := by
  have hs := high_signed_bounds i hb
  have ht := high_signed_bounds j hB
  have ha := angular_after hx
  dsimp [cost,marker]
  linarith [Arithmetic.pi_hand_enclosure.1]

theorem high_high (i j : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1) (hx : hhTail i j≤x) :
    (9099/10000:ℝ)<cost false false i j b B x := by
  have hs := H_bounds hb
  have ht := H_bounds hB
  have hch := CorePairGeometry.charge_upper x
  cases i <;> cases j
  · dsimp [hhTail,cost,marker,sign] at *
    linarith
  · have hl : (15543/10000:ℝ)≤Real.pi/2 := by linarith [Arithmetic.pi_hand_enclosure.1]
    have ha := angular_from_before hl hx
    dsimp [cost,marker,sign]
    linarith [Arithmetic.pi_hand_enclosure.2]
  · dsimp [hhTail,cost,marker,sign] at *
    linarith
  · exact high_high_late true true hb hB hx

end SquaresInCircles.Eight.FrameDiagonalTails
end
end
end

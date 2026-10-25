module

public import SquaresInCircles.Eight.Frames.Pair.Domain

/-!
# Eight squares: exact support and curvature on the canonical outer arc

The closed arc is parameterized by its actual
secondary coordinate.  Its positive radical, first and second derivatives,
endpoint concavity and full-circle support are proved on the whole arc.
These are shared geometric ingredients of the nine remaining frame-pair
inequalities; none of them assumes frame concentration.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCircleArc
open FramePair

def R : ℝ := Real.sqrt Q0
def A (b : ℝ) : ℝ := Real.sqrt (Q0-(b+1/2)^2)-1/2
def Ad (b : ℝ) : ℝ := -(b+1/2)/(A b+1/2)
def Add (b : ℝ) : ℝ := -Q0/(A b+1/2)^3
def linear (p q b : ℝ) : ℝ := p*A b+q*b

theorem R_pos : 0<R := Real.sqrt_pos.mpr (by norm_num [Q0])
theorem R_sq : R^2=Q0 := Real.sq_sqrt (by norm_num [Q0])

theorem c0_bounds : (899/1000:ℝ)<c0 ∧ c0<9/10 := by
  have hs := Real.sq_sqrt (show 0≤Q0/2 by norm_num [Q0])
  have hn := Real.sqrt_nonneg (Q0/2)
  dsimp [c0,Q0] at *
  constructor <;> nlinarith

theorem c0_circle : 2*(c0+1/2)^2=Q0 := by
  have hs := Real.sq_sqrt (show 0≤Q0/2 by norm_num [Q0])
  dsimp [c0]
  nlinarith

theorem radicand_pos {b : ℝ} (hb : b∈Icc 0 c0) :
    0<Q0-(b+1/2)^2 := by
  have hs := pow_le_pow_left₀ (show 0≤b+1/2 by linarith [hb.1])
    (show b+1/2≤c0+1/2 by linarith [hb.2]) 2
  have hc := c0_circle
  norm_num [Q0] at hc ⊢
  nlinarith

theorem A_shift_pos {b : ℝ} (hb : b∈Icc 0 c0) : 0<A b+1/2 := by
  simpa [A] using Real.sqrt_pos.mpr (radicand_pos hb)

theorem A_circle {b : ℝ} (hb : b∈Icc 0 c0) :
    (A b+1/2)^2+(b+1/2)^2=Q0 := by
  have hh := Real.sq_sqrt (radicand_pos hb).le
  dsimp [A]
  nlinarith

theorem A_hasDerivAt {b : ℝ} (hb : b∈Icc 0 c0) : HasDerivAt A (Ad b) b := by
  have hh := ((hasDerivAt_const b Q0).sub
    (((hasDerivAt_id b).add_const (1/2)).pow 2)).sqrt (radicand_pos hb).ne'
  convert hh.sub_const (1/2) using 1
  · rfl
  · dsimp [Ad,A]
    ring

theorem Ad_hasDerivAt {b : ℝ} (hb : b∈Icc 0 c0) : HasDerivAt Ad (Add b) b := by
  have hd := A_hasDerivAt hb
  have hn := (A_shift_pos hb).ne'
  have hc := A_circle hb
  have hh := ((hasDerivAt_id' b).add_const (1/2)).fun_neg.fun_div (hd.add_const (1/2)) hn
  convert hh using 1
  · rfl
  · dsimp [Ad,Add]
    rw [← hc]
    field_simp
    ring

theorem Ad_nonpos {b : ℝ} (hb : b∈Icc 0 c0) : Ad b≤0 := by
  dsimp [Ad]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith [hb.1]) (A_shift_pos hb).le

theorem Add_negative {b : ℝ} (hb : b∈Icc 0 c0) : Add b<0 := by
  dsimp [Add]
  exact div_neg_of_neg_of_pos (by norm_num [Q0]) (pow_pos (A_shift_pos hb) 3)

theorem A_antitone : AntitoneOn A (Icc 0 c0) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun b hb => (A_hasDerivAt hb).continuousAt.continuousWithinAt
  · exact fun b hb => A_hasDerivAt (Ioo_subset_Icc_self hb)
  · exact fun b hb => Ad_nonpos (Ioo_subset_Icc_self hb)

@[simp] theorem A_zero : A 0=a0 := by simp [A,a0]; congr 1 <;> norm_num

@[simp] theorem A_c0 : A c0=c0 := by
  have hc := c0_circle
  have hp : 0≤c0+1/2 := by linarith [c0_bounds.1]
  dsimp [A]
  rw [show Q0-(c0+1/2)^2=(c0+1/2)^2 by linarith,
    Real.sqrt_sq hp]
  ring

theorem A_bounds {b : ℝ} (hb : b∈Icc 0 c0) : c0≤A b ∧ A b≤a0 := by
  have hc0 : 0≤c0 := by linarith [c0_bounds.1]
  have hleft := A_antitone ⟨le_rfl,hc0⟩ hb hb.1
  have hright := A_antitone hb ⟨hc0,le_rfl⟩ hb.2
  simpa only [A_zero,A_c0] using And.intro hright hleft

theorem linear_hasDerivAt {b : ℝ} (hb : b∈Icc 0 c0) (p q : ℝ) :
    HasDerivAt (linear p q) (p*Ad b+q) b := by
  have h := ((A_hasDerivAt hb).const_mul p).fun_add ((hasDerivAt_id' b).const_mul q)
  rw [mul_one] at h
  exact h

theorem linear_concave {p q l u : ℝ} (hp : 0≤p)
    (hl : 0≤l) (hu : u≤c0) : ConcaveOn ℝ (Icc l u) (linear p q) := by
  apply concave_of_deriv2
    (f' := fun b => p*Ad b+q) (f'' := fun b => p*Add b)
  · intro b hb
    exact linear_hasDerivAt ⟨hl.trans hb.1,hb.2.trans hu⟩ p q
  · intro b hb
    exact ((Ad_hasDerivAt ⟨hl.trans hb.1,hb.2.trans hu⟩).const_mul p).add_const q
  · intro b hb
    exact mul_nonpos_of_nonneg_of_nonpos hp
      (Add_negative ⟨hl.trans hb.1,hb.2.trans hu⟩).le

theorem linear_endpoint_lower {p q l u b : ℝ} (hp : 0≤p)
    (hl : 0≤l) (hu : u≤c0) (hb : b∈Icc l u) :
    min (linear p q l) (linear p q u)≤linear p q b :=
  (linear_concave hp hl hu).min_le_of_mem_Icc
    ⟨le_rfl,hb.1.trans hb.2⟩ ⟨hb.1.trans hb.2,le_rfl⟩ hb

theorem linear_monotone {p q : ℝ} (hp : p≤0) (hq : 0≤q) :
    MonotoneOn (linear p q) (Icc 0 c0) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (linear_hasDerivAt hb p q).continuousAt.continuousWithinAt
  · exact fun b hb => linear_hasDerivAt (Ioo_subset_Icc_self hb) p q
  · intro b hb
    exact add_nonneg (mul_nonneg_of_nonpos_of_nonpos hp
      (Ad_nonpos (Ioo_subset_Icc_self hb))) hq

/-- The lower full-circle support has no coefficient sign restriction. -/
theorem circle_linear_lower {a b : ℝ}
    (hc : (a+1/2)^2+(b+1/2)^2=Q0) (p q : ℝ) :
    -R*Real.sqrt (p^2+q^2)-(p+q)/2≤p*a+q*b := by
  let N : ℝ := Real.sqrt (p^2+q^2)
  have hN : 0≤N := Real.sqrt_nonneg _
  have hN2 : N^2=p^2+q^2 := Real.sq_sqrt (by positivity)
  have hprod : 0≤R*N := mul_nonneg R_pos.le hN
  have he : Q0*(p^2+q^2)-(p*(a+1/2)+q*(b+1/2))^2=
      (p*(b+1/2)-q*(a+1/2))^2 := by
    rw [← hc]
    ring
  have hsq : (p*(a+1/2)+q*(b+1/2))^2≤(R*N)^2 := by
    rw [mul_pow,R_sq,hN2]
    nlinarith only [he,sq_nonneg (p*(b+1/2)-q*(a+1/2))]
  have hlo : -R*N≤p*(a+1/2)+q*(b+1/2) := by
    nlinarith
  change -R*N-(p+q)/2≤p*a+q*b
  linarith

theorem state_outer_chart (s : FramePair.State) (hs : s.branch.type≠0) :
    s.a=A s.b ∧ s.b∈Icc 0 c0 := by
  have hc := s.outer_eq hs
  have hb := s.b_nonneg
  have ha := s.a_pos
  have hsb := pow_le_pow_left₀ (show 0≤ s.b+1/2 by linarith)
    (show s.b+1/2≤ s.a+1/2 by linarith [s.canonical]) 2
  have hc0 := c0_circle
  have hcp : 0<c0+1/2 := by linarith [c0_bounds.1]
  have hbU : s.b≤c0 := by nlinarith
  refine ⟨?_,⟨hb,hbU⟩⟩
  dsimp [A]
  rw [show Q0-(s.b+1/2)^2=(s.a+1/2)^2 by linarith,
    Real.sqrt_sq (by linarith)]
  ring

theorem periodic_cost_quadrant {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    periodicFrameCost x=(Real.cos x+Real.sin x-1)/2 := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_pos])
  have hc := Real.cos_nonneg_of_mem_Icc
    (show x∈Icc (-(Real.pi/2)) (Real.pi/2) by exact ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩)
  simp [periodicFrameCost,abs_of_nonneg hs,abs_of_nonneg hc]

end SquaresInCircles.Eight.FrameCircleArc

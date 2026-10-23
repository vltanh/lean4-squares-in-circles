module

public import SquaresInCircles.Eight.TableFree.FrameHighArc

/-!
# The exact outer circle in diagonal coordinates

The coordinate change is `(a,b) ↦ (a+b,a-b)`.  It retains both closed
intrinsic cuts.  Its circle, derivatives, endpoint supports and physical
center radii are established before any frame or word concentration.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameDiagonalArc
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
  convert (Ad_hasDerivAt hb).neg using 1 <;> dsimp [Ad,Add,slope,slopeD] <;> ring

theorem Ad_nonpos {b : ℝ} (hb : b∈Icc 0 b2) : Ad b≤0 := by
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.1) (A_shift_pos hb).le

theorem Add_negative {b : ℝ} (hb : b∈Icc 0 b2) : Add b<0 := by
  exact div_neg_of_neg_of_pos (by norm_num [Q0]) (pow_pos (A_shift_pos hb) 3)

theorem A_antitone : AntitoneOn A (Icc 0 b2) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun b hb => (A_hasDerivAt hb).continuousAt.continuousWithinAt
  · exact fun b hb => A_hasDerivAt (Ioo_subset_Icc_self hb)
  · exact fun b hb => Ad_nonpos (Ioo_subset_Icc_self hb)

theorem A_concave : ConcaveOn ℝ (Icc 0 b2) A :=
  concave_of_deriv2 (fun b hb => A_hasDerivAt hb)
    (fun b hb => Ad_hasDerivAt hb) (fun b hb => (Add_negative hb).le)

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
    0≤slope b ∧ slope b<(253/1000:ℝ) := by
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

theorem slope_bounds {b : ℝ} (hb : b∈Icc 0 b2) : 0≤slope b ∧ slope b<1 := by
  have hp := A_shift_pos hb
  constructor
  · exact div_nonneg hb.1 hp.le
  · apply (div_lt_iff₀ hp).2
    linarith [hb.2,b2_bounds.2,(A_bounds hb).1,a2_precise.1]

theorem linear_hasDerivAt {b : ℝ} (hb : b∈Icc 0 b2) (p q : ℝ) :
    HasDerivAt (linear p q) (p*Ad b+q) b := by
  simpa [linear] using ((A_hasDerivAt hb).const_mul p).add
    ((hasDerivAt_id b).const_mul q)

theorem linear_concave {p q l h : ℝ} (hp : 0≤p)
    (hl : 0≤l) (hh : h≤b2) : ConcaveOn ℝ (Icc l h) (linear p q) := by
  apply concave_of_deriv2
    (f' := fun b => p*Ad b+q) (f'' := fun b => p*Add b)
  · exact fun b hb => linear_hasDerivAt ⟨hl.trans hb.1,hb.2.trans hh⟩ p q
  · exact fun b hb => ((Ad_hasDerivAt ⟨hl.trans hb.1,hb.2.trans hh⟩).
      const_mul p).add_const q
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
  · exact fun b hb => ((A_hasDerivAt hb).add (hasDerivAt_id b)).
      continuousAt.continuousWithinAt
  · exact fun b hb => (A_hasDerivAt (Ioo_subset_Icc_self hb)).add (hasDerivAt_id b)
  · intro b hb
    have hs := (slope_bounds (Ioo_subset_Icc_self hb)).2
    dsimp [Ad,slope] at *
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
  rw [A_b1,b1_eq] at hp hm
  constructor <;> linarith [a1_precise.1,a1_precise.2]

theorem mid_coordinates {b : ℝ} (hb : b∈Icc b1 b2) :
    A b+b<(1299/500:ℝ) ∧ (649/1000:ℝ)<A b-b := by
  have hp := plus_monotone (mid_subset hb)
    ⟨by linarith [b2_bounds.1],le_rfl⟩ hb.2
  have hm := minus_antitone (mid_subset hb)
    ⟨by linarith [b2_bounds.1],le_rfl⟩ hb.2
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

end SquaresInCircles.Eight.TableFree.FrameDiagonalArc

module

public import SquaresInCircles.Eight.TableFree.FrameMidParallel

/-!
# Exact supports and sign-dependent angles for middle/middle pairs

All constants are derived from the original closed middle arc.  The
source supports are whole-arc concavity or monotonicity statements, and
the angle bounds use only the physical gap and the intrinsic type cuts.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidMidGeometry
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameCoreMidScalars FrameCoreMidGeometry

def cost (i k : Bool) (b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*M b-sign k*M B
def secondary (i k : Bool) (b B x : ℝ) : ℝ :=
  sign i*b+A B*Real.sin x-sign k*B*Real.cos x-pairWidth x
def primary (k : Bool) (b B x : ℝ) : ℝ :=
  A b-A B*Real.cos x-sign k*B*Real.sin x-pairWidth x

def lambda : ℝ := 87/100
def mF : ℝ := 911/2000-lambda*(128491721/250000000)
def mP : ℝ := -(455511/1000000)-(599628031/500000000)
def KF : ℝ := 9/100+mF-cM+(p+q+lambda)/2
def KP : ℝ := 9/100+mP-cM+(p+q+1)/2

theorem b2_precise : b2<(128491721/250000000:ℝ) := by
  dsimp [b2]
  linarith [a2_bounds.2]

theorem transverse_source_lower {b : ℝ} (hb : b∈Icc b1 b2) :
    mF≤M b-lambda*b := by
  have hh := linear_endpoint_lower (p := p) (q := q-lambda)
    (by norm_num [p]) b1_mem.1 b2_mem.2 hb
  dsimp [linear] at hh
  rw [A_b1,A_b2] at hh
  have hl : mF-cM≤p*a1+(q-lambda)*b1 := by
    have he := M_endpoints.1
    dsimp [M1] at he
    dsimp [mF,lambda]
    linarith [b1_bounds.2]
  have hu : mF-cM≤p*a2+(q-lambda)*b2 := by
    have he := M_endpoints.2.2.1
    dsimp [M2] at he
    dsimp [mF,lambda]
    linarith [b2_precise]
  have hmin := le_min hl hu
  dsimp [M]
  linarith

theorem primary_source_antitone :
    AntitoneOn (linear (-p-1) (-q)) (Icc b1 b2) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro b hb
    exact (linear_hasDerivAt ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩ _ _).
      continuousAt.continuousWithinAt
  · intro b hb
    exact linear_hasDerivAt ⟨b1_mem.1.trans hb.1.le,hb.2.le.trans b2_mem.2⟩ _ _
  · intro b hb
    have hr := slope_mid_bounds (Ioo_subset_Icc_self hb)
    dsimp [Ad,slope,p,q] at *
    linarith

theorem primary_source_lower (i : Bool) {b : ℝ} (hb : b∈Icc b1 b2) :
    mP≤sign i*M b-A b := by
  have hs := middle_minus_label i hb
  have hh := primary_source_antitone hb ⟨b1_lt_b2.le,le_rfl⟩ hb.2
  dsimp [linear] at hh
  rw [A_b2] at hh
  have hnum : mP≤-M2-a2 := by
    dsimp [mP]
    linarith [M_endpoints.2.2.2,a2_bounds.2]
  dsimp [M,M2] at *
  nlinarith

theorem intrinsic_angle (s : FramePair.State) (hs : s.branch=.middle) :
    (2449/10000:ℝ)<Real.arctan (s.b/s.a) ∧
      Real.arctan (s.b/s.a)<4049/10000 := by
  have ht : s.a≤4*s.b ∧ 7*s.b≤3*s.a := by simpa [hs,TypeMem] using s.type_mem
  have hratioL : (1/4:ℝ)≤s.b/s.a := (le_div_iff₀ s.a_pos).2 (by linarith [ht.1])
  have hratioU : s.b/s.a≤3/7 := (div_le_iff₀ s.a_pos).2 (by linarith [ht.2])
  have hl := Arithmetic.atanLower_le (show (0:ℝ)≤1/4 by norm_num)
  have hu := Arithmetic.arctan_le_atanUpper (show (0:ℝ)≤3/7 by norm_num)
  have hnumL : (2449/10000:ℝ)<Arithmetic.atanLower (1/4:ℝ) := by
    norm_num [Arithmetic.atanLower]
  have hnumU : Arithmetic.atanUpper (3/7:ℝ)<(4049/10000:ℝ) := by
    norm_num [Arithmetic.atanUpper]
  exact ⟨hnumL.trans_le (hl.trans (Real.arctan_le_arctan hratioL)),
    (Real.arctan_le_arctan hratioU).trans_lt (hu.trans_lt hnumU)⟩

theorem angle_floor (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) {x : ℝ} (hgap : (19/25:ℝ)≤s.gap t x) :
    -(1/20:ℝ)<x := by
  have hso := middle_offset_bounds s hs
  have hto := middle_offset_bounds t ht
  dsimp [State.gap] at hgap
  linarith

theorem same_sign_angle (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) (hsame : s.positive=t.positive) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) : (3/5:ℝ)<x := by
  have hso := intrinsic_angle s hs
  have hto := intrinsic_angle t ht
  dsimp [State.gap,State.offset] at hgap
  rw [hsame] at hgap
  cases hk : t.positive <;> simp only [hk,sign,ite_true,ite_false,one_mul,neg_one_mul] at hgap
  all_goals linarith

theorem negative_positive_angle (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) (hss : s.positive=false) (htt : t.positive=true) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) : (31/25:ℝ)<x := by
  have hso := intrinsic_angle s hs
  have hto := intrinsic_angle t ht
  dsimp [State.gap,State.offset] at hgap
  simp only [hss,htt,sign,ite_true,ite_false,one_mul,neg_one_mul] at hgap
  linarith

theorem same_tail (i : Bool) {b B x : ℝ} (hb : b∈Icc b1 b2)
    (hB : B∈Icc b1 b2) (hx : (109/100:ℝ)≤x) :
    (557/625:ℝ)<cost i i b B x := by
  have hs := M_bounds hb
  have ht := M_bounds hB
  have hch := CorePairGeometry.charge_upper x
  cases i <;> dsimp [cost,sign] <;> linarith [M_endpoints.1,M_endpoints.2.2.2]

theorem positive_negative_tail {b B x : ℝ} (hb : b∈Icc b1 b2)
    (hB : B∈Icc b1 b2) (hx : (8/25:ℝ)≤x) :
    (557/625:ℝ)<cost true false b B x := by
  have hs := M_bounds hb
  have ht := M_bounds hB
  have hch := CorePairGeometry.charge_upper x
  dsimp [cost,sign]
  linarith [M_endpoints.1]

theorem negative_positive_tail {b B x : ℝ} (hb : b∈Icc b1 b2)
    (hB : B∈Icc b1 b2) (hx : (37/20:ℝ)≤x) :
    (557/625:ℝ)<cost false true b B x := by
  have hs := M_bounds hb
  have ht := M_bounds hB
  have hch := CorePairGeometry.charge_upper x
  dsimp [cost,sign]
  linarith [M_endpoints.2.2.2]

theorem weaken_source (i k : Bool) {b B x : ℝ} (hb : b∈Icc b1 b2) :
    cost false k b B x≤cost i k b B x := by
  have hh := middle_minus_label i hb
  dsimp [cost,sign]
  linarith

theorem negative_secondary_false (k : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc 0 Real.pi) (hm : 0≤secondary false k b B x) : False := by
  have hs : 0≤Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2
  have hsrc := middle_bounds hb
  have htgt := middle_bounds hB
  have hsign := negative_signed_sin_le k (x := Real.pi/2-x)
    (show 0≤B by linarith [htgt.1])
  simp only [Real.sin_pi_div_two_sub] at hsign
  have hA := mul_le_mul_of_nonneg_right
    (show A B-1/2≤799/1000 by linarith [htgt.2.2.2]) hs
  have hB' := mul_le_mul_of_nonneg_right
    (show B-1/2≤7/500 by linarith [htgt.2.1]) (abs_nonneg (Real.cos x))
  have hnorm : (799/1000)*Real.sin x+(7/500)*|Real.cos x|<(4123/5000:ℝ) := by
    by_cases hcos : 0≤Real.cos x
    · rw [abs_of_nonneg hcos]
      exact projection_lt (by norm_num : (0:ℝ)<4123/5000) (by norm_num) x
    · rw [abs_of_nonpos (le_of_not_ge hcos)]
      have hh := projection_lt (a := (799/1000:ℝ)) (b := -(7/500:ℝ))
        (by norm_num : (0:ℝ)<4123/5000) (by norm_num) x
      nlinarith
  dsimp [secondary,pairWidth,sign] at hm
  rw [abs_of_nonneg hs] at hm
  nlinarith

end SquaresInCircles.Eight.TableFree.FrameMidMidGeometry

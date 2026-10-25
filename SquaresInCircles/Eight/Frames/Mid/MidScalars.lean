module

public import SquaresInCircles.Eight.Frames.Core.HighHighSecondaryScalars
public import SquaresInCircles.Eight.Owners.CircularNorm

/-!
# Eight squares: the scalar supports of the middle/middle pairs

For the secondary axis, the circle support `F x` increases on `[3/5, 109/100]` (`F_monotone`): in
the half-angle variable `z ∈ [1/8, 5/8]` its derivative has the sign of a polynomial `P` of
degree six (`half_angle_domain`, `Fd_positive`), and `P` is positive since its expansion about
`z = 3/8` leaves a positive remainder on both sides (`polynomial_remainder`,
`polynomial_positive`). With `F (3/5) > 4507/5000`, `F` exceeds `557/625` on the interval
(`transverse_lower`). For the primary axis, the circle support `primaryF` is concave on
`[π/2, 37/20]`, the part of the second quadrant that occurs, by the curvature identity of the
circular norm `NP` (`primaryDD_negative`, `primary_concave`), and exceeds `557/625` at both ends,
hence on the interval (`primary_lower`).
-/

section
/-!
## Exact supports and sign-dependent angles for middle/middle pairs

All constants are derived from the original closed middle arc.  The
source supports are whole-arc concavity or monotonicity statements, and
the angle bounds use only the physical gap and the intrinsic type cuts.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidMidGeometry
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
    exact (linear_hasDerivAt ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩ _ _
      ).continuousAt.continuousWithinAt
  · intro b hb
    exact linear_hasDerivAt ⟨b1_mem.1.trans hb.1.le,hb.2.le.trans b2_mem.2⟩ _ _
  · intro b hb
    have hr := slope_mid_bounds (Ioo_subset_Icc_self hb)
    have he : Ad b=-FrameLowArc.slope b := by
      simp only [Ad,FrameLowArc.slope]
      ring
    rw [he]
    norm_num [p,q]
    linarith [hr.2]

theorem primary_source_lower (i : Bool) {b : ℝ} (hb : b∈Icc b1 b2) :
    mP≤ sign i*M b-A b := by
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
  have hratioL : (1/4:ℝ)≤ s.b/s.a := (le_div_iff₀ s.a_pos).2 (by linarith [ht.1])
  have hratioU : s.b/s.a≤3/7 := (div_le_iff₀ s.a_pos).2 (by linarith [ht.2])
  have hl := Arithmetic.atanLower_le (show (0:ℝ)≤1/4 by norm_num)
  have hu := Arithmetic.arctan_le_atanUpper (show (0:ℝ)≤3/7 by norm_num)
  have hnumL : (2449/10000:ℝ)<Arithmetic.atanLower (1/4:ℝ) := by
    norm_num [Arithmetic.atanLower]
  have hnumU : Arithmetic.atanUpper (3/7:ℝ)<(4049/10000:ℝ) := by
    norm_num [Arithmetic.atanUpper]
  exact ⟨hnumL.trans_le (hl.trans (Real.arctan_mono hratioL)),
    (Real.arctan_mono hratioU).trans_lt (hu.trans_lt hnumU)⟩

theorem angle_floor (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    -(1/20:ℝ)<x := by
  have hso := middle_offset_bounds s hs
  have hto := middle_offset_bounds t ht
  dsimp [State.gap] at hgap
  linarith

theorem same_sign_angle (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) (hsame : s.positive=t.positive) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) : (3/5:ℝ)<x := by
  have hso := intrinsic_angle s hs
  have hto := intrinsic_angle t ht
  dsimp [State.gap,State.offset] at hgap
  rw [hsame] at hgap
  cases hk : t.positive <;>
    simp only [hk,sign,Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul] at hgap
  all_goals linarith

theorem negative_positive_angle (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) (hss : s.positive=false) (htt : t.positive=true) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) : (31/25:ℝ)<x := by
  have hso := intrinsic_angle s hs
  have hto := intrinsic_angle t ht
  dsimp [State.gap,State.offset] at hgap
  simp only [hss,htt,sign,Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul] at hgap
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
  have hf : sign false=-1 := rfl
  simp only [cost,hf]
  linarith

theorem negative_secondary_false (k : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc 0 Real.pi) (hm : 0≤ secondary false k b B x) : False := by
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
      linarith
  have hf : sign false=-1 := rfl
  simp only [secondary,pairWidth,hf,abs_of_nonneg hs] at hm
  linarith

end SquaresInCircles.Eight.FrameMidMidGeometry
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidMidScalars
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameMidMidGeometry

def NF (x : ℝ) : ℝ :=
  CircularNorm.norm (p^2+q^2+lambda^2) (-2*lambda*q) (2*lambda*p) x
def NFd (x : ℝ) : ℝ := lambda*(p*Real.cos x+q*Real.sin x)/NF x
def F (x : ℝ) : ℝ :=
  x+KF+(lambda-9/100)*Real.sin x-(9/100)*Real.cos x-R*NF x
def Fd (x : ℝ) : ℝ :=
  1+(lambda-9/100)*Real.cos x+(9/100)*Real.sin x-R*NFd x

theorem NF_energy_pos {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    0<CircularNorm.energy (p^2+q^2+lambda^2) (-2*lambda*q) (2*lambda*p) x := by
  have ht := FrameLowPair.quadrant hx
  have hp : 0<p+lambda*Real.sin x := by dsimp [p,lambda]; nlinarith [ht.1]
  have he : CircularNorm.energy (p^2+q^2+lambda^2) (-2*lambda*q) (2*lambda*p) x=
      (p+lambda*Real.sin x)^2+(q-lambda*Real.cos x)^2 := by
    dsimp [CircularNorm.energy]
    linear_combination -lambda^2*(Real.sin_sq_add_cos_sq x)
  rw [he]
  nlinarith [sq_pos_of_pos hp,sq_nonneg (q-lambda*Real.cos x)]

theorem NF_pos {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : 0<NF x :=
  CircularNorm.norm_pos (NF_energy_pos hx)

theorem NF_sq {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    (NF x)^2=p^2+q^2+lambda^2+2*lambda*(p*Real.sin x-q*Real.cos x) := by
  have hh := CircularNorm.norm_sq (NF_energy_pos hx).le
  convert hh using 1 <;> dsimp [NF,CircularNorm.energy]
  ring

theorem NF_deriv {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : HasDerivAt NF (NFd x) x := by
  convert CircularNorm.norm_hasDerivAt (NF_energy_pos hx) using 1
  · rfl
  · dsimp [NFd,NF,CircularNorm.d1,CircularNorm.slope]
    ring

theorem F_deriv {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : HasDerivAt F (Fd x) x := by
  have h := ((((hasDerivAt_id x).add_const KF).add
    ((Real.hasDerivAt_sin x).const_mul (lambda-9/100))).sub
    ((Real.hasDerivAt_cos x).const_mul (9/100))).sub ((NF_deriv hx).const_mul R)
  convert h using 1
  · funext y
    simp only [F,Pi.add_apply,Pi.sub_apply,id]
  · simp only [Fd]
    ring

abbrev D := FrameCoreMidFullCircle.D
abbrev S := FrameCoreMidFullCircle.S
abbrev C := FrameCoreMidFullCircle.C
def E (z : ℝ) : ℝ :=
  (p^2+q^2+lambda^2)*D z+2*lambda*(p*S z-q*C z)
def J (z : ℝ) : ℝ := D z+(lambda-9/100)*C z+(9/100)*S z
def P (z : ℝ) : ℝ :=
  (J z)^2*E z-Q0*lambda^2*(p*C z+q*S z)^2*D z
def lowerP (t : ℝ) : ℝ :=
  3/1000-(17/500)*t+(39/2)*t^2-(201/10)*t^3-15*t^5-(31/5)*t^6

/-- About `z = 3/8`, `P (3/8 ± t)` exceeds `lowerP t` for both signs and every `t ≥ 0`. -/
theorem polynomial_remainder (i : Bool) {t : ℝ} (ht : 0≤t) :
    lowerP t<P (3/8+sign i*t) := by
  apply sub_pos.mp
  cases i <;>
    dsimp [P,J,E,D,S,C,FrameCoreMidFullCircle.D,FrameCoreMidFullCircle.S,
      FrameCoreMidFullCircle.C,lowerP,p,q,lambda,Q0,sign] <;>
    ring_nf <;> positivity

theorem lowerP_positive {t : ℝ} (ht : t∈Icc (0:ℝ) (1/4)) : 0<lowerP t := by
  have ht3 := pow_le_pow_left₀ ht.1 ht.2 3
  have ht4 := pow_le_pow_left₀ ht.1 ht.2 4
  have hbracket : (14:ℝ)<39/2-(201/10)*t-15*t^3-(31/5)*t^4 := by
    nlinarith [ht.2]
  have hmul := mul_le_mul_of_nonneg_left hbracket.le (sq_nonneg t)
  have hsquare := sq_nonneg (28*t-17/500)
  dsimp [lowerP]
  nlinarith

theorem polynomial_positive {z : ℝ} (hz : z∈Icc (1/8:ℝ) (5/8)) : 0<P z := by
  by_cases hsign : 3/8≤z
  · have ht : z-3/8∈Icc (0:ℝ) (1/4) := ⟨by linarith,by linarith [hz.2]⟩
    have hh := polynomial_remainder true ht.1
    simp only [sign,↓reduceIte,one_mul] at hh
    convert (lowerP_positive ht).trans hh using 2
    ring
  · have ht : 3/8-z∈Icc (0:ℝ) (1/4) := ⟨by linarith,by linarith [hz.1]⟩
    have hh := polynomial_remainder false ht.1
    simp only [sign,Bool.false_eq_true,↓reduceIte,neg_one_mul] at hh
    convert (lowerP_positive ht).trans hh using 2
    ring

theorem half_angle_domain {x : ℝ} (hx : x∈Icc (3/5:ℝ) (109/100)) :
    ∃z∈Icc (1/8:ℝ) (5/8), D z*Real.sin x=S z ∧ D z*Real.cos x=C z := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  obtain ⟨z,hz,hs,hc⟩ := FrameCoreMidFullCircle.half_angle hxq
  have hD : D z≠0 := by dsimp [D,FrameCoreMidFullCircle.D]; positivity
  have hid : z*(1+Real.cos x)=Real.sin x := by
    apply (mul_left_cancel₀ hD)
    dsimp [D,S,C,FrameCoreMidFullCircle.D,FrameCoreMidFullCircle.S,
      FrameCoreMidFullCircle.C] at hs hc ⊢
    linear_combination z*hc-hs
  have hsl := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(3/5:ℝ)) hxq.2 hx.1
  have hsu := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hx.1,Real.pi_pos] : -(Real.pi/2)≤x)
    (by linarith [FrameLowPair.pi_lower] : (109/100:ℝ)≤Real.pi/2) hx.2
  have hcl := Real.cos_le_cos_of_nonneg_of_le_pi hxq.1
    (by linarith [FrameLowPair.pi_lower] : (109/100:ℝ)≤Real.pi) hx.2
  have hsL := Real.sin_ge_sub_cube (show (0:ℝ)≤3/5 by norm_num)
  have hsU := sin_upper_five (show (0:ℝ)≤109/100 by norm_num)
  have hcL := cos_lower_six (show (0:ℝ)≤109/100 by norm_num)
  norm_num at hsL hsU hcL
  have hsinL : (14/25:ℝ)<Real.sin x := by linarith
  have hsinU : Real.sin x<(89/100:ℝ) := by linarith
  have hcosL : (23/50:ℝ)<Real.cos x := by linarith
  refine ⟨z,⟨?_,?_⟩,hs,hc⟩
  · have hm := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hz.1
    linarith
  · have hm := mul_le_mul_of_nonneg_left hcosL.le hz.1
    linarith

theorem Fd_positive {x : ℝ} (hx : x∈Icc (3/5:ℝ) (109/100)) : 0<Fd x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  obtain ⟨z,hz,hs,hc⟩ := half_angle_domain hx
  have hD : 0<D z := by dsimp [D,FrameCoreMidFullCircle.D]; positivity
  have hn := NF_pos hxq
  have hN2 := NF_sq hxq
  have ht := FrameLowPair.quadrant hxq
  obtain ⟨a,had⟩ : ∃ a : ℝ, a=1+(lambda-9/100)*Real.cos x+(9/100)*Real.sin x := ⟨_,rfl⟩
  have ha : 0<a := by rw [had]; dsimp [lambda]; nlinarith [ht.1,ht.2.2.1]
  have hE : E z=D z*(NF x)^2 := by
    dsimp [E]
    rw [← hs,← hc,hN2]
    ring
  have hJ : J z=D z*a := by dsimp [J]; rw [had,← hs,← hc]; ring
  have hP : P z=(D z)^3*
      (a^2*(NF x)^2-Q0*lambda^2*(p*Real.cos x+q*Real.sin x)^2) := by
    dsimp [P]
    rw [hE,hJ,← hs,← hc]
    ring
  have hdelta : 0<a^2*(NF x)^2-Q0*lambda^2*(p*Real.cos x+q*Real.sin x)^2 := by
    have hh := polynomial_positive hz
    rw [hP] at hh
    exact (mul_pos_iff_of_pos_left (pow_pos hD 3)).mp hh
  have hforce : 0≤R*lambda*(p*Real.cos x+q*Real.sin x) := by
    apply mul_nonneg (mul_nonneg R_pos.le (by norm_num [lambda]))
    exact add_nonneg (mul_nonneg (by norm_num [p]) ht.2.2.1)
      (mul_nonneg (by norm_num [q]) ht.1)
  have hsq : (R*lambda*(p*Real.cos x+q*Real.sin x))^2=
      Q0*lambda^2*(p*Real.cos x+q*Real.sin x)^2 := by rw [mul_pow,mul_pow,R_sq]
  have hlt : R*lambda*(p*Real.cos x+q*Real.sin x)<a*NF x := by
    have h2 : (R*lambda*(p*Real.cos x+q*Real.sin x))^2<(a*NF x)^2 := by
      rw [hsq,mul_pow]
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (mul_pos ha hn).le h2
  have hdiv := (div_lt_iff₀ hn).2 hlt
  dsimp [Fd,NFd]
  have he : R*(lambda*(p*Real.cos x+q*Real.sin x)/NF x)=
      R*lambda*(p*Real.cos x+q*Real.sin x)/NF x := by ring
  rw [he]
  linarith

theorem F_monotone : MonotoneOn F (Icc (3/5:ℝ) (109/100)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro x hx
    exact (F_deriv ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩).continuousAt.continuousWithinAt
  · intro x hx
    exact F_deriv ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  · intro x hx
    exact (Fd_positive (Ioo_subset_Icc_self hx)).le

theorem transverse_endpoint_trig :
    (2823/5000:ℝ)<Real.sin (3/5:ℝ) ∧ Real.sin (3/5:ℝ)<5647/10000 ∧
      (8253/10000:ℝ)<Real.cos (3/5:ℝ) ∧ Real.cos (3/5:ℝ)<4127/5000 := by
  have hsL := sin_lower_seven (show (0:ℝ)≤3/5 by norm_num)
  have hsU := sin_upper_five (show (0:ℝ)≤3/5 by norm_num)
  have hcL := cos_lower_six (show (0:ℝ)≤3/5 by norm_num)
  have hcU := Arithmetic.cos_le_cos8 (show (0:ℝ)≤3/5 by norm_num)
  norm_num [Arithmetic.cos8] at *
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem F_endpoint : (4507/5000:ℝ)<F (3/5:ℝ) := by
  have ht := transverse_endpoint_trig
  have hdom : (3/5:ℝ)∈Icc 0 (Real.pi/2) :=
    ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩
  have hn := NF_pos hdom
  have hn2 := NF_sq hdom
  have hsq : (R*NF (3/5:ℝ))^2=Q0*(NF (3/5:ℝ))^2 := by rw [mul_pow,R_sq]
  have hrad : R*NF (3/5:ℝ)<1069/250 := by
    have hprod := mul_pos R_pos hn
    dsimp [p,q,lambda,Q0] at hn2 hsq
    nlinarith
  have hbase : (25887/5000:ℝ)<
      (3/5:ℝ)+KF+(lambda-9/100)*Real.sin (3/5:ℝ)-(9/100)*Real.cos (3/5:ℝ) := by
    dsimp [KF,mF,cM,p,q,lambda]
    linarith
  dsimp [F]
  linarith

theorem transverse_lower {x : ℝ} (hx : x∈Icc (3/5:ℝ) (109/100)) :
    (557/625:ℝ)<F x := by
  have hh := F_monotone ⟨le_rfl,by norm_num⟩ hx hx.1
  linarith [F_endpoint]

/-! ## The primary norm and its curvature on the second quadrant -/

def NP (x : ℝ) : ℝ := CircularNorm.norm (p^2+q^2+1) (-2*p) (-2*q) x
def primaryF (x : ℝ) : ℝ :=
  x+KP-(9/100)*Real.sin x-(91/100)*Real.cos x-R*NP x
def primaryD (x : ℝ) : ℝ :=
  1-(9/100)*Real.cos x+(91/100)*Real.sin x-
    R*CircularNorm.d1 (p^2+q^2+1) (-2*p) (-2*q) x
def primaryDD (x : ℝ) : ℝ :=
  (9/100)*Real.sin x+(91/100)*Real.cos x-
    R*CircularNorm.d2 (p^2+q^2+1) (-2*p) (-2*q) x

theorem NP_energy_pos (x : ℝ) :
    0<CircularNorm.energy (p^2+q^2+1) (-2*p) (-2*q) x := by
  have hp : 0<p-Real.cos x := by dsimp [p]; linarith [Real.cos_le_one x]
  have he : CircularNorm.energy (p^2+q^2+1) (-2*p) (-2*q) x=
      (p-Real.cos x)^2+(q-Real.sin x)^2 := by
    dsimp [CircularNorm.energy]
    linear_combination -(Real.sin_sq_add_cos_sq x)
  rw [he]
  nlinarith [sq_pos_of_pos hp,sq_nonneg (q-Real.sin x)]

theorem NP_pos (x : ℝ) : 0<NP x := CircularNorm.norm_pos (NP_energy_pos x)
theorem NP_sq (x : ℝ) :
    (NP x)^2=p^2+q^2+1-2*(p*Real.cos x+q*Real.sin x) := by
  have hh := CircularNorm.norm_sq (NP_energy_pos x).le
  convert hh using 1 <;> dsimp [NP,CircularNorm.energy]
  ring

theorem primaryF_deriv (x : ℝ) : HasDerivAt primaryF (primaryD x) x := by
  have h := ((((hasDerivAt_id x).add_const KP).sub
    ((Real.hasDerivAt_sin x).const_mul (9/100))).sub
    ((Real.hasDerivAt_cos x).const_mul (91/100))).sub
    ((CircularNorm.norm_hasDerivAt (NP_energy_pos x)).const_mul R)
  convert h using 1
  · funext y
    simp only [primaryF,NP,Pi.sub_apply,id]
  · simp only [primaryD]
    ring

theorem primaryD_deriv (x : ℝ) : HasDerivAt primaryD (primaryDD x) x := by
  have h := ((((Real.hasDerivAt_cos x).const_mul (-(9/100:ℝ))).const_add 1).add
    ((Real.hasDerivAt_sin x).const_mul (91/100))).sub
    ((CircularNorm.d1_hasDerivAt (NP_energy_pos x)).const_mul R)
  convert h using 1
  · funext y
    simp only [primaryD,Pi.add_apply,Pi.sub_apply]
    ring
  · simp only [primaryDD]
    ring

theorem radius_bounds : (197/100:ℝ)<R ∧ R<(99/50:ℝ) := by
  have hs := R_sq
  have hp := R_pos
  norm_num [Q0] at hs
  constructor <;> nlinarith

theorem primary_endpoint_trig : (24/25:ℝ)<Real.sin (37/20:ℝ) ∧
    -(69/250:ℝ)<Real.cos (37/20:ℝ) ∧ Real.cos (37/20:ℝ)< -(11/40:ℝ) := by
  have hs := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤37/20 by norm_num)
  have hcL := Arithmetic.cos10_le_cos (show (0:ℝ)≤37/20 by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤37/20 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,
    Arithmetic.cos8,HighOrderTaylor.C12] at *
  exact ⟨by linarith,by linarith,by linarith⟩

theorem primary_trig {x : ℝ} (hx : x∈Icc (Real.pi/2) (37/20:ℝ)) :
    (24/25:ℝ)<Real.sin x ∧ -(69/250:ℝ)<Real.cos x ∧ Real.cos x≤0 := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := sin_endpoint_lower (by positivity : (0:ℝ)≤Real.pi/2)
    (by linarith [FrameLowPair.pi_lower] : (37/20:ℝ)≤Real.pi) hx
    (by norm_num : (24/25:ℝ)<Real.sin (Real.pi/2)) primary_endpoint_trig.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1,Real.pi_pos] : 0≤x)
    (by linarith [FrameLowPair.pi_lower]) hx.2
  exact ⟨hs,primary_endpoint_trig.2.1.trans_le hc,(second_signs hxq).2⟩

theorem NP_upper {x : ℝ} (hx : x∈Icc (Real.pi/2) (37/20:ℝ)) : NP x<(15/8:ℝ) := by
  have ht := primary_trig hx
  have hn := NP_pos x
  have hh := NP_sq x
  dsimp [p,q] at hh
  nlinarith

theorem primaryDD_negative {x : ℝ} (hx : x∈Icc (Real.pi/2) (37/20:ℝ)) :
    primaryDD x<0 := by
  have hn := NP_pos x
  have hnu := NP_upper hx
  have ht := primary_trig hx
  have hR := radius_bounds
  have hK : (69/5:ℝ)<(p^2+q^2-1)^2 := by norm_num [p,q]
  have hden : 0<4*(NP x)^3 := by positivity
  have hdenU : 4*(NP x)^3≤4*(15/8:ℝ)^3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn.le hnu.le 3) (by norm_num)
  have hnum : (197/100:ℝ)*(69/5)<R*(p^2+q^2-1)^2 := by
    exact (mul_lt_mul_of_pos_left hK (by norm_num : (0:ℝ)<197/100)).trans
      (mul_lt_mul_of_pos_right hR.1 (by linarith [hK] : 0<(p^2+q^2-1)^2))
  have hratio : (197/100:ℝ)*(69/5)/(4*(15/8:ℝ)^3)<
      R*(p^2+q^2-1)^2/(4*(NP x)^3) := by
    apply (lt_div_iff₀ hden).2
    have hm := mul_le_mul_of_nonneg_left hdenU
      (show (0:ℝ)≤(197/100)*(69/5)/(4*(15/8)^3) by norm_num)
    norm_num at hm
    linarith
  have hRN : R*NP x<(99/50:ℝ)*(15/8) := by
    exact (mul_lt_mul_of_pos_left hnu R_pos).trans
      (mul_lt_mul_of_pos_right hR.2 (by norm_num : (0:ℝ)<15/8))
  have hid := CircularNorm.curvature_identity (NP_energy_pos x)
  have hcoef : (p^2+q^2+1)^2-(-2*p)^2-(-2*q)^2=(p^2+q^2-1)^2 := by ring
  rw [hcoef] at hid
  change CircularNorm.d2 (p^2+q^2+1) (-2*p) (-2*q) x+NP x/4=
    (p^2+q^2-1)^2/(4*(NP x)^3) at hid
  have hmul := congrArg (fun z : ℝ => R*z) hid
  have he : R*((p^2+q^2-1)^2/(4*(NP x)^3))=
      R*(p^2+q^2-1)^2/(4*(NP x)^3) := by ring
  rw [he] at hmul
  dsimp [primaryDD]
  nlinarith [Real.sin_le_one x,ht.2.2]

theorem primary_concave : ConcaveOn ℝ (Icc (Real.pi/2) (37/20:ℝ)) primaryF :=
  concave_of_deriv2 (fun x _ => primaryF_deriv x)
    (fun x _ => primaryD_deriv x) (fun _ hx => (primaryDD_negative hx).le)

theorem primary_quarter_lower : (557/625:ℝ)<primaryF (Real.pi/2) := by
  have hn := NP_pos (Real.pi/2)
  have hh := NP_sq (Real.pi/2)
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero] at hh
  have hnu : NP (Real.pi/2)<8/5 := by dsimp [p,q] at hh; nlinarith
  have hRN : R*NP (Real.pi/2)<(99/50:ℝ)*(8/5) := by
    exact (mul_lt_mul_of_pos_left hnu R_pos).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<8/5))
  dsimp [primaryF,KP,mP,cM,p,q]
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero,sub_zero]
  linarith [FrameLowPair.pi_lower]

theorem primary_last_lower : (557/625:ℝ)<primaryF (37/20:ℝ) := by
  have hx : (37/20:ℝ)∈Icc (Real.pi/2) (37/20:ℝ) :=
    ⟨by linarith [Arithmetic.pi_hand_enclosure.2],le_rfl⟩
  have hnu := NP_upper hx
  have hRN : R*NP (37/20:ℝ)<(99/50:ℝ)*(15/8) := by
    exact (mul_lt_mul_of_pos_left hnu R_pos).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<15/8))
  dsimp [primaryF,KP,mP,cM,p,q]
  linarith [Real.sin_le_one (37/20:ℝ),primary_endpoint_trig.2.2]

theorem primary_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (37/20:ℝ)) :
    (557/625:ℝ)<primaryF x :=
  concave_gt_of_endpoints primary_concave hx primary_quarter_lower primary_last_lower

end SquaresInCircles.Eight.FrameMidMidScalars
end
end
end

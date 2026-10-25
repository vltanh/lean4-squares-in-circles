module

public import SquaresInCircles.Eight.Words.Second.Mixed.TransverseSupportWide
public import SquaresInCircles.Eight.Words.Second.Mixed.Edge.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Mixed.TSmallEnvelope
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoFirstOwners
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeUpperEasy

/-!
# Eight squares: exact derivatives of the polynomial corner lower cost

The source polynomial is applied only after the original-height
comparison. Every derivative below is of that explicit relaxed scalar,
on the complete canonical core corner.
-/

section
/-!
## The whole negative-core corner contact rectangle

One pair of harmonic coordinates gives every contact height and
angular speed. The original core circle supplies the exact slope
ratio and its derivative, including both closed endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

def angles : Set ℝ := Icc lowerAngle (1191/1000)
def lateAngles : Set ℝ := Icc (11/10) (1191/1000)
def u (B φ : ℝ) : ℝ := 1+(MixedCorner.a B+1/2)*Real.cos φ-(B-1/2)*Real.sin φ
def speed (B φ : ℝ) : ℝ := (MixedCorner.a B+1/2)*Real.sin φ+(B-1/2)*Real.cos φ
def L (B φ : ℝ) : ℝ := Real.sin φ+MixedCorner.w B*Real.cos φ
def N (B φ : ℝ) : ℝ := Real.cos φ-MixedCorner.w B*Real.sin φ
def D (B : ℝ) : ℝ := (1+(MixedCorner.w B)^2)/MixedCorner.z B

lemma terminal_trig :
    (46437/50000:ℝ)<Real.sin (1191/1000) ∧ Real.sin (1191/1000)<928741/1000000 ∧
    (370731/1000000:ℝ)<Real.cos (1191/1000) ∧ Real.cos (1191/1000)<92683/250000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (1191/1000:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (1191/1000:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (1191/1000:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (1191/1000:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma transition_trig :
    (891207/1000000:ℝ)<Real.sin (11/10) ∧ Real.sin (11/10)<111401/125000 ∧
    (113399/250000:ℝ)<Real.cos (11/10) ∧ Real.cos (11/10)<453597/1000000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (11/10:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (11/10:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (11/10:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (11/10:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma lower_mem {φ : ℝ} (hφ : φ∈angles) : Lower φ :=
  ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩
lemma late_subset : lateAngles⊆angles := fun _ hφ =>
  ⟨by dsimp [lowerAngle]; linarith [hφ.1,pi_hand_enclosure.2],hφ.2⟩

lemma u_bounds {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈angles) :
    (6689/5000:ℝ)<u B φ ∧ u B φ<(17/10:ℝ) := by
  have hc := CoreAngleEndpoint.state_bounds (MixedCorner.state hB)
  have hd := MixedCorner.chart_bounds hB
  have ht := lower_trig (lower_mem hφ)
  have he : (1191/1000:ℝ)∈angles := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],le_rfl⟩
  have hs := PositiveThree.lower_sin_monotone (lower_mem hφ) (lower_mem he) hφ.2
  have hcos := PositiveThree.lower_cos_antitone (lower_mem hφ) (lower_mem he) hφ.2
  have hAl : (13973139/25000000:ℝ)<MixedCorner.a B := by
    dsimp [MixedCorner.a]
    linarith [hd.1,CoreAngleEndpoint.diagonal_bounds.1]
  have hBu : B<(55892557/100000000:ℝ) := hB.2.trans_lt CoreAngleEndpoint.diagonal_bounds.2
  have hl := mul_le_mul
    (show (26473139/25000000:ℝ)≤MixedCorner.a B+1/2 by linarith) terminal_trig.2.2.1.le
    (by norm_num : (0:ℝ)≤370731/1000000) (by linarith [hAl] : 0≤MixedCorner.a B+1/2)
  have hcs := mul_le_mul_of_nonneg_left hcos
    (by linarith [hAl] : 0≤MixedCorner.a B+1/2)
  have hu := mul_le_mul
    (show B-1/2≤5892557/100000000 by linarith) (hs.trans terminal_trig.2.1.le)
    (by linarith [ht.1] : 0≤Real.sin φ) (by norm_num : (0:ℝ)≤5892557/100000000)
  have hupper := mul_le_mul (show MixedCorner.a B+1/2≤13/12 by linarith [hc.2.1]) ht.2.2.2.1.le
    ht.2.2.1 (by norm_num : (0:ℝ)≤13/12)
  have hnonneg := mul_nonneg (sub_nonneg.mpr hB.1) (by linarith [ht.1] : 0≤Real.sin φ)
  dsimp [u]
  constructor <;> nlinarith

lemma early_height {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈angles) (he : φ≤11/10) :
    u B φ∈Icc (7/5:ℝ) (17/10) := by
  have ht := lower_trig (lower_mem hφ)
  have hi : (11/10:ℝ)∈angles := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],by norm_num⟩
  have hc := PositiveThree.lower_cos_antitone (lower_mem hφ) (lower_mem hi) he
  have hcore := MixedCorner.chart_bounds hB
  have ha : (10589/10000:ℝ)≤MixedCorner.a B+1/2 := by
    dsimp [MixedCorner.a]
    linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1]
  have hb : B-1/2≤59/1000 := by linarith [hB.2,CoreAngleEndpoint.diagonal_bounds.2]
  have hp := mul_le_mul ha (transition_trig.2.2.1.le.trans hc)
    (by norm_num : (0:ℝ)≤113399/250000) (by linarith [ha] : 0≤MixedCorner.a B+1/2)
  have hq := mul_le_mul hb (Real.sin_le_one φ) (by linarith [ht.1] : 0≤Real.sin φ)
    (by norm_num : (0:ℝ)≤59/1000)
  exact ⟨by dsimp [u]; nlinarith,(u_bounds hB hφ).2.le⟩

lemma late_height {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈lateAngles) :
    u B φ∈Icc (133/100:ℝ) (373/250) := by
  have hi : (11/10:ℝ)∈angles := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],by norm_num⟩
  have hc := PositiveThree.lower_cos_antitone (lower_mem hi) (lower_mem (late_subset hφ)) hφ.1
  have ht := lower_trig (lower_mem (late_subset hφ))
  have hcore := CoreAngleEndpoint.state_bounds (MixedCorner.state hB)
  have hp := mul_le_mul (show MixedCorner.a B+1/2≤13/12 by linarith [hcore.2.1])
    (hc.trans transition_trig.2.2.2.le) ht.2.2.1 (by norm_num : (0:ℝ)≤13/12)
  have hq := mul_nonneg (sub_nonneg.mpr hB.1) (by linarith [ht.1] : 0≤Real.sin φ)
  exact ⟨by linarith [(u_bounds hB (late_subset hφ)).1],by dsimp [u]; nlinarith⟩

lemma terminal_height {B : ℝ} (hB : B∈MixedCorner.domain) :
    u B (1191/1000)∈Icc (6689/5000:ℝ) (701/500) := by
  have he : (1191/1000:ℝ)∈angles := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],le_rfl⟩
  have hcore := CoreAngleEndpoint.state_bounds (MixedCorner.state hB)
  have hp := mul_le_mul (show MixedCorner.a B+1/2≤13/12 by linarith [hcore.2.1]) terminal_trig.2.2.2.le
    (by linarith [terminal_trig.2.2.1] : 0≤Real.cos (1191/1000)) (by norm_num : (0:ℝ)≤13/12)
  have hq := mul_nonneg (sub_nonneg.mpr hB.1) (by linarith [terminal_trig.1] : 0≤Real.sin (1191/1000))
  exact ⟨(u_bounds hB he).1.le,by dsimp [u]; nlinarith⟩

lemma D_bounds {B : ℝ} (hB : B∈MixedCorner.domain) :
    0<D B ∧ 12*(1+(MixedCorner.w B)^2)≤D B ∧ D B<34 := by
  have hz := MixedCorner.z_positive hB
  have hw := MixedCorner.w_bounds hB
  have hc := MixedCorner.chart_bounds hB
  have hwp : (MixedCorner.w B)^2≤1 := by nlinarith
  have he : D B*MixedCorner.z B=1+(MixedCorner.w B)^2 := by
    dsimp [D]
    field_simp [hz.ne']
  have hp : 0<D B := by dsimp [D]; positivity
  have hlo := mul_le_mul_of_nonneg_left hc.2.1 hp.le
  have hhi := mul_le_mul_of_nonneg_left
    (show (589/10000:ℝ)≤MixedCorner.z B by linarith [hc.1,CoreAngleEndpoint.diagonal_bounds.1]) hp.le
  exact ⟨hp,by nlinarith,by nlinarith⟩

lemma harmonic_circle (B φ : ℝ) : (u B φ-1)^2+(speed B φ)^2=
    (MixedCorner.a B+1/2)^2+(B-1/2)^2 := by
  dsimp [u,speed]
  linear_combination ((MixedCorner.a B+1/2)^2+(B-1/2)^2)*(Real.sin_sq_add_cos_sq φ)

lemma speed_bounds {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈angles) :
    0<speed B φ ∧ speed B φ<(109/100:ℝ) := by
  have ht := lower_trig (lower_mem hφ)
  have hc := CoreAngleEndpoint.state_bounds (MixedCorner.state hB)
  have hfirst := mul_pos (show 0<MixedCorner.a B+1/2 by linarith [hc.1])
    (show 0<Real.sin φ by linarith [ht.1])
  have hsecond := mul_nonneg (sub_nonneg.mpr hB.1) ht.2.2.1
  have hpos : 0<speed B φ := by dsimp [speed]; linarith
  have he := harmonic_circle B φ
  have hm := (MixedCorner.endpoint_mass hB).2
  exact ⟨hpos,by nlinarith [sq_nonneg (u B φ-1)]⟩

lemma LN_circle (B φ : ℝ) : (L B φ)^2+(N B φ)^2=1+(MixedCorner.w B)^2 := by
  dsimp [L,N]
  linear_combination (1+(MixedCorner.w B)^2)*(Real.sin_sq_add_cos_sq φ)

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
end
end
end

section
/-!
## Original data for negative outer to negative core at edge two

The whole core has one affine lower label bound, and its corner has
the sharper join lower bound. These give the complete direct tails.
The primary separator is transferred only to a polynomial lower
bound at the original outer height.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget
open CommonQuarter CorePairGeometry Arithmetic

def γ : ℝ := 17953/20000
def e : ℝ := 11021/50000-(8623/25000)*(7/12)
def g : ℝ := 98439/100000
def h : ℝ := 8623/25000
def z : ℝ := 2667/50000
def value (b A B φ : ℝ) : ℝ := φ-P b+MixedThree.negativeCore A B

lemma core_transverse {A B : ℝ} (ht : CoreState A B) : 0≤B ∧ B<(559/1000:ℝ) :=
  ⟨(CoreAngleEndpoint.state_bounds ht).2.2.1,
    (CoreAngleEndpoint.state_bounds ht).2.2.2.2.trans_lt (by linarith [CoreAngleEndpoint.diagonal_bounds.2])⟩

lemma core_affine {A B : ℝ} (ht : CoreState A B) : e+(1909/2000)*B≤MixedThree.negativeCore A B := by
  have hh := core_transverse ht
  have hA := (CoreAngleEndpoint.state_bounds ht).2.1
  have hp := mul_nonneg hh.1 (show 0≤98439/100000-1909/2000-(2667/50000)*B by linarith [hh.2])
  dsimp [e,MixedThree.negativeCore]
  nlinarith

lemma core_minimum {A B : ℝ} (ht : CoreState A B) : e≤MixedThree.negativeCore A B := by
  have hh := core_affine ht
  linarith [(core_transverse ht).1]

lemma corner_minimum {A B : ℝ} (ht : CoreState A B) (hB : 1/2≤B) :
    (49807/100000:ℝ)<MixedThree.negativeCore A B := by
  have hh := core_transverse ht
  have hA := (CoreAngleEndpoint.state_bounds ht).2.1
  have hp := mul_nonneg (show 0≤B-1/2 by linarith)
    (show 0≤98439/100000-(2667/50000)*(B+1/2) by linarith [hh.2])
  dsimp [MixedThree.negativeCore]
  nlinarith

lemma source_upper {a b : ℝ} (hs : OuterState a b) : P b<(79091/100000:ℝ) := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(CommonQuarter.outer_bounds hs).2.2.2.1⟩
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨by linarith [fine_outer_endpoint_bounds.2],le_rfl⟩
  exact (P_monotone hb hd hb.2).trans_lt P_diagonal_upper

lemma tail {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B) (hφ : (167/100:ℝ)≤φ) :
    γ<value b A B φ := by
  have hh := core_minimum ht
  dsimp [value,e,γ] at *
  linarith [source_upper hs]

lemma corner_tail {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hB : 1/2≤B) (hφ : (1191/1000:ℝ)≤φ) : γ<value b A B φ := by
  have hh := corner_minimum ht hB
  dsimp [value,γ]
  linarith [source_upper hs]

lemma primary_height_lower {a b A B φ : ℝ} (hs : OuterState a b)
    (hu : 1+(A+1/2)*Real.cos φ+(1/2-B)*Real.sin φ∈PHeightBounds.heights)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ) :
    φ+PHeightTaylor.poly (1+(A+1/2)*Real.cos φ+(1/2-B)*Real.sin φ)+
      MixedThree.negativeCore A B<value b A B φ := by
  have hh := PHeightTaylor.original_lower hs hu (by nlinarith)
  dsimp [value]
  linarith

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget
end
end
end

section
/-!
## The exact side discriminant and its first four derivatives

The side expression is kept as a quadratic discriminant in the core coordinate,
`E x = 4 * qa x * qc x - (qb x)^2` (`discriminant_identity`). Its two-harmonic expansion permits a
single sign of the fourth derivative `E4` on the whole angle interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Side
open CommonQuarter CorePairGeometry Arithmetic

abbrev p := PHeightQuadratic.p
abbrev k := PHeightQuadratic.k
def v0 : ℝ := Real.pi/2+PHeightQuadratic.c+e-γ
def contactD (x : ℝ) : ℝ := -2/5+(13/12)*Real.sin x+Real.cos x/2
def qa (x : ℝ) : ℝ := k*(Real.cos x)^2-z
def qb (x : ℝ) : ℝ := g-Real.cos x*(p+2*k*contactD x)
def qc (x : ℝ) : ℝ := v0-x+p*contactD x+k*(contactD x)^2
def A : ℝ := 12316256254413/10000000000000
def B : ℝ := -7644002660021/50000000000000
def C : ℝ := (39/100)*Real.pi-2705833101088507809/2000000000000000000
def H : ℝ := 3146949/4000000
def J : ℝ := -7083/12500
def Z : ℝ := (7083/25000)*Real.pi-3987658073098843809/2000000000000000000
def q : ℝ := 39/50
def E (x : ℝ) : ℝ := A*Real.cos x+B*Real.sin x+(C-q*x)*Real.cos (2*x)+
  H*Real.sin (2*x)+Z+J*x
def E1 (x : ℝ) : ℝ := -A*Real.sin x+B*Real.cos x+(-q+2*H)*Real.cos (2*x)-
  2*(C-q*x)*Real.sin (2*x)+J
def E2 (x : ℝ) : ℝ := -A*Real.cos x-B*Real.sin x-4*(C-q*x)*Real.cos (2*x)+
  (4*q-4*H)*Real.sin (2*x)
def E3 (x : ℝ) : ℝ := A*Real.sin x-B*Real.cos x+(12*q-8*H)*Real.cos (2*x)+
  8*(C-q*x)*Real.sin (2*x)
def E4 (x : ℝ) : ℝ := A*Real.cos x+B*Real.sin x+16*(C-q*x)*Real.cos (2*x)+
  (16*H-32*q)*Real.sin (2*x)

lemma C_bounds : -(25539083129/200000000000:ℝ)<C ∧ C< -(31923853911/250000000000:ℝ) := by
  dsimp [C]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]

lemma Z_bounds : -(220750601187/200000000000:ℝ)<Z ∧ Z< -(551876502967/500000000000:ℝ) := by
  dsimp [Z]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]

lemma discriminant_identity (x : ℝ) : E x=4*qa x*qc x-(qb x)^2 := by
  dsimp [E,qa,qb,qc,contactD,v0,A,B,C,H,Z,J,q,p,k,PHeightQuadratic.p,PHeightQuadratic.k,
    PHeightQuadratic.c,g,z,e,γ]
  rw [Real.cos_two_mul,Real.sin_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma E_hasDerivAt (x : ℝ) : HasDerivAt E (E1 x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert ((((((Real.hasDerivAt_cos x).const_mul A).add ((Real.hasDerivAt_sin x).const_mul B)).add
    ((((hasDerivAt_id x).const_mul q).const_sub C).mul hc)).add (hs.const_mul H)).add_const Z).add
      ((hasDerivAt_id x).const_mul J) using 1
  · funext y
    simp only [E,Pi.add_apply,Pi.mul_apply,Function.comp_apply,id]
  · dsimp [E1]
    ring

lemma E1_hasDerivAt (x : ℝ) : HasDerivAt E1 (E2 x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert (((((Real.hasDerivAt_sin x).const_mul (-A)).add ((Real.hasDerivAt_cos x).const_mul B)).add
    (hc.const_mul (-q+2*H))).sub
      (((((hasDerivAt_id x).const_mul q).const_sub C).mul hs).const_mul 2)).add_const J
    using 1
  · funext y
    simp only [E1,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Function.comp_apply,id]
    ring
  · dsimp [E2]
    ring

lemma E2_hasDerivAt (x : ℝ) : HasDerivAt E2 (E3 x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert ((((Real.hasDerivAt_cos x).const_mul (-A)).sub ((Real.hasDerivAt_sin x).const_mul B)).sub
    (((((hasDerivAt_id x).const_mul q).const_sub C).mul hc).const_mul 4)).add
      (hs.const_mul (4*q-4*H)) using 1
  · funext y
    simp only [E2,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Function.comp_apply,id]
    ring
  · dsimp [E3]
    ring

lemma E3_hasDerivAt (x : ℝ) : HasDerivAt E3 (E4 x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert ((((Real.hasDerivAt_sin x).const_mul A).sub ((Real.hasDerivAt_cos x).const_mul B)).add
    (hc.const_mul (12*q-8*H))).add
      (((((hasDerivAt_id x).const_mul q).const_sub C).mul hs).const_mul 8) using 1
  · funext y
    simp only [E3,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Function.comp_apply,id]
    ring
  · dsimp [E4]
    ring

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Side
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
open CommonQuarter CorePairGeometry Arithmetic

def f (B φ : ℝ) : ℝ := φ+PHeightTaylor.poly (u B φ)+MixedThree.negativeCore (MixedCorner.a B) B
def fB (B φ : ℝ) : ℝ := -PHeightTaylor.d1 (u B φ)*L B φ+h*MixedCorner.w B+g-2*z*B
def fBB (B φ : ℝ) : ℝ := PHeightTaylor.d2 (u B φ)*(L B φ)^2-
  (PHeightTaylor.d1 (u B φ)*Real.cos φ-h)*D B-2*z
def fAngle (B φ : ℝ) : ℝ := 1-PHeightTaylor.d1 (u B φ)*speed B φ
def fAngleD (B φ : ℝ) : ℝ := PHeightTaylor.d2 (u B φ)*(speed B φ)^2-
  PHeightTaylor.d1 (u B φ)*(u B φ-1)
def fBBAngle (B φ : ℝ) : ℝ := -PHeightTaylor.c3*speed B φ*(L B φ)^2+
  2*PHeightTaylor.d2 (u B φ)*L B φ*N B φ+
  D B*(PHeightTaylor.d2 (u B φ)*speed B φ*Real.cos φ+PHeightTaylor.d1 (u B φ)*Real.sin φ)

lemma u_core_hasDerivAt {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun B => u B φ) (-L B φ) B := by
  exact ((((MixedCorner.a_hasDerivAt hB).add_const (1/2)).mul_const (Real.cos φ)).const_add 1).sub
    (((hasDerivAt_id' B).sub_const (1/2)).mul_const (Real.sin φ))
    |>.congr_deriv (by dsimp only [L]; ring)

lemma L_core_hasDerivAt {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun B => L B φ) (D B*Real.cos φ) B := by
  convert ((MixedCorner.w_hasDerivAt hB).mul_const (Real.cos φ)).const_add (Real.sin φ) using 1 <;>
    dsimp [L,D]

lemma u_angle_hasDerivAt (B φ : ℝ) : HasDerivAt (u B) (-speed B φ) φ := by
  exact ((((Real.hasDerivAt_cos φ).const_mul (MixedCorner.a B+1/2)).const_add 1).sub
    ((Real.hasDerivAt_sin φ).const_mul (B-1/2))) |>.congr_deriv (by dsimp only [speed]; ring)

lemma speed_hasDerivAt (B φ : ℝ) : HasDerivAt (speed B) (u B φ-1) φ := by
  exact ((Real.hasDerivAt_sin φ).const_mul (MixedCorner.a B+1/2)).add
    ((Real.hasDerivAt_cos φ).const_mul (B-1/2)) |>.congr_deriv (by dsimp only [u]; ring)

lemma L_angle_hasDerivAt (B φ : ℝ) : HasDerivAt (L B) (N B φ) φ := by
  exact (Real.hasDerivAt_sin φ).add ((Real.hasDerivAt_cos φ).const_mul (MixedCorner.w B))
    |>.congr_deriv (by dsimp only [N]; ring)

lemma f_core_hasDerivAt {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun B => f B φ) (fB B φ) B := by
  have hc : HasDerivAt (fun x => MixedThree.negativeCore (MixedCorner.a x) x) _ B :=
    ((((MixedCorner.a_hasDerivAt hB).const_mul (8623/25000)).const_sub (11021/50000)).add
      ((hasDerivAt_id' B).const_mul (98439/100000))).sub
        (((hasDerivAt_id' B).pow 2).const_mul (2667/50000))
  have hf := (((PHeightTaylor.poly_hasDerivAt (u B φ)).comp B
    (u_core_hasDerivAt (φ := φ) hB)).const_add φ).add hc
  convert hf using 1
  · funext x
    simp only [f,Pi.add_apply,Function.comp_apply]
  · simp only [fB,h,g,z,Nat.cast_ofNat]
    ring

lemma fB_hasDerivAt {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun B => fB B φ) (fBB B φ) B := by
  exact (((((PHeightTaylor.d1_hasDerivAt (u B φ)).comp B
    (u_core_hasDerivAt (φ := φ) hB)).neg.mul (L_core_hasDerivAt (φ := φ) hB)).add
      ((MixedCorner.w_hasDerivAt hB).const_mul h)).add_const g).sub
        ((hasDerivAt_id' B).const_mul (2*z)) |>.congr_deriv (by
      simp only [fBB,D,Function.comp_apply,Pi.neg_apply]
      ring)

lemma f_angle_hasDerivAt (B φ : ℝ) : HasDerivAt (f B) (fAngle B φ) φ := by
  exact ((hasDerivAt_id' φ).add
    ((PHeightTaylor.poly_hasDerivAt (u B φ)).comp φ (u_angle_hasDerivAt B φ))).add_const
      (MixedThree.negativeCore (MixedCorner.a B) B) |>.congr_deriv (by
      simp only [fAngle]
      ring)

lemma fAngle_hasDerivAt (B φ : ℝ) : HasDerivAt (fAngle B) (fAngleD B φ) φ := by
  exact (((PHeightTaylor.d1_hasDerivAt (u B φ)).comp φ (u_angle_hasDerivAt B φ)).mul
    (speed_hasDerivAt B φ)).const_sub 1 |>.congr_deriv (by
      simp only [fAngleD,Function.comp_apply]
      ring)

lemma fBB_angle_hasDerivAt (B φ : ℝ) : HasDerivAt (fBB B) (fBBAngle B φ) φ := by
  have hd := ((PHeightTaylor.d2_hasDerivAt (u B φ)).comp φ (u_angle_hasDerivAt B φ)).mul
    ((L_angle_hasDerivAt B φ).pow 2)
  have he := ((((PHeightTaylor.d1_hasDerivAt (u B φ)).comp φ (u_angle_hasDerivAt B φ)).mul
    (Real.hasDerivAt_cos φ)).sub_const h).mul_const (D B)
  exact (hd.sub he).sub_const (2*z) |>.congr_deriv (by
      simp only [fBBAngle,Function.comp_apply,Pi.pow_apply,Nat.cast_ofNat]
      ring)

lemma angle_curvature {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈angles) :
    (1/20:ℝ)<fAngleD B φ := by
  have hu := u_bounds hB hφ
  have hc := PHeightTaylor.curvature_lower
    (show u B φ∈Icc (133/100:ℝ) (17/10) from ⟨by linarith [hu.1],hu.2.le⟩)
  have hd := PHeightTaylor.d2_positive
    (show u B φ∈PHeightBounds.heights from ⟨by linarith [hu.1],by linarith [hu.2]⟩)
  have hm := (MixedCorner.endpoint_mass hB).1
  have hp := mul_nonneg hd.le (sub_nonneg.mpr hm)
  have he := congrArg (fun t : ℝ => PHeightTaylor.d2 (u B φ)*t) (harmonic_circle B φ)
  dsimp [fAngleD,PHeightTaylor.curvature,PHeightTaylor.mass] at *
  nlinarith

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
end
end
end

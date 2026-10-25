module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Frames.Diagonal.Tails
public import SquaresInCircles.Eight.Frames.Pair.Shape
public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds

/-!
# Eight squares: fourth derivatives of the two varying middle/high supports

Both supports use the same affine multiplier and the same two-dimensional
norm identity.  A strict fourth-derivative sign proves concavity of the
second derivative on each complete geometric interval.  The original
folded endpoint, radius, and marker remain literal in the scalar.
-/

section
/-!
## Literal fixed-target supports for the two middle/high orders

The scalar forms are exactly the generic signed diagonal support with
the stated actual source endpoint or source circle.  Only the target
endpoint is fixed.  All derivatives retain the original support constant.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighFixedCalculus
open FramePair FramePairCalculus FrameDiagonalArc FrameDiagonalLabels

def gamma : ℝ := 4463/5000
def K (m n i j : Bool) (l S B : ℝ) : ℝ :=
  9/100+l+sign i*constant m-sign j*marker n B+S
def Cc (before j : Bool) (l B : ℝ) : ℝ :=
  if before then l*(1+A B+sign j*B)-9/100
  else l*(A B+sign j*B-1)+9/100
def Ss (j : Bool) (l B : ℝ) : ℝ := l*(1-A B+sign j*B)-9/100
def F (before m n i j : Bool) (l S B x : ℝ) : ℝ :=
  x+K m n i j l S B+Cc before j l B*Real.cos x+Ss j l B*Real.sin x
def Fd (before j : Bool) (l B x : ℝ) : ℝ :=
  1-Cc before j l B*Real.sin x+Ss j l B*Real.cos x
def Fdd (before j : Bool) (l B x : ℝ) : ℝ :=
  -Cc before j l B*Real.cos x-Ss j l B*Real.sin x
def Fddd (before j : Bool) (l B x : ℝ) : ℝ :=
  Cc before j l B*Real.sin x-Ss j l B*Real.cos x

def middleSource : ℝ := FrameDiagonalSupport.source true false (2/5) b1
def targetB (cut : Bool) : ℝ := if cut then b2 else b1
def mhPlusMinus (x : ℝ) : ℝ :=
  F true true false true false (11/20) (FrameDiagonalSupport.sourceCircle true true (11/20)) b1 x
def mhNegative (x : ℝ) : ℝ := F true true false false false (2/5) middleSource b1 x
def mhOpposite (x : ℝ) : ℝ := F true true false false true (2/5) middleSource 0 x
def hmPositive (x : ℝ) : ℝ :=
  F true false true true true (1/2) (FrameDiagonalSupport.sourceCircle false true (1/2)) b1 x
def hmOpposite (before cut : Bool) (x : ℝ) : ℝ :=
  F before false true false true (2/5) (FrameDiagonalSupport.sourceCircle false false (2/5))
    (targetB cut) x

theorem first_formula (m n i j : Bool) (l S B : ℝ) {x : ℝ}
    (hx : x∈Icc 0 (Real.pi/2)) :
    FrameDiagonalSupport.base m n i j l x+S+FrameDiagonalSupport.target n j l x B=
      F true m n i j l S B x := by
  rw [FrameDiagonalSupport.fixed_target_first m n i j l B S hx]
  dsimp [F,K,Cc,Ss]
  ring

theorem second_formula (m n i j : Bool) (l S B : ℝ) {x : ℝ}
    (hx : x∈Icc (Real.pi/2) Real.pi) :
    FrameDiagonalSupport.base m n i j l x+S+FrameDiagonalSupport.target n j l x B=
      F false m n i j l S B x := by
  rw [FrameDiagonalSupport.fixed_target_second m n i j l B S hx]
  dsimp [F,K,Cc,Ss]
  ring

theorem F_deriv (before m n i j : Bool) (l S B x : ℝ) :
    HasDerivAt (F before m n i j l S B) (Fd before j l B x) x := by
  have h := (((hasDerivAt_id x).add_const (K m n i j l S B)).add
    ((Real.hasDerivAt_cos x).const_mul (Cc before j l B))).add
    ((Real.hasDerivAt_sin x).const_mul (Ss j l B))
  convert h using 1
  · funext y
    simp only [F,id,Pi.add_apply]
  · dsimp only [Fd]
    ring

theorem Fd_deriv (before j : Bool) (l B x : ℝ) :
    HasDerivAt (Fd before j l B) (Fdd before j l B x) x := by
  have h := (((Real.hasDerivAt_sin x).const_mul (-Cc before j l B)).const_add 1).add
    ((Real.hasDerivAt_cos x).const_mul (Ss j l B))
  convert h using 1
  · funext y
    simp only [Fd,Pi.add_apply]
    ring
  · dsimp only [Fdd]
    ring

theorem Fdd_deriv (before j : Bool) (l B x : ℝ) :
    HasDerivAt (Fdd before j l B) (Fddd before j l B x) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul (-Cc before j l B)).sub
    ((Real.hasDerivAt_sin x).const_mul (Ss j l B))
  convert h using 1
  · funext y
    simp only [Fdd,Pi.sub_apply]
  · dsimp only [Fddd]
    ring

theorem endpoint_minimum (before m n i j : Bool) {l S B a b x : ℝ}
    (ha : 0≤a) (hb : b≤Real.pi/2) (hx : x∈Icc a b)
    (hC : 0≤Cc before j l B) (hS : Ss j l B≤0) (hd : Fd before j l B b<0) :
    min (F before m n i j l S B a) (F before m n i j l S B b)≤
      F before m n i j l S B x := by
  apply SecondWord.MinimumCalculus.endpoint_minimum hx
    (fun t _ => F_deriv before m n i j l S B t)
    (fun t _ => Fd_deriv before j l B t) (fun t _ => Fdd_deriv before j l B t) _ hd
  intro t ht
  have hq := FrameLowPair.quadrant ⟨ha.trans ht.1,ht.2.trans hb⟩
  have h1 := mul_nonneg hC hq.1
  have h2 := mul_nonpos_of_nonpos_of_nonneg hS hq.2.2.1
  dsimp [Fddd]
  linarith

theorem concave (before m n i j : Bool) (l S B : ℝ) {a b : ℝ}
    (ha : 0≤a) (hb : b≤Real.pi/2) (hC : 0≤Cc before j l B) (hS : 0≤Ss j l B) :
    ConcaveOn ℝ (Icc a b) (F before m n i j l S B) := by
  apply concave_of_deriv2 (fun x _ => F_deriv before m n i j l S B x)
    (fun x _ => Fd_deriv before j l B x)
  intro x hx
  have ht := FrameLowPair.quadrant ⟨ha.trans hx.1,hx.2.trans hb⟩
  have h1 := mul_nonneg hC ht.2.2.1
  have h2 := mul_nonneg hS ht.1
  dsimp [Fdd]
  linarith

theorem amplitude_monotone (before m n i j : Bool) {l S B : ℝ}
    (hamp : (Cc before j l B)^2+(Ss j l B)^2<1) :
    Monotone (F before m n i j l S B) := by
  intro x y hxy
  have hm : MonotoneOn (F before m n i j l S B) (Icc x y) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z _ => (F_deriv before m n i j l S B z).continuousAt.continuousWithinAt
    · exact fun z _ => F_deriv before m n i j l S B z
    · intro z _
      have hp : Cc before j l B*Real.sin z+(-Ss j l B)*Real.cos z<1 := by
        apply FrameCoreArc.projection_lt (by norm_num : (0:ℝ)<1)
        simpa only [neg_sq,one_pow] using hamp
      dsimp [Fd]
      linarith
  exact hm ⟨le_rfl,hxy⟩ ⟨hxy,le_rfl⟩ hxy

end SquaresInCircles.Eight.FrameMidHighFixedCalculus
end
end
end

section
/-!
## Actual middle-source and high-target support selection

The negative middle source uses a concave support whose second endpoint
is strictly larger.  The target selections use the original signed
coefficient derivatives on the entire closed intrinsic arc.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighSupports
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalSupport
open FrameDiagonalSelection FrameDiagonalTrigonometry FrameDiagonalCuts
open FramePairCalculus

theorem positive_source {b : ℝ} (hb : b∈arc true) :
    source true true (7/20) b1≤ source true true (7/20) b := by
  apply source_first_of_derivative hb
  intro z hz
  have hr := slope_mid_bounds hz
  norm_num [sourceU,sourceV,primary,transverse,sign,k,q]
  linarith [hr.1]

theorem negative_source_endpoints :
    source true false (2/5) b1+(1/2000:ℝ)<source true false (2/5) b2 := by
  dsimp [source,linear,sourceU,sourceV,primary,transverse,sign]
  rw [A_b1,A_b2,b1_eq,b2_eq]
  norm_num [k,q]
  linarith [a1_precise.2,a2_precise.1]

theorem negative_source {b : ℝ} (hb : b∈arc true) :
    source true false (2/5) b1≤ source true false (2/5) b := by
  have he := source_endpoints hb
    (show 0≤ sourceU true false (2/5) by norm_num [sourceU,primary,sign,k])
  change min (source true false (2/5) b1) (source true false (2/5) b2)≤_ at he
  have hc : source true false (2/5) b1≤ source true false (2/5) b2 := by
    linarith [negative_source_endpoints]
  exact (le_min le_rfl hc).trans he

theorem high_target_early {B x : ℝ} (hB : B∈arc false)
    (hx : x∈Icc 0 (61/100:ℝ)) :
    target false false (11/20) x b1≤target false false (11/20) x B := by
  have hxq := rational_quadrant ⟨hx.1,by linarith [hx.2]⟩
  have hD := difference_061_negative hx
  have hw := FrameCoreArc.width_one_le x
  rw [(first_width hxq).1] at hw
  apply target_last_of_coefficients hB
  · norm_num [targetU,primary,sign,u]
    linarith
  · norm_num [targetV,transverse,sign,v]
    linarith

theorem high_target_negative {B x : ℝ} (hB : B∈arc false)
    (hx : x∈Icc (9/10:ℝ) (6/5)) :
    target false false (2/5) x b1≤target false false (2/5) x B := by
  have hC := sum_negative hx
  have hW := weighted_negative hx
  apply target_last_of_derivative hB
  intro z hz
  have hr := slope_high_bounds hz
  by_cases hU : 0≤targetU false false (2/5) x
  · have hp := mul_nonneg hU hr.1
    norm_num [targetU,targetV,primary,transverse,sign,u,v] at hp ⊢
    linarith
  · have hU' : targetU false false (2/5) x≤0 := (lt_of_not_ge hU).le
    have hp := mul_le_mul_of_nonneg_left hr.2.le (neg_nonneg.mpr hU')
    norm_num [targetU,targetV,primary,transverse,sign,u,v] at hp ⊢
    linarith

theorem high_target_opposite {B x : ℝ} (hB : B∈arc false)
    (hx : x∈Icc (1:ℝ) (13/10)) :
    target false true (2/5) x 0≤target false true (2/5) x B := by
  have hD := difference_100_positive hx
  have hC := sum_high hx
  apply target_first_of_coefficients hB
  · norm_num [targetU,primary,sign,u]
    linarith
  · norm_num [targetV,transverse,sign,v]
    linarith

theorem positive_high_source {lam b : ℝ} (hb : b∈arc false)
    (hlam : lam∈Icc (17/50:ℝ) (43/100)) :
    source false true lam 0≤ source false true lam b := by
  apply source_first_of_coefficients hb
  · norm_num [sourceU,primary,sign,u]
    linarith [hlam.1]
  · norm_num [sourceV,transverse,sign,v]
    linarith [hlam.2]

theorem middle_target_positive {B x : ℝ} (hB : B∈arc true)
    (hx : x∈Icc (11/10:ℝ) (71/50)) :
    target true true (1/2) x b1≤target true true (1/2) x B := by
  have hD := difference_110_lower hx
  have hC := sum_target_middle hx
  have ht := FrameLowPair.quadrant
    (rational_quadrant ⟨by linarith [hx.1],hx.2⟩)
  have hU : 0≤targetU true true (1/2) x := by
    norm_num [targetU,primary,sign,k]
    linarith
  have hUb : targetU true true (1/2) x<(1319906/1000000:ℝ) := by
    norm_num [targetU,primary,sign,k]
    linarith
  apply target_first_of_derivative hB
  intro z hz
  have hr := slope_mid_bounds hz
  have hp := mul_le_mul_of_nonneg_left hr.2.le hU
  norm_num [targetU,targetV,primary,transverse,sign,k,q] at hUb hp ⊢
  linarith

theorem middle_target_opposite_endpoints {B x : ℝ} (hB : B∈arc true) :
    min (target true true (2/5) x b1) (target true true (2/5) x b2)≤
      target true true (2/5) x B := by
  apply target_endpoints hB
  have hs := Real.sin_le_one x
  have hc := Real.neg_one_le_cos x
  norm_num [targetU,primary,sign,k]
  linarith

end SquaresInCircles.Eight.FrameMidHighSupports
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighVaryingCalculus
open FramePair FramePairCalculus FrameDiagonalArc FrameDiagonalLabels

def m (i : Bool) : ℝ := if i then 2/5 else 73/200
def origin (i : Bool) : ℝ := if i then 33/50 else 16/25
def left (i : Bool) : ℝ := if i then 1/10 else 2/5
def right (i : Bool) : ℝ := if i then 21/50 else 3/5
def domain (i : Bool) : Set ℝ := Icc (left i) (right i)
def lam (i : Bool) (x : ℝ) : ℝ := origin i-m i*x
def X : ℝ := 1+a2-b2
def Y : ℝ := 1-a2-b2
def N (i : Bool) (x : ℝ) : ℝ :=
  Real.sqrt ((lam i x-sign i*u)^2+(lam i x-v)^2)
def Delta (i : Bool) : ℝ := (m i)^2*(v-sign i*u)^2
def T (i : Bool) (x : ℝ) : ℝ := m i*(sign i*u+v-2*lam i x)
def N1 (i : Bool) (x : ℝ) : ℝ := T i x/N i x
def N2 (i : Bool) (x : ℝ) : ℝ := Delta i/(N i x)^3
def N3 (i : Bool) (x : ℝ) : ℝ := -3*Delta i*T i x/(N i x)^5
def N4 (i : Bool) (x : ℝ) : ℝ :=
  3*Delta i*(4*(T i x)^2-Delta i)/(N i x)^7

def F (i : Bool) (x : ℝ) : ℝ :=
  x+9/100+M2+2*lam i x-sign i*u*R+
    (lam i x*X-9/100)*Real.cos x+(lam i x*Y-9/100)*Real.sin x-R*N i x
def Fd (i : Bool) (x : ℝ) : ℝ :=
  1-2*m i+(lam i x*Y-9/100-m i*X)*Real.cos x+
    (-lam i x*X+9/100-m i*Y)*Real.sin x-R*N1 i x
def Fdd (i : Bool) (x : ℝ) : ℝ :=
  (-lam i x*X+9/100-2*m i*Y)*Real.cos x+
    (-lam i x*Y+9/100+2*m i*X)*Real.sin x-R*N2 i x
def Fddd (i : Bool) (x : ℝ) : ℝ :=
  (-lam i x*Y+9/100+3*m i*X)*Real.cos x+
    (lam i x*X-9/100+3*m i*Y)*Real.sin x-R*N3 i x
def Fdddd (i : Bool) (x : ℝ) : ℝ :=
  (lam i x*X-9/100+4*m i*Y)*Real.cos x+
    (lam i x*Y-9/100-4*m i*X)*Real.sin x-R*N4 i x

theorem endpoint_order (i : Bool) : left i<right i := by cases i <;> norm_num [left,right]
theorem left_mem (i : Bool) : left i∈domain i := ⟨le_rfl,(endpoint_order i).le⟩
theorem right_mem (i : Bool) : right i∈domain i := ⟨(endpoint_order i).le,le_rfl⟩

theorem domain_quadrant {i : Bool} {x : ℝ} (hx : x∈domain i) :
    x∈Icc 0 (Real.pi/2) := by
  cases i <;> dsimp [domain,left,right] at hx <;>
    constructor <;> linarith [hx.1,hx.2,FrameLowPair.pi_lower]

theorem m_bounds (i : Bool) : (73/200:ℝ)≤ m i ∧ m i≤2/5 := by
  cases i <;> norm_num [m]
theorem transverse_positive (i : Bool) : 0<v-sign i*u := by
  cases i <;> norm_num [sign,u,v]
theorem Delta_pos (i : Bool) : 0<Delta i := by
  exact mul_pos (sq_pos_of_pos (by linarith [(m_bounds i).1]))
    (sq_pos_of_pos (transverse_positive i))

theorem multiplier_bounds {i : Bool} {x : ℝ} (hx : x∈domain i) :
    (421/1000:ℝ)≤lam i x ∧ lam i x≤31/50 ∧
      0<2*lam i x-sign i*u-v ∧ 0<4*lam i x-sign i*u-3*v := by
  obtain ⟨h1,h2⟩ := hx
  cases i <;> dsimp [domain,left,right,lam,origin,m,sign,u,v] at * <;>
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem endpoint_coefficients :
    0<X ∧ X<(33/20:ℝ) ∧ Y< -(1597/1000:ℝ) := by
  rw [X,Y,b2_eq]
  have h := a2_precise
  exact ⟨by linarith [h.1],by linarith [h.2],by linarith [h.1]⟩

theorem N_energy_pos (i : Bool) (x : ℝ) :
    0<(lam i x-sign i*u)^2+(lam i x-v)^2 := by
  have hgap := sq_pos_of_pos (transverse_positive i)
  nlinarith [sq_nonneg (2*lam i x-sign i*u-v)]

theorem N_pos (i : Bool) (x : ℝ) : 0<N i x := Real.sqrt_pos.mpr (N_energy_pos i x)
theorem N_sq (i : Bool) (x : ℝ) :
    (N i x)^2=(lam i x-sign i*u)^2+(lam i x-v)^2 :=
  Real.sq_sqrt (N_energy_pos i x).le

theorem norm_identity (i : Bool) (x : ℝ) :
    2*(m i)^2*(N i x)^2-(T i x)^2=Delta i := by
  rw [N_sq]
  dsimp [T,Delta]
  ring

theorem lam_deriv (i : Bool) (x : ℝ) : HasDerivAt (lam i) (-m i) x := by
  have h := (hasDerivAt_const x (origin i)).fun_sub ((hasDerivAt_id x).const_mul (m i))
  convert h using 1
  · funext y
    simp only [lam,id]
  · ring

theorem T_deriv (i : Bool) (x : ℝ) : HasDerivAt (T i) (2*(m i)^2) x := by
  have h := ((hasDerivAt_const x (sign i*u+v)).fun_sub
    ((lam_deriv i x).const_mul 2)).const_mul (m i)
  convert h using 1
  · funext y
    simp only [T]
  · ring

theorem N_deriv (i : Bool) (x : ℝ) : HasDerivAt (N i) (N1 i x) x := by
  have hd := (((lam_deriv i x).sub_const (sign i*u)).pow 2).add
    (((lam_deriv i x).sub_const v).pow 2)
  convert hd.sqrt (N_energy_pos i x).ne' using 1
  · rfl
  · dsimp [N1,T,N]
    ring

theorem N1_deriv (i : Bool) (x : ℝ) : HasDerivAt (N1 i) (N2 i x) x := by
  have hd := (T_deriv i x).div (N_deriv i x) (N_pos i x).ne'
  convert hd using 1
  · rfl
  · dsimp [N1,N2]
    field_simp [(N_pos i x).ne']
    nlinarith only [norm_identity i x]

theorem N2_deriv (i : Bool) (x : ℝ) : HasDerivAt (N2 i) (N3 i x) x := by
  have hd := (hasDerivAt_const x (Delta i)).div ((N_deriv i x).pow 3)
    (pow_ne_zero 3 (N_pos i x).ne')
  convert hd using 1
  · rfl
  · dsimp [N1,N2,N3]
    field_simp [(N_pos i x).ne']
    ring

theorem N3_deriv (i : Bool) (x : ℝ) : HasDerivAt (N3 i) (N4 i x) x := by
  have hd := ((T_deriv i x).const_mul (-3*Delta i)).div
    ((N_deriv i x).pow 5) (pow_ne_zero 5 (N_pos i x).ne')
  convert hd using 1
  · rfl
  · simp only [N1,N4,Pi.pow_apply]
    field_simp [(N_pos i x).ne']
    linear_combination Delta i*(N i x)^4*norm_identity i x

theorem N4_positive {i : Bool} {x : ℝ} (hx : x∈domain i) : 0<N4 i x := by
  have hh := multiplier_bounds hx
  have hgap := transverse_positive i
  have hsq : (v-sign i*u)^2<4*(2*lam i x-sign i*u-v)^2 := by
    nlinarith
  have hm := mul_lt_mul_of_pos_left hsq
    (sq_pos_of_pos (by linarith [(m_bounds i).1] : 0< m i))
  have hnum : 0<4*(T i x)^2-Delta i := by dsimp [T,Delta]; nlinarith only [hm]
  exact div_pos (mul_pos (mul_pos (by norm_num) (Delta_pos i)) hnum)
    (pow_pos (N_pos i x) 7)

theorem F_deriv (i : Bool) (x : ℝ) : HasDerivAt (F i) (Fd i x) x := by
  have hbase := ((((hasDerivAt_id x).add_const (9/100)).add_const M2).add
    ((lam_deriv i x).const_mul 2)).sub_const (sign i*u*R)
  have hc := (((lam_deriv i x).mul_const X).sub_const (9/100)).mul
    (Real.hasDerivAt_cos x)
  have hs := (((lam_deriv i x).mul_const Y).sub_const (9/100)).mul
    (Real.hasDerivAt_sin x)
  convert ((hbase.add hc).add hs).sub ((N_deriv i x).const_mul R) using 1
  · funext y
    simp only [F,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,id]
  · simp only [Fd,N1]
    ring

theorem Fd_deriv (i : Bool) (x : ℝ) : HasDerivAt (Fd i) (Fdd i x) x := by
  have hc := ((((lam_deriv i x).mul_const Y).sub_const (9/100)).sub_const (m i*X)).mul
    (Real.hasDerivAt_cos x)
  have hl := (((lam_deriv i x).mul_const X).neg).add_const (9/100)
  have hs := (hl.sub_const (m i*Y)).mul (Real.hasDerivAt_sin x)
  convert (((hasDerivAt_const x (1-2*m i)).add hc).add hs).sub
    ((N1_deriv i x).const_mul R) using 1
  · funext y
    simp only [Fd,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.neg_apply]
    ring
  · simp only [Fdd,Pi.neg_apply]
    ring

theorem Fdd_deriv (i : Bool) (x : ℝ) : HasDerivAt (Fdd i) (Fddd i x) x := by
  have hlc := (((lam_deriv i x).mul_const X).neg).add_const (9/100)
  have hc := (hlc.sub_const (2*m i*Y)).mul (Real.hasDerivAt_cos x)
  have hls := (((lam_deriv i x).mul_const Y).neg).add_const (9/100)
  have hs := (hls.add_const (2*m i*X)).mul (Real.hasDerivAt_sin x)
  convert (hc.add hs).sub ((N2_deriv i x).const_mul R) using 1
  · funext y
    simp only [Fdd,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.neg_apply]
    ring
  · simp only [Fddd,Pi.neg_apply]
    ring

theorem Fddd_deriv (i : Bool) (x : ℝ) : HasDerivAt (Fddd i) (Fdddd i x) x := by
  have hlc := (((lam_deriv i x).mul_const Y).neg).add_const (9/100)
  have hc := (hlc.add_const (3*m i*X)).mul (Real.hasDerivAt_cos x)
  have hls := ((lam_deriv i x).mul_const X).sub_const (9/100)
  have hs := (hls.add_const (3*m i*Y)).mul (Real.hasDerivAt_sin x)
  convert (hc.add hs).sub ((N3_deriv i x).const_mul R) using 1
  · funext y
    simp only [Fddd,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.neg_apply]
    ring
  · simp only [Fdddd,Pi.neg_apply]
    ring

theorem fourth_negative {i : Bool} {x : ℝ} (hx : x∈domain i) : Fdddd i x<0 := by
  have hcoeff := endpoint_coefficients
  have hmult := multiplier_bounds hx
  have hm := m_bounds i
  have htrig := FrameLowPair.quadrant (domain_quadrant hx)
  have hlamX := mul_le_mul hmult.2.1 hcoeff.2.1.le hcoeff.1.le (by norm_num : (0:ℝ)≤31/50)
  have hmY := mul_le_mul_of_nonpos_right hm.1 (by linarith [hcoeff.2.2] : Y≤0)
  have hc : lam i x*X-9/100+4*m i*Y<0 := by nlinarith [hcoeff.2.2]
  have hlamY : lam i x*Y≤0 := mul_nonpos_of_nonneg_of_nonpos
    (by linarith [hmult.1]) (by linarith [hcoeff.2.2])
  have hmX := mul_pos (by linarith [hm.1] : 0< m i) hcoeff.1
  have hs : lam i x*Y-9/100-4*m i*X<0 := by linarith
  have hcos := mul_nonpos_of_nonpos_of_nonneg hc.le htrig.2.2.1
  have hsin := mul_nonpos_of_nonpos_of_nonneg hs.le htrig.1
  have hnorm := mul_pos R_pos (N4_positive hx)
  dsimp [Fdddd]
  linarith

theorem second_concave (i : Bool) : ConcaveOn ℝ (domain i) (Fdd i) := by
  exact concave_of_deriv2 (fun x _ => Fdd_deriv i x)
    (fun x _ => Fddd_deriv i x) (fun x hx => (fourth_negative hx).le)

end SquaresInCircles.Eight.FrameMidHighVaryingCalculus
end
end
end

module

public import SquaresInCircles.Eight.Frames.Diagonal.Support
public import SquaresInCircles.Eight.Words.Second.Outer.MinimumCalculus

/-!
# Eight squares: literal fixed-target supports for the two middle/high orders

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

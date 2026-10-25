module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsCharges

/-!
# The exact full-support alternatives at the A and T endpoints

Uncompiled transcription of equations (12)--(19) and (40)--(43).
The only weakening is the stated replacement of D's clipped support by
full support. The original A and E support charges remain separate.
Each scalar index records which norm retains the entire negative total.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Analytic
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus

def fullBaseline (k l c z : ℝ) : ℝ :=
  k+2*l+PositiveTD.tilted c z+c*edgeWidth z+2-c*PositiveTD.sigma*Real.sin z-
    fullSupport 1 k-fullSupport l k-fullSupport (PositiveTD.tilted c z) l-fullSupport 1 c

def negative (k l m t : ℝ) : Fin 3→ℝ :=
  ![V R k 1 t,V R k l t,V R (min l m) (max l m) t]

def largeScalar (k l c theta e a : ℝ) (i : Fin 3) : ℝ :=
  fullBaseline k l c (theta-a)+l*TwoPositive.ASupport.charge a+
    TwoPositive.ASupport.charge e+negative k l (PositiveTD.tilted c (theta-a)) (theta+e) i

def aAt : Endpoint→ℝ→ℝ | .atA,t => t | .atT,_ => 0
def zAt : Endpoint→ℝ→ℝ | .atA,_ => 0 | .atT,t => t
def mAt (ep : Endpoint) (c theta : ℝ) : ℝ := PositiveTD.tilted c (zAt ep theta)

def endpoint (r : Region) (ep : Endpoint) (i : Fin 3) (x y : ℝ) : ℝ :=
  largeScalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
    (Explicit.theta r x y) (Explicit.e r x y) (aAt ep (Explicit.theta r x y)) i

def pAt (r : Region) (x y : ℝ) : Fin 4→ℝ :=
  ![Explicit.k r x y,Explicit.k r x y,Explicit.l r x y,Explicit.c r x y]
def qAt (r : Region) (ep : Endpoint) (x y : ℝ) : Fin 4→ℝ :=
  ![1,Explicit.l r x y,mAt ep (Explicit.c r x y) (Explicit.theta r x y),1]
def largeCoefficient (r : Region) (ep : Endpoint) (x y : ℝ) : Fin 3→ℝ :=
  ![1,Explicit.l r x y,max (Explicit.l r x y) (mAt ep (Explicit.c r x y) (Explicit.theta r x y))]
def normAt (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4) (x y : ℝ) : ℝ :=
  pairNorm (pAt r x y j) (qAt r ep x y j)
    (if j.val=i.val then -Explicit.delta r x y else 0)

def nonradicalBase (r : Region) (ep : Endpoint) (x y : ℝ) : ℝ :=
  match ep with
  | .atA => 2*Explicit.k r x y+3*Explicit.l r x y+3*Explicit.c r x y+3+
      Explicit.l r x y*TwoPositive.ASupport.charge (Explicit.theta r x y)+
        TwoPositive.ASupport.charge (Explicit.e r x y)
  | .atT => 2*Explicit.k r x y+3*Explicit.l r x y+3+
      Explicit.c r x y*(1+2*Real.cos (Explicit.theta r x y)+
        ((3/2)*PositiveTD.eta+1/2-PositiveTD.sigma)*Real.sin (Explicit.theta r x y))+
          TwoPositive.ASupport.charge (Explicit.e r x y)

def nonradical (r : Region) (ep : Endpoint) (i : Fin 3) (x y : ℝ) : ℝ :=
  nonradicalBase r ep x y+largeCoefficient r ep x y i*(Real.cos (Explicit.delta r x y)-1)

theorem aAt_domain (ep : Endpoint) {t : ℝ} (ht : t∈Icc 0 frameCap) :
    aAt ep t∈Icc 0 t := by
  cases ep <;> simp only [aAt] <;> constructor <;> linarith [ht.1]

theorem zAt_domain (ep : Endpoint) {t : ℝ} (ht : t∈Icc 0 frameCap) :
    zAt ep t∈Icc 0 t := by
  cases ep <;> simp only [zAt] <;> constructor <;> linarith [ht.1]

theorem split_identity (ep : Endpoint) (t : ℝ) : t-aAt ep t=zAt ep t := by
  cases ep <;> simp [aAt,zAt]

theorem pairNorm_min_max (p q t : ℝ) : pairNorm (min p q) (max p q) t=pairNorm p q t := by
  rcases le_total p q with h|h
  · simp [min_eq_left h,max_eq_right h]
  · simp [min_eq_right h,max_eq_left h,pairNorm_symm]

theorem negative_identity (k l m t : ℝ) (i : Fin 3) :
    negative k l m t i=(![1,l,max l m] i)*(Real.cos t-1)-
      R*(pairNorm (![k,k,l] i) (![1,l,m] i) (-t)-
        pairNorm (![k,k,l] i) (![1,l,m] i) 0) := by
  fin_cases i
  · change V R k 1 t=(1:ℝ)*(Real.cos t-1)-R*(pairNorm k 1 (-t)-pairNorm k 1 0)
    simp only [V]
  · change V R k l t=l*(Real.cos t-1)-R*(pairNorm k l (-t)-pairNorm k l 0)
    simp only [V]
  · change V R (min l m) (max l m) t=max l m*(Real.cos t-1)-
      R*(pairNorm l m (-t)-pairNorm l m 0)
    simp only [V,pairNorm_min_max]

/-- The common full-support baseline is weaker than the already proved
clipped-D baseline, not an asserted identity between those supports. -/
theorem fullBaseline_le (k l c z : ℝ) : fullBaseline k l c z≤PositiveTD.baseline k l c z := by
  have hs : clippedSupport 1 c≤fullSupport 1 c := by
    unfold clippedSupport
    split_ifs
    · have hh := raw_full_support (a:=GlobalGA.Secondary.diagonal) (b:=GlobalGA.Secondary.diagonal) (f:=(1:ℝ)) (g:=c)
        (by nlinarith [diagonal_circle])
      simpa [diagonalSupport,add_mul] using hh
    · exact le_rfl
  dsimp [fullBaseline,PositiveTD.baseline]
  linarith

theorem fullBaseline_norms (k l c z : ℝ) :
    fullBaseline k l c z=2*k+3*l+(3/2)*PositiveTD.tilted c z+
      c*(edgeWidth z+1/2)+3-c*PositiveTD.sigma*Real.sin z-
        R*(pairNorm k 1 0+pairNorm k l 0+
          pairNorm l (PositiveTD.tilted c z) 0+pairNorm c 1 0) := by
  rw [fullBaseline,fullSupport_pair k 1,fullSupport_pair k l,
    fullSupport_pair l (PositiveTD.tilted c z),fullSupport_pair c 1]
  ring

theorem endpoint_identity (r : Region) (ep : Endpoint) (i : Fin 3)
    {x y : ℝ} (hd : Explicit.Domain r x y) :
    endpoint r ep i x y=nonradical r ep i x y-
      R*(normAt r ep i 0 x y+normAt r ep i 1 x y+
        normAt r ep i 2 x y+normAt r ep i 3 x y) := by
  have hθ := (Explicit.domains hd).1
  unfold endpoint largeScalar
  rw [split_identity,fullBaseline_norms,negative_identity]
  cases ep <;> fin_cases i <;>
    simp only [aAt,zAt,mAt,nonradical,nonradicalBase,largeCoefficient,
      normAt,pAt,qAt,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.reduceFinMk,ite_true,ite_false,PositiveTD.tilted,Real.cos_zero,
      Real.sin_zero,mul_one,mul_zero,add_zero,TwoPositive.ASupport.charge_zero,
      edgeWidth_zero]
  all_goals
    try rw [edgeWidth_positive_formula hθ]
    dsimp [Explicit.delta]
    ring

theorem norm_nonnegative (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4) (x y : ℝ) :
    0≤normAt r ep i j x y := Real.sqrt_nonneg _

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Analytic

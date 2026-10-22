module

public import SquaresInCircles.Eight.TableFree.TwoVariablePolynomial
public import SquaresInCircles.Eight.TableFree.GlobalGAChargeSubadditive
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDScalarBounds

/-!
# The two continuous weight families for nonnegative A and E totals

Uncompiled transcription of Sections 4--5 of
`HAND_G3_NONNEGATIVE_A_E_TOTALS_TD0_OR_POSITIVE_TD2_EXCLUSION.md`.
Native triangle coordinates are `(theta-1/6,e)`.  Native rectangle
coordinates are `(1/6-theta,theta+e-1/6)`.  Every displayed decimal in the
hand proof is represented here by its exact rational value.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals
open TensorWholeIntervalPolynomial

inductive Region | triangle | rectangle deriving DecidableEq
inductive Endpoint | atA | atT deriving DecidableEq

namespace Explicit

def Domain : Region → ℝ → ℝ → Prop
  | .triangle,x,y => 0≤x ∧ 0≤y ∧ x+y≤8/15
  | .rectangle,x,y => x∈Icc 0 (1/6) ∧ y∈Icc 0 (8/15)

def theta : Region → ℝ → ℝ → ℝ
  | .triangle,x,_ => 1/6+x
  | .rectangle,x,_ => 1/6-x

def e : Region → ℝ → ℝ → ℝ
  | .triangle,_,y => y
  | .rectangle,x,y => x+y

def delta (r : Region) (x y : ℝ) : ℝ := theta r x y+e r x y

def k : Region → ℝ → ℝ → ℝ
  | .triangle,t,e => 1673/2500+2609/5000*t-1489/2500*t^2+527/1250*t^3+7/25*e
  | .rectangle,x,y => 1673/2500+9/50*x+7/25*y

def l : Region → ℝ → ℝ → ℝ
  | .triangle,t,e => 1+7/400*t-2733/2500*t^2+639/500*t^3+1/4*e
  | .rectangle,x,y => 1+1/4*(x+y)

def c : Region → ℝ → ℝ → ℝ
  | .triangle,t,e => 10163/10000-209/10000*t-5743/5000*t^2+14069/10000*t^3+1/4*e
  | .rectangle,x,y => 10163/10000+1/4*(x+y)

def qStar (r : Region) (x y : ℝ) : ℝ :=
  l r x y+3/20*(8/15-x)

theorem domains {r : Region} {x y : ℝ} (h : Domain r x y) :
    theta r x y∈Icc 0 Secondary.frameCap ∧
    e r x y∈Icc 0 Secondary.frameCap ∧
    delta r x y∈Icc (1/6) Secondary.frameCap := by
  cases r <;> dsimp [Domain,theta,e,delta,Secondary.frameCap] at * <;>
    rcases h with ⟨h0,h1,h2⟩ <;> constructor
  · constructor <;> linarith
  · constructor <;> constructor <;> linarith
  · constructor <;> linarith [h0.1,h0.2]
  · constructor <;> constructor <;> linarith [h0.1,h0.2,h1,h2]

theorem coordinates {theta e : ℝ} (ht : 0≤theta) (he : 0≤e)
    (hs : theta+e∈Icc (1/6) Secondary.frameCap) :
    ∃ r x y,Domain r x y ∧ Explicit.theta r x y=theta ∧ Explicit.e r x y=e := by
  by_cases hL : 1/6≤theta
  · refine ⟨.triangle,theta-1/6,e,?_,?_,rfl⟩
    · dsimp [Domain,Secondary.frameCap] at *
      exact ⟨by linarith,he,by linarith [hs.2]⟩
    · simp [Explicit.theta]
  · refine ⟨.rectangle,1/6-theta,theta+e-1/6,?_,?_,?_⟩
    · dsimp [Domain,Secondary.frameCap] at *
      exact ⟨⟨by linarith,by linarith⟩,⟨by linarith [hs.1],by linarith [hs.2]⟩⟩
    · simp [Explicit.theta]
    · dsimp [Explicit.e]; ring

end Explicit

namespace Certificate
open TwoVariablePolynomial

def theta : Region → Bivar
  | .triangle => scalar (1/6)+X
  | .rectangle => scalar (1/6)-X

def e : Region → Bivar
  | .triangle => C X
  | .rectangle => X+C X

def delta (r : Region) : Bivar := theta r+e r

def k : Region → Bivar
  | .triangle => scalar (1673/2500)+scalar (2609/5000)*X-
      scalar (1489/2500)*X^2+scalar (527/1250)*X^3+scalar (7/25)*C X
  | .rectangle => scalar (1673/2500)+scalar (9/50)*X+scalar (7/25)*C X

def l : Region → Bivar
  | .triangle => 1+scalar (7/400)*X-scalar (2733/2500)*X^2+
      scalar (639/500)*X^3+scalar (1/4)*C X
  | .rectangle => 1+scalar (1/4)*(X+C X)

def c : Region → Bivar
  | .triangle => scalar (10163/10000)-scalar (209/10000)*X-
      scalar (5743/5000)*X^2+scalar (14069/10000)*X^3+scalar (1/4)*C X
  | .rectangle => scalar (10163/10000)+scalar (1/4)*(X+C X)

def qStar (r : Region) : Bivar := l r+scalar (3/20)*(scalar (8/15)-X)

def Rbar : ℚ := 494696877/250000000

def abar : ℚ := 176821959/125000000

def sigmabar : ℚ := 1415477291/1000000000

def J (u : Bivar) : Bivar :=
  scalar (1/2)*(lift u PositiveTD.Certificate.C10-1)+
    scalar (1/2-abar)*lift u PositiveTD.Certificate.S9

def jTheta : Region → Bivar
  | .triangle => J (theta .triangle)-scalar (43/500)*X^4
  | .rectangle => J (theta .rectangle)

def jE : Region → Bivar
  | .triangle => J (e .triangle)-scalar (1/500)*(e .triangle)^4
  | .rectangle => J (e .rectangle)-scalar (29/1000)*(e .rectangle)^4

def M (r : Region) : Endpoint → Bivar
  | .atA => c r
  | .atT => c r*(lift (theta r) PositiveTD.Certificate.C12+
      scalar (293/1000)*lift (theta r) PositiveTD.Certificate.S9)

def ABase (r : Region) : Endpoint → Bivar
  | .atA => scalar 2*k r+scalar 3*l r+scalar 3*c r+scalar 3+
      l r*jTheta r+jE r
  | .atT => scalar 2*k r+scalar 3*l r+scalar 3+
      c r*(1+scalar 2*lift (theta r) PositiveTD.Certificate.C10+
        scalar ((3/2)*(293/1000)+1/2-sigmabar)*
          lift (theta r) PositiveTD.Certificate.S9)+jE r

def qB (r : Region) (ep : Endpoint) : Bivar :=
  match r with
  | .triangle => qStar r
  | .rectangle => M r ep

/-- H, G, B are the three intrinsic negative-block alternatives. -/
def A (r : Region) (ep : Endpoint) (i : Fin 3) : Bivar :=
  ABase r ep+(![1,l r,qB r ep] i)*
    (lift (delta r) PositiveTD.Certificate.C10-1)

def baseNorm (r : Region) (ep : Endpoint) : Fin 4 → Bivar :=
  ![1+(k r)^2,(k r)^2+(l r)^2,(l r)^2+(M r ep)^2,1+(c r)^2]

def P (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4) : Bivar :=
  baseNorm r ep j-
    if j.val=i.val then scalar 2*(![k r,k r*l r,l r*M r ep,0] j)*
      lift (delta r) PositiveTD.Certificate.S11 else 0

def rho (ep : Endpoint) (i : Fin 3) (j : Fin 4) : ℚ :=
  if j.val=i.val then
    if j=2 then match ep with
      | .atA => 81386069/62500000
      | .atT => 1325511353/1000000000
    else 27678887/25000000
  else if j=2 then match ep with
    | .atA => 142578599/100000000
    | .atT => 1451171531/1000000000
  else if j=3 then 142578599/100000000
  else 150407189/125000000

def mass (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4) : Bivar :=
  cubicMass (rho ep i j) (P r ep i j)

def numerator (r : Region) (ep : Endpoint) (i : Fin 3) : Bivar :=
  let w := mass r ep i
  scalar 2*A r ep i*w 0*w 1*w 2*w 3-scalar Rbar*
    ((P r ep i 0+(w 0)^2)*w 1*w 2*w 3+
      (P r ep i 1+(w 1)^2)*w 0*w 2*w 3+
      (P r ep i 2+(w 2)^2)*w 0*w 1*w 3+
      (P r ep i 3+(w 3)^2)*w 0*w 1*w 2)

def degree (r : Region) (ep : Endpoint) (i : Fin 3) : ℕ :=
  match r,ep with
  | .triangle,.atA => if i=0 then 25 else 26
  | .triangle,.atT => 39
  | .rectangle,.atA => 23
  | .rectangle,.atT => 35

def transform (r : Region) (p : Bivar) : Bivar :=
  match r with
  | .triangle => triangle (8/15) p
  | .rectangle => rectangle (1/6) (8/15) p

def lowerOn (r : Region) (D : ℕ) (p : Bivar) : ℚ :=
  lower D (coefficient D (transform r p))

def upperOn (r : Region) (D : ℕ) (p : Bivar) : ℚ :=
  TwoVariablePolynomial.upper D (coefficient D (transform r p))

@[simp] theorem evaluate_theta (r : Region) (x y : ℝ) :
    evaluate x y (theta r)=Explicit.theta r x y := by
  cases r <;> simp [theta,Explicit.theta]

@[simp] theorem evaluate_e (r : Region) (x y : ℝ) :
    evaluate x y (e r)=Explicit.e r x y := by
  cases r <;> simp [e,Explicit.e]

@[simp] theorem evaluate_delta (r : Region) (x y : ℝ) :
    evaluate x y (delta r)=Explicit.delta r x y := by
  simp [delta,Explicit.delta]

@[simp] theorem evaluate_k (r : Region) (x y : ℝ) :
    evaluate x y (k r)=Explicit.k r x y := by
  cases r <;> simp [k,Explicit.k]

@[simp] theorem evaluate_l (r : Region) (x y : ℝ) :
    evaluate x y (l r)=Explicit.l r x y := by
  cases r <;> simp [l,Explicit.l]

@[simp] theorem evaluate_c (r : Region) (x y : ℝ) :
    evaluate x y (c r)=Explicit.c r x y := by
  cases r <;> simp [c,Explicit.c]

@[simp] theorem evaluate_qStar (r : Region) (x y : ℝ) :
    evaluate x y (qStar r)=Explicit.qStar r x y := by
  simp [qStar,Explicit.qStar]

theorem domain_bounds {r : Region} {D : ℕ} {p : Bivar}
    (hid : transform r p=expansion D (transform r p))
    {x y : ℝ} (h : Explicit.Domain r x y) :
    (lowerOn r D p:ℝ)≤evaluate x y p ∧
      evaluate x y p≤(upperOn r D p:ℝ) := by
  cases r with
  | triangle => exact triangle_bounds (by norm_num) hid h.1 h.2.1 h.2.2
  | rectangle => exact rectangle_bounds (by norm_num) (by norm_num) hid h.1 h.2

theorem positive_on_domain {r : Region} {D : ℕ} {p : Bivar} {reserve : ℚ}
    (hid : transform r p=expansion D (transform r p))
    (hlo : reserve<lowerOn r D p)
    {x y : ℝ} (h : Explicit.Domain r x y) : (reserve:ℝ)<evaluate x y p := by
  have hc : (reserve:ℝ)<(lowerOn r D p:ℝ) := by exact_mod_cast hlo
  exact hc.trans_le (domain_bounds hid h).1

theorem upper_on_domain {r : Region} {D : ℕ} {p : Bivar} {reserve : ℚ}
    (hid : transform r p=expansion D (transform r p))
    (hhi : upperOn r D p<reserve)
    {x y : ℝ} (h : Explicit.Domain r x y) : evaluate x y p<(reserve:ℝ) := by
  have hc : (upperOn r D p:ℝ)<(reserve:ℚ) := by exact_mod_cast hhi
  exact (domain_bounds hid h).2.trans_lt hc

end Certificate
end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals

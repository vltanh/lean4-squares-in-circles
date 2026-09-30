import SquaresInCircles.Six.Stress.VertexEnvelope
import SquaresInCircles.Six.ProofTools.SmoothCalculus

/-!
# Exact expressions for the common pair lower bound

The constants are the candidate radicals, not rounded replacements. Outside a
small square the exact cap/vertex pair value is checked directly. Inside that
square six sign sectors use the universally valid smooth vertex upper support.
The sector derivative check carries its regularity conditions in the formula.
-/

namespace SquaresInCircles.Six.Stress.PairCertificate
open ProofTools Normalization

abbrev sr {n : ℕ} (q : ℚ) : Smooth n := .rat q
abbrev er {n : ℕ} (q : ℚ) : Expr n := .rat q

def hE {n : ℕ} : Smooth n := .sqrt 2/2
def AE {n : ℕ} : Smooth n := (1466+1940*hE)/267
def BE {n : ℕ} : Smooth n := (327+432*hE)/712
def sE {n : ℕ} : Smooth n := 2*BE/(AE+.sqrt (AE*AE-4*BE))
def tE {n : ℕ} : Smooth n := (-20+30*hE)*sE+sr (7/2)-sr (9/2)*hE
def qE {n : ℕ} : Smooth n := 2*sE*sE+4*sE+sr (5/2)
def radiusE {n : ℕ} : Smooth n := .sqrt qE
def rhoE {n : ℕ} : Smooth n := .sqrt (qE-sr (1/4))-sr (1/2)
def rE {n : ℕ} : Smooth n := (sE+sr (1/2))/(sE+sr (3/2))
def mE {n : ℕ} : Smooth n := (1+rE)*(tE+sr (1/2))/(sr (3/2)-sE)
def baseE {n : ℕ} : Smooth n := mE*(sr (1/2)-tE)

def alphaE {k : ℕ} (no wo : Bool) (n w : Smooth k) : Smooth k :=
  if no then
    if wo then (.cos w+.sin w)/.cos (w-n) else 1/.cos n
  else if wo then (.cos w+.sin w)/.cos w else 1

def gammaE {k : ℕ} (no wo : Bool) (n w : Smooth k) : Smooth k :=
  if no then
    if wo then (.cos n-.sin n)/.cos (w-n) else (.cos n-.sin n)/.cos n
  else if wo then 1/.cos w else 1

def northBaseE {k : ℕ} (own : Bool) (n : Smooth k) : Smooth k × Smooth k :=
  if own then (1,0) else (.cos n,-.sin n)

def westBaseE {k : ℕ} (own : Bool) (w : Smooth k) : Smooth k × Smooth k :=
  if own then (1,0) else (.cos w,-.sin w)

def northSourceE {k : ℕ} (u : Fin 4) (q : Smooth k) : Smooth k × Smooth k :=
  ![(-.sin q,-.cos q),(.cos q,-.sin q),(1,0),(0,-1)] u

def westSourceE {k : ℕ} (u : Fin 4) (q : Smooth k) : Smooth k × Smooth k :=
  ![(1,0),(0,1),(-.sin q,.cos q),(.cos q,.sin q)] u

def northForceE {k : ℕ} (no wo : Bool) (u : Fin 4) (n w : Smooth k) : Smooth k × Smooth k :=
  (alphaE no wo n w*(northBaseE no n).1+rE*(northSourceE u (n-w)).1,
   alphaE no wo n w*(northBaseE no n).2+rE*(northSourceE u (n-w)).2)

def westForceE {k : ℕ} (no wo : Bool) (u : Fin 4) (n w : Smooth k) : Smooth k × Smooth k :=
  (gammaE no wo n w*(westBaseE wo w).1+rE*(westSourceE u (n-w)).1,
   gammaE no wo n w*(westBaseE wo w).2+rE*(westSourceE u (n-w)).2-mE)

def thresholdE {k : ℕ} (no wo : Bool) (n w : Smooth k) : Expr k :=
  (alphaE no wo n w).expr*(er (1/2)+Certificates.widthE n.expr)+
    (gammaE no wo n w).expr*(er (1/2)+Certificates.widthE w.expr)+
    (rE : Smooth k).expr*(er (1/2)+Certificates.widthE (n-w).expr)+(mE : Smooth k).expr/2

def lineE {k : ℕ} (x : Expr k) : Expr k := er (73/100)*.max (-x) 0-er (13/50)*.max x 0

def pairE {k : ℕ} (no wo : Bool) (u : Fin 4) (n w : Smooth k) : Expr k :=
  thresholdE no wo n w-
    Reified.support (radiusE : Smooth k).expr (northForceE no wo u n w).1.expr
      (northForceE no wo u n w).2.expr-
    Reified.support (radiusE : Smooth k).expr (westForceE no wo u n w).1.expr
      (westForceE no wo u n w).2.expr

def gapE (no wo : Bool) (u : Fin 4) : Expr 2 :=
  pairE no wo u (.var 0) (.var 1)-(baseE : Smooth 2).expr-
    lineE (.var 1)-er (1/1000)*.abs (.var 0)

def root : RBox 2 := ![⟨-3/10,5/12⟩,⟨-11/25,2/5⟩]
def localRoot : RBox 2 := fun _ => ⟨0,1/128⟩

def localSquare : Formula 2 :=
  .conj (.le (.abs (.var 0)) (er (1/128))) (.le (.abs (.var 1)) (er (1/128)))

def outerClaim (no wo : Bool) (u : Fin 4) : Formula 2 :=
  if u=0 ∨ u=3 then .disj localSquare (.lt 0 (gapE no wo u)) else .lt 0 (gapE no wo u)

/-- Rays of the six sectors cut out by n=0, w=0 and n-w=0. -/
def nRay : Fin 6 → ℚ × ℚ := ![(-1,-1),(-1,0),(-1,0),(1,0),(1,0),(1,1)]
def wRay : Fin 6 → ℚ × ℚ := ![(0,-1),(-1,-1),(0,1),(0,-1),(1,1),(0,1)]
def nSign : Fin 6 → ℚ := ![-1,-1,-1,1,1,1]
def wSign : Fin 6 → ℚ := ![-1,-1,1,-1,1,1]
def qSign : Fin 6 → ℚ := ![-1,1,-1,1,-1,1]

def rayE (ray : ℚ × ℚ) : Smooth 2 := sr ray.1*.var 0+sr ray.2*.var 1

def signedHalfE {k : ℕ} (sgn : ℚ) (x : Smooth k) : Smooth k :=
  (1+.cos x+sr sgn*.sin x)/2

def vertexE {k : ℕ} (x y : Smooth k) : Smooth k :=
  radiusE*.sqrt (x*x+y*y)-(x-y)/2

def localGap (no wo : Bool) (u : Fin 4) (sector : Fin 6) : Smooth 2 :=
  let n := rayE (nRay sector)
  let w := rayE (wRay sector)
  let fn := northForceE no wo u n w
  let fw := westForceE no wo u n w
  alphaE no wo n w*signedHalfE (nSign sector) n+
    gammaE no wo n w*signedHalfE (wSign sector) w+
    rE*signedHalfE (qSign sector) (n-w)+mE/2-
    vertexE fn.1 fn.2-vertexE fw.1 fw.2-baseE-
    sr (if wSign sector=1 then -13/50 else -73/100)*w-
    sr (1/1000)*sr (nSign sector)*n

noncomputable section

@[simp] lemma denote_smooth {k : ℕ} (e : Smooth k) (x : Fin k → ℝ) :
    Expr.denote e.expr x=e.value x := rfl

@[simp] lemma value_hE {k : ℕ} (x : Fin k → ℝ) : (hE : Smooth k).value x=Six.hStar := by
  simp [hE,Six.hStar,halfDiagonal]

@[simp] lemma value_AE {k : ℕ} (x : Fin k → ℝ) : (AE : Smooth k).value x=Six.AStar := by
  simp [AE,Six.AStar]

@[simp] lemma value_BE {k : ℕ} (x : Fin k → ℝ) : (BE : Smooth k).value x=Six.BStar := by
  simp [BE,Six.BStar]

@[simp] lemma value_sE {k : ℕ} (x : Fin k → ℝ) : (sE : Smooth k).value x=Six.sStar := by
  simp [sE,Six.sStar,Six.discriminant,pow_two]

@[simp] lemma value_tE {k : ℕ} (x : Fin k → ℝ) : (tE : Smooth k).value x=Six.tStar := by
  simp [tE,Six.tStar]
  ring

@[simp] lemma value_qE {k : ℕ} (x : Fin k → ℝ) : (qE : Smooth k).value x=Six.qStar := by
  simp [qE,Six.qStar,pow_two]

@[simp] lemma value_radiusE {k : ℕ} (x : Fin k → ℝ) : (radiusE : Smooth k).value x=Six.radius := by
  simp [radiusE,Six.radius]

@[simp] lemma value_rhoE {k : ℕ} (x : Fin k → ℝ) : (rhoE : Smooth k).value x=rhoStar := by
  simp [rhoE,rhoStar,rhoAt,Six.radius_sq]

@[simp] lemma value_rE {k : ℕ} (x : Fin k → ℝ) : (rE : Smooth k).value x=rStar := by
  simp [rE,rStar]

@[simp] lemma value_mE {k : ℕ} (x : Fin k → ℝ) : (mE : Smooth k).value x=mStar := by
  simp [mE,mStar,kStar,div_eq_mul_inv,mul_assoc]

@[simp] lemma value_baseE {k : ℕ} (x : Fin k → ℝ) : (baseE : Smooth k).value x=pairBase := by
  simp [baseE,pairBase]

@[simp] lemma value_alphaE {k : ℕ} (x : Fin k → ℝ) (no wo : Bool) (n w : Smooth k) :
    (alphaE no wo n w).value x=pairAlpha no wo (n.value x) (w.value x) := by
  cases no <;> cases wo <;> simp [alphaE,pairAlpha]

@[simp] lemma value_gammaE {k : ℕ} (x : Fin k → ℝ) (no wo : Bool) (n w : Smooth k) :
    (gammaE no wo n w).value x=pairGamma no wo (n.value x) (w.value x) := by
  cases no <;> cases wo <;> simp [gammaE,pairGamma]

@[simp] lemma value_northForceE {k : ℕ} (x : Fin k → ℝ) (no wo : Bool) (u : Fin 4) (n w : Smooth k) :
    ((northForceE no wo u n w).1.value x,(northForceE no wo u n w).2.value x)=
      pairNorthForce no wo u (n.value x) (w.value x) := by
  fin_cases u <;> cases no <;>
    simp [northForceE,northBaseE,northSourceE,pairNorthForce,pairNorthBase,pairNorthSource]

@[simp] lemma value_westForceE {k : ℕ} (x : Fin k → ℝ) (no wo : Bool) (u : Fin 4) (n w : Smooth k) :
    ((westForceE no wo u n w).1.value x,(westForceE no wo u n w).2.value x)=
      pairWestForce no wo u (n.value x) (w.value x) := by
  fin_cases u <;> cases wo <;>
    simp [westForceE,westBaseE,westSourceE,pairWestForce,pairWestBase,pairWestSource]

lemma denote_thresholdE {k : ℕ} (x : Fin k → ℝ) (no wo : Bool) (n w : Smooth k) :
    Expr.denote (thresholdE no wo n w) x=pairThreshold no wo (n.value x) (w.value x) := by
  simp [thresholdE,pairThreshold,Expr.denote]

lemma denote_pairE {k : ℕ} (x : Fin k → ℝ) (no wo : Bool) (u : Fin 4) (n w : Smooth k) :
    Expr.denote (pairE no wo u n w) x=pairValue no wo u (n.value x) (w.value x) := by
  have hfn := value_northForceE x no wo u n w
  have hfw := value_westForceE x no wo u n w
  have hnx := congrArg Prod.fst hfn
  have hny := congrArg Prod.snd hfn
  have hwx := congrArg Prod.fst hfw
  have hwy := congrArg Prod.snd hfw
  simp only [pairE,Expr.denote,Reified.denote_support,denote_smooth,value_radiusE,
    denote_thresholdE]
  change pairThreshold no wo (n.value x) (w.value x)-
    scalarSupport Six.radius ((northForceE no wo u n w).1.value x)
      ((northForceE no wo u n w).2.value x)-
    scalarSupport Six.radius ((westForceE no wo u n w).1.value x)
      ((westForceE no wo u n w).2.value x)=_
  rw [hnx,hny,hwx,hwy]
  rfl

@[simp] lemma denote_lineE {k : ℕ} (x : Fin k → ℝ) (e : Expr k) :
    Expr.denote (lineE e) x=pairLine (Expr.denote e x) := by
  simp [lineE,pairLine,Expr.denote]

lemma denote_gapE (no wo : Bool) (u : Fin 4) (n w : ℝ) :
    Expr.denote (gapE no wo u) ![n,w]=pairValue no wo u n w-pairBase-pairLine w-(1/1000)*|n| := by
  simp [gapE,denote_pairE,Expr.denote]

@[simp] lemma value_vertexE {k : ℕ} (x : Fin k → ℝ) (a b : Smooth k) :
    (vertexE a b).value x=northVertex (a.value x) (b.value x) := by
  simp [vertexE,northVertex,pow_two]

@[simp] lemma value_rayE (ray : ℚ × ℚ) (x y : ℝ) :
    (rayE ray).value ![x,y]=(ray.1:ℝ)*x+(ray.2:ℝ)*y := by simp [rayE]

@[simp] lemma value_signedHalfE {k : ℕ} (sgn : ℚ) (a : Smooth k) (x : Fin k → ℝ) :
    (signedHalfE sgn a).value x=(1+Real.cos (a.value x)+(sgn:ℝ)*Real.sin (a.value x))/2 := by
  simp [signedHalfE]

end
end SquaresInCircles.Six.Stress.PairCertificate

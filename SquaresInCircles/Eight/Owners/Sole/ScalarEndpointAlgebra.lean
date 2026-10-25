module

public import SquaresInCircles.Eight.Owners.Sole.EndpointSupport
public import SquaresInCircles.Eight.Owners.Sole.SplitAnchorBounds

/-!
# Eight squares: exact decomposition of the sole-E endpoint scalars

Each scalar is its zero-angle anchor baseline plus
one negative ordinary charge. The fifth radical is the explicit primary
support. These identities connect the analytic scalar data to the
fixed-coordinate split; they contain no numerical evaluation premise.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleScalarEndpointAlgebra
open Candidate SoleECoefficients SoleResiduals SoleOriginalBlocks SoleEndpointSupport
open PositiveAngularEnvelope SingleAngleConcavity SoleScalarData
open SoleScalarPolynomials (ScalarCase band atG isDE negativeIndex)

def lastRadical (s : ScalarCase) (t : ℝ) : ℝ :=
  weightData s t (Real.sin t) 4*Real.sqrt (squareData s t (Real.sin t) (Real.cos t) 4)

def baseAt (s : ScalarCase) (R M t : ℝ) : ℝ :=
  outsideData s R M t (Real.sin t) (Real.cos t) (Real.sin (t/2))-
    nuData s t (Real.sin t) (Real.cos t)*(Real.cos t-1)-
    R*((∑i : Fin 4,pairNorm (firstData s t (Real.sin t) (Real.cos t) i)
      (secondData s t (Real.sin t) (Real.cos t) i) 0)+lastRadical s t)

def charge (s : ScalarCase) (R t : ℝ) : ℝ :=
  Vnu R (firstData s t (Real.sin t) (Real.cos t) (negativeIndex s))
    (secondData s t (Real.sin t) (Real.cos t) (negativeIndex s))
    (nuData s t (Real.sin t) (Real.cos t)) t

theorem row_decomposition (s : ScalarCase) (t : ℝ) :
    rowSum s t (Real.sin t) (Real.cos t)=
      (∑i : Fin 4,pairNorm (firstData s t (Real.sin t) (Real.cos t) i)
        (secondData s t (Real.sin t) (Real.cos t) i) 0)+
      pairNorm (firstData s t (Real.sin t) (Real.cos t) (negativeIndex s))
        (secondData s t (Real.sin t) (Real.cos t) (negativeIndex s)) (-t)-
      pairNorm (firstData s t (Real.sin t) (Real.cos t) (negativeIndex s))
        (secondData s t (Real.sin t) (Real.cos t) (negativeIndex s)) 0+lastRadical s t := by
  have key : ∀ j : Fin 4,negativeIndex s=j →
      rowSum s t (Real.sin t) (Real.cos t)=
      (∑i : Fin 4,pairNorm (firstData s t (Real.sin t) (Real.cos t) i)
        (secondData s t (Real.sin t) (Real.cos t) i) 0)+
      pairNorm (firstData s t (Real.sin t) (Real.cos t) j)
        (secondData s t (Real.sin t) (Real.cos t) j) (-t)-
      pairNorm (firstData s t (Real.sin t) (Real.cos t) j)
        (secondData s t (Real.sin t) (Real.cos t) j) 0+lastRadical s t := by
    intro j hj
    fin_cases j <;>
      simp [rowSum,lastRadical,Fin.sum_univ_succ,weightData,squareData,squaredData,
        hj,pairNorm,Real.sin_neg,sub_eq_add_neg] <;> ring_nf
  exact key _ rfl

theorem value_decomposition (s : ScalarCase) (R M t : ℝ) :
    valueAt s R M t=baseAt s R M t+charge s R t := by
  rw [valueAt,row_decomposition]
  dsimp [baseAt,charge,Vnu]
  ring

def Gbase (b : Band) (R t : ℝ) : ℝ :=
  3+2*ell b t+3*c b t+k b t*(1+2*Real.cos t+(1+2*g b t)*Real.sin t)-
    R*(pairNorm 1 (n b t t) 0+pairNorm (k b t) (ell b t) 0+
      pairNorm (ell b t) (c b t) 0+pairNorm 1 (c b t) 0+
      k b t*Real.sin t*Real.sqrt (1+(g b t)^2))

def Ebase (b : Band) (de : Bool) (R M t : ℝ) : ℝ :=
  if b=.high then
    3+Real.sin t-2*R*Real.sin (t/2)+3*k b t+2*ell b t+3*c b t-
      R*(pairNorm 1 (k b t) 0+pairNorm (k b t) (ell b t) 0+
        pairNorm (ell b t) (c b t) 0+pairNorm 1 (c b t) 0)
  else if de then
    3*k b t+2*ell b t+3*c b t+1+Real.cos t/2+
      (1/2-M)*Real.sin t+(3/2)*r b t-
      R*(pairNorm (r b t) (k b t) 0+pairNorm (k b t) (ell b t) 0+
        pairNorm (ell b t) (c b t) 0+pairNorm 1 (c b t) 0)
  else
    3*k b t+2*ell b t+3*c b t+1+2*Real.cos t+(1+2*eta b t)*Real.sin t-
      R*(pairNorm 1 (k b t) 0+pairNorm (k b t) (ell b t) 0+
        pairNorm (ell b t) (c b t) 0+pairNorm (p b t t) (c b t) 0+
        Real.sin t*Real.sqrt (1+(eta b t)^2))

theorem base_at_G (s : ScalarCase) (R M t : ℝ) (hs : atG s=true) :
    baseAt s R M t=Gbase (band s) R t := by
  cases s <;>
    simp_all [atG,band,baseAt,Gbase,outsideData,firstData,secondData,lastRadical,
      Fin.sum_univ_succ,weightData,squareData,nData,n,SecondaryEStress.tiltedWeight,
      pairNorm_zero] <;> ring_nf <;> simp

theorem base_at_E (s : ScalarCase) (R M t : ℝ) (hs : atG s=false) :
    baseAt s R M t=Ebase (band s) (isDE s) R M t := by
  cases s <;>
    simp_all [atG,isDE,band,baseAt,Ebase,outsideData,firstData,secondData,lastRadical,
      Fin.sum_univ_succ,weightData,squareData,pData,rData,p,r,pairNorm_zero] <;> ring_nf <;> simp

theorem baseline_at_G {b : Band} (de : Bool) (R t : ℝ) (ht : t∈domain b) :
    SoleSplitAnchorBounds.baseline b de R t t 0 0=Gbase b R t := by
  have hs := (transport_trig (angle ht)).2.2.1
  have hc := (transport_trig (angle ht)).1
  have hc0 : 0≤Real.cos t := by linarith
  cases b <;> cases de <;>
    simp [SoleSplitAnchorBounds.baseline,Gbase,eMultiplier,hMultiplier,
      SoleEStress.zeroNorms,n,SecondaryEStress.tiltedWeight,p,r,sigma,
      edgeWidth,pairWidth,abs_of_nonneg hs,abs_of_nonneg hc0] <;> ring

theorem baseline_at_E {b : Band} (de : Bool) (R M t : ℝ) (ht : t∈domain b) :
    SoleSplitAnchorBounds.baseline b de R t 0 t (endpointWork b de R M t)=Ebase b de R M t := by
  have hs := (transport_trig (angle ht)).2.2.1
  have hc := (transport_trig (angle ht)).1
  have hc0 : 0≤Real.cos t := by linarith
  cases b <;> cases de <;>
    simp [SoleSplitAnchorBounds.baseline,Ebase,endpointWork,highWork,eMultiplier,hMultiplier,
      SoleEStress.zeroNorms,n,SecondaryEStress.tiltedWeight,p,r,sigma,
      edgeWidth,pairWidth,abs_of_nonneg hs,abs_of_nonneg hc0] <;> ring

end SquaresInCircles.Eight.SoleScalarEndpointAlgebra

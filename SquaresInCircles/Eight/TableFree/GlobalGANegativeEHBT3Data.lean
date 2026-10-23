module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3Source
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeAShortESource

/-!
# Negative EH1 with nonnegative A total and positive BT3

Uncompiled definitions from Sections 2--8. Four prescribed coefficient
families cover the two EH magnitude ranges and their total intervals.
The large EH multiplier is 1.005; its gain and positive-mass correction
are retained separately from the original four ordinary pairs.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

inductive Family where | smallLow | smallHigh | farLow | farHigh
  deriving DecidableEq, Fintype

abbrev v : ℝ := 1/10
abbrev u : ℝ := 1/4
abbrev L : ℝ := 1/6
def far : Family→Bool | .smallLow=>false | .smallHigh=>false | _=>true
def epsilon (f : Family) : ℝ := if far f then 1/200 else 0
def gain (s : ℝ) : ℝ := (13/12)*Real.sin s-(82/125)*(1-Real.cos s)
def charge (f : Family) (s : ℝ) : ℝ := if far f then (201/200)*gain s-11/50000 else gain s

namespace Explicit
def k : Family→ℝ→ℝ
  | .smallLow,t => 2933/5000+(1239/2500)*t
  | .smallHigh,t => 1673/2500+(2609/5000)*(t-L)-(1489/2500)*(t-L)^2+(527/1250)*(t-L)^3
  | .farLow,_ => 121/200
  | .farHigh,t => 101/200+(2/5)*t
def l : Family→ℝ→ℝ
  | .smallLow,_ => 1
  | .smallHigh,t => 1+(7/400)*(t-L)-(2733/2500)*(t-L)^2+(639/500)*(t-L)^3
  | .farLow,t => 1-(9/25)*t
  | .farHigh,t => 381/400-(17/100)*t
def m : Family→ℝ→ℝ
  | .smallLow,t => 5821/5000-(4437/5000)*t
  | .smallHigh,t => 10163/10000-(209/10000)*(t-L)-(5743/5000)*(t-L)^2+(14069/10000)*(t-L)^3
  | .farLow,t => 111/100-(77/100)*t
  | .farHigh,t => 1929/2000-(47/250)*t
def c (f : Family) (t z : ℝ) : ℝ := PositiveBT3.tilted (m f t) z
end Explicit

def baseline (f : Family) (t a z : ℝ) : ℝ :=
  (if f=.smallLow then PositiveBT3.Analytic.lowBaseline (Explicit.k f t) (Explicit.m f t) z
   else PositiveBT3.Analytic.fullBaseline (Explicit.k f t) (Explicit.l f t) (Explicit.m f t) z)+
    Explicit.l f t*TwoPositive.ASupport.charge a

namespace Certificate
inductive Split where | atA | atT
  deriving DecidableEq, Fintype
inductive Row where
  | lowEqual | lowNegative | smallHigh (i : Fin 3)
  | farPositive (i : Fin 3) | farNegative (i : Fin 2) | farEqual
  | farHigh (i : Fin 3) (atUpper : Bool)
  deriving DecidableEq, Fintype
def family : Row→Family
  | .lowEqual=>.smallLow | .lowNegative=>.smallLow | .smallHigh _=>.smallHigh
  | .farPositive _=>.farLow | .farNegative _=>.farLow | .farEqual=>.farLow
  | .farHigh _ _=>.farHigh
def left : Row→ℚ
  | .lowEqual=>0 | .lowNegative=>1/10 | .smallHigh _=>1/6
  | .farPositive _=>0 | .farNegative _=>1/10 | .farEqual=>1/10 | .farHigh _ _=>1/4
def right : Row→ℚ
  | .lowEqual=>1/10 | .lowNegative=>1/6 | .smallHigh _=>7/10
  | .farPositive _=>1/10 | .farNegative _=>1/4 | .farEqual=>1/4 | .farHigh _ _=>7/10
def width (r : Row) : ℚ := right r-left r
def equal : Row→Bool | .lowEqual=>true | .farEqual=>true | _=>false
def positive : Row→Bool | .farPositive _=>true | _=>false
def index : Row→Fin 4
  | .lowEqual=>0 | .lowNegative=>0 | .smallHigh i=>i.castSucc
  | .farPositive i=>![0,2,3] i | .farNegative i=>i.castSucc.castSucc
  | .farEqual=>0 | .farHigh i _=>i.castSucc
def gainArgument (r : Row) (t : ℝ) : ℝ :=
  if equal r then t else match r with | .farHigh _ true=>u | _=>v
def active (r : Row) (i : Fin 4) : Prop := family r≠.smallLow∨i≠3
instance (r : Row) (i : Fin 4) : Decidable (active r i) := by unfold active; infer_instance

theorem interval_positive (r : Row) : 0<width r := by
  cases r <;> norm_num [width,left,right]
theorem total_domain (r : Row) {t : ℝ} (ht : t∈Icc (left r:ℝ) (right r:ℝ)) :
    t∈Icc 0 frameCap := by
  cases r <;> norm_num [left,right,frameCap] at ht ⊢ <;>
    constructor <;> linarith [ht.1,ht.2]
end Certificate

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3

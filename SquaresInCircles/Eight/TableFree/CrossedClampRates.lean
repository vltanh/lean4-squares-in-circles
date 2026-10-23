module

public import SquaresInCircles.Eight.TableFree.CrossedLargeScalar

/-!
# Shared exact rates for the crossed common-frame clamp

Uncompiled source draft.  The transverse-corner parameters are Y for A
and B for the opposite middle point.  Every radical uses the actual q.
The scalar angle parameters are tangents of the two physical errors;
this separates rational rate algebra from the contact-angle bounds.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.CrossedClampRates

def radius (q Y : ℝ) : ℝ := Real.sqrt (q-Y^2)
def transverse (q Y : ℝ) : ℝ := radius q Y-1
def adjacent (q Y : ℝ) : ℝ := Real.sqrt (q-(transverse q Y)^2)

def inverseRate (q Y t : ℝ) : ℝ :=
  (radius q Y/Y)*(adjacent q Y-1+
    t*(adjacent q Y-transverse q Y)/(adjacent q Y-transverse q Y*t))

def hardRate (q B τ : ℝ) : ℝ :=
  radius q B*(B+(radius q B-1)*τ)/(B+radius q B*τ)

def angularInverseRate (q Y r : ℝ) : ℝ := inverseRate q Y (Real.tan r)
def angularHardRate (q B u : ℝ) : ℝ := hardRate q B (Real.tan u)

end SquaresInCircles.Eight.TableFree.CrossedClampRates

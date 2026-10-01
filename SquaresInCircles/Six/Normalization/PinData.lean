import SquaresInCircles.Six.Normalization.CentralSAT

/-!
# The pins and the windows

The pins of E, N, W, D and S are the points at distance `9/10` from the origin
in the directions `0`, `π/2`, `11π/12`, `5π/4` and `19π/12`. Each label has a
centre for its phase, `0`, `π/2`, `π`, `5π/4` and `3π/2`, a window about that
centre, and the axes along which the square may be separated from the central
square.
-/

namespace SquaresInCircles.Six.Normalization.Certificates

noncomputable def fixedPin (i : Fin 5) : Point :=
  ![(9/10,0),(0,9/10),
    ((9/10)*Real.cos ((11/12)*Real.pi),(9/10)*Real.sin ((11/12)*Real.pi)),
    ((9/10)*Real.cos ((5/4)*Real.pi),(9/10)*Real.sin ((5/4)*Real.pi)),
    ((9/10)*Real.cos ((19/12)*Real.pi),(9/10)*Real.sin ((19/12)*Real.pi))] i

noncomputable def phaseCenter (i : Fin 5) : ℝ :=
  ![0,Real.pi/2,Real.pi,(5/4)*Real.pi,(3/2)*Real.pi] i

def windowLower : Fin 5 → ℚ := ![-5/12,-3/10,-2/3,-15/14,-5/8]
def windowUpper : Fin 5 → ℚ := ![3/10,5/12,5/8,15/14,2/3]

def allowed : Fin 5 → List CentralAxis :=
  ![[.own,.east],[.own,.north],[.own,.west],[.own,.west,.south],[.own,.south]]

end SquaresInCircles.Six.Normalization.Certificates

import SquaresInCircles.Six.Normalization.CentralSAT

/-!
# The five fixed pins and labelled angular conventions

These are ordinary real geometric definitions. The namespace `Certificates`
is retained for compatibility with earlier source; this file imports no
expression evaluator, finite cover, interval arithmetic or certificate check.
The historical exploratory model imports this file, not conversely.
-/

namespace SquaresInCircles.Six.Normalization.Certificates

noncomputable def fixedPin (i : Fin 5) : Point :=
  ![(9/10,0),(0,9/10),
    ((9/10)*Real.cos ((11/12)*Real.pi),(9/10)*Real.sin ((11/12)*Real.pi)),
    ((9/10)*Real.cos ((5/4)*Real.pi),(9/10)*Real.sin ((5/4)*Real.pi)),
    ((9/10)*Real.cos ((19/12)*Real.pi),(9/10)*Real.sin ((19/12)*Real.pi))] i

noncomputable def pinMargin (t a b : ℝ) (q : Point) : ℝ :=
  1/2-max |q.1*Real.cos t+q.2*Real.sin t-a| |-q.1*Real.sin t+q.2*Real.cos t-b|

noncomputable def phaseCenter (i : Fin 5) : ℝ :=
  ![0,Real.pi/2,Real.pi,(5/4)*Real.pi,(3/2)*Real.pi] i

def windowLower : Fin 5 → ℚ := ![-5/12,-3/10,-2/3,-15/14,-5/8]
def windowUpper : Fin 5 → ℚ := ![3/10,5/12,5/8,15/14,2/3]

def allowed : Fin 5 → List CentralAxis :=
  ![[.own,.east],[.own,.north],[.own,.west],[.own,.west,.south],[.own,.south]]

end SquaresInCircles.Six.Normalization.Certificates

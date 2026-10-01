import SquaresInCircles.Six.Analytic.FixedPair
import SquaresInCircles.Six.PinAxes

/-!
# Actual coordinates of the fixed-weight N/W stress

This file imports the analytic normalization and pin-oriented four-axis
inventory, but not CandidateGraph, CommonDomain or any fixed-row checker.
Both central weights are one. Their nonzero central resultant is accounted
for explicitly; it must not be replaced by the variable-weight balance.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

def project (t : ℝ) (g : Point) : Point :=
  (Real.cos t*g.1+Real.sin t*g.2,-Real.sin t*g.1+Real.cos t*g.2)

def northNormal (own : Bool) (n : ℝ) : Point :=
  if own then (-Real.sin n,Real.cos n) else (0,1)

def westNormal (own : Bool) (w : ℝ) : Point :=
  if own then (-Real.cos w,-Real.sin w) else (-1,0)

/-- W-to-N: negative W-primary, negative W-secondary, N-primary,
negative N-secondary. These are the actual pin-oriented source choices. -/
def sourceAxis (n w : ℝ) : Fin 4 → Point :=
  ![scale (-1) (primary (Real.pi+w)),scale (-1) (secondary (Real.pi+w)),
    primary (Real.pi/2+n),scale (-1) (secondary (Real.pi/2+n))]

def northResultant (no : Bool) (u : Fin 4) (n w : ℝ) : Point :=
  add (northNormal no n) (scale rStar (sourceAxis n w u))

def westResultant (wo : Bool) (u : Fin 4) (n w : ℝ) : Point :=
  add (westNormal wo w)
    (add (scale (-rStar) (sourceAxis n w u))
      (scale (-mStar) (secondary (Real.pi+w))))

private lemma cos_pi_add' (x : ℝ) : Real.cos (Real.pi+x)=-Real.cos x := by
  rw [add_comm]; exact Real.cos_add_pi x

private lemma sin_pi_add' (x : ℝ) : Real.sin (Real.pi+x)=-Real.sin x := by
  rw [add_comm]; exact Real.sin_add_pi x

lemma project_add (t : ℝ) (p q : Point) :
    project t (add p q)=add (project t p) (project t q) := by
  apply Prod.ext <;> dsimp [project,add] <;> ring

lemma project_scale (t l : ℝ) (p : Point) :
    project t (scale l p)=scale l (project t p) := by
  apply Prod.ext <;> dsimp [project,scale] <;> ring

lemma project_primary (t z : ℝ) :
    project t (primary z)=(Real.cos (z-t),Real.sin (z-t)) := by
  apply Prod.ext <;> dsimp [project,primary] <;>
    simp only [Real.cos_sub,Real.sin_sub] <;> ring

lemma project_secondary (t z : ℝ) :
    project t (secondary z)=(-Real.sin (z-t),Real.cos (z-t)) := by
  apply Prod.ext <;> dsimp [project,secondary] <;>
    simp only [Real.cos_sub,Real.sin_sub] <;> ring

lemma project_north_normal (no : Bool) (n : ℝ) :
    project (Real.pi/2+n) (northNormal no n)=pairNorthBase no n := by
  cases no
  · simp [project,northNormal,pairNorthBase,Real.cos_add,Real.sin_add]
  · have hn : northNormal true n=primary (Real.pi/2+n) := by
      simp [northNormal,primary,Real.cos_add,Real.sin_add]
    rw [hn,project_primary]
    simp [pairNorthBase]

lemma project_west_normal (wo : Bool) (w : ℝ) :
    project (Real.pi+w) (westNormal wo w)=pairWestBase wo w := by
  cases wo
  · simp [project,westNormal,pairWestBase,cos_pi_add',sin_pi_add']
  · have hw : westNormal true w=primary (Real.pi+w) := by
      simp [westNormal,primary,cos_pi_add',sin_pi_add']
    rw [hw,project_primary]
    simp [pairWestBase]

lemma source_north_projection (u : Fin 4) (n w : ℝ) :
    project (Real.pi/2+n) (sourceAxis n w u)=pairNorthSource u (n-w) := by
  have hq : (Real.pi+w)-(Real.pi/2+n)=Real.pi/2-(n-w) := by ring
  have hu4 : u=0 ∨ u=1 ∨ u=2 ∨ u=3 := by fin_cases u <;> simp
  rcases hu4 with rfl | rfl | rfl | rfl
  all_goals simp only [sourceAxis,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,project_scale,project_primary,project_secondary,hq,
    sub_self,Real.cos_zero,Real.sin_zero,Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub,pairNorthSource]
  all_goals apply Prod.ext <;> dsimp [scale] <;> ring

lemma source_west_projection (u : Fin 4) (n w : ℝ) :
    project (Real.pi+w) (scale (-1) (sourceAxis n w u))=pairWestSource u (n-w) := by
  have hq : (Real.pi/2+n)-(Real.pi+w)=(n-w)-Real.pi/2 := by ring
  have hu4 : u=0 ∨ u=1 ∨ u=2 ∨ u=3 := by fin_cases u <;> simp
  rcases hu4 with rfl | rfl | rfl | rfl
  all_goals simp only [sourceAxis,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,project_scale,project_primary,project_secondary,hq,
    sub_self,Real.cos_zero,Real.sin_zero,Real.cos_sub,Real.sin_sub,
    Real.cos_pi_div_two,Real.sin_pi_div_two,pairWestSource]
  all_goals apply Prod.ext <;> dsimp [scale] <;> ring

lemma north_resultant_projection (no : Bool) (u : Fin 4) (n w : ℝ) :
    project (Real.pi/2+n) (northResultant no u n w)=northForce no u n w := by
  rw [northResultant,project_add,project_scale,project_north_normal,source_north_projection]
  rfl

lemma west_resultant_projection (wo : Bool) (u : Fin 4) (n w : ℝ) :
    project (Real.pi+w) (westResultant wo u n w)=westForce wo u n w := by
  have hneg : scale (-rStar) (sourceAxis n w u)=
      scale rStar (scale (-1) (sourceAxis n w u)) := by
    apply Prod.ext <;> dsimp [scale] <;> ring
  rw [westResultant,project_add,project_add,hneg,project_scale (Real.pi+w) rStar,
    project_scale (Real.pi+w) (-mStar),project_west_normal,source_west_projection,
    project_secondary]
  simp only [sub_self,Real.sin_zero,Real.cos_zero,neg_zero]
  apply Prod.ext <;> dsimp [westForce,add,scale] <;> ring

lemma center_dot_project (t a b : ℝ) (g : Point) :
    dot g (orientedSquare t a b).center=dot (project t g) (a,b) := by
  dsimp [dot,project,orientedSquare]
  ring

/-- Negative central work, including its exact excess over (1,-1). -/
lemma central_work (no wo : Bool) (n w : ℝ) (c : Point) :
    -dot (add (northNormal no n) (westNormal wo w)) c=
      c.1-c.2+dot (centralExcess no wo n w) c := by
  cases no <;> cases wo <;>
    dsimp [northNormal,westNormal,centralExcess,dot,add] <;> ring

lemma west_secondary_center (w a b : ℝ) :
    dot (secondary (Real.pi+w)) (orientedSquare (Real.pi+w) a b).center=b := by
  rw [center_dot_project,project_secondary]
  simp [dot]

/-- The three selected edge works have exactly these two exterior resultants
and the accounted-for central remainder. No diagonal edge is assumed here. -/
theorem edge_work_identity (no wo : Bool) (u : Fin 4)
    (n w an bn aw bw : ℝ) (c : Point) :
    dot (northNormal no n) (sub (orientedSquare (Real.pi/2+n) an bn).center c)+
      dot (westNormal wo w) (sub (orientedSquare (Real.pi+w) aw bw).center c)+
      rStar*dot (sourceAxis n w u)
        (sub (orientedSquare (Real.pi/2+n) an bn).center
          (orientedSquare (Real.pi+w) aw bw).center)=
      dot (northForce no u n w) (an,bn)+dot (westForce wo u n w) (aw,bw)+
        mStar*bw+c.1-c.2+dot (centralExcess no wo n w) c := by
  have hN := center_dot_project (Real.pi/2+n) an bn (northResultant no u n w)
  have hW := center_dot_project (Real.pi+w) aw bw (westResultant wo u n w)
  rw [north_resultant_projection] at hN
  rw [west_resultant_projection] at hW
  have hC := central_work no wo n w c
  have hB := west_secondary_center w aw bw
  have hid :
      dot (northNormal no n) (sub (orientedSquare (Real.pi/2+n) an bn).center c)+
        dot (westNormal wo w) (sub (orientedSquare (Real.pi+w) aw bw).center c)+
        rStar*dot (sourceAxis n w u)
          (sub (orientedSquare (Real.pi/2+n) an bn).center
            (orientedSquare (Real.pi+w) aw bw).center)=
      dot (northResultant no u n w) (orientedSquare (Real.pi/2+n) an bn).center+
        dot (westResultant wo u n w) (orientedSquare (Real.pi+w) aw bw).center+
        mStar*dot (secondary (Real.pi+w)) (orientedSquare (Real.pi+w) aw bw).center-
        dot (add (northNormal no n) (westNormal wo w)) c := by
    dsimp [northResultant,westResultant,dot,add,sub,scale]
    ring
  rw [hid,hN,hW,hB]
  linarith only [hC]

end SquaresInCircles.Six.Analytic.FixedPair

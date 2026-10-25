module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.Nonpositive.MixedE
public import SquaresInCircles.Eight.Owners.Positive.ScalarPolynomials

/-!
# Eight squares: transferring the exact polynomial reserves through the radicals

The support majorant follows from a positive
square, and multiplication uses the proved positive masses. The norm
perturbation lemma is global, so the later Taylor transfer does not need
a sampled lower bound on a segment of radicands.
-/

section
/-!
## Inserting E along a rotated DE2 contact

`HardInput.fromBelowERotated` replaces E by a sorted point `p` in the circle, off the core, with
`p.y ≤ 0` and frame `θ` between the frames of E and D, when DE has the rotated owner `2` and EH
the primary owner `1` at `p`. The other owners stay (`Witnesses.belowERotated`), and the radial
alternative of E is the coordinate inequality `max |H.y| |D.y| ≤ p.a`. This is the DE2
counterpart of the primary outside-E insertion.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate

theorem belowEPrimaryCycle_DE2 (C : SignedCycle) (p : SignedPoint) (θ : ℝ) :
    (belowEPrimaryCycle C p θ).Feasible D 2 ↔
      quarterFeasible (C.point D) p (θ-C.theta D) 2 := by
  simp [belowEPrimaryCycle,replacePoint,Feasible,slack,edge,word,delta,next,D,E,
    quarterFeasible,sub_nonneg]

def Witnesses.belowERotated {C : SignedCycle} (w : C.Witnesses)
    {p : SignedPoint} {θ : ℝ}
    (hDE : quarterFeasible (C.point D) p (θ-C.theta D) 2)
    (hEH : quarterFeasible p (C.point H) (C.theta H-θ) 1) :
    (belowEPrimaryCycle C p θ).Witnesses where
  owner i := if i=D then 2 else if i=E then 1 else w.owner i
  feasible := by
    intro i
    by_cases hiD : i=D
    · subst i
      simpa [D,E] using (belowEPrimaryCycle_DE2 C p θ).2 hDE
    by_cases hiE : i=E
    · subst i
      simpa [D,E] using (belowEPrimaryCycle_EH C p θ).2 hEH
    have hn : next i≠E := by
      have key : ∀ j : Vertex, j≠D → next j≠E := by decide
      exact key i hiD
    simpa [hiD,hiE,belowEPrimaryCycle] using
      (replacePoint_other_feasible (p := p) (t := θ) hiE hn).2 (w.feasible i)
  allowed := by
    intro i
    by_cases hiD : i=D
    · subst i; norm_num [normalOwners,D,E]
    by_cases hiE : i=E
    · subst i; norm_num [normalOwners,D,E]
    · simpa [hiD,hiE] using w.allowed i

def HardInput.fromBelowERotated {q : ℝ} (I : HardInput q)
    {p : SignedPoint} {θ : ℝ}
    (hs : p.Sorted) (hc : p.Contained q) (hcore : p.AvoidsCore) (hy : p.y≤0)
    (hrad : max |(I.cycle.point H).y| |(I.cycle.point D).y|≤p.a)
    (hθ : θ∈Icc (I.cycle.theta E) (I.cycle.theta D))
    (hDE : quarterFeasible (I.cycle.point D) p (θ-I.cycle.theta D) 2)
    (hEH : quarterFeasible p (I.cycle.point H) (I.cycle.theta H-θ) 1) : HardInput q where
  cycle := belowEPrimaryCycle I.cycle p θ
  necessary := by
    apply necessary_replace_clamped (v := E) (a := E) (b := D)
      I.necessary hs hc hcore
    right
    rw [min_eq_left (hθ.1.trans hθ.2),max_eq_right (hθ.1.trans hθ.2)]
    exact hθ
  anchors_normal := {
    H_nonneg := by simpa [belowEPrimaryCycle,replacePoint,H,E] using I.anchors_normal.H_nonneg
    A_nonneg := by simpa [belowEPrimaryCycle,replacePoint,A,E] using I.anchors_normal.A_nonneg
    B_nonpos := by simpa [belowEPrimaryCycle,replacePoint,B,E] using I.anchors_normal.B_nonpos
    D_nonpos := by simpa [belowEPrimaryCycle,replacePoint,D,E] using I.anchors_normal.D_nonpos }
  E_nonpos := by simpa [belowEPrimaryCycle,replacePoint] using hy
  witnesses := I.witnesses.belowERotated hDE hEH
  GA_hard := (replacePoint_other_feasible (v := E) (by decide : G≠E)
    (by decide : next G≠E)).2 I.GA_hard
  BT_hard := (replacePoint_other_feasible (v := E) (by decide : B≠E)
    (by decide : next B≠E)).2 I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hj
      have hh : I.witnesses.owner H=2 := by
        simpa [Witnesses.belowERotated,H,D,E] using hj
      simpa [belowEPrimaryCycle,replacePoint,G,E] using I.zero_signs.HG_canceling hh
    TD_canceling := by
      intro hj
      have hh : I.witnesses.owner T=0 := by
        simpa [Witnesses.belowERotated,T,D,E] using hj
      simpa [belowEPrimaryCycle,replacePoint,T,E] using I.zero_signs.TD_canceling hh }
  E_radial := by
    right
    simpa [belowEPrimaryCycle,replacePoint,H,D,E] using hrad

end SquaresInCircles.Eight.SignedCycle
end
end
end

section
@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ScalarRadicalTransfer
open Polynomial PositiveScalarPolynomials

theorem sqrt_le_mass_majorant {v a : ℝ} (hv : 0≤v) (ha : 0<a) :
    Real.sqrt v≤(v+a^2)/(2*a) := by
  apply (le_div_iff₀ (mul_pos (by norm_num) ha)).2
  nlinarith [Real.sq_sqrt hv,sq_nonneg (Real.sqrt v-a)]

/-- Changing one coordinate changes the Euclidean norm by no more than
the absolute coordinate change, including at zero. -/
theorem norm_coordinate_perturbation (a x y : ℝ) :
    Real.sqrt (a^2+x^2)≤Real.sqrt (a^2+y^2)+|x-y| := by
  have hx := Real.sq_sqrt (show 0≤a^2+x^2 by positivity)
  have hy := Real.sq_sqrt (show 0≤a^2+y^2 by positivity)
  have hyabs : |y|≤Real.sqrt (a^2+y^2) := by
    nlinarith [sq_abs y,Real.sqrt_nonneg (a^2+y^2),abs_nonneg y,sq_nonneg a]
  have hcross : y*(x-y)≤Real.sqrt (a^2+y^2)*|x-y| := by
    calc
      y*(x-y)≤|y*(x-y)| := le_abs_self _
      _=|y| *|x-y| := abs_mul _ _
      _≤Real.sqrt (a^2+y^2)*|x-y| :=
        mul_le_mul_of_nonneg_right hyabs (abs_nonneg _)
  have hnonneg : 0≤Real.sqrt (a^2+y^2)+|x-y| := by positivity
  nlinarith [sq_abs (x-y),Real.sqrt_nonneg (a^2+x^2)]

def radicalSum (c : ScalarCase) (d : ℝ) : ℝ :=
  ∑ i : Fin 5,aeval d (rows c i).w*Real.sqrt (aeval d (rows c i).v)

def rationalSum (c : ScalarCase) (d : ℝ) : ℝ :=
  ∑ i : Fin 5,aeval d (rows c i).w*
    (aeval d (rows c i).v+(aeval d (rows c i).a)^2)/(2*aeval d (rows c i).a)

private theorem five_mass_identity (a v w : Fin 5 → ℝ)
    (ha : ∀ i,a i≠0) :
    (∑ i : Fin 5,w i*(v i+(a i)^2)*∏ j : Fin 5,if j=i then 1 else a j)=
      2*(∏ i : Fin 5,a i)*(∑ i : Fin 5,w i*(v i+(a i)^2)/(2*a i)) := by
  simp [Fin.sum_univ_succ,Fin.prod_univ_succ]
  field_simp [ha 0,ha 1,ha 2,ha 3,ha 4]

theorem certificate_factorization {c : ScalarCase} {d : ℝ}
    (hd : d∈Set.Icc 0 frameCap) :
    aeval d (certificate c)=
      2*(∏ i : Fin 5,aeval d (rows c i).a)*
        (aeval d (demand c)-(epsilon:ℝ)-(radiusUpper:ℝ)*rationalSum c d) := by
  have ha : ∀ i : Fin 5,aeval d (rows c i).a≠0 := by
    intro i
    have hi := (mass_positive c i hd).1
    linarith
  have hid := five_mass_identity (fun i => aeval d (rows c i).a)
    (fun i => aeval d (rows c i).v) (fun i => aeval d (rows c i).w) ha
  simp only [certificate,mass,massExcept,map_sub,map_mul,map_add,map_ofNat,map_sum,map_pow,
    map_prod,aeval_C,map_one,apply_ite,eq_ratCast] at *
  rw [hid]
  unfold rationalSum
  ring

theorem rational_model_positive {c : ScalarCase} {d : ℝ}
    (hd : d∈Set.Icc 0 frameCap) :
    0<aeval d (demand c)-(epsilon:ℝ)-(radiusUpper:ℝ)*rationalSum c d := by
  have hp := certificate_positive c hd
  rw [certificate_factorization hd] at hp
  have hM : 0<∏ i : Fin 5,aeval d (rows c i).a := by
    apply Finset.prod_pos
    intro i _
    have hi := (mass_positive c i hd).1
    linarith
  by_contra h
  have hle : aeval d (demand c)-(epsilon:ℝ)-(radiusUpper:ℝ)*rationalSum c d≤0 :=
    le_of_not_gt h
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤2*(∏ i : Fin 5,aeval d (rows c i).a) by positivity) hle
  linarith

theorem radical_le_rational {c : ScalarCase} {d : ℝ}
    (hd : d∈Set.Icc 0 frameCap)
    (hv : ∀ i : Fin 5,0≤aeval d (rows c i).v)
    (hw : ∀ i : Fin 5,0≤aeval d (rows c i).w) :
    radicalSum c d≤rationalSum c d := by
  apply Finset.sum_le_sum
  intro i _
  have ha : 0<aeval d (rows c i).a := by have := (mass_positive c i hd).1; linarith
  have h := mul_le_mul_of_nonneg_left (sqrt_le_mass_majorant (hv i) ha) (hw i)
  simpa only [mul_div_assoc] using h

theorem radical_model_positive {c : ScalarCase} {d : ℝ}
    (hd : d∈Set.Icc 0 frameCap)
    (hv : ∀ i : Fin 5,0≤aeval d (rows c i).v)
    (hw : ∀ i : Fin 5,0≤aeval d (rows c i).w) :
    (epsilon:ℝ)<aeval d (demand c)-(radiusUpper:ℝ)*radicalSum c d := by
  have h := rational_model_positive (c := c) hd
  have hm := mul_le_mul_of_nonneg_left (radical_le_rational hd hv hw)
    (show (0:ℝ)≤(radiusUpper:ℝ) by norm_num [radiusUpper])
  linarith

theorem sqrt_qCap_le_radiusUpper : Real.sqrt qCap≤(radiusUpper:ℝ) := by
  have hR := Real.sq_sqrt (show (0:ℝ)≤qCap by norm_num [qCap])
  have hp := radiusUpper_sq_gt
  have hupper : (0:ℝ)<(radiusUpper:ℝ) := by norm_num [radiusUpper]
  nlinarith [Real.sqrt_nonneg qCap]

end SquaresInCircles.Eight.ScalarRadicalTransfer
end
end
end

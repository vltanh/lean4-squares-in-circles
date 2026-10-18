module

public import SquaresInCircles.Eight.ExactFamily.AdaptiveBounds
public import SquaresInCircles.Eight.ExactFamily.CenterCompletion
public import SquaresInCircles.Common.Trigonometry

/-!
# Eight squares: the terminal dual at arbitrary centres

The terminal dual is written for seven arbitrary centres (`Positions`), five frame errors
(`Errors`) and a choice of owners (`Owners`). All positions are free variables; the only finite
choice is which of the two allowed axes owns each of the five aligned edges. The gaps `actualGap`
are the projections of the differences of the centres on the owner normals less the supports, and
`dual` is the sum of the five corner constraints at the anchored corners, weighted by the circle
weights, less the seven gaps, weighted by the contact weights. When the corners lie in the disk
and the gaps are nonnegative, `dual` is at most the squared radius (`dual_le`). Completing the
square in each anchored centre writes `dual` as the nonnegative sum of squares `completed` plus
the part `reduced` (`exact_completion`, `completed_nonneg`). The file ends with the first-order
terms of the reduced part and the coefficients that `PerturbationEstimates.lean` bounds.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.ExactFamily.Perturbation
open Coordinates

abbrev Errors := Fin 5 → ℝ
abbrev Owners := Fin 5 → Bool
abbrev Positions := Fin 7 → Point

def R (t : ℝ) (p : Point) : Point :=
  (Real.cos t*p.1-Real.sin t*p.2,Real.sin t*p.1+Real.cos t*p.2)
def ex (t : ℝ) : Point := (Real.cos t,Real.sin t)
def ey (t : ℝ) : Point := (-Real.sin t,Real.cos t)

theorem norm_R (t : ℝ) (p : Point) : normSq (R t p)=normSq p := by
  dsimp [normSq,R]
  linear_combination (p.1^2+p.2^2)*(Real.cos_sq_add_sin_sq t)

theorem dot_R (t : ℝ) (p q : Point) : dot (R t p) (R t q)=dot p q := by
  dsimp [dot,R]
  linear_combination (p.1*q.1+p.2*q.2)*(Real.cos_sq_add_sin_sq t)

theorem R_add (t u : ℝ) (p : Point) : R t (R u p)=R (t+u) p := by
  ext <;> simp [R,Real.cos_add,Real.sin_add] <;> ring

theorem atan_frame (z : ℝ) :
    Real.cos (2*Real.arctan z)=halfAngleCos z ∧
    Real.sin (2*Real.arctan z)=halfAngleSin z := by
  have hp : 0<1+z^2 := halfAngle_den_pos z
  have hs : (Real.sqrt (1+z^2))^2=1+z^2 := Real.sq_sqrt hp.le
  have hn : Real.sqrt (1+z^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  constructor
  · rw [Real.cos_two_mul,Real.cos_arctan]
    dsimp [halfAngleCos]
    field_simp [hn,ne_of_gt hp]
    rw [hs]
    ring
  · rw [Real.sin_two_mul,Real.sin_arctan,Real.cos_arctan]
    dsimp [halfAngleSin]
    field_simp [hn,ne_of_gt hp]
    rw [hs]

def tree (a : Errors) : Fin 5 → ℝ := ![-a 0,a 1-a 0,a 2-a 1,a 3-a 2,a 4]
def errorSum (a : Errors) : ℝ := ∑ i, |tree a i|
def chainSum (a : Errors) : ℝ := |tree a 0|+|tree a 1|+|tree a 2|+|tree a 3|
def ownerB (a : Errors) (o : Owners) : ℝ := if o 0 then a 0 else 0
def ownerU (a : Errors) (o : Owners) : ℝ := if o 1 then a 0 else a 1
def ownerV (a : Errors) (o : Owners) : ℝ := if o 2 then a 1 else a 2
def ownerD (a : Errors) (o : Owners) : ℝ := if o 3 then a 3 else a 2
def ownerH (a : Errors) (o : Owners) : ℝ := if o 4 then a 4 else 0

def phases (t : ℝ) (a : Errors) : Fin 7 → ℝ :=
  ![0,a 0,a 2,a 3,t+a 4,a 1,t]
def offset (t : ℝ) (a : Errors) : Fin 5 → Point :=
  ![(1/2,-1/2),R (a 0) (1/2,1/2),R (a 2) (-1/2,1/2),
    R (a 3) (-1/2,-1/2),R (t+a 4) (-1/2,-1/2)]
def tails : Fin 7 → Fin 7 := ![0,5,2,3,6,4,4]
def heads : Fin 7 → Fin 7 := ![1,1,5,2,0,6,3]
def normal (t : ℝ) (a : Errors) (o : Owners) : Fin 7 → Point :=
  ![ey (ownerB a o),ex (ownerU a o),ex (ownerV a o),ey (ownerD a o),
    ex t,ex (t+ownerH a o),ey (t+a 4)]
def support (t : ℝ) (a : Errors) (i : Fin 7) : ℝ :=
  (1+|Real.cos (phases t a (heads i)-phases t a (tails i))|+
    |Real.sin (phases t a (heads i)-phases t a (tails i))|)/2
def actualGap (t : ℝ) (a : Errors) (o : Owners) (p : Positions) (i : Fin 7) : ℝ :=
  dot (normal t a o i) (sub (p (heads i)) (p (tails i)))-support t a i

def force (d : Coordinates) (t : ℝ) (a : Errors) (o : Owners) : Fin 7 → Point :=
  ![sub (scale d.edgeAlpha (ey (ownerB a o))) (scale d.edgeOmega (ex t)),
    scale (-1) (add (scale d.edgeAlpha (ey (ownerB a o)))
      (scale d.edgeBeta (ex (ownerU a o)))),
    sub (scale d.edgeBeta (ex (ownerV a o))) (scale d.edgeDelta (ey (ownerD a o))),
    sub (scale d.edgeDelta (ey (ownerD a o))) (scale d.edgeEpsilon (ey (t+a 4))),
    add (scale d.edgeOmega (ex (t+ownerH a o))) (scale d.edgeEpsilon (ey (t+a 4))),
    scale d.edgeBeta (sub (ex (ownerU a o)) (ex (ownerV a o))),
    scale d.edgeOmega (sub (ex t) (ex (t+ownerH a o)))]

def completed (d : Coordinates) (t : ℝ) (a : Errors) (o : Owners) (p : Positions) : ℝ :=
  ∑ i : Fin 5, d.mu i*normSq
    (add (add (p i.castSucc.castSucc) (offset t a i))
      (scale (1/(2*d.mu i)) (force d t a o i.castSucc.castSucc)))
def forceTerm (d : Coordinates) (t : ℝ) (a : Errors) (o : Owners) : ℝ :=
  -∑ i : Fin 5, normSq (force d t a o i.castSucc.castSucc)/(4*d.mu i)
def supportTerm (d : Coordinates) (t : ℝ) (a : Errors) (o : Owners) : ℝ :=
  (∑ i : Fin 7, d.lam i*support t a i)-
    ∑ i : Fin 5, dot (force d t a o i.castSucc.castSucc) (offset t a i)
def sliderTerm (d : Coordinates) (t : ℝ) (a : Errors) (o : Owners) (p : Positions) : ℝ :=
  dot (force d t a o 5) (p 5)+dot (force d t a o 6) (p 6)
def reduced (d : Coordinates) (t : ℝ) (a : Errors) (o : Owners) (p : Positions) : ℝ :=
  forceTerm d t a o+supportTerm d t a o+sliderTerm d t a o p
def dual (d : Coordinates) (t : ℝ) (a : Errors) (o : Owners) (p : Positions) : ℝ :=
  (∑ i : Fin 5, d.mu i*normSq (add (p i.castSucc.castSucc) (offset t a i)))-
    ∑ i : Fin 7, d.lam i*actualGap t a o p i

theorem errorSum_nonneg (a : Errors) : 0≤errorSum a :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem chainSum_nonneg (a : Errors) : 0≤chainSum a := by
  dsimp [chainSum]; positivity

theorem errorSum_decompose (a : Errors) : errorSum a=chainSum a+|a 4| := by
  simp [errorSum,chainSum,Fin.sum_univ_five,tree]

theorem tree_bound (a : Errors) (i : Fin 5) : |tree a i|≤errorSum a :=
  Finset.single_le_sum (f := fun i => |tree a i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem error_bound (a : Errors) (i : Fin 4) : |a i.castSucc|≤chainSum a := by
  have h₀ : |tree a 0| = |a 0| := by simp [tree]
  have h₁ : |tree a 1| = |a 1-a 0| := by simp [tree]
  have h₂ : |tree a 2| = |a 2-a 1| := by simp [tree]
  have h₃ : |tree a 3| = |a 3-a 2| := by simp [tree]
  have hb : |a 1| ≤ |a 0|+|a 1-a 0| := by simpa using abs_add_le (a 0) (a 1-a 0)
  have hd : |a 2| ≤ |a 1|+|a 2-a 1| := by simpa using abs_add_le (a 1) (a 2-a 1)
  have he : |a 3| ≤ |a 2|+|a 3-a 2| := by simpa using abs_add_le (a 2) (a 3-a 2)
  have n₀ := abs_nonneg (a 0)
  have n₁ := abs_nonneg (a 1-a 0)
  have n₂ := abs_nonneg (a 2-a 1)
  have n₃ := abs_nonneg (a 3-a 2)
  simp only [chainSum, h₀, h₁, h₂, h₃]
  fin_cases i <;> simp <;> linarith only [n₁, n₂, n₃, hb, hd, he]

theorem error_difference_bound (a : Errors) (i j : Fin 5) :
    |(![0,a 0,a 1,a 2,a 3] i)-(![0,a 0,a 1,a 2,a 3] j)|≤chainSum a := by
  have hc : chainSum a = |a 0|+|a 1-a 0|+|a 2-a 1|+|a 3-a 2| := by simp [chainSum,tree]
  have h20 : |a 2-a 0|≤|a 2-a 1|+|a 1-a 0| := by
    convert abs_add_le (a 2-a 1) (a 1-a 0) using 2; ring
  have h31 : |a 3-a 1|≤|a 3-a 2|+|a 2-a 1| := by
    convert abs_add_le (a 3-a 2) (a 2-a 1) using 2; ring
  have h30 : |a 3-a 0|≤|a 3-a 1|+|a 1-a 0| := by
    convert abs_add_le (a 3-a 1) (a 1-a 0) using 2; ring
  have h₀ : |a 0| ≤ chainSum a := error_bound a 0
  have h₁ : |a 1| ≤ chainSum a := error_bound a 1
  have h₂ : |a 2| ≤ chainSum a := error_bound a 2
  have h₃ : |a 3| ≤ chainSum a := error_bound a 3
  have hn₀ := abs_nonneg (a 0)
  have hn₁ := abs_nonneg (a 1-a 0)
  have hn₂ := abs_nonneg (a 2-a 1)
  have hn₃ := abs_nonneg (a 3-a 2)
  rw [hc] at h₀ h₁ h₂ h₃ ⊢
  have c₁ := abs_sub_comm (a 0) (a 1)
  have c₂ := abs_sub_comm (a 1) (a 2)
  have c₃ := abs_sub_comm (a 2) (a 3)
  have c₄ := abs_sub_comm (a 0) (a 2)
  have c₅ := abs_sub_comm (a 1) (a 3)
  have c₆ := abs_sub_comm (a 0) (a 3)
  fin_cases i <;> fin_cases j <;> simp <;> linarith only [h₀, hn₀, h₁, h₂, h₃, hn₂, hn₃, c₁, h20,
    c₄, h31, h30, c₆, hn₁, c₂, c₅, c₃]

theorem owner_error_bounds (a : Errors) (o : Owners) :
    |ownerB a o|≤chainSum a ∧ |ownerU a o|≤chainSum a ∧
    |ownerV a o|≤chainSum a ∧ |ownerD a o|≤chainSum a ∧
    |ownerU a o-ownerB a o|≤chainSum a ∧
    |ownerV a o-ownerD a o|≤chainSum a ∧
    |a 4-ownerD a o|≤errorSum a ∧ |a 4-a 3|≤errorSum a := by
  have e₀ : |a 0| ≤ chainSum a := error_bound a 0
  have e₁ : |a 1| ≤ chainSum a := error_bound a 1
  have e₂ : |a 2| ≤ chainSum a := error_bound a 2
  have e₃ : |a 3| ≤ chainSum a := error_bound a 3
  have hb : |ownerB a o|≤chainSum a := by
    cases h : o 0
    · simpa [ownerB,h] using chainSum_nonneg a
    · simpa [ownerB,h] using e₀
  have hu : |ownerU a o|≤chainSum a := by
    cases h : o 1
    · simpa [ownerU,h] using e₁
    · simpa [ownerU,h] using e₀
  have hv : |ownerV a o|≤chainSum a := by
    cases h : o 2
    · simpa [ownerV,h] using e₂
    · simpa [ownerV,h] using e₁
  have hd : |ownerD a o|≤chainSum a := by
    cases h : o 3
    · simpa [ownerD,h] using e₂
    · simpa [ownerD,h] using e₃
  have hub : |ownerU a o-ownerB a o|≤chainSum a := by
    cases h₀ : o 0 <;> cases h₁ : o 1
    · simpa [ownerU,ownerB,h₀,h₁] using error_difference_bound a 2 0
    · simpa [ownerU,ownerB,h₀,h₁] using error_difference_bound a 1 0
    · simpa [ownerU,ownerB,h₀,h₁] using error_difference_bound a 2 1
    · simpa [ownerU,ownerB,h₀,h₁] using error_difference_bound a 1 1
  have hvd : |ownerV a o-ownerD a o|≤chainSum a := by
    cases h₂ : o 2 <;> cases h₃ : o 3
    · simpa [ownerV,ownerD,h₂,h₃] using error_difference_bound a 3 3
    · simpa [ownerV,ownerD,h₂,h₃] using error_difference_bound a 3 4
    · simpa [ownerV,ownerD,h₂,h₃] using error_difference_bound a 2 3
    · simpa [ownerV,ownerD,h₂,h₃] using error_difference_bound a 2 4
  have hh := errorSum_decompose a
  have hhd := abs_sub (a 4) (ownerD a o)
  have hhe := abs_sub (a 4) (a 3)
  exact ⟨hb,hu,hv,hd,hub,hvd,by linarith only [hd, hh, hhd],by linarith only [e₃, hh, hhe]⟩

theorem force_expansion (d : Coordinates) (t : ℝ) (a : Errors) (o : Owners) (p : Positions) :
    -(∑ i : Fin 7, d.lam i*actualGap t a o p i) =
      (∑ i : Fin 7, dot (force d t a o i) (p i))+
      ∑ i : Fin 7, d.lam i*support t a i := by
  simp [Fin.sum_univ_succ,actualGap,force,normal,tails,heads,
    edgeAlpha,edgeBeta,edgeDelta,edgeEpsilon,edgeOmega,lam,rawLambda,
    dot,sub,scale,add]
  ring

theorem exact_completion {d : Coordinates} (hw : d.WeightDomain)
    (t : ℝ) (a : Errors) (o : Owners) (p : Positions) :
    dual d t a o p=completed d t a o p+reduced d t a o p := by
  have h (i : Fin 5) := complete_center_square (d.mu i) (ne_of_gt (hw.mu_pos i))
    (p i.castSucc.castSucc) (offset t a i) (force d t a o i.castSucc.castSucc)
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) => h i)
  have he := force_expansion d t a o p
  dsimp [dual,completed,reduced,forceTerm,supportTerm,sliderTerm]
  simp [Fin.sum_univ_succ] at he hs ⊢
  linarith only [he, hs]

theorem completed_nonneg {d : Coordinates} (hw : d.WeightDomain)
    (t : ℝ) (a : Errors) (o : Owners) (p : Positions) : 0≤completed d t a o p :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw.mu_pos i).le (normSq_nonneg _))

theorem dual_le {d : Coordinates} (hw : d.WeightDomain)
    {q t : ℝ} {a : Errors} {o : Owners} {p : Positions}
    (hv : ∀ i : Fin 5, normSq (add (p i.castSucc.castSucc) (offset t a i))≤q)
    (hg : ∀ i : Fin 7, 0≤actualGap t a o p i) : dual d t a o p≤q := by
  have hc := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin 5)))
    (fun i _ => mul_le_mul_of_nonneg_left (hv i) (hw.mu_pos i).le)
  have hgap := Finset.sum_nonneg (s:=(Finset.univ : Finset (Fin 7)))
    (fun i _ => mul_nonneg (hw.lam_pos i).le (hg i))
  rw [← Finset.sum_mul,hw.mu_sum,one_mul] at hc
  dsimp [dual]
  linarith only [hc, hgap]

def KA (d : Coordinates) : ℝ := d.edgeAlpha*d.edgeOmega/(2*d.mu 0)
def KB (d : Coordinates) : ℝ := d.edgeAlpha*d.edgeBeta/(2*d.mu 1)
def KD (d : Coordinates) : ℝ := d.edgeBeta*d.edgeDelta/(2*d.mu 2)
def KE (d : Coordinates) : ℝ := d.edgeDelta*d.edgeEpsilon/(2*d.mu 3)
def KH (d : Coordinates) : ℝ := d.edgeOmega*d.edgeEpsilon/(2*d.mu 4)

def forceLinear (d : Coordinates) (a : Errors) (o : Owners) : ℝ :=
  -KA d*d.c*ownerB a o-KB d*(ownerU a o-ownerB a o)+
    KD d*(ownerV a o-ownerD a o)-KE d*d.s*(a 4-ownerD a o)+
    if o 4 then 0 else KH d*a 4
def supportLinear (d : Coordinates) (a : Errors) (o : Owners) : ℝ :=
  -(d.edgeAlpha/2)*tree a 0+
    (if o 1 then 0 else d.edgeBeta/2)*tree a 1+
    (if o 2 then d.edgeBeta/2 else 0)*tree a 2+
    (d.edgeDelta/2)*tree a 3+
    (if o 4 then 0 else -d.edgeOmega/2)*tree a 4+
    d.edgeEpsilon*d.c*(a 4-a 3)
def sliderLinear (d : Coordinates) (a : Errors) (o : Owners) (Z V : ℝ) : ℝ :=
  d.edgeBeta*Z*(ownerU a o-ownerV a o)-(if o 4 then d.edgeOmega*V*a 4 else 0)
def edgeWeights (d : Coordinates) : Fin 5 → ℝ :=
  ![d.edgeAlpha,d.edgeBeta,d.edgeBeta,d.edgeDelta,d.edgeOmega]
def cusp (d : Coordinates) (a : Errors) : ℝ := ∑ i : Fin 5, (edgeWeights d i/2)*|tree a i|
def coefficient (d : Coordinates) (o : Owners) (Z η : ℝ) : Fin 5 → ℝ :=
  ![-d.edgeAlpha/2+d.cutX+(if o 0 then d.edgeAlpha*d.cutY else 0),
    if o 1 then -d.edgeBeta*(Z+d.cutJ) else -d.edgeBeta*(d.y+3/2+d.cutJ),
    if o 2 then d.edgeBeta/2-d.cutK else -d.edgeBeta*(Z+d.cutJ),
    d.edgeDelta/2-d.edgeEpsilon*d.c-(if o 3 then d.edgeDelta*(d.x₄-d.x₃) else 0),
    -d.edgeOmega/2+d.cutN-(if o 4 then d.edgeOmega*η else 0)]

end SquaresInCircles.Eight.ExactFamily.Perturbation

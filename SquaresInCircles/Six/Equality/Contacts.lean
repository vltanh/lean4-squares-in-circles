import SquaresInCircles.Six.Construction

/-!
# Eight contacts fix the centres

Let C be at `c` and E, N, W, D, S be turned as in the model, at the local
coordinates `(a i, b i)`, in the disk of radius `radius`, and let them satisfy the
eight separating inequalities of the contacts of the model. Summed with the
weights `1`, `rStar` and `mStar` of the stress of the model, their thresholds add
up to `4 + 2 rStar + mStar + 2 hStar mStar`, and their left sides to the works of
the five exterior forces on their centres. Each work is at most its value in the
model: for a force `(x, y)` with `x, y > 0` pointing at the point `(A, B)` of the
circle, completing the square in `|a| + 1/2 - A` and `|b| + 1/2 - B` gives
`x a + y b ≤ x (A - 1/2) + y (B - 1/2)`, with equality only at
`(A - 1/2, B - 1/2)`; for the axial force on D the disk gives `a ≤ rhoStar`, with
equality only at `(rhoStar, 0)`. In the model these bounds add up to the
thresholds, so all of them are attained.
-/

noncomputable section
namespace SquaresInCircles.Six.Equality

/-- The eight contacts of the model, for C at `c` and E, N, W, D, S turned as in
the model at the local coordinates `(a i, b i)`: C with E, N, W and S along the
sides of C, N–W and E–S along the sides of W and S, and W–D, D–S along the
secondary axes of W and S. -/
structure Contacts (c : Point) (a b : Fin 5 → ℝ) : Prop where
  east : 1+c.1 ≤ a 0
  north : 1+c.2 ≤ a 1
  west : 1 ≤ a 2+c.1
  south : 1 ≤ a 4+c.2
  northwest : 1 ≤ a 2-b 1
  eastsouth : 1 ≤ a 4+b 0
  westDiagonal : 1/2+hStar ≤ hStar*(a 3+b 3)-b 2
  diagonalSouth : 1/2+hStar ≤ b 4+hStar*(a 3-b 3)

/-- The local coordinates of E, N, W, D, S in the model. -/
def modelRadial : Fin 5 → ℝ := ![1+sStar,1+sStar,1-sStar,rhoStar,1-sStar]
def modelTransverse : Fin 5 → ℝ := ![sStar,-sStar,-tStar,0,tStar]

/-- A force `(x, y)` with `x, y > 0` pointing at the point `(A, B)` of the circle
of radius `R`: its work on a centre `(a, b)` of a square in the disk is at most
its work on `(A - 1/2, B - 1/2)`, and only that centre attains it. -/
lemma corner_bound {R μ x y A B a b : ℝ} (hμ : 0<μ) (hx : 0<x) (hy : 0<y)
    (hA : A=μ*x) (hB : B=μ*y) (hcircle : A^2+B^2=R^2)
    (hbox : (|a|+1/2)^2+(|b|+1/2)^2≤R^2) :
    x*a+y*b≤x*(A-1/2)+y*(B-1/2) ∧
      (x*(A-1/2)+y*(B-1/2)≤x*a+y*b → a=A-1/2 ∧ b=B-1/2) := by
  have ha := mul_le_mul_of_nonneg_left (le_abs_self a) hx.le
  have hb := mul_le_mul_of_nonneg_left (le_abs_self b) hy.le
  have hsq : (|a|+1/2-A)^2+(|b|+1/2-B)^2+
      2*μ*(x*(|a|+1/2-A)+y*(|b|+1/2-B))≤0 := by
    subst hA hB
    nlinarith only [hbox,hcircle]
  have hwork : 0≤x*(A-(|a|+1/2))+y*(B-(|b|+1/2)) := by
    nlinarith only [hsq,hμ,sq_nonneg (|a|+1/2-A),sq_nonneg (|b|+1/2-B)]
  refine ⟨by linarith,fun he => ?_⟩
  have hzero : x*(|a|+1/2-A)+y*(|b|+1/2-B)=0 := by linarith
  rw [hzero,mul_zero,add_zero] at hsq
  have hA' : |a|+1/2=A := by nlinarith only [hsq,sq_nonneg (|a|+1/2-A),sq_nonneg (|b|+1/2-B)]
  have hB' : |b|+1/2=B := by nlinarith only [hsq,sq_nonneg (|a|+1/2-A),sq_nonneg (|b|+1/2-B)]
  have hae : a=|a| := by nlinarith only [ha,hb,he,hA',hB',hx,hy]
  have hbe : b=|b| := by nlinarith only [ha,hb,he,hA',hB',hx,hy]
  exact ⟨by linarith,by linarith⟩

/-- Proposition 10.15: the eight contacts and the disk fix the local coordinates
of the exterior squares and the centre of C. -/
theorem model_of_contacts {c : Point} {a b : Fin 5 → ℝ} (h : Contacts c a b)
    (hbox : ∀ i, (|a i|+1/2)^2+(|b i|+1/2)^2≤radius^2) :
    a=modelRadial ∧ b=modelTransverse ∧ c=(sStar,sStar) := by
  have hq := radius_sq
  have hs := sStar_pos
  have hr := rStar_pos
  have hk := kStar_pos
  have hrd := rStar_den_pos
  have hkd := kStar_den_pos
  have hrA : (sStar+3/2)*rStar=sStar+1/2 := by
    rw [mul_comm]; exact div_mul_cancel₀ _ hrd.ne'
  have hmA : (3/2-sStar)/(1+rStar)*mStar=tStar+1/2 := by
    have h1 := one_add_rStar_pos.ne'
    have h2 : (3/2-sStar)*kStar=tStar+1/2 := by rw [mul_comm]; exact div_mul_cancel₀ _ hkd.ne'
    rw [← h2]
    dsimp [mStar]
    field_simp
  have heast := east_radius_identity
  have hwest := west_radius_identity
  have hE := corner_bound (R := radius) (x := 1) (y := rStar) (μ := sStar+3/2) (A := sStar+3/2)
    (B := sStar+1/2) (a := a 0) (b := b 0) (by linarith) one_pos hr (by ring) hrA.symm
    (by linarith) (hbox 0)
  have hN := corner_bound (R := radius) (x := 1) (y := rStar) (μ := sStar+3/2) (A := sStar+3/2)
    (B := sStar+1/2) (a := a 1) (b := -b 1) (by linarith) one_pos hr (by ring) hrA.symm
    (by linarith) (by simpa only [abs_neg] using hbox 1)
  have hW := corner_bound (R := radius) (x := 1+rStar) (y := mStar) (μ := (3/2-sStar)/(1+rStar))
    (A := 3/2-sStar) (B := tStar+1/2) (a := a 2) (b := -b 2) (by positivity)
    one_add_rStar_pos mStar_pos (by field_simp) hmA.symm (by linarith)
    (by simpa only [abs_neg] using hbox 2)
  have hS := corner_bound (R := radius) (x := 1+rStar) (y := mStar) (μ := (3/2-sStar)/(1+rStar))
    (A := 3/2-sStar) (B := tStar+1/2) (a := a 4) (b := b 4) (by positivity)
    one_add_rStar_pos mStar_pos (by field_simp) hmA.symm (by linarith) (hbox 4)
  have hρ := rhoStar_identity
  have hρ0 : 0<rhoStar := by linarith [rhoStar_bounds.1]
  have hD : |a 3|≤rhoStar := by
    nlinarith [hbox 3,abs_nonneg (a 3),abs_nonneg (b 3)]
  have hK : 0<2*hStar*mStar := by have := hStar_pos; have := mStar_pos; positivity
  have hDa := mul_le_mul_of_nonneg_left ((le_abs_self (a 3)).trans hD) hK.le
  have hid := pairBase_diagonal_identity
  dsimp [pairBase,diagonalK] at hid
  have hsum : 4+2*rStar+mStar+2*hStar*mStar ≤
      (1*a 0+rStar*b 0)+(1*a 1+rStar*(-b 1))+((1+rStar)*a 2+mStar*(-b 2))+
        ((1+rStar)*a 4+mStar*b 4)+2*hStar*mStar*a 3 := by
    have h1 := mul_le_mul_of_nonneg_left h.northwest hr.le
    have h2 := mul_le_mul_of_nonneg_left h.eastsouth hr.le
    have h3 := mul_le_mul_of_nonneg_left h.westDiagonal mStar_pos.le
    have h4 := mul_le_mul_of_nonneg_left h.diagonalSouth mStar_pos.le
    linarith [h.east,h.north,h.west,h.south]
  have e0 := hE.2 (by linarith [hN.1,hW.1,hS.1])
  have e1 := hN.2 (by linarith [hE.1,hW.1,hS.1])
  have e2 := hW.2 (by linarith [hE.1,hN.1,hS.1])
  have e4 := hS.2 (by linarith [hE.1,hN.1,hW.1])
  have e3 : a 3=rhoStar := by
    have hge : 2*hStar*mStar*rhoStar ≤ 2*hStar*mStar*a 3 := by
      linarith [hE.1,hN.1,hW.1,hS.1]
    have := le_of_mul_le_mul_left hge hK
    linarith [le_abs_self (a 3)]
  have f3 : b 3=0 := by
    have hb := hbox 3
    rw [e3,abs_of_pos hρ0] at hb
    exact abs_eq_zero.mp (le_antisymm
      (by nlinarith only [hb,hq,hρ,abs_nonneg (b 3)]) (abs_nonneg _))
  refine ⟨?_,?_,?_⟩
  · funext i
    fin_cases i
    · show a 0=1+sStar; linarith only [e0.1]
    · show a 1=1+sStar; linarith only [e1.1]
    · show a 2=1-sStar; linarith only [e2.1]
    · exact e3
    · show a 4=1-sStar; linarith only [e4.1]
  · funext i
    fin_cases i
    · show b 0=sStar; linarith only [e0.2]
    · show b 1=-sStar; linarith only [e1.2]
    · show b 2=-tStar; linarith only [e2.2]
    · exact f3
    · show b 4=tStar; linarith only [e4.2]
  · apply Prod.ext
    · show c.1=sStar; linarith only [h.east,h.west,e0.1,e2.1]
    · show c.2=sStar; linarith only [h.north,h.south,e1.1,e4.1]

end SquaresInCircles.Six.Equality

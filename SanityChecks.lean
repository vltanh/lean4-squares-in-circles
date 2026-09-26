import SquaresInCircles

/-!
Regression checks: the radius and model tables, the exact rational margins the
proofs rely on, the contact points of the polygon relaxations, the public
statements, and the column packings of seven squares, which are exactly the
optimal ones.
-/
noncomputable section
open SquaresInCircles

-- The radius table.
example : optimalRadius 1 = Real.sqrt 2 / 2 := rfl
example : optimalRadius 2 = Real.sqrt 5 / 2 := rfl
example : optimalRadius 3 = 5 * Real.sqrt 17 / 16 := rfl
example : optimalRadius 4 = Real.sqrt 2 := rfl
example : optimalRadius 5 = Real.sqrt (5 / 2) := rfl
example : optimalRadius 7 = Real.sqrt 13 / 2 := rfl

-- The model table: axis-parallel squares at these centres.
example : optimalPackings 1 = {fun i => axisSquare (![(0,0)] i)} := rfl
example : optimalPackings 2 = {fun i => axisSquare (![(-1/2,0),(1/2,0)] i)} := rfl
example : optimalPackings 3 =
    {fun i => axisSquare (![(-1/2,-5/16),(1/2,-5/16),(0,11/16)] i)} := rfl
example : optimalPackings 4 =
    {fun i => axisSquare (![(1/2,1/2),(-1/2,1/2),(-1/2,-1/2),(1/2,-1/2)] i)} := rfl
example : optimalPackings 5 =
    {fun i => axisSquare (![(0,0),(1,0),(0,1),(-1,0),(0,-1)] i)} := rfl
example : optimalPackings 7 = Set.range fun c : Seven.Column => fun i =>
    axisSquare (![(1,-1/2),(1,1/2),(-1,-1/2),(-1,1/2),(0,c.bottom),(0,c.middle),(0,c.top)] i) :=
  rfl
example : Seven.columnCenters Seven.centeredColumn =
    ![(1,-1/2),(1,1/2),(-1,-1/2),(-1,1/2),(0,-1),(0,0),(0,1)] := rfl

-- Three squares: deficit, radial and transverse margins.
example : (22:ℝ)/42-13/29 = 46/609 := by norm_num
example : (46:ℝ)/609 < 1/12 := by norm_num
example : (1/2:ℝ)-1/24-(1/24)^2/4 > 9/20 := by norm_num
example : (9/20:ℝ)*(3/8)=27/160 := by norm_num
example : (57/128:ℝ)-(19/8)*(27/160)=57/1280 := by norm_num
example : (57/1280:ℝ) < 1/16 := by norm_num
example : (3/5:ℝ)/5-(4/5)*(2/5)+11/16 < 1/2 := by norm_num
example : (7/8:ℝ)/5+(3/5)*(2/5)+1/16 < 1/2 := by norm_num
example : (1/5:ℝ)-11/16 > -1/2 := by norm_num
example : (2/5:ℝ)+1/16 < 1/2 := by norm_num

-- Four and five squares: radical and Taylor margins.
example : ((109:ℝ)/100)^3/6 < 1/4 := by norm_num
example : (5:ℝ) < (2237/1000)^2 := by norm_num
example : ((707:ℝ)/1000)^2 < 1/2 := by norm_num
example : (401:ℝ)/500 < 1-((22:ℝ)/35)^2/2 := by norm_num
example : (1:ℝ) < (401/500)^2+(3/5)^2 := by norm_num
example : (17:ℝ)/30 < (707/1000)*(401/500) := by norm_num
example : (6:ℝ)/5*(237/1000)+(54/125)*(237/1000)^3 < 313/1000 := by norm_num
example : (6:ℝ)/5*(237/1000)+(54/125)*(23/60)^3 < 313/1000 := by norm_num
example : (6:ℝ)/5*(1-2*(23/60))+(54/125)*(23/60)^3 < 313/1000 := by norm_num
example : (2:ℝ)/3 < Real.sqrt 2/2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg 2]
example : ((5:ℝ)/6+1/2)^2+(1/2)^2 > 2 := by norm_num

-- Seven squares: the outer corners, the side state and its label, the margin
-- of the marker arc at the near edge, and the discriminant certificate of the
-- inward sector at its endpoint.
example : (3/2:ℝ)^2+1 = 13/4 := by norm_num
example : (1/2:ℝ)^2+3 = 13/4 := by norm_num
example : Seven.Admissible 1 (1/2) := ⟨by norm_num,by norm_num,by norm_num,by norm_num [phi,Seven.targetSq]⟩
example : Seven.label 1 (1/2) = Real.pi/6 := by
  have hs : Seven.side 1 (1/2) = Real.pi/6 := by unfold Seven.side; ring
  unfold Seven.label Seven.axial
  rw [hs,min_eq_right (show Real.pi/6 ≤ 5*(1/2)/4 by linarith [Real.pi_lt_d4]),
    min_eq_left (show Real.pi/6 ≤ Real.pi/4 by linarith [Real.pi_pos])]
example : (87061:ℝ) < (2951/10)^2 := by norm_num
example : ((2951:ℝ)/10-86)/384+801/1600 < 157/150 := by norm_num
example : (0:ℝ) < Seven.radialPolynomial (5/8) := Seven.radialPolynomial_pos (by norm_num)

-- Contact points of the polygon relaxations.
example : Three.P3 (1/2) (5/16) := by norm_num [Three.P3]
example : Three.P3 (11/16) 0 := by norm_num [Three.P3]
example : Five.P5 1 0 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  exact ⟨by norm_num [P8],by nlinarith [Real.sqrt_nonneg 5]⟩
example : Five.P5 ((Real.sqrt 5-1)/2) ((Real.sqrt 5-1)/2) := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  refine ⟨⟨?_,?_⟩,by linarith⟩ <;> nlinarith [Real.sqrt_nonneg 5]

-- Public statements.
example (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : Three.radius ≤ R := Three.optimum.optimality S o R hp
example : IsLeast {R | ∃ (S : Fin 7 → UnitSquare) (o : Point), Packing S o R}
    (Real.sqrt 13 / 2) := optimal_radius 7 (Or.inr rfl)
example (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5) (S : Fin n → UnitSquare) (o : Point)
    (hp : Packing S o (optimalRadius n)) : ∃ M, optimalPackings n = {M} ∧ Congruent S o M := by
  obtain ⟨M,hM,h⟩ := (optimal_packings n (Or.inl hn) S o).mp hp
  obtain ⟨h1,h5⟩ := hn
  refine ⟨M,?_,h⟩
  interval_cases n <;> exact (Set.mem_singleton_iff.mp hM) ▸ rfl
example (S : Fin 4 → UnitSquare) (o : Point) (hp : Packing S o (optimalRadius 4)) :
    Congruent S o Four.model := by
  obtain ⟨M,hM,h⟩ := (optimal_packings 4 (Or.inl ⟨by norm_num,by norm_num⟩) S o).mp hp
  exact (show M = Four.model from hM) ▸ h
example (S : Fin 7 → UnitSquare) (o : Point) (hp : Packing S o (optimalRadius 7)) :
    ∃ c : Seven.Column, Congruent S o (Seven.columnModel c) := by
  obtain ⟨_,⟨c,rfl⟩,h⟩ := (optimal_packings 7 (Or.inr rfl) S o).mp hp
  exact ⟨c,h⟩
example (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : Seven.radius ≤ R := Seven.optimum.optimality S o R hp
example (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7) :
    (optimum n hn).radius = optimalRadius n := (optimum_spec n hn).1

-- The models, each congruent to itself.
example : Congruent One.model (0,0) One.model := One.uniqueness One.model (0,0) One.model_packing
example : Congruent Two.model (0,0) Two.model := Two.uniqueness Two.model (0,0) Two.model_packing
example : Congruent Three.model (0,0) Three.model :=
  Three.uniqueness Three.model (0,0) Three.model_packing
example : Congruent Four.model (0,0) Four.model :=
  Four.uniqueness Four.model (0,0) Four.model_packing
example : Congruent Five.model (0,0) Five.model :=
  Five.uniqueness Five.model (0,0) Five.model_packing
example : ∃ c : Seven.Column, Congruent Seven.model (0,0) (Seven.columnModel c) :=
  Seven.uniqueness Seven.model (0,0) Seven.model_packing

-- Seven squares: every position of the three middle squares is optimal, for
-- example the bottom one pushed down by one fifth.
example : Packing Seven.model (0,0) Seven.radius := Seven.model_packing
example (c : Seven.Column) : Packing (Seven.columnModel c) (0,0) Seven.radius :=
  Seven.column_packing c
example : ∃ c : Seven.Column, c.bottom = -6/5 ∧
    Packing (Seven.columnModel c) (0,0) Seven.radius := by
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hl : (6/5:ℝ) ≤ Seven.columnLimit := by
    unfold Seven.columnLimit
    nlinarith [Real.sqrt_nonneg (3:ℝ)]
  exact ⟨⟨-6/5,0,1,by linarith,by norm_num,by norm_num,by linarith⟩,rfl,
    Seven.column_packing _⟩

-- Seven squares: the four gaps of the column, and the middle square within 1/4
-- of the disk centre.
example (c : Seven.Column) : ∑ i, c.slots i = 2 * Real.sqrt 3 - 3 := c.sum_slots
example (c : Seven.Column) : |c.middle| < 1/4 := by
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hs : Real.sqrt 3 < 7/4 := by nlinarith [Real.sqrt_nonneg (3:ℝ)]
  have hl := c.lower
  have hu := c.upper
  unfold Seven.columnLimit at hl hu
  exact abs_lt.mpr ⟨by linarith [c.gap_lower],by linarith [c.gap_upper]⟩

-- Seven squares: the three contacts of the optimal packing, the two squares of
-- a side column, a side square and the top square at any admissible height, and
-- the top square and the next side square.
example : Seven.OrderedContact 1 (1/2) 1 (1/2) .negative .positive :=
  Or.inl ⟨rfl,rfl,⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩
example {a : ℝ} (ha : 1/2 ≤ a ∧ a ≤ Seven.columnLimit) :
    Seven.OrderedContact 1 (1/2) a 0 .positive .negative :=
  Or.inr (Or.inl ⟨rfl,⟨rfl,rfl⟩,⟨rfl,ha.1,ha.2⟩⟩)
example {a : ℝ} (ha : 1/2 ≤ a ∧ a ≤ Seven.columnLimit) :
    Seven.OrderedContact a 0 1 (1/2) .positive .negative :=
  Or.inr (Or.inr ⟨rfl,⟨rfl,ha.1,ha.2⟩,⟨rfl,rfl⟩⟩)

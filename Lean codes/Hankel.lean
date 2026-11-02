/-
# Properties of the block Hankel matrix: Theorem 6.1 of Katayama (2005)

The deterministic system (6.1),

  `x(t+1) = A x(t) + B u(t)`,   `y(t) = C x(t) + D u(t)`,   `x ∈ ℝⁿ`, `u ∈ ℝᵐ`, `y ∈ ℝᵖ`,

has the impulse response (Markov parameters) `G₀ = D`, `G_t = C A^{t-1} B` for `t ≥ 1` (6.3).
The block Hankel matrix `H` (6.6) has the block `G_{i+j+1}` in block row `i` and block column `j`
(counting from `0`), and `𝒪 = [C; CA; CA²; ⋯]`, `𝒞 = [B, AB, A²B, ⋯]`.

## Formalization choices

* A block matrix is a Mathlib matrix whose rows and columns are indexed by pairs: row `(i, a)` is
  row `a` of block row `i`. `H`, `𝒪` and `𝒞` are infinite (`i, j ∈ ℕ`); the product `𝒪 * 𝒞` is
  still defined, because the inner dimension `n` is finite.
* `rank H` is the dimension of the column space `colSpace H`, the span of the columns of `H`;
  `H` has finite rank if `colSpace H` is finite-dimensional.
* `(A, B, C)` is minimal if `rank 𝒪ₙ = n` and `rank 𝒞ₙ = n`, with the finite matrices
  `𝒪ₖ = [C; CA; ⋯; CA^{k-1}]` (`obsMat`) and `𝒞ₗ = [B, AB, ⋯, A^{l-1}B]` (`reachMat`).
* Item 1 holds for every sequence `G`; minimality is not needed there.
* In item 3 the past has finite length `l`: the system is at rest at time `-l`. Time is shifted
  by `l`, so the simulation starts at `0` and the book's time `t` is `l + t` here.

## Main results (Theorem 6.1)

* `finiteRank_iff`          : item 1, `H` has finite rank iff `G_t = C A^{t-1} B` for some
                              finite-dimensional `(A, B, C)`; `realization_of_finiteRank`
                              builds a realization of order `rank H` (the minimal order).
* `hankel_eq_obs_mul_reach` : item 2, `H = 𝒪𝒞`; `hankel_eq_obsT_mul`: `H = 𝒪T T⁻¹𝒞`.
* `rank_hankel`             : item 2, `rank H = n` if `(A, B, C)` is minimal.
* `past_to_future`          : item 3, `x(0) = 𝒞u₋`, `y₊ = 𝒪x(0)` (6.8) and `y₊ = Hu₋` (6.7).
* `shift_invariance`        : item 4, `H↑ = 𝒪↑𝒞 = 𝒪A𝒞 = 𝒪 A𝒞 = 𝒪𝒞← = H←`.
-/
import Mathlib

open Matrix

namespace SysId

variable {n m p : ℕ}

/-! ### Definitions -/

-- ANCHOR: defs
/-- The block Hankel matrix (6.6): block `(i, j)` is `G_{i+j+1}`. -/
def hankel (G : ℕ → Matrix (Fin p) (Fin m) ℝ) :
    Matrix (ℕ × Fin p) (ℕ × Fin m) ℝ :=
  Matrix.of fun r c => G (r.1 + c.1 + 1) r.2 c.2

/-- Observability matrix `𝒪`: block row `i` is `C Aⁱ`. -/
def obs (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (ℕ × Fin p) (Fin n) ℝ :=
  Matrix.of fun r x => (C * A ^ r.1) r.2 x

/-- Reachability matrix `𝒞`: block column `j` is `Aʲ B`. -/
def reach (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n) (ℕ × Fin m) ℝ :=
  Matrix.of fun x c => (A ^ c.1 * B) x c.2

/-- The column space of `H`, spanned by its columns; `rank H` is its
dimension. -/
def colSpace (H : Matrix (ℕ × Fin p) (ℕ × Fin m) ℝ) :
    Submodule ℝ (ℕ × Fin p → ℝ) :=
  Submodule.span ℝ (Set.range H.col)
-- ANCHOR_END: defs

/-- `𝒪ₖ = [C; CA; ⋯; CA^{k-1}]`, the first `k` block rows of `𝒪`. -/
def obsMat (k : ℕ) (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin k × Fin p) (Fin n) ℝ :=
  Matrix.of fun r x => (C * A ^ (r.1 : ℕ)) r.2 x

/-- `𝒞ₗ = [B, AB, ⋯, A^{l-1}B]`, the first `l` block columns of `𝒞`. -/
def reachMat (l : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n) (Fin l × Fin m) ℝ :=
  Matrix.of fun x c => (A ^ (c.1 : ℕ) * B) x c.2

-- ANCHOR: minimal
/-- `(A, B, C)` is minimal: `(C, A)` is observable, `(A, B)` reachable. -/
def IsMinimal (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) : Prop :=
  (obsMat n C A).rank = n ∧ (reachMat n A B).rank = n
-- ANCHOR_END: minimal

/-- `M↑`: delete the first block row. -/
def shiftUp {κ : Type*} (M : Matrix (ℕ × Fin p) κ ℝ) : Matrix (ℕ × Fin p) κ ℝ :=
  M.submatrix (fun r => (r.1 + 1, r.2)) id

/-- `M←`: delete the first block column. -/
def shiftLeft {κ : Type*} (M : Matrix κ (ℕ × Fin m) ℝ) : Matrix κ (ℕ × Fin m) ℝ :=
  M.submatrix id (fun c => (c.1 + 1, c.2))

/-- The shift `σ` on output sequences, `(σ y)(i) = y(i + 1)`: it deletes the first block. -/
def shift : (ℕ × Fin p → ℝ) →ₗ[ℝ] (ℕ × Fin p → ℝ) :=
  LinearMap.funLeft ℝ ℝ fun r => (r.1 + 1, r.2)

lemma shift_apply (y : ℕ × Fin p → ℝ) (r : ℕ × Fin p) : shift y r = y (r.1 + 1, r.2) := rfl

/-- The state of (6.1a), `x(t+1) = A x(t) + B u(t)`, started at `x(0) = x₀`. -/
def traj (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (x₀ : Fin n → ℝ)
    (u : ℕ → Fin m → ℝ) : ℕ → Fin n → ℝ
  | 0 => x₀
  | t + 1 => A *ᵥ traj A B x₀ u t + B *ᵥ u t

/-- The past input `u₋ = [u(-1); u(-2); ⋯; u(-l)]`; the book's `u(-1-j)` is `u (l-1-j)`. -/
def uMinus (l : ℕ) (u : ℕ → Fin m → ℝ) : Fin l × Fin m → ℝ :=
  fun c => u (l - 1 - c.1) c.2

/-- The future output `y₊ = [y(0); y(1); ⋯]` with `y = C x + D u`; the book's `y(t)` is the
output at time `l + t` here. -/
def yPlus (C : Matrix (Fin p) (Fin n) ℝ) (D : Matrix (Fin p) (Fin m) ℝ)
    (x : ℕ → Fin n → ℝ) (u : ℕ → Fin m → ℝ) (l : ℕ) : ℕ × Fin p → ℝ :=
  fun r => (C *ᵥ x (l + r.1) + D *ᵥ u (l + r.1)) r.2

variable (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
  (C : Matrix (Fin p) (Fin n) ℝ) (G : ℕ → Matrix (Fin p) (Fin m) ℝ)

/-! ### Item 2: factorization; item 4: shift invariance -/

-- ANCHOR: factor
/-- Theorem 6.1, item 2: if `G_t = C A^{t-1} B` (6.3), then `H = 𝒪 𝒞`. -/
theorem hankel_eq_obs_mul_reach (hG : ∀ t, G (t + 1) = C * A ^ t * B) :
    hankel G = obs C A * reach A B := by
  ext r c                     -- compare the entries in row r, column c
  rw [Matrix.mul_apply]       -- (𝒪𝒞)_{rc} = ∑ₓ 𝒪_{rx} 𝒞_{xc}
  simp only [hankel, obs, reach, Matrix.of_apply]
  -- G_{i+j+1} = C A^{i+j} B = (C Aⁱ)(Aʲ B)
  rw [← Matrix.mul_apply, hG, pow_add]
  simp only [Matrix.mul_assoc]
-- ANCHOR_END: factor

-- ANCHOR: shift
/-- Theorem 6.1, item 4: `H↑ = 𝒪↑𝒞 = 𝒪A·𝒞 = 𝒪·A𝒞 = 𝒪𝒞← = H←`. -/
theorem shift_invariance (hG : ∀ t, G (t + 1) = C * A ^ t * B) :
    shiftUp (hankel G) = shiftUp (obs C A) * reach A B ∧
      shiftUp (obs C A) * reach A B = obs C A * A * reach A B ∧
      obs C A * A * reach A B = obs C A * (A * reach A B) ∧
      obs C A * (A * reach A B) = obs C A * shiftLeft (reach A B) ∧
      obs C A * shiftLeft (reach A B) = shiftLeft (hankel G) := by
  rw [hankel_eq_obs_mul_reach A B C G hG]
  -- 𝒪↑ = 𝒪A: block row i + 1 of 𝒪 is C Aⁱ⁺¹ = (C Aⁱ) A
  have hO : shiftUp (obs C A) = obs C A * A := by
    ext r x
    rw [Matrix.mul_apply]
    simp only [shiftUp, obs, submatrix_apply, of_apply, id]
    rw [← Matrix.mul_apply, pow_succ, Matrix.mul_assoc]
  -- 𝒞← = A𝒞: block column j + 1 of 𝒞 is Aʲ⁺¹ B = A (Aʲ B)
  have hC : shiftLeft (reach A B) = A * reach A B := by
    ext x c
    rw [Matrix.mul_apply]
    simp only [shiftLeft, reach, submatrix_apply, of_apply, id]
    rw [← Matrix.mul_apply, pow_succ', Matrix.mul_assoc]
  exact ⟨rfl, by rw [hO], Matrix.mul_assoc _ _ _, by rw [hC], rfl⟩
-- ANCHOR_END: shift

/-- Theorem 6.1, item 2: `H = 𝒪T T⁻¹𝒞` for every invertible `T`. -/
theorem hankel_eq_obsT_mul (hG : ∀ t, G (t + 1) = C * A ^ t * B)
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T.det) :
    hankel G = (obs C A * T) * (T⁻¹ * reach A B) := by
  rw [hankel_eq_obs_mul_reach A B C G hG, Matrix.mul_assoc, ← Matrix.mul_assoc T,
    Matrix.mul_nonsing_inv T hT, Matrix.one_mul]

/-- `(T⁻¹AT)ᵏ = T⁻¹AᵏT`. -/
lemma conj_pow (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T.det) (k : ℕ) :
    (T⁻¹ * A * T) ^ k = T⁻¹ * A ^ k * T := by
  induction k with
  | zero => simp [Matrix.nonsing_inv_mul T hT]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left T _ hT]

/-- `𝒪T` and `T⁻¹𝒞` are `𝒪` and `𝒞` of the similar realization `(T⁻¹AT, T⁻¹B, CT)`. -/
theorem obs_reach_similar (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T.det) :
    obs (C * T) (T⁻¹ * A * T) = obs C A * T ∧
      reach (T⁻¹ * A * T) (T⁻¹ * B) = T⁻¹ * reach A B := by
  constructor
  · ext r x
    rw [Matrix.mul_apply]
    simp only [obs, Matrix.of_apply]
    rw [← Matrix.mul_apply, conj_pow A T hT]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left T _ hT]
  · ext x c
    rw [Matrix.mul_apply]
    simp only [reach, Matrix.of_apply]
    rw [← Matrix.mul_apply, conj_pow A T hT]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left T _ hT]

/-! ### Item 2: rank -/

/-- The columns of `O * R` are `O` times the columns of `R`. -/
lemma colSpace_mul (O : Matrix (ℕ × Fin p) (Fin n) ℝ) (R : Matrix (Fin n) (ℕ × Fin m) ℝ) :
    colSpace (O * R) = (Submodule.span ℝ (Set.range R.col)).map O.mulVecLin := by
  rw [colSpace, Submodule.map_span, ← Set.range_comp]
  rfl   -- column `c` of `O * R` is, by definition, `O` times column `c` of `R`

/-- Observability: `rank 𝒪ₙ = n` makes `𝒪` injective, `𝒪 x = 0 ⇒ x = 0`. -/
lemma obs_injective (h : (obsMat n C A).rank = n) :
    Function.Injective (obs C A).mulVecLin := by
  -- rank–nullity: `𝒪ₙ` has a trivial kernel
  have hker : LinearMap.ker (obsMat n C A).mulVecLin = ⊥ := by
    have := LinearMap.finrank_range_add_finrank_ker (obsMat n C A).mulVecLin
    have hr : Module.finrank ℝ (LinearMap.range (obsMat n C A).mulVecLin) = n := h
    rw [hr, Module.finrank_fin_fun] at this
    exact Submodule.finrank_eq_zero.mp (by omega)
  -- `𝒪ₙ` consists of the first `n` block rows of `𝒪`
  rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro x hx
  refine Matrix.ker_mulVecLin_eq_bot_iff.mp hker x ?_
  ext r
  exact congrFun hx ((r.1 : ℕ), r.2)

/-- Reachability: `rank 𝒞ₙ = n` makes the columns of `𝒞` span `ℝⁿ`. -/
lemma span_reach (h : (reachMat n A B).rank = n) :
    Submodule.span ℝ (Set.range (reach A B).col) = ⊤ := by
  -- the columns of `𝒞ₙ` span `ℝⁿ` ...
  have htop : LinearMap.range (reachMat n A B).mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact h)
  rw [Matrix.range_mulVecLin] at htop
  -- ... and they are columns of `𝒞`
  rw [eq_top_iff, ← htop]
  apply Submodule.span_mono
  rintro _ ⟨c, rfl⟩
  exact ⟨((c.1 : ℕ), c.2), rfl⟩

-- ANCHOR: rank
/-- Theorem 6.1, item 2: if `(A, B, C)` is minimal, then `rank H = n`. -/
theorem rank_hankel (hmin : IsMinimal A B C)
    (hG : ∀ t, G (t + 1) = C * A ^ t * B) :
    FiniteDimensional ℝ (colSpace (hankel G)) ∧
      Module.finrank ℝ (colSpace (hankel G)) = n := by
  -- the columns of 𝒞 span ℝⁿ: the column space of H = 𝒪𝒞 is range 𝒪
  have hcol :
      colSpace (hankel G) = LinearMap.range (obs C A).mulVecLin := by
    rw [hankel_eq_obs_mul_reach A B C G hG, colSpace_mul,
      span_reach A B hmin.2, Submodule.map_top]
  rw [hcol]
  -- 𝒪 is injective, so its range is n-dimensional
  exact ⟨inferInstance, by rw [LinearMap.finrank_range_of_inj
    (obs_injective A C hmin.1), Module.finrank_fin_fun]⟩
-- ANCHOR_END: rank

/-! ### Item 1: finite rank and realizability -/

/-- Theorem 6.1, item 1 (⇐): a realization of order `n` gives `rank H ≤ n`. -/
theorem finiteRank_of_realization (hG : ∀ t, G (t + 1) = C * A ^ t * B) :
    FiniteDimensional ℝ (colSpace (hankel G)) ∧ Module.finrank ℝ (colSpace (hankel G)) ≤ n := by
  have hle : colSpace (hankel G) ≤ LinearMap.range (obs C A).mulVecLin := by
    rw [hankel_eq_obs_mul_reach A B C G hG, colSpace_mul]
    exact LinearMap.map_le_range
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  calc Module.finrank ℝ (colSpace (hankel G))
      ≤ Module.finrank ℝ (LinearMap.range (obs C A).mulVecLin) := Submodule.finrank_mono hle
    _ ≤ Module.finrank ℝ (Fin n → ℝ) := LinearMap.finrank_range_le _
    _ = n := Module.finrank_fin_fun ℝ

/-- `H↑ = H←`: the shift maps column `(j, b)` of `H` to column `(j + 1, b)`, hence the column
space of `H` into itself. -/
lemma shift_mem_colSpace : ∀ y ∈ colSpace (hankel G), shift y ∈ colSpace (hankel G) := by
  have hmap : (colSpace (hankel G)).map shift ≤ colSpace (hankel G) := by
    rw [colSpace, Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨(c.1 + 1, c.2), ?_⟩
    ext r
    simp only [shift_apply, Matrix.col_apply, hankel, Matrix.of_apply]
    ring_nf                         -- G_{(i+1)+j+1} = G_{i+(j+1)+1}
  exact fun y hy => hmap (Submodule.mem_map_of_mem hy)

/-- The first block column `H₀ = [G₁; G₂; ⋯]` of `H` maps `ℝᵐ` into the column space of `H`. -/
lemma firstCol_mem_colSpace (u : Fin m → ℝ) :
    (hankel G).submatrix id (fun b : Fin m => ((0 : ℕ), b)) *ᵥ u ∈ colSpace (hankel G) := by
  have hle : LinearMap.range ((hankel G).submatrix id (fun b : Fin m => ((0 : ℕ), b))).mulVecLin
      ≤ colSpace (hankel G) := by
    rw [Matrix.range_mulVecLin, colSpace]
    apply Submodule.span_mono
    rintro _ ⟨b, rfl⟩
    exact ⟨(0, b), rfl⟩             -- column `b` of `H₀` is column `(0, b)` of `H`
  exact hle (LinearMap.mem_range_self _ u)

-- ANCHOR: realization
/-- Theorem 6.1, item 1 (⇒): if `H` has finite rank `r`, then `G` has a
realization (6.3) of order `r`: the state space is the column space `V`
of `H`, `A` the shift, `B` the first block column of `H`. -/
theorem realization_of_finiteRank
    [FiniteDimensional ℝ (colSpace (hankel G))] :
    ∃ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ)
      (B : Matrix (Fin r) (Fin m) ℝ) (C : Matrix (Fin p) (Fin r) ℝ),
      r = Module.finrank ℝ (colSpace (hankel G)) ∧
      ∀ t, G (t + 1) = C * A ^ t * B := by
  set V := colSpace (hankel G)
  set H₀ := (hankel G).submatrix id (fun b : Fin m => ((0 : ℕ), b))
    with hH₀
  -- the realization, as linear maps on the state space V
  obtain ⟨A, hA⟩ : ∃ A : V →ₗ[ℝ] V,
      ∀ y, (A y : ℕ × Fin p → ℝ) = shift y :=          -- A = σ on V
    ⟨shift.restrict (shift_mem_colSpace G), fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : (Fin m → ℝ) →ₗ[ℝ] V,
      ∀ u, (B u : ℕ × Fin p → ℝ) = H₀ *ᵥ u :=          -- B u = H₀ u
    ⟨LinearMap.codRestrict V H₀.mulVecLin (firstCol_mem_colSpace G),
      fun _ => rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : V →ₗ[ℝ] (Fin p → ℝ),
      ∀ y a, C y a = (y : ℕ × Fin p → ℝ) (0, a) :=   -- C y = y(0)
    ⟨LinearMap.funLeft ℝ ℝ (fun a => ((0 : ℕ), a)) ∘ₗ V.subtype,
      fun _ _ => rfl⟩
  -- Aᵗ B u is H₀ u shifted by t blocks
  have key : ∀ t u r,
      ((A ^ t) (B u) : ℕ × Fin p → ℝ) r = (H₀ *ᵥ u) (r.1 + t, r.2) := by
    intro t u
    induction t with
    | zero => intro r; simp [hB]
    | succ t ih =>
      intro r
      rw [pow_succ', Module.End.mul_apply, hA, shift_apply, ih]
      ring_nf
  -- in a basis b of V, the matrix of C Aᵗ B is block t of H₀, i.e. G_{t+1}
  let b := Module.finBasis ℝ V
  refine ⟨Module.finrank ℝ V, LinearMap.toMatrix b b A,
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) b B,
    LinearMap.toMatrix b (Pi.basisFun ℝ (Fin p)) C, rfl, fun t => ?_⟩
  rw [LinearMap.toMatrix_pow, ← LinearMap.toMatrix_comp,
    ← LinearMap.toMatrix_comp]
  ext a c
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, hC, key]
  simp [hH₀, hankel]
-- ANCHOR_END: realization

-- ANCHOR: item1
/-- Theorem 6.1, item 1: `H` has finite rank iff `G` has a factorization
of the form (6.3). -/
theorem finiteRank_iff :
    FiniteDimensional ℝ (colSpace (hankel G)) ↔
      ∃ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ)
        (B : Matrix (Fin r) (Fin m) ℝ) (C : Matrix (Fin p) (Fin r) ℝ),
        ∀ t, G (t + 1) = C * A ^ t * B := by
  constructor
  · intro                             -- (⇒) build the realization
    obtain ⟨r, A, B, C, -, hG⟩ := realization_of_finiteRank G
    exact ⟨r, A, B, C, hG⟩
  · rintro ⟨r, A, B, C, hG⟩           -- (⇐) H = 𝒪𝒞 has rank ≤ r
    exact (finiteRank_of_realization A B C G hG).1
-- ANCHOR_END: item1

/-! ### Item 3: past inputs, present state, future outputs -/

/-- From rest, `x(t) = ∑_{j<t} Aʲ B u(t-1-j)`. -/
lemma traj_from_rest (u : ℕ → Fin m → ℝ) (t : ℕ) :
    traj A B 0 u t = ∑ j : Fin t, A ^ (j : ℕ) *ᵥ (B *ᵥ u (t - 1 - j)) := by
  induction t with
  | zero => simp [traj]
  | succ t ih =>
    rw [traj, ih, Fin.sum_univ_succ, Matrix.mulVec_sum, add_comm _ (B *ᵥ u t)]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.val_succ, pow_succ', ← Matrix.mulVec_mulVec,
        show t + 1 - 1 - (j + 1) = t - 1 - j by omega]

/-- `𝒞ₗ v = ∑_{j<l} Aʲ B vⱼ`, where `vⱼ` is block `j` of `v`. -/
lemma reachMat_mulVec (l : ℕ) (v : Fin l × Fin m → ℝ) :
    reachMat l A B *ᵥ v = ∑ j : Fin l, A ^ (j : ℕ) *ᵥ (B *ᵥ fun b => v (j, b)) := by
  ext x
  simp only [Matrix.mulVec_mulVec, Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct, reachMat, Matrix.of_apply, Fintype.sum_prod_type]

-- ANCHOR: item3
/-- Theorem 6.1, item 3: at rest at time `-l`, inputs
`u(-l), …, u(-1)`, no input from time `0` on. Then
`x(0) = 𝒞u₋`, `y₊ = 𝒪x(0)` (6.8), and the convolution
`y(t) = ∑ⱼ G_{t+j+1} u(-1-j)` (6.5), i.e. `y₊ = Hu₋`. -/
theorem past_to_future (hG : ∀ t, G (t + 1) = C * A ^ t * B)
    (D : Matrix (Fin p) (Fin m) ℝ) (u : ℕ → Fin m → ℝ) (l : ℕ)
    (hu : ∀ t, l ≤ t → u t = 0) :
    traj A B 0 u l = reachMat l A B *ᵥ uMinus l u ∧
      yPlus C D (traj A B 0 u) u l = obs C A *ᵥ traj A B 0 u l ∧
      ∀ t, C *ᵥ traj A B 0 u (l + t) + D *ᵥ u (l + t) =
        ∑ j : Fin l, G (t + j + 1) *ᵥ u (l - 1 - j) := by
  -- x(0) = ∑_{j<l} Aʲ B u(-1-j) = 𝒞 u₋
  have hx0 : traj A B 0 u l = reachMat l A B *ᵥ uMinus l u := by
    rw [traj_from_rest, reachMat_mulVec]
    rfl
  -- no input from time 0 on: x(t) = Aᵗ x(0)
  have hx : ∀ t, traj A B 0 u (l + t) = A ^ t *ᵥ traj A B 0 u l := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [← add_assoc, traj, ih, hu (l + t) (by omega), mulVec_zero,
        add_zero, mulVec_mulVec, pow_succ']
  -- y(t) = C x(t) = C Aᵗ x(0), which is block row t of 𝒪 x(0)
  have hy : ∀ t, C *ᵥ traj A B 0 u (l + t) + D *ᵥ u (l + t) =
      C *ᵥ (A ^ t *ᵥ traj A B 0 u l) := by
    intro t
    rw [hx, hu (l + t) (by omega), mulVec_zero, add_zero]
  refine ⟨hx0, ?_, fun t => ?_⟩
  · ext r
    simp only [yPlus, hy, mulVec_mulVec]
    rfl
  -- C Aᵗ ∑ⱼ Aʲ B u(-1-j) = ∑ⱼ C A^{t+j} B u(-1-j) = ∑ⱼ G_{t+j+1} u(-1-j)
  rw [hy, traj_from_rest, mulVec_sum, mulVec_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hG, pow_add]
  simp only [mulVec_mulVec, Matrix.mul_assoc]
-- ANCHOR_END: item3

end SysId

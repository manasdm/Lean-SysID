/-
# The Ho–Kalman realization algorithm: Lemma 6.1 of Katayama (2005)

Let `(A, B, C)` be a realization of order `n` with Markov parameters `G_t = C A^{t-1} B`, and let
`H_{k,l}` be the finite block Hankel matrix (6.10). Lemma 6.1 computes a realization in three
steps:

1. the SVD `H_{k,l} = U_s Σ_s V_sᵀ` (6.14), with `n` nonzero singular values;
2. the factors `𝒪_k = U_s Σ_s^{1/2} T` and `𝒞_l = T⁻¹ Σ_s^{1/2} V_sᵀ` (6.15);
3. `A = 𝒪_{k-1}^† 𝒪_k^↑`, `B = 𝒞_l(1:n, 1:m)` and `C = 𝒪_k(1:p, 1:n)` (6.16).

## Formalization choices

* Steps 2–3 are proved correct for *every* factorization `H_{k,l} = Ohat * Rhat` with `n` inner
  columns. The SVD of Step 1 is one way to compute such a factorization. It is not formalized
  (Mathlib has no SVD), and correctness does not depend on it.
* `H_{k+1,l+1}` has `k + 1` block rows and `l + 1` block columns. The book's `𝒪_{k-1}` is then
  the first `k` block rows of `Ohat` (`Fin.castSucc`), `𝒪_k^↑` its last `k` block rows
  (`Fin.succ`), and the first block row and column exist.
* `pinv M = (MᵀM)⁻¹Mᵀ` is the least-squares solution operator of Lemma 4.1 (Söderström and
  Stoica); for `M` of full column rank it is the pseudo-inverse `M^†` of (6.16).
* The hypotheses are `rank 𝒪_k = n` and `rank 𝒞_{l+1} = n`. For a minimal system both hold
  when `k ≥ n` and `l + 1 ≥ n` (`hoKalman_of_minimal`).

## Main results

* `hankelMat_eq`        : `H_{k,l} = 𝒪_k 𝒞_l` (6.11).
* `rank_hankelMat`      : `rank H_{k,l} = n`, the number of nonzero singular values in (6.14).
* `factor_unique`       : `𝒪 𝒞 = Ohat * Rhat` ⇒ `Ohat = 𝒪 T`, `Rhat = T⁻¹ 𝒞`, `T` invertible.
* `hoKalman`            : Steps 2–3 return `(T⁻¹AT, T⁻¹B, CT)`.
* `hoKalman_of_minimal` : hence, for a minimal system, `Chat Ahatᵗ Bhat = G_{t+1}` for all `t`.

(`Ohat`, `Rhat` are the computed factors `𝒪_k`, `𝒞_l` of (6.15); `Ahat`, `Bhat`, `Chat` the
computed realization.)
-/
import PISVerification.Hankel

open Matrix

namespace SysId

variable {n m p : ℕ}

/-- The finite block Hankel matrix `H_{k,l}` (6.10). -/
def hankelMat (k l : ℕ) (G : ℕ → Matrix (Fin p) (Fin m) ℝ) :
    Matrix (Fin k × Fin p) (Fin l × Fin m) ℝ :=
  Matrix.of fun r c => G (r.1 + c.1 + 1) r.2 c.2

/-- `pinv M = (MᵀM)⁻¹Mᵀ`, the least-squares left inverse. -/
noncomputable def pinv {ι : Type*} [Fintype ι] (M : Matrix ι (Fin n) ℝ) : Matrix (Fin n) ι ℝ :=
  (Mᵀ * M)⁻¹ * Mᵀ

-- ANCHOR: steps
/-- Step 3, `A = 𝒪_{k-1}^† 𝒪_k^↑`: least squares on the shift equation
(6.12); `castSucc` selects the first `k` block rows, `succ` the last `k`. -/
noncomputable def hoKalmanA {k : ℕ}
    (O : Matrix (Fin (k + 1) × Fin p) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  pinv (O.submatrix (fun r : Fin k × Fin p => (r.1.castSucc, r.2)) id) *
    O.submatrix (fun r : Fin k × Fin p => (r.1.succ, r.2)) id

/-- Step 3, `B = 𝒞_l(1:n, 1:m)`: the first block column. -/
def hoKalmanB {l : ℕ} (R : Matrix (Fin n) (Fin (l + 1) × Fin m) ℝ) :
    Matrix (Fin n) (Fin m) ℝ :=
  R.submatrix id (fun b => (0, b))

/-- Step 3, `C = 𝒪_k(1:p, 1:n)`: the first block row. -/
def hoKalmanC {k : ℕ} (O : Matrix (Fin (k + 1) × Fin p) (Fin n) ℝ) :
    Matrix (Fin p) (Fin n) ℝ :=
  O.submatrix (fun a => (0, a)) id
-- ANCHOR_END: steps

/-! ### Full-rank matrices have one-sided inverses -/

/-- A square matrix of full rank is invertible. -/
lemma isUnit_det_of_rank_eq {M : Matrix (Fin n) (Fin n) ℝ} (h : M.rank = n) :
    IsUnit M.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
  have htop : LinearMap.range M.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact h)
  exact LinearMap.range_eq_top.mp htop

/-- Full column rank: `pinv M` is a left inverse, `M^† M = I`. -/
lemma pinv_mul {ι : Type*} [Fintype ι] {M : Matrix ι (Fin n) ℝ} (h : M.rank = n) :
    pinv M * M = 1 := by
  have hu : IsUnit (Mᵀ * M).det :=
    isUnit_det_of_rank_eq (by rw [Matrix.rank_transpose_mul_self, h])
  rw [pinv, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu]

/-- Full row rank: `Rᵀ(RRᵀ)⁻¹` is a right inverse. -/
lemma mul_rightInv {ι : Type*} [Fintype ι] {R : Matrix (Fin n) ι ℝ} (h : R.rank = n) :
    R * (Rᵀ * (R * Rᵀ)⁻¹) = 1 := by
  have hu : IsUnit (R * Rᵀ).det :=
    isUnit_det_of_rank_eq (by rw [Matrix.rank_self_mul_transpose, h])
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu]

-- ANCHOR: factor_unique
/-- Uniqueness of (6.11): if `𝒪 𝒞 = Ohat * Rhat`, where `𝒪` has full column rank
and `𝒞` full row rank, then `Ohat = 𝒪 T`, `Rhat = T⁻¹ 𝒞` with `T` invertible. -/
theorem factor_unique {ι κ : Type*} [Finite ι] [Fintype κ]
    (O Ohat : Matrix ι (Fin n) ℝ) (R Rhat : Matrix (Fin n) κ ℝ)
    (hO : O.rank = n) (hR : R.rank = n) (h : O * R = Ohat * Rhat) :
    ∃ T : Matrix (Fin n) (Fin n) ℝ,
      IsUnit T.det ∧ Ohat = O * T ∧ Rhat = T⁻¹ * R := by
  have := Fintype.ofFinite ι
  -- a left inverse L of 𝒪 and a right inverse Rr of 𝒞 (least squares)
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin n) ι ℝ, L * O = 1 :=
    ⟨pinv O, pinv_mul hO⟩
  obtain ⟨Rr, hRr⟩ : ∃ Rr : Matrix κ (Fin n) ℝ, R * Rr = 1 :=
    ⟨_, mul_rightInv hR⟩
  -- T = L Ohat and S = Rhat Rr are inverse to each other
  have hTS : (L * Ohat) * (Rhat * Rr) = 1 := by
    calc (L * Ohat) * (Rhat * Rr) = L * (Ohat * Rhat) * Rr := by
          simp only [Matrix.mul_assoc]
      _ = (L * O) * (R * Rr) := by rw [← h]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hL, hRr, Matrix.one_mul]
  have hST : (Rhat * Rr) * (L * Ohat) = 1 := mul_eq_one_comm.mp hTS
  -- 𝒪 = Ohat S and 𝒞 = T Rhat
  have hO' : O = Ohat * (Rhat * Rr) := by
    rw [← Matrix.mul_assoc, ← h, Matrix.mul_assoc, hRr, Matrix.mul_one]
  have hR' : R = (L * Ohat) * Rhat := by
    rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, hL, Matrix.one_mul]
  refine ⟨L * Ohat, isUnit_det_of_right_inverse hTS, ?_, ?_⟩
  · -- Ohat = Ohat S T = 𝒪 T
    rw [hO', Matrix.mul_assoc, hST, Matrix.mul_one]
  · -- T⁻¹ = S, and S 𝒞 = S T Rhat = Rhat
    rw [Matrix.inv_eq_right_inv hTS, hR', ← Matrix.mul_assoc, hST,
      Matrix.one_mul]
-- ANCHOR_END: factor_unique

variable (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
  (C : Matrix (Fin p) (Fin n) ℝ) (G : ℕ → Matrix (Fin p) (Fin m) ℝ)

/-! ### The finite Hankel matrix -/

/-- (6.11): `H_{k,l} = 𝒪_k 𝒞_l`. -/
theorem hankelMat_eq (hG : ∀ t, G (t + 1) = C * A ^ t * B) (k l : ℕ) :
    hankelMat k l G = obsMat k C A * reachMat l A B := by
  ext r c
  rw [Matrix.mul_apply]
  simp only [hankelMat, obsMat, reachMat, Matrix.of_apply]
  rw [← Matrix.mul_apply, hG, pow_add]
  simp only [Matrix.mul_assoc]

/-- `rank 𝒪_k = n` for every `k ≥ n` if `rank 𝒪ₙ = n`. -/
lemma rank_obsMat_of_le (h : (obsMat n C A).rank = n) {k : ℕ} (hk : n ≤ k) :
    (obsMat k C A).rank = n := by
  apply le_antisymm
  · simpa using Matrix.rank_le_card_width (obsMat k C A)
  · calc n = (obsMat n C A).rank := h.symm
      _ = ((obsMat k C A).submatrix (fun r : Fin n × Fin p => (Fin.castLE hk r.1, r.2))
            id).rank := rfl
      _ ≤ (obsMat k C A).rank := Matrix.rank_submatrix_le _ _ _

/-- `rank 𝒞_l = n` for every `l ≥ n` if `rank 𝒞ₙ = n`. -/
lemma rank_reachMat_of_le (h : (reachMat n A B).rank = n) {l : ℕ} (hl : n ≤ l) :
    (reachMat l A B).rank = n := by
  apply le_antisymm
  · simpa using Matrix.rank_le_card_height (reachMat l A B)
  · calc n = (reachMat n A B).rank := h.symm
      _ = ((reachMat l A B).submatrix id
            (fun c : Fin n × Fin m => (Fin.castLE hl c.1, c.2))).rank := rfl
      _ ≤ (reachMat l A B).rank := Matrix.rank_submatrix_le _ _ _

/-- `rank H_{k,l} = n`: the SVD (6.14) has exactly `n` nonzero singular values. -/
theorem rank_hankelMat (hG : ∀ t, G (t + 1) = C * A ^ t * B) {k l : ℕ}
    (hO : (obsMat k C A).rank = n) (hR : (reachMat l A B).rank = n) :
    (hankelMat k l G).rank = n := by
  rw [hankelMat_eq A B C G hG]
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin n) (Fin k × Fin p) ℝ, L * obsMat k C A = 1 :=
    ⟨_, pinv_mul hO⟩
  obtain ⟨Rr, hRr⟩ : ∃ Rr : Matrix (Fin l × Fin m) (Fin n) ℝ, reachMat l A B * Rr = 1 :=
    ⟨_, mul_rightInv hR⟩
  apply le_antisymm
  · calc (obsMat k C A * reachMat l A B).rank ≤ (obsMat k C A).rank :=
          Matrix.rank_mul_le_left _ _
      _ = n := hO
  · calc n = (1 : Matrix (Fin n) (Fin n) ℝ).rank := by simp
      _ = (L * (obsMat k C A * reachMat l A B) * Rr).rank := by
          rw [← Matrix.mul_assoc, hL, Matrix.one_mul, hRr]
      _ ≤ (L * (obsMat k C A * reachMat l A B)).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (obsMat k C A * reachMat l A B).rank := Matrix.rank_mul_le_right _ _

/-- The first `k` block rows of `𝒪_{k+1}` form `𝒪_k`. -/
lemma obsMat_castSucc (k : ℕ) :
    (obsMat (k + 1) C A).submatrix (fun r : Fin k × Fin p => (r.1.castSucc, r.2)) id =
      obsMat k C A := rfl

/-- (6.12), shift structure: the last `k` block rows of `𝒪_{k+1}` form `𝒪_k A`. -/
lemma obsMat_succ (k : ℕ) :
    (obsMat (k + 1) C A).submatrix (fun r : Fin k × Fin p => (r.1.succ, r.2)) id =
      obsMat k C A * A := by
  ext r x
  rw [Matrix.mul_apply]
  simp only [obsMat, Matrix.submatrix_apply, Matrix.of_apply, id, Fin.val_succ]
  rw [← Matrix.mul_apply, pow_succ, Matrix.mul_assoc]

/-- `rank 𝒪_{k+1} = n` if `rank 𝒪_k = n`: `𝒪_k` is a submatrix of `𝒪_{k+1}`. -/
lemma rank_obsMat_succ {k : ℕ} (hO : (obsMat k C A).rank = n) :
    (obsMat (k + 1) C A).rank = n := by
  apply le_antisymm
  · simpa using Matrix.rank_le_card_width (obsMat (k + 1) C A)
  · calc n = (obsMat k C A).rank := hO.symm
      _ ≤ (obsMat (k + 1) C A).rank := by
          rw [← obsMat_castSucc A C k]; exact Matrix.rank_submatrix_le _ _ _

/-! ### Correctness of the algorithm -/

-- ANCHOR: hoKalman
/-- Lemma 6.1 (Ho–Kalman), Steps 2–3: for any factorization
`H_{k+1,l+1} = Ohat * Rhat` with `n` inner columns, Step 3
returns `(T⁻¹AT, T⁻¹B, CT)` for an invertible `T`. -/
theorem hoKalman (hG : ∀ t, G (t + 1) = C * A ^ t * B) {k l : ℕ}
    (hO : (obsMat k C A).rank = n)
    (hR : (reachMat (l + 1) A B).rank = n)
    (Ohat : Matrix (Fin (k + 1) × Fin p) (Fin n) ℝ)
    (Rhat : Matrix (Fin n) (Fin (l + 1) × Fin m) ℝ)
    (hfac : hankelMat (k + 1) (l + 1) G = Ohat * Rhat) :
    ∃ T : Matrix (Fin n) (Fin n) ℝ, IsUnit T.det ∧
      hoKalmanA Ohat = T⁻¹ * A * T ∧ hoKalmanB Rhat = T⁻¹ * B ∧
      hoKalmanC Ohat = C * T := by
  -- (6.11), (6.15): Ohat = 𝒪_{k+1} T and Rhat = T⁻¹ 𝒞_{l+1}
  obtain ⟨T, hT, hOT, hRT⟩ := factor_unique (obsMat (k + 1) C A) Ohat
    (reachMat (l + 1) A B) Rhat (rank_obsMat_succ A C hO) hR
    (by rw [← hankelMat_eq A B C G hG, hfac])
  refine ⟨T, hT, ?_, ?_, ?_⟩
  · -- (6.12): Ahat = (𝒪_k T)^† (𝒪_k A T) = (𝒪_k T)^† (𝒪_k T)(T⁻¹AT) = T⁻¹AT
    have hdown : Ohat.submatrix (fun r : Fin k × Fin p => (r.1.castSucc, r.2))
        id = obsMat k C A * T := by
      rw [hOT, ← obsMat_castSucc A C k]; rfl
    have hup : Ohat.submatrix (fun r : Fin k × Fin p => (r.1.succ, r.2))
        id = obsMat k C A * T * (T⁻¹ * A * T) := by
      rw [hOT, Matrix.mul_assoc _ T, Matrix.mul_assoc T⁻¹,
        Matrix.mul_nonsing_inv_cancel_left T _ hT, ← Matrix.mul_assoc,
        ← obsMat_succ A C k]
      rfl
    have hrank : (obsMat k C A * T).rank = n := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det T _ hT, hO]
    rw [hoKalmanA, hdown, hup, ← Matrix.mul_assoc, pinv_mul hrank,
      Matrix.one_mul]
  · -- Bhat = first block column of T⁻¹ 𝒞_{l+1} = T⁻¹ B
    rw [hoKalmanB, hRT]
    calc (T⁻¹ * reachMat (l + 1) A B).submatrix id (fun b => (0, b))
        = T⁻¹ * (reachMat (l + 1) A B).submatrix id (fun b => (0, b)) :=
          rfl
      _ = T⁻¹ * B := by congr 1; ext x b; simp [reachMat]
  · -- Chat = first block row of 𝒪_{k+1} T = C T
    rw [hoKalmanC, hOT]
    calc (obsMat (k + 1) C A * T).submatrix (fun a => (0, a)) id
        = (obsMat (k + 1) C A).submatrix (fun a => (0, a)) id * T := rfl
      _ = C * T := by congr 1; ext a x; simp [obsMat]
-- ANCHOR_END: hoKalman

-- ANCHOR: minimal_markov
/-- For a minimal system, Steps 2–3 reproduce every Markov parameter,
`Chat Ahatᵗ Bhat = G_{t+1}`, as soon as `H` has `k + 1 > n` block rows and
`l + 1 ≥ n` block columns. -/
theorem hoKalman_of_minimal (hmin : IsMinimal A B C)
    (hG : ∀ t, G (t + 1) = C * A ^ t * B) {k l : ℕ} (hk : n ≤ k)
    (hl : n ≤ l + 1) (Ohat : Matrix (Fin (k + 1) × Fin p) (Fin n) ℝ)
    (Rhat : Matrix (Fin n) (Fin (l + 1) × Fin m) ℝ)
    (hfac : hankelMat (k + 1) (l + 1) G = Ohat * Rhat) (t : ℕ) :
    hoKalmanC Ohat * hoKalmanA Ohat ^ t * hoKalmanB Rhat = G (t + 1) := by
  obtain ⟨T, hT, hA, hB, hC⟩ := hoKalman A B C G hG
    (rank_obsMat_of_le A C hmin.1 hk) (rank_reachMat_of_le A B hmin.2 hl)
    Ohat Rhat hfac
  -- (CT)(T⁻¹AT)ᵗ(T⁻¹B) = C Aᵗ B
  rw [hA, hB, hC, conj_pow A T hT, hG]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left T _ hT]
-- ANCHOR_END: minimal_markov

end SysId

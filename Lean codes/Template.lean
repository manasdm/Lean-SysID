/-
# A template and building blocks for system identification in Lean

Notation follows Ljung (1999), System Identification: Theory for the User.

* `Signal`, `ModelStructure` : a signal is `ℤ → ℝ`; a model structure maps a parameter `θ` to
                               the one-step-ahead predictor `ŷ(t|θ)` (Def. 4.3, eq. (4.6)).
* `IsIdentifiable`           : global identifiability, `M(θ₁) = M(θ₂) → θ₁ = θ₂` (Defs. 4.6–4.7).
* `ARXParams`, `arx`         : the ARX structure (4.7)–(4.8), with predictor (4.10)–(4.12).
* `arx_isIdentifiable`       : ARX is strictly globally identifiable (Sec. 4.6, after (4.139)).
* `predErr`, `VN`            : prediction error (7.8) and PEM criterion (7.11), `ℓ(ε) = ε²`.
* `VN_min_at_true`           : without noise, the true parameter minimizes `V_N`, cf. (7.12).
* `regressor`, `IsPE`        : persistent excitation of order `n` from `N` samples,
                               `∑ φ(t) φ(t)ᵀ ≻ 0` (cf. Def. 13.1, Lemma 13.1).
* `simulate`                 : state-space recursion `x(t+1) = A x(t) + B u(t)`.
* `simulate_zero_input`      : with zero input, `x(t) = Aᵗ x(0)`, by induction on `t`.

This file imports only Mathlib and compiles on its own.
-/
import Mathlib

open Matrix

namespace SysId

-- ANCHOR: blocks
-- a signal u(t), t ∈ ℤ
abbrev Signal := ℤ → ℝ
-- a model structure (Def. 4.3): M θ u y t is the prediction ŷ(t|θ)
abbrev ModelStructure (Θ : Type) := Θ → Signal → Signal → Signal
variable {Θ : Type}
-- global identifiability (Defs. 4.6-4.7)
def IsIdentifiable (M : ModelStructure Θ) : Prop :=
  ∀ θ₁ θ₂ : Θ, M θ₁ = M θ₂ → θ₁ = θ₂
-- ANCHOR_END: blocks

-- ANCHOR: template
-- Step 1: ARX model parameters. See Ljung's (4.8).
@[ext] structure ARXParams (na nb : ℕ) where
  a : Fin na → ℝ    -- a i is the coefficient of y(t-1-i)
  b : Fin nb → ℝ    -- b j is the coefficient of u(t-1-j)

-- Step 2: the model structure, given by its predictor (4.10)-(4.12).
def arx (na nb : ℕ) : ModelStructure (ARXParams na nb) :=
  fun θ u y t =>
    -∑ i, θ.a i * y (t - 1 - i.val) + ∑ j, θ.b j * u (t - 1 - j.val)

-- A unit pulse at time s: the test signal of the proof.
def pulse (s : ℤ) : Signal := fun t => if t = s then 1 else 0

-- Step 3: the claim, first stated with `sorry` as its proof.
theorem arx_isIdentifiable (na nb : ℕ) :
    IsIdentifiable (arx na nb) := by
  -- Step 4: the proof. A pulse in y (or u) isolates one coefficient.
  intro θ₁ θ₂ h                     -- h : arx θ₁ = arx θ₂
  have hM : ∀ u y t, arx na nb θ₁ u y t = arx na nb θ₂ u y t := by
    intro u y t; rw [h]             -- equal predictions everywhere
  ext i                             -- compare a i, then b i
  · -- u = 0, y = pulse at time -1-i: ŷ(0|θ) = -a i
    simpa [arx, pulse, Fin.val_inj] using hM 0 (pulse (-1 - i.val)) 0
  · -- u = pulse at time -1-i, y = 0: ŷ(0|θ) = b i
    simpa [arx, pulse, Fin.val_inj] using hM (pulse (-1 - i.val)) 0 0
-- ANCHOR_END: template

-- ANCHOR: pem
/-- Prediction error `ε(t,θ) = y(t) - ŷ(t|θ)` (7.8). -/
def predErr (M : ModelStructure Θ) (θ : Θ) (u y : Signal) (t : ℤ) :
    ℝ :=
  y t - M θ u y t

/-- PEM criterion (7.11): the mean of `ε(t,θ)²` over `t = 1, …, N`. -/
noncomputable def VN (M : ModelStructure Θ) (N : ℕ) (u y : Signal)
    (θ : Θ) : ℝ :=
  (1 / N) * ∑ t ∈ Finset.range N, predErr M θ u y (t + 1) ^ 2

/-- Without noise, `y(t) = ŷ(t|θ₀)`, the true θ₀ minimizes `V_N`. -/
theorem VN_min_at_true (M : ModelStructure Θ) (N : ℕ) (u y : Signal)
    (θ₀ : Θ) (hy : ∀ t, y t = M θ₀ u y t) (θ : Θ) :
    VN M N u y θ₀ ≤ VN M N u y θ := by
  have h0 : VN M N u y θ₀ = 0 := by
    simp [VN, predErr, ← hy]        -- every ε(t,θ₀) is 0
  rw [h0]                           -- goal: 0 ≤ V_N(θ)
  unfold VN
  positivity                        -- a sum of squares is ≥ 0
-- ANCHOR_END: pem

-- ANCHOR: pe
/-- Regressor `φ(t) = [u(t-1), …, u(t-n)]ᵀ`. -/
def regressor (u : Signal) (n : ℕ) (t : ℤ) : Fin n → ℝ :=
  fun i => u (t - 1 - i.val)

/-- Persistent excitation of order `n` from `N` samples:
`∑_{t=1}^{N} φ(t) φ(t)ᵀ ≻ 0`. -/
def IsPE (u : Signal) (n N : ℕ) : Prop :=
  (∑ t ∈ Finset.range N,
    vecMulVec (regressor u n (t + 1)) (regressor u n (t + 1))).PosDef
-- ANCHOR_END: pe

-- ANCHOR: sim
/-- State-space recursion `x(t+1) = A x(t) + B u(t)`, `x(0) = x₀`. -/
def simulate {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (x₀ : Fin n → ℝ)
    (u : ℕ → Fin m → ℝ) : ℕ → Fin n → ℝ
  | 0 => x₀
  | t + 1 => A *ᵥ simulate A B x₀ u t + B *ᵥ u t

/-- With zero input, `x(t) = Aᵗ x(0)`. -/
theorem simulate_zero_input {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (x₀ : Fin n → ℝ) (t : ℕ) :
    simulate A B x₀ 0 t = (A ^ t) *ᵥ x₀ := by
  induction t with
  | zero => simp [simulate]         -- x(0) = x₀ = A⁰ x₀
  | succ t ih =>                    -- x(t+1) = A x(t) = A Aᵗ x₀
    rw [simulate, ih, pow_succ', ← mulVec_mulVec]
    simp
-- ANCHOR_END: sim

end SysId

/-
# Identifiability and persistent excitation from one step of data (Lemma 1)

The scalar data-generating system is `y_k = φ_k θ`, with unknown true parameter `θ`, regressor
`φ_k` and measured output `y_k`. From the single-step data `D = {φ₁, y₁}` the algebraic
estimator is `θ̂ = y₁ / φ₁`. The parameter is identifiable from `D` when two different
parameters never produce the same data, i.e. when `θ ↦ φ₁ θ` is injective.

* `identifiable_iff_PE` : `θ` is identifiable from `D` if and only if `φ₁ ≠ 0` (single-step PE).
* `estimator_exact`     : under PE the estimator is exact, `θ̂ = y₁ / φ₁ = θ`.

This file imports only Mathlib and compiles on its own.
-/
import Mathlib

namespace Identification

-- ANCHOR: identify
-- θ is identifiable from D = {φ₁, y₁}: equal outputs force equal θ.
def Identifiable (φ₁ : ℝ) : Prop :=
  ∀ θ₁ θ₂ : ℝ, φ₁ * θ₁ = φ₁ * θ₂ → θ₁ = θ₂

-- Lemma 1: θ is identifiable from D if and only if φ₁ ≠ 0 (PE).
theorem identifiable_iff_PE (φ₁ : ℝ) : Identifiable φ₁ ↔ φ₁ ≠ 0 := by
  constructor
  · intro hid hφ                      -- only if: suppose φ₁ = 0
    have h01 := hid 0 1 (by simp [hφ]) -- θ = 0, θ = 1: same output
    norm_num at h01                   -- h01 : 0 = 1, contradiction
  · intro hφ θ₁ θ₂ hy              -- if: φ₁ ≠ 0 and φ₁ θ₁ = φ₁ θ₂
    exact mul_left_cancel₀ hφ hy   -- cancel φ₁

-- Lemma 1 (estimator): under PE the estimate θ̂ = y₁ / φ₁ is the true θ.
theorem estimator_exact (θ φ₁ y₁ : ℝ) (hdata : y₁ = φ₁ * θ)
    (hφ : φ₁ ≠ 0) : y₁ / φ₁ = θ := by
  rw [hdata]        -- goal becomes  φ₁ * θ / φ₁ = θ
  field_simp        -- cancel φ₁; allowed because hφ : φ₁ ≠ 0
-- ANCHOR_END: identify

end Identification

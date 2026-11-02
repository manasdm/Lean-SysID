import Mathlib

/-!
# A first taste of Lean for control people

Very small examples for the introduction of the tutorial paper
"Lean for system identification and control".
-/

namespace Tutorial

/-! ## (1) The simplest possible proof -/

-- If ρ < 1 then 1 - ρ > 0.  The tactic `linarith` (linear arithmetic)
-- closes the goal in one step; afterwards there are no goals left.
-- ANCHOR: ex1
example (ρ : ℝ) (h : ρ < 1) : 0 < 1 - ρ := by
  linarith
-- ANCHOR_END: ex1

/-! ## (2) The same fact, step by step -/

-- `sub_pos : 0 < a - b ↔ b < a` is a Mathlib lemma.
-- ANCHOR: ex2
example (ρ : ℝ) (h : ρ < 1) : 0 < 1 - ρ := by
    rw [sub_pos]   -- rewrite the goal  0 < 1 - ρ  into  ρ < 1
    exact h        -- this is exactly the hypothesis h: no goals left
-- ANCHOR_END: ex2

/-! ## (3) Scalar invariance: x⁺ = a x with |a| ≤ 1 -/

-- ANCHOR: scalar
-- The interval {x | |x| ≤ r} is invariant for x⁺ = a x when |a| ≤ 1.
theorem interval_invariant (a r x : ℝ) (ha : |a| ≤ 1) (hx : |x| ≤ r) :
    |a * x| ≤ r := by
  rw [abs_mul]   -- goal becomes  |a| * |x| ≤ r
  calc |a| * |x| ≤ 1 * |x| :=
        mul_le_mul_of_nonneg_right ha (abs_nonneg x)
    _ = |x| := one_mul |x|   -- 1 * |x| = |x|
    _ ≤ r := hx              -- the hypothesis hx (initial state)
-- ANCHOR_END: scalar

/-! ## (4) Invariance along the whole trajectory, by induction -/

-- ANCHOR: induction
-- The trajectory x_k of x⁺ = a x, defined by recursion on k.
def traj (a x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀                       -- x_0 = x₀
  | k + 1 => a * traj a x₀ k      -- x_{k+1} = a x_k

-- If |a| ≤ 1 and |x₀| ≤ r, then |x_k| ≤ r for every k.
theorem traj_bounded (a x₀ r : ℝ) (ha : |a| ≤ 1) (h0 : |x₀| ≤ r) :
    ∀ k, |traj a x₀ k| ≤ r := by
  intro k              -- fix an arbitrary k : ℕ
  induction k with
  | zero =>            -- base case k = 0
    rw [traj]          -- unfold traj: goal becomes |x₀| ≤ r
    exact h0
  | succ k ih =>       -- step: from ih : |x_k| ≤ r prove |x_{k+1}| ≤ r
    rw [traj]          -- unfold traj: goal becomes |a * x_k| ≤ r
    exact interval_invariant a r (traj a x₀ k) ha ih   -- reuse Claim 1
-- ANCHOR_END: induction

end Tutorial

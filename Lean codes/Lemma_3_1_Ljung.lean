import Mathlib

/-!
# Ljung (1999), Lemma 3.1 — inverting the noise filter

L. Ljung, *System Identification: Theory for the User*, 2nd ed., Section 3.2.

Consider `v(t) = H(q) e(t) = ∑ₖ h(k) e(t-k)`, `H(z) = ∑ₖ h(k) z⁻ᵏ`, `1/H(z) = ∑ₖ h̃(k) z⁻ᵏ`, and
define the filter `H⁻¹(q) = ∑ₖ h̃(k) q⁻ᵏ`.

**Assumptions.**
* (A1) `H` is stable: `∑ₖ |h(k)| < ∞`, and `H⁻¹` is stable: `∑ₖ |h̃(k)| < ∞` (Remark 1).
* (A2) `1/H(z) = ∑ₖ h̃(k) z⁻ᵏ` holds, with a convergent series, for every `|z| ≥ 1`.
* (A3) `sup_t E|e(t)| < ∞` (this follows from zero-mean white noise with finite variance `λ`:
  `E|e(t)| ≤ √λ`, see `whiteNoise_A3`).

**Lemma 5 (precise form of Ljung's Lemma 3.1), `lemma_3_1` below.** Under (A1)–(A3), with
probability one, for every `t ∈ ℤ`, the series defining `v(t)` converges absolutely and
`H⁻¹(q) v(t) = ∑ₖ h̃(k) v(t-k) = e(t)`, where the series converges absolutely.

Proof (Ljung's, with the missing steps added):
* Step A (`eq_3_10`): Cauchy product and uniqueness of power-series coefficients give
  `∑_{k=0}^{ℓ} h(k) h̃(ℓ-k) = δ(ℓ)`;
* the double series `∑_{k,s} h̃(k) h(s) e(t-k-s)` converges absolutely almost surely
  (`ae_absConv`, from Tonelli and (A3));
* Step B (`inverse_filter_hasSum`): under that absolute convergence the order of summation may be
  changed, giving `∑ₖ h̃(k) v(t-k) = e(t)`.
Remark 1 (`remark_inverse_stable`): Ljung's hypothesis that `1/H` is analytic on a neighbourhood
of `{|z| ≥ 1} ∪ {∞}` implies the stability of `H⁻¹` in (A1). It is not needed for Lemma 5.

Lean conventions: `∑'` is unconditional (= absolute) summation and equals `0` for a divergent
series, so the conclusion uses `HasSum` (convergence *and* value).
-/

noncomputable section

namespace Ljung31

/-! ## Definitions -/

/-- `H(q) e (t) = ∑_{k ≥ 0} h(k) e(t-k)` (Ljung (3.4)). Time `t : ℤ`, lags `k : ℕ`. -/
def filt (h : ℕ → ℝ) (e : ℤ → ℝ) (t : ℤ) : ℝ := ∑' k : ℕ, h k * e (t - k)

/-- Stability (Ljung (2.27), (3.5)): `∑ₖ |h(k)| < ∞`. -/
def IsStable (h : ℕ → ℝ) : Prop := Summable fun k => |h k|

/-- Convolution `(a ⋆ b)(n) = ∑_{k=0}^{n} a(k) b(n-k)` (left side of (3.10)). -/
def conv (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2

/-- Kronecker delta `δ(n)` (right side of (3.10)). -/
def kron (n : ℕ) : ℝ := if n = 0 then 1 else 0

/-- z-transform `H(z) = ∑ₖ h(k) z⁻ᵏ` (Ljung (3.7)). -/
def zT (h : ℕ → ℝ) (z : ℂ) : ℂ := ∑' k : ℕ, (h k : ℂ) * z⁻¹ ^ k

/-- (AC): absolute convergence of the double series of Step B at time `t`. -/
def AbsConv (h ht : ℕ → ℝ) (e : ℤ → ℝ) (t : ℤ) : Prop :=
  Summable fun p : ℕ × ℕ => |ht p.1| * |h p.2| * |e (t - p.1 - p.2)|

/-- White noise (Ljung §2.1): independent random variables, zero mean, variance `λ`. -/
structure IsWhiteNoise {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (e : ℤ → Ω → ℝ) (lam : ℝ) : Prop where
  indep : ProbabilityTheory.iIndepFun e μ
  memLp : ∀ t, MeasureTheory.MemLp (e t) 2 μ
  zero_mean : ∀ t, ∫ ω, e t ω ∂μ = 0
  variance : ∀ t, ∫ ω, e t ω ^ 2 ∂μ = lam

theorem conv_comm (a b : ℕ → ℝ) : conv a b = conv b a := by
  funext n
  unfold conv
  rw [← Finset.Nat.sum_antidiagonal_swap]
  simp [mul_comm]

/-! ## Step A: `h ⋆ h̃ = δ` (3.10) -/

section StepA

open Finset Filter Topology

/-- Uniqueness of power-series coefficients ("comparing coefficients"). -/
theorem coeff_unique (c : ℕ → ℂ) (hc : Summable fun n => ‖c n‖) (r : ℝ) (hr : 0 < r)
    (h1 : ∀ w : ℂ, w ≠ 0 → ‖w‖ < r → ∑' n, c n * w ^ n = 1) :
    ∀ n, c n = if n = 0 then 1 else 0 := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c with hp
  have hrad : ((1 : NNReal) : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_summable_norm ?_
    simpa [p] using hc
  have hpos : 0 < p.radius := lt_of_lt_of_le (by simp) hrad
  have hball : HasFPowerSeriesOnBall p.sum p 0 p.radius := p.hasFPowerSeriesOnBall hpos
  have hsum : ∀ w, p.sum w = ∑' n, c n * w ^ n := fun w => by
    show FormalMultilinearSeries.ofScalarsSum c w = _
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    rfl
  have hev : ∀ᶠ w in 𝓝[≠] (0:ℂ), p.sum w = 1 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0:ℂ) hr),
      self_mem_nhdsWithin] with w hw hw0
    rw [hsum]
    exact h1 w hw0 (by simpa using hw)
  have hcont : ContinuousAt p.sum 0 := hball.hasFPowerSeriesAt.continuousAt
  have h0 : p.sum 0 = 1 := by
    have t1 : Tendsto p.sum (𝓝[≠] (0:ℂ)) (𝓝 (p.sum 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto p.sum (𝓝[≠] (0:ℂ)) (𝓝 1) :=
      tendsto_const_nhds.congr' (hev.mono fun w hw => hw.symm)
    exact tendsto_nhds_unique t1 t2
  have hev2 : p.sum =ᶠ[𝓝 0] fun _ => (1:ℂ) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr] with w hw
    by_cases hw0 : w = 0
    · subst hw0; exact h0
    · rw [hsum]; exact h1 w hw0 (by simpa using hw)
  have hfps : HasFPowerSeriesAt (fun _ => (1:ℂ)) p 0 := hball.hasFPowerSeriesAt.congr hev2
  have heq : p = constFormalMultilinearSeries ℂ ℂ (1:ℂ) :=
    hfps.eq_formalMultilinearSeries hasFPowerSeriesAt_const
  intro n
  have := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q n (fun _ => 1)) heq
  simp only [p, FormalMultilinearSeries.ofScalars_apply_eq] at this
  rcases n with _ | n
  · simpa using this
  · simpa using this

/-- Cauchy product of the z-transforms (first equality of Step A), for `|z| ≥ 1`. -/
theorem zT_mul_zT (h ht : ℕ → ℝ) (hh : IsStable h) (hht : IsStable ht) (z : ℂ) (hz : 1 ≤ ‖z‖) :
    zT h z * zT ht z = ∑' n, (conv h ht n : ℂ) * z⁻¹ ^ n := by
  have hz1 : ‖z⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hz
  have hpow : ∀ k : ℕ, ‖z⁻¹ ^ k‖ ≤ 1 := fun k => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz1
  have hbd : ∀ a : ℕ → ℝ, IsStable a → Summable fun k => ‖(a k : ℂ) * z⁻¹ ^ k‖ := by
    intro a ha
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) ha
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (hpow k)
  unfold zT
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (hbd h hh) (hbd ht hht)]
  refine tsum_congr fun n => ?_
  unfold conv
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hkl' : kl.1 + kl.2 = n := by simpa using hkl
  rw [← hkl', pow_add]
  ring

/-- **Step A, (3.10)**: `∑_{k=0}^{ℓ} h(k) h̃(ℓ-k) = δ(ℓ)`. Only `|z| ≥ ρ` (near `z = ∞`) is used. -/
theorem eq_3_10 (h ht : ℕ → ℝ) (hh : IsStable h) (hht : IsStable ht) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (h38 : ∀ z : ℂ, ρ ≤ ‖z‖ → zT h z * zT ht z = 1) :
    ∀ n, conv h ht n = kron n := by
  set c : ℕ → ℂ := fun n => (conv h ht n : ℂ) with hcdef
  have hh' : Summable fun k => ‖h k‖ := by
    have : Summable fun k => |h k| := hh
    simpa only [Real.norm_eq_abs] using this
  have hht' : Summable fun k => ‖ht k‖ := by
    have : Summable fun k => |ht k| := hht
    simpa only [Real.norm_eq_abs] using this
  have hcs : Summable fun n => ‖c n‖ := by
    have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hh' hht'
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => le_of_eq ?_) hs
    show ‖((conv h ht n : ℝ) : ℂ)‖ = _
    exact Complex.norm_real _
  have hρpos : 0 < ρ := by linarith
  have key := coeff_unique c hcs (1 / ρ) (by positivity) (fun w hw0 hw => by
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hz : ρ ≤ ‖w⁻¹‖ := by
      rw [norm_inv]
      rw [one_div] at hw
      exact (le_inv_comm₀ hρpos hwpos).mpr hw.le
    have h1 : 1 ≤ ‖w⁻¹‖ := le_trans hρ hz
    have := zT_mul_zT h ht hh hht w⁻¹ h1
    rw [h38 _ hz, inv_inv] at this
    exact this.symm)
  intro n
  have hn : ((conv h ht n : ℝ) : ℂ) = ((kron n : ℝ) : ℂ) := by
    rw [show ((conv h ht n : ℝ) : ℂ) = c n from rfl, key n, kron]
    split_ifs <;> simp
  exact_mod_cast hn

/-! ## Remark: `H⁻¹` is stable -/

/-- **Remark 1** (Ljung): if `∑ₖ h̃(k) z⁻ᵏ` converges for all `|z| > ρ` with `ρ < 1`
(`1/H` analytic in a neighbourhood of `{|z| ≥ 1} ∪ {∞}`), then `∑ₖ |h̃(k)| < ∞`, i.e. `H⁻¹` is
stable, as required in (A1). Not used in the proof of Lemma 5. -/
theorem remark_inverse_stable (ht : ℕ → ℝ) (ρ : ℝ) (hρ : ρ < 1)
    (hconv : ∀ z : ℂ, ρ < ‖z‖ → Summable fun k => (ht k : ℂ) * z⁻¹ ^ k) : IsStable ht := by
  -- pick `r` with `max ρ 0 < r < 1`; convergence at `z = r` forces `|h̃(k)| r⁻ᵏ → 0`,
  -- so `|h̃(k)| ≤ rᵏ` eventually, and the geometric series `∑ rᵏ` dominates.
  set r : ℝ := (1 + max ρ 0) / 2 with hrdef
  have hm0 : 0 ≤ max ρ 0 := le_max_right ρ 0
  have hmρ : ρ ≤ max ρ 0 := le_max_left ρ 0
  have hm1 : max ρ 0 < 1 := max_lt hρ one_pos
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hr1 : r < 1 := by rw [hrdef]; linarith
  have hρr : ρ < r := by rw [hrdef]; linarith
  have hs := hconv (r : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]; exact hρr)
  have ht0 := hs.tendsto_atTop_zero.norm
  rw [norm_zero] at ht0
  have hev : ∀ᶠ k in atTop, ‖(ht k : ℂ) * (r : ℂ)⁻¹ ^ k‖ < 1 :=
    ht0.eventually (gt_mem_nhds zero_lt_one)
  have hgeom : Summable fun k : ℕ => r ^ k := summable_geometric_of_lt_one hr0.le hr1
  refine Summable.of_norm_bounded_eventually_nat hgeom ?_
  filter_upwards [hev] with k hk
  have hrk : 0 < r ^ k := pow_pos hr0 k
  rw [norm_mul, Complex.norm_real, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hr0, inv_pow, ← div_eq_mul_inv, div_lt_one hrk] at hk
  rw [Real.norm_eq_abs, abs_abs]
  exact hk.le

end StepA

/-! ## Step B: `∑ₖ h̃(k) v(t-k) = e(t)` under (AC) -/

section StepB

open Finset

/-- Regrouping a summable double series along the anti-diagonals `k + s = ℓ`. -/
theorem tsum_prod_eq_tsum_antidiagonal {f : ℕ × ℕ → ℝ} (hf : Summable f) :
    ∑' p, f p = ∑' n, ∑ p ∈ antidiagonal n, f p := by
  conv_rhs => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq f]
  exact (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hf).tsum_sigma'
    (fun n ↦ (hasSum_fintype _).summable)

/-- Step B (value): if `h̃ ⋆ h = δ` and (AC) holds at `t`, then `∑ₖ h̃(k) v(t-k) = e(t)`. -/
theorem inverse_filter_core (h ht : ℕ → ℝ) (e : ℤ → ℝ) (t : ℤ)
    (hδ : ∀ n, conv ht h n = kron n) (hAC : AbsConv h ht e t) :
    ∑' k, ht k * filt h e (t - k) = e t := by
  set f : ℕ × ℕ → ℝ := fun p => ht p.1 * (h p.2 * e (t - p.1 - p.2)) with hfdef
  have hf : Summable f := by
    refine Summable.of_norm ?_
    refine hAC.congr fun p => ?_
    simp only [hfdef, Real.norm_eq_abs, abs_mul, mul_assoc]
  have h1 : ∀ k : ℕ, ht k * filt h e (t - k) = ∑' s, f (k, s) := by
    intro k
    simp only [filt, hfdef, ← tsum_mul_left]
  have h2 : ∀ n : ℕ, ∑ p ∈ antidiagonal n, f p = conv ht h n * e (t - n) := by
    intro n
    simp only [conv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have : t - (p.1 : ℤ) - (p.2 : ℤ) = t - (n : ℤ) := by
      rw [← hp]; push_cast; ring
    simp only [hfdef, this]
    ring
  calc ∑' k, ht k * filt h e (t - k) = ∑' k, ∑' s, f (k, s) := tsum_congr h1
    _ = ∑' p, f p := hf.tsum_prod.symm
    _ = ∑' n, ∑ p ∈ antidiagonal n, f p := tsum_prod_eq_tsum_antidiagonal hf
    _ = ∑' n : ℕ, conv ht h n * e (t - n) := tsum_congr h2
    _ = e t := by
      simp only [hδ, kron, ite_mul, one_mul, zero_mul]
      simp

/-- **Step B**: under (AC) the series `∑ₖ h̃(k) v(t-k)` converges, and its sum is `e(t)`. -/
theorem inverse_filter_hasSum (h ht : ℕ → ℝ) (e : ℤ → ℝ) (t : ℤ)
    (hδ : ∀ n, conv ht h n = kron n) (hAC : AbsConv h ht e t) :
    HasSum (fun k => ht k * filt h e (t - k)) (e t) := by
  set f : ℕ × ℕ → ℝ := fun p => ht p.1 * (h p.2 * e (t - p.1 - p.2)) with hfdef
  have hf : Summable f := by
    refine Summable.of_norm ?_
    refine hAC.congr fun p => ?_
    simp only [hfdef, Real.norm_eq_abs, abs_mul, mul_assoc]
  have h1 : ∀ k : ℕ, ht k * filt h e (t - k) = ∑' s, f (k, s) := by
    intro k
    simp only [filt, hfdef, ← tsum_mul_left]
  have hs : Summable fun k => ht k * filt h e (t - k) :=
    hf.prod.congr fun k => (h1 k).symm
  have hsum := hs.hasSum
  rwa [inverse_filter_core h ht e t hδ hAC] at hsum

end StepB

/-! ## (AC) and convergence of (3.4) hold almost surely -/

section Probability

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Tonelli for series: weighted sums of random variables with bounded first absolute moments
converge absolutely almost surely. -/
theorem ae_summable_weighted {μ : Measure Ω} {ι : Type*} [Countable ι]
    (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha : Summable a)
    (X : ι → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (C : ENNReal) (hC : C ≠ ⊤) (hb : ∀ i, ∫⁻ ω, ‖X i ω‖ₑ ∂μ ≤ C) :
    ∀ᵐ ω ∂μ, Summable fun i => a i * |X i ω| := by
  set g : Ω → ENNReal := fun ω => ∑' i, ENNReal.ofReal (a i) * ‖X i ω‖ₑ with hg
  have hmeas : ∀ i, AEMeasurable (fun ω => ENNReal.ofReal (a i) * ‖X i ω‖ₑ) μ :=
    fun i => (hX i).enorm.const_mul _
  have h1 : ∫⁻ ω, g ω ∂μ = ∑' i, ENNReal.ofReal (a i) * ∫⁻ ω, ‖X i ω‖ₑ ∂μ := by
    rw [hg, lintegral_tsum hmeas]
    congr 1
    funext i
    exact lintegral_const_mul'' _ (hX i).enorm
  have h2 : ∑' i, ENNReal.ofReal (a i) * ∫⁻ ω, ‖X i ω‖ₑ ∂μ ≤ ∑' i, ENNReal.ofReal (a i) * C :=
    Summable.tsum_le_tsum (fun i => by gcongr; exact hb i) (by simp) (by simp)
  rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg ha0 ha] at h2
  have hint : ∫⁻ ω, g ω ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC) (h1 ▸ h2)
  have hae := ae_lt_top' (AEMeasurable.tsum hmeas) hint
  filter_upwards [hae] with ω hω
  have hs := ENNReal.summable_toReal hω.ne
  refine hs.congr fun i => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (ha0 i),
    ENNReal.toReal_ofReal (mul_nonneg (ha0 i) (abs_nonneg _))]

/-- (AC) holds almost surely, for all `t ∈ ℤ` simultaneously. -/
theorem ae_absConv {μ : Measure Ω} (h ht : ℕ → ℝ) (hh : IsStable h) (hht : IsStable ht)
    (e : ℤ → Ω → ℝ) (he : ∀ t, AEMeasurable (e t) μ)
    (C : ENNReal) (hC : C ≠ ⊤) (hb : ∀ t, ∫⁻ ω, ‖e t ω‖ₑ ∂μ ≤ C) :
    ∀ᵐ ω ∂μ, ∀ t : ℤ, AbsConv h ht (fun s => e s ω) t := by
  rw [ae_all_iff]
  intro t
  have ha : Summable fun p : ℕ × ℕ => |ht p.1| * |h p.2| :=
    Summable.mul_of_nonneg (f := fun k => |ht k|) (g := fun k => |h k|) hht hh
      (fun k => abs_nonneg (ht k)) (fun k => abs_nonneg (h k))
  have hw := ae_summable_weighted (μ := μ) (fun p : ℕ × ℕ => |ht p.1| * |h p.2|)
    (fun p => mul_nonneg (abs_nonneg _) (abs_nonneg _)) ha
    (fun p ω => e (t - p.1 - p.2) ω) (fun p => he _) C hC (fun p => hb _)
  filter_upwards [hw] with ω hω
  exact hω

/-- (3.4) converges absolutely almost surely, for all `t ∈ ℤ` simultaneously. -/
theorem ae_filt_summable {μ : Measure Ω} (h : ℕ → ℝ) (hh : IsStable h)
    (e : ℤ → Ω → ℝ) (he : ∀ t, AEMeasurable (e t) μ)
    (C : ENNReal) (hC : C ≠ ⊤) (hb : ∀ t, ∫⁻ ω, ‖e t ω‖ₑ ∂μ ≤ C) :
    ∀ᵐ ω ∂μ, ∀ t : ℤ, Summable fun k : ℕ => |h k| * |e (t - k) ω| := by
  rw [ae_all_iff]
  intro t
  exact ae_summable_weighted (μ := μ) (fun k => |h k|) (fun k => abs_nonneg (h k)) hh
    (fun k ω => e (t - k) ω) (fun k => he _) C hC (fun k => hb _)

/-- For white noise, `E|e(t)| ≤ √λ`. -/
theorem IsWhiteNoise.lintegral_enorm_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {e : ℤ → Ω → ℝ} {lam : ℝ} (hw : IsWhiteNoise μ e lam) (t : ℤ) :
    ∫⁻ ω, ‖e t ω‖ₑ ∂μ ≤ ENNReal.ofReal (Real.sqrt lam) := by
  have hY : MemLp (fun ω => ‖e t ω‖) 2 μ := (hw.memLp t).norm
  have hint : Integrable (e t) μ := (hw.memLp t).integrable one_le_two
  have hvar := variance_eq_sub hY
  have hnn := variance_nonneg (fun ω => ‖e t ω‖) μ
  have hsq : ∫ ω, ((fun ω => ‖e t ω‖) ^ 2) ω ∂μ = lam := by
    rw [← hw.variance t]
    congr 1
    funext ω
    simp [Real.norm_eq_abs, sq_abs]
  rw [hsq] at hvar
  have hle : (∫ ω, ‖e t ω‖ ∂μ) ^ 2 ≤ lam := by linarith
  rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Real.abs_le_sqrt hle))

end Probability

/-! ## Lemma 3.1 -/

section Main

open MeasureTheory

/-- **Lemma 5 (precise form of Ljung (1999), Lemma 3.1).** Consider `v(t) = ∑ₖ h(k) e(t-k)` (4).
Let `H(z) = ∑ₖ h(k) z⁻ᵏ`, `1/H(z) = ∑ₖ h̃(k) z⁻ᵏ` (10), and define `H⁻¹(q) = ∑ₖ h̃(k) q⁻ᵏ`.
Under assumptions (A1)–(A3), with probability one, for every `t ∈ ℤ`, the series defining `v(t)`
converges absolutely and `H⁻¹(q) v(t) = ∑ₖ h̃(k) v(t-k) = e(t)`, where the series converges
absolutely; that is, `H̃(q) = H⁻¹(q)` satisfies (5). -/
theorem lemma_3_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h ht : ℕ → ℝ) (e : ℤ → Ω → ℝ) (he : ∀ t, AEMeasurable (e t) μ)
    -- (A1) `H` is stable and `H⁻¹` is stable
    (hA1 : IsStable h ∧ IsStable ht)
    -- (A2) `1/H(z) = ∑ₖ h̃(k) z⁻ᵏ` (convergent) for every `|z| ≥ 1`, i.e. `H(z) · ∑ₖ h̃(k) z⁻ᵏ = 1`
    (hA2 : ∀ z : ℂ, 1 ≤ ‖z‖ → zT h z * zT ht z = 1)
    -- (A3) `sup_t E|e(t)| < ∞`
    (hA3 : ∃ C : ℝ, ∀ t, ∫⁻ ω, ‖e t ω‖ₑ ∂μ ≤ ENNReal.ofReal C) :
    ∀ᵐ ω ∂μ, ∀ t : ℤ,
      Summable (fun k : ℕ => |h k| * |e (t - k) ω|) ∧
      HasSum (fun k : ℕ => ht k * filt h (fun s => e s ω) (t - k)) (e t ω) := by
  obtain ⟨hH, hHt⟩ := hA1
  obtain ⟨C, hC⟩ := hA3
  -- Step A: `h ⋆ h̃ = δ`, hence `h̃ ⋆ h = δ`
  have hδ : ∀ n, conv h ht n = kron n := eq_3_10 h ht hH hHt 1 le_rfl hA2
  have hδ' : ∀ n, conv ht h n = kron n := fun n => by rw [conv_comm]; exact hδ n
  -- the double series converges absolutely, and (3.4) converges, almost surely
  filter_upwards [ae_absConv (μ := μ) h ht hH hHt e he _ ENNReal.ofReal_ne_top hC,
    ae_filt_summable (μ := μ) h hH e he _ ENNReal.ofReal_ne_top hC] with ω hAC hS
  -- Step B, pathwise
  intro t
  exact ⟨hS t, inverse_filter_hasSum h ht (fun s => e s ω) t hδ' (hAC t)⟩

/-- (A3) holds for white noise (Ljung's setting): `E|e(t)| ≤ √λ`. -/
theorem whiteNoise_A3 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {e : ℤ → Ω → ℝ} {lam : ℝ} (hw : IsWhiteNoise μ e lam) :
    (∀ t, AEMeasurable (e t) μ) ∧ ∃ C : ℝ, ∀ t, ∫⁻ ω, ‖e t ω‖ₑ ∂μ ≤ ENNReal.ofReal C :=
  ⟨fun t => (hw.memLp t).aestronglyMeasurable.aemeasurable,
    ⟨Real.sqrt lam, hw.lintegral_enorm_le⟩⟩

end Main

end Ljung31

#print axioms Ljung31.lemma_3_1

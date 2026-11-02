module

public import LDPC.Helpers.ExpansionParameters

/-! Review layout: PaperLemmas.Applications. Declaration names are unchanged. -/

@[expose] public section

open scoped BigOperators

namespace SmoothLDPC

section PaperInterfaces
variable {L R F : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] [Field F] [DecidableEq F]
    {G : TannerGraph L R} {c k K : ℕ} {γ δ τ α : ℚ}

/-- Actual proximity at radius `ρ` gives the bad-check budget `α = kρ/n`.
A passing random transcript is not assumed to certify proximity. -/
theorem ligero_few_bad_checks [Nonempty L] (hreg : G.IsRegular c k)
    (H : G.WeightedSystem F) (u v : L → F) {ρ : ℚ}
    (hclose : ∃ cu ∈ H.code, ∃ cv ∈ H.code, (pairDistance u v cu cv : ℚ) ≤ ρ) :
    ((H.badChecks u v).card : ℚ) ≤
      ((k : ℚ) * ρ / Fintype.card L) * Fintype.card R := by
  rw [G.regular_scale hreg]
  obtain ⟨cu, hcu, cv, hcv, he⟩ := hclose
  calc
    _ ≤ (c : ℚ) * pairDistance u v cu cv := by
      exact_mod_cast badChecks_card_le_pairDistance hreg H u v cu cv hcu hcv
    _ ≤ c * ρ := mul_le_mul_of_nonneg_left he (by positivity)

end PaperInterfaces

/-- The slack in the final paragraph supplies the strict threshold interval. -/
theorem ligero_threshold_choice (γ ε : ℚ) (hε0 : 0 < ε) (hε : ε < 1 - 3 * γ) :
    γ < 1 - 2 * γ - ε / 2 ∧ 1 - 2 * γ - ε / 2 < 1 - 2 * γ := by
  constructor <;> linarith

/-- The proposed `α` lies strictly below the smoothness upper bound. -/
theorem ligero_alpha_choice (γ ε : ℚ) (n k K : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hK : 0 < K)
    (hε0 : 0 < ε) (hε : ε < 1 - 3 * γ) :
    0 < (1 - 3 * γ - ε) * k * ((1 - γ) * K) / n ∧
    (1 - 3 * γ - ε) * k * ((1 - γ) * K) / n <
      ((1 - 2 * γ - ε / 2) - γ) * k * ((1 - γ) * K) / n := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hkQ : (0 : ℚ) < k := by exact_mod_cast hk
  have hP : (0 : ℚ) < (1 - γ) * K := mul_pos (by linarith) (by exact_mod_cast hK)
  constructor
  · exact div_pos (mul_pos (mul_pos (by linarith) hkQ) hP) hnQ
  · exact div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right (by linarith) hkQ) hP) hnQ

end SmoothLDPC

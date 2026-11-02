module

public import LDPC.Statements.SharedQueries
public import LDPC.Helpers.Algebra
public import ArkLib.Data.Probability.Instances
public import Mathlib.Tactic.Finiteness

/-! A lower bound on the fraction of detecting checks bounds the miss probability. -/
@[expose] public section
open scoped ProbabilityTheory
namespace SmoothLDPC.Protocol

variable {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]

/-- All samples avoid a detecting set with probability at most (1-alpha)^Q. -/
theorem miss_checks_le (B : Finset R) (α : ℚ) (hα : α ≤ 1)
    (hB : α * Fintype.card R ≤ B.card) (Q : ℕ) :
    Pr_{let sample ← $ᵖ (Fin Q → R)}[
      ∀ q, sample q ∈ Finset.univ \ B] ≤ ENNReal.ofReal (1 - (α : ℝ))^Q := by
  rw [Probability.prob_uniform_pi_mem_finset_eq]
  apply pow_le_pow_left'
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  have hBR : B.card ≤ Fintype.card R := Finset.card_le_univ _
  have hB' : (α : ℝ) * Fintype.card R ≤ B.card := by exact_mod_cast hB
  have hα' : (α : ℝ) ≤ 1 := by exact_mod_cast hα
  simp only [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hα')]
  rw [Nat.cast_sub hBR]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < Fintype.card R)).mpr
  nlinarith

end SmoothLDPC.Protocol

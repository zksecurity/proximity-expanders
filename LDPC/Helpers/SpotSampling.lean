module

public import LDPC.Statements.Protocol
public import LDPC.Helpers.Algebra
public import ArkLib.Data.Probability.Instances

/-! Exact coordinate-query error for a response fixed before sampling. -/
@[expose] public section
open scoped ProbabilityTheory
namespace SmoothLDPC.Protocol

variable {L F : Type} [Fintype L] [DecidableEq L] [Nonempty L]
    [Field F] [DecidableEq F]

/-- All samples miss the disagreement set with its exact product probability. -/
theorem spotAccept_probability (u v : L → F) (r : F) (claimed : L → F) (Q : ℕ) :
    Pr_{let coords ← $ᵖ (Fin Q → L)}[spotAccept u v r claimed coords] =
      (((Fintype.card L - distance (u + r • v) claimed : ℕ) : ENNReal) /
        Fintype.card L)^Q := by
  classical
  let I := Finset.univ \ support (u + r • v - claimed)
  have heq : ∀ coords : Fin Q → L,
      spotAccept u v r claimed coords ↔ ∀ i, coords i ∈ I := by
    intro coords
    simp [spotAccept, I, mem_support, sub_eq_zero, smul_eq_mul]
  rw [Probability.Pr_congr heq, Probability.prob_uniform_pi_mem_finset_eq]
  simp only [I, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    distance]

theorem spotAccept_probability_le (u v : L → F) (r : F) (claimed : L → F)
    (Q s : ℕ) (hfar : s ≤ distance (u + r • v) claimed) :
    Pr_{let coords ← $ᵖ (Fin Q → L)}[spotAccept u v r claimed coords] ≤
      (((Fintype.card L - s : ℕ) : ENNReal) / Fintype.card L)^Q := by
  rw [spotAccept_probability]
  apply pow_le_pow_left'
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.sub_le_sub_left hfar (Fintype.card L)

end SmoothLDPC.Protocol

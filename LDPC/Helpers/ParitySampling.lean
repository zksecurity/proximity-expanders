module

public import LDPC.Statements.MCA

/-! Independent parity sampling turns the smoothness MCA bridge into a joint-event theorem. -/
@[expose] public section
open scoped BigOperators ProbabilityTheory
namespace SmoothLDPC.MCA

variable {L R F : Type} [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Field F] [Fintype F] [DecidableEq F] {G : TannerGraph L R}
    [SampleableType F] [SampleableType R]

omit [DecidableEq F] in
/-- The field seed and check samples are independent. -/
theorem queried_probability_eq_mul (H : G.WeightedSystem F) (ρ : ℚ) (u v : L → F) (Q : ℕ) :
    Pr{let z ← $ᵗ F;let sample ← $ᵗ (Fin Q → R)}[
      parityAccept H u v sample ∧ Bad H.code ρ u v z] =
    Pr{let z ← $ᵗ F}[Bad H.code ρ u v z]*
      Pr{let sample ← $ᵗ (Fin Q → R)}[parityAccept H u v sample] := by
  rw [prEvent_bind_and_eq_mul ($ᵗ F) (fun _ => $ᵗ (Fin Q → R)) _ _ (fun _ => rfl), mul_comm]

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Exact probability of missing every failed check, with replacement. -/
theorem parityAccept_probability_eq (H : G.WeightedSystem F) (u v : L → F) (Q : ℕ) :
    Pr{let sample ← $ᵗ (Fin Q → R)}[parityAccept H u v sample] =
      (((Fintype.card R-(H.badChecks u v).card:ℕ):ENNReal)/Fintype.card R)^Q := by
  change Pr{let sample ← $ᵗ (Fin Q → R)}[∀ i,sample i∈Finset.univ \ H.badChecks u v] = _
  rw [Probability.prob_uniform_pi_mem_finset_eq,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]

omit [Fintype F] [DecidableEq F] [SampleableType F] in
theorem parityAccept_probability_le (H : G.WeightedSystem F) (u v : L → F) (Q t : ℕ)
    (hb : t≤(H.badChecks u v).card) :
    Pr{let sample ← $ᵗ (Fin Q → R)}[parityAccept H u v sample] ≤
      (((Fintype.card R-t:ℕ):ENNReal)/Fintype.card R)^Q := by
  rw [parityAccept_probability_eq]
  have hr : (((Fintype.card R-(H.badChecks u v).card:ℕ):ENNReal)/Fintype.card R) ≤
      (((Fintype.card R-t:ℕ):ENNReal)/Fintype.card R) :=
    ENNReal.div_le_div_right (by exact_mod_cast Nat.sub_le_sub_left hb (Fintype.card R)) _
  exact pow_le_pow_left' hr Q

end SmoothLDPC.MCA



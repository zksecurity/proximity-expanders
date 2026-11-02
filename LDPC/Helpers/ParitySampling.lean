module

public import LDPC.Statements.MCA

/-! Independent parity sampling turns the smoothness MCA bridge into a joint-event theorem. -/
@[expose] public section
open scoped BigOperators ProbabilityTheory
namespace SmoothLDPC.MCA

variable {L R F : Type} [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Field F] [Fintype F] [DecidableEq F] {G : TannerGraph L R}

omit [DecidableEq F] in
/-- The field seed and check samples are independent. -/
theorem queried_probability_eq_mul (H : G.WeightedSystem F) (ρ : ℚ) (u v : L → F) (Q : ℕ) :
    Pr_{let z ← $ᵖ F;let sample ← $ᵖ (Fin Q → R)}[
      parityAccept H u v sample ∧ Bad H.code ρ u v z] =
    Pr_{let z ← $ᵖ F}[Bad H.code ρ u v z]*
      Pr_{let sample ← $ᵖ (Fin Q → R)}[parityAccept H u v sample] := by
  classical
  rw [← Probability.prob_split_uniform_sampling_of_prod
    (P := fun t : F × (Fin Q → R) => parityAccept H u v t.2 ∧ Bad H.code ρ u v t.1)]
  simp only [Probability.prob_uniform_eq_card_filter_div_card]
  have hf : (Finset.univ.filter fun t : F × (Fin Q → R) =>
      parityAccept H u v t.2 ∧ Bad H.code ρ u v t.1) =
      (Finset.univ.filter (Bad H.code ρ u v)) ×ˢ
        (Finset.univ.filter fun sample : Fin Q → R => parityAccept H u v sample) := by
    ext t
    simp [and_comm]
  rw [hf,Finset.card_product,Fintype.card_prod]
  push_cast
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (by simp) (by simp)]
  ac_rfl

omit [Fintype F] [DecidableEq F] in
/-- Exact probability of missing every failed check, with replacement. -/
theorem parityAccept_probability_eq (H : G.WeightedSystem F) (u v : L → F) (Q : ℕ) :
    Pr_{let sample ← $ᵖ (Fin Q → R)}[parityAccept H u v sample] =
      (((Fintype.card R-(H.badChecks u v).card:ℕ):ENNReal)/Fintype.card R)^Q := by
  change Pr_{let sample ← $ᵖ (Fin Q → R)}[∀ i,sample i∈Finset.univ \ H.badChecks u v] = _
  rw [Probability.prob_uniform_pi_mem_finset_eq,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]

omit [Fintype F] [DecidableEq F] in
theorem parityAccept_probability_le (H : G.WeightedSystem F) (u v : L → F) (Q t : ℕ)
    (hb : t≤(H.badChecks u v).card) :
    Pr_{let sample ← $ᵖ (Fin Q → R)}[parityAccept H u v sample] ≤
      (((Fintype.card R-t:ℕ):ENNReal)/Fintype.card R)^Q := by
  rw [parityAccept_probability_eq]
  have hr : (((Fintype.card R-(H.badChecks u v).card:ℕ):ENNReal)/Fintype.card R) ≤
      (((Fintype.card R-t:ℕ):ENNReal)/Fintype.card R) :=
    ENNReal.div_le_div_right (by exact_mod_cast Nat.sub_le_sub_left hb (Fintype.card R)) _
  exact pow_le_pow_left' hr Q

end SmoothLDPC.MCA



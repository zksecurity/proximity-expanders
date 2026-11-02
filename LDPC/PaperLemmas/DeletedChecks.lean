module

public import LDPC.Helpers.ExpansionDistance

/-! Review layout: PaperLemmas.DeletedChecks. Declaration names are unchanged. -/

@[expose] public section

open scoped BigOperators

namespace SmoothLDPC

section ImprovedDistance
variable {L R F : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] [Field F] [DecidableEq F]
    {G : TannerGraph L R} {c k K : ℕ} {γ δ : ℚ}

/-- Original distance at an integer cutoff: `K` is an integer, with `K ≤ δn`. -/
theorem proposition_5 (hG : G.IsExpander c k γ δ)
    (hc : 0 < c) (hγ : γ < 1 / 2) (hK : (K : ℚ) ≤ δ * Fintype.card L)
    (H : G.WeightedSystem F) : HasDistance H.code (2 * (1 - γ) * K) := by
  intro x hx hx0
  have hKcard : K ≤ (support x).card := by
    exact_mod_cast (hK.trans_lt (nonzero_codeword_large hG hc hγ H hx hx0)).le
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hKcard
  have hu := proposition_4 hG S
    (show (S.card : ℚ) ≤ δ * Fintype.card L by simpa [hcard] using hK)
  have hsub : G.uniqueNeighbors S ⊆ G.neighborhood (support x \ S) := by
    simpa using unique_subset_removed H (code_le_relaxed H ∅ hx) S hS
  have hbound := (Finset.card_le_card hsub).trans
    (neighborhood_card_le hG.toIsRegular (support x \ S))
  have hdiff : (support x \ S).card = (support x).card - K := by
    rw [Finset.card_sdiff_of_subset hS, hcard]
  rw [hdiff] at hbound
  have hboundQ : ((G.uniqueNeighbors S).card : ℚ) ≤
      c * (((support x).card : ℚ) - K) := by exact_mod_cast hbound
  rw [hcard] at hu
  have hcQ : (0 : ℚ) < c := by exact_mod_cast hc
  nlinarith

end ImprovedDistance

end SmoothLDPC

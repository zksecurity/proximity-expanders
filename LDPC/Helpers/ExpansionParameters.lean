module

public import LDPC.PaperLemmas.Smoothness

/-! Review layout: Helpers.ExpansionParameters. Declaration names are unchanged. -/

@[expose] public section

open scoped BigOperators

namespace SmoothLDPC

section PaperInterfaces
variable {L R F : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] [Field F] [DecidableEq F]
    {G : TannerGraph L R} {c k K : ℕ} {γ δ τ α : ℚ}

/-- Expansion at an actual set of size `K` bounds the normalized radius.
The condition `K ≤ |L|` follows from `K ≤ δ|L|` when `δ ≤ 1`. -/
theorem radius_rate_le_one [Nonempty L] (hG : G.IsExpander c k γ δ)
    (hc : 0 < c) (hK : (K : ℚ) ≤ δ * Fintype.card L)
    (hKn : K ≤ Fintype.card L) :
    (k : ℚ) * ((1 - γ) * K) / Fintype.card L ≤ 1 := by
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (show K ≤ (Finset.univ : Finset L).card by simpa using hKn)
  have hexp := hG.expansion S (by simpa [hS] using hK)
  have hsize : ((G.neighborhood S).card : ℚ) ≤ Fintype.card R := by
    exact_mod_cast Finset.card_le_univ (G.neighborhood S)
  rw [hS] at hexp
  have hh : (c : ℚ) * Fintype.card L = k * Fintype.card R := by
    exact_mod_cast G.regular_handshake hG.toIsRegular
  have hb := mul_le_mul_of_nonneg_left (hexp.trans hsize)
    (show (0 : ℚ) ≤ k by positivity)
  have hcQ : (0 : ℚ) < c := by exact_mod_cast hc
  have hn : (0 : ℚ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
  apply (div_le_one hn).mpr
  nlinarith [hb]

/-- The integer-cutoff admissible bad-check fraction is automatically below one. -/
theorem smoothness_alpha_lt_one [Nonempty L] (hG : G.IsExpander c k γ δ)
    (hc : 0 < c) (hγ0 : 0 ≤ γ) (hτlo : γ < τ) (hτhi : τ < 1 - 2 * γ)
    (hK : (K : ℚ) ≤ δ * Fintype.card L) (hKn : K ≤ Fintype.card L)
    (hα : α < (τ - γ) * k * ((1 - γ) * K) / Fintype.card L) : α < 1 := by
  apply hα.trans_le
  calc
    _ = (τ - γ) * ((k : ℚ) * ((1 - γ) * K) / Fintype.card L) := by ring
    _ ≤ (τ - γ) * 1 :=
      mul_le_mul_of_nonneg_left (radius_rate_le_one hG hc hK hKn) (by linarith)
    _ ≤ 1 := by linarith

/-- Every jointly bad check touches the joint error support relative to any
pair of codewords. This is the check-counting claim used by the main folding theorem. -/
theorem badChecks_subset_error_neighborhood (H : G.WeightedSystem F)
    (u v cu cv : L → F) (hcu : cu ∈ H.code) (hcv : cv ∈ H.code) :
    H.badChecks u v ⊆ G.neighborhood (support (u - cu) ∪ support (v - cv)) := by
  classical
  intro j hj
  by_contra hn
  have hag : ∀ i ∈ G.left j, u i = cu i ∧ v i = cv i := by
    intro i hij
    have hnot : i ∉ support (u - cu) ∪ support (v - cv) :=
      fun hi => hn ((G.mem_neighborhood _ j).mpr ⟨i, hi, hij⟩)
    simpa [mem_support, sub_ne_zero] using hnot
  have hu : H.check u j = 0 := calc
    _ = H.check cu j := Finset.sum_congr rfl fun i hi => by rw [(hag i hi).1]
    _ = 0 := (mem_code H cu).mp hcu j
  have hv : H.check v j = 0 := calc
    _ = H.check cv j := Finset.sum_congr rfl fun i hi => by rw [(hag i hi).2]
    _ = 0 := (mem_code H cv).mp hcv j
  simp [TannerGraph.WeightedSystem.badChecks, hu, hv] at hj

theorem badChecks_card_le_pairDistance (hreg : G.IsRegular c k)
    (H : G.WeightedSystem F) (u v cu cv : L → F)
    (hcu : cu ∈ H.code) (hcv : cv ∈ H.code) :
    (H.badChecks u v).card ≤ c * pairDistance u v cu cv :=
  (Finset.card_le_card (badChecks_subset_error_neighborhood H u v cu cv hcu hcv)).trans
    (neighborhood_card_le hreg _)


end PaperInterfaces

end SmoothLDPC

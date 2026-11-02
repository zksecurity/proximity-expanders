module

public import LDPC.PaperLemmas.MCA

/-! Smoothness to ArkLib's exact, closed-radius MCA event and parity-query soundness. -/
@[expose] public section
open scoped BigOperators ProbabilityTheory
namespace SmoothLDPC
namespace MCA
open CoreDefinitions LinearCode

variable {L R F : Type} [Fintype L] [DecidableEq L]
    [Field F] [DecidableEq F] [Fintype F]

variable [Fintype R] [DecidableEq R] {G : TannerGraph L R}

open Classical in
/-- Few failed checks give an MCA error proportional to the puncture budget,
without any input-farness hypothesis. -/
theorem card_bad_le_of_smooth [Nonempty L] (H : G.WeightedSystem F)
    {α D d ρ : ℚ} {p : ℕ} (hs : IsSmooth H α p D)
    (hd : HasDistance H.code d) (hp : (p:ℚ)<d) (hρ : ρ<D)
    (u v : L → F) (hbad : ((H.badChecks u v).card:ℚ)≤α*Fintype.card R) :
    (Finset.univ.filter (Bad H.code ρ u v)).card≤max 1 p := by
  classical
  obtain ⟨L₀,hp₀,hD⟩ := hs (H.badChecks u v) hbad
  let B := Finset.univ.filter (Bad H.code ρ u v)
  by_cases hb : B.card≤1
  · exact hb.trans (le_max_left _ _)
  · obtain ⟨r₁,hr₁,r₂,hr₂,hne⟩ := Finset.one_lt_card.mp (by omega : 1<B.card)
    obtain ⟨cu,hcu,cv,hcv,hpair,halign⟩ := alignment_of_punctures H u v L₀ hρ hd
      (hp₀.trans_lt hp) hD hne
      (nearby_of_bad _ _ _ _ _ (Finset.mem_filter.mp hr₁).2)
      (nearby_of_bad _ _ _ _ _ (Finset.mem_filter.mp hr₂).2)
    have hcount := card_bad_le_of_alignment H.code ρ u v cu cv hcu hcv halign
    have hp₀' : L₀.card≤p := by exact_mod_cast hp₀
    exact (hcount.trans (hpair.trans hp₀')).trans (le_max_right _ _)

theorem probability_le_of_smooth [Nonempty L] (H : G.WeightedSystem F)
    {α D d ρ : ℚ} {p : ℕ} (hs : IsSmooth H α p D)
    (hd : HasDistance H.code d) (hp : (p:ℚ)<d) (hρ : ρ<D)
    (u v : L → F) (hbad : ((H.badChecks u v).card:ℚ)≤α*Fintype.card R) :
    Pr_{let z ← $ᵖ F}[Bad H.code ρ u v z]≤(max 1 p:ℕ)/ (Fintype.card F:ENNReal) := by
  classical
  rw [Probability.prob_uniform_eq_card_filter_div_card]
  apply ENNReal.div_le_div_right
  exact_mod_cast card_bad_le_of_smooth H hs hd hp hρ u v hbad

end MCA
end SmoothLDPC

module

public import LDPC.Theorems.MCA
public import LDPC.Helpers.ParitySampling

/-! Independent parity sampling turns the smoothness MCA bridge into a joint-event theorem. -/
@[expose] public section
open scoped BigOperators ProbabilityTheory
namespace SmoothLDPC.MCA

variable {L R F : Type} [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Field F] [Fintype F] [DecidableEq F] {G : TannerGraph L R}

/-- Queried MCA, for every fixed input pair, at a closed radius.
The maximum bounds the joint event of parity acceptance and ArkLib MCA failure. -/
theorem queried_soundness [Nonempty L] [SampleableType F] [SampleableType R] (H : G.WeightedSystem F)
    {D d ρ : ℚ} {p t : ℕ}
    (hs : IsSmooth H ((t:ℚ)/Fintype.card R) p D)
    (hd : HasDistance H.code d) (hp : (p:ℚ)<d) (hρ : ρ<D)
    (u v : L → F) (Q : ℕ) :
    Pr{let z ← $ᵗ F;let sample ← $ᵗ (Fin Q → R)}[
      parityAccept H u v sample ∧ Bad H.code ρ u v z] ≤
      max ((max 1 p:ℕ)/(Fintype.card F:ENNReal))
        ((((Fintype.card R-t:ℕ):ENNReal)/Fintype.card R)^Q) := by
  rw [queried_probability_eq_mul]
  by_cases hb : (H.badChecks u v).card≤t
  · have hthreshold : (t:ℚ)/Fintype.card R*Fintype.card R=t :=
      div_mul_cancel₀ _ (by positivity)
    have hbad : ((H.badChecks u v).card:ℚ)≤(t:ℚ)/Fintype.card R*Fintype.card R := by
      rw [hthreshold]
      exact_mod_cast hb
    calc
      _ ≤ Pr{let z ← $ᵗ F}[Bad H.code ρ u v z] :=
        mul_le_of_le_one_right' (prEvent_le_one _)
      _ ≤ (max 1 p:ℕ)/(Fintype.card F:ENNReal) := probability_le_of_smooth H hs hd hp hρ u v hbad
      _ ≤ _ := le_max_left _ _
  · calc
      _ ≤ Pr{let sample ← $ᵗ (Fin Q → R)}[parityAccept H u v sample] :=
        mul_le_of_le_one_left' (prEvent_le_one _)
      _ ≤ (((Fintype.card R-t:ℕ):ENNReal)/Fintype.card R)^Q :=
        parityAccept_probability_le H u v Q t (by omega)
      _ ≤ _ := le_max_right _ _

/-- A field budget and a sampling budget give the desired joint error. -/
theorem queried_soundness_of_budgets [Nonempty L] [SampleableType F] [SampleableType R]
    (H : G.WeightedSystem F)
    {D d ρ : ℚ} {p t Q : ℕ} {ε : ENNReal}
    (hs : IsSmooth H ((t:ℚ)/Fintype.card R) p D)
    (hd : HasDistance H.code d) (hp : (p:ℚ)<d) (hρ : ρ<D)
    (hfield : (max 1 p:ℕ)/(Fintype.card F:ENNReal)≤ε)
    (hquery : (((Fintype.card R-t:ℕ):ENNReal)/Fintype.card R)^Q≤ε)
    (u v : L → F) :
    Pr{let z ← $ᵗ F;let sample ← $ᵗ (Fin Q → R)}[
      parityAccept H u v sample ∧ Bad H.code ρ u v z]≤ε :=
  (queried_soundness H hs hd hp hρ u v Q).trans (max_le hfield hquery)

theorem guarantees_of_smooth [Nonempty L] (H : G.WeightedSystem F)
    {D d ρ : ℚ} {p t : ℕ}
    (hs : IsSmooth H ((t:ℚ)/Fintype.card R) p D)
    (hd : HasDistance H.code d) (hp : (p:ℚ)<d) (hρ : ρ<D) :
    Guarantees H ρ p t := by
  let _ := SampleableType.ofFintype F; let _ := SampleableType.ofFintype R
  constructor
  · intro u v hb
    apply probability_le_of_smooth H hs hd hp hρ u v
    have hthreshold : (t:ℚ)/Fintype.card R*Fintype.card R=t := div_mul_cancel₀ _ (by positivity)
    rw [hthreshold]
    exact_mod_cast hb
  · intro u v Q
    exact queried_soundness H hs hd hp hρ u v Q

end SmoothLDPC.MCA

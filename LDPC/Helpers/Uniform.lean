module

public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! A counting bound for one uniform draw, stated on VCVio's native sampler. -/
@[expose] public section

/-- An event met by at most one point of a uniform finite sample has probability at most `1/|F|`. -/
theorem prEvent_uniformSample_le_inv_of_card_le_one {F : Type} [Fintype F] [SampleableType F]
    (P : F → Prop) [DecidablePred P] (h : (Finset.univ.filter P).card ≤ 1) :
    Pr{let r ← $ᵗ F}[P r] ≤ (Fintype.card F : ENNReal)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample, ← one_div]
  gcongr
  exact_mod_cast h

/-- `prEvent_bind_le_of_forall_le` for an event of two sequential draws. -/
theorem prEvent_bind_bind_le_of_forall_le {α β : Type} (mx : ProbComp α) (my : α → ProbComp β)
    (q : α → β → Prop) {ε : ENNReal} (h : ∀ a, Pr{let y ← my a}[q a y] ≤ ε) :
    Pr{let x ← mx; let y ← my x}[q x y] ≤ ε := by
  simpa only [id_map, bind_pure_comp] using
    prEvent_bind_le_of_forall_le mx (fun a => do let y ← my a; return q a y) id
      (fun a => by simpa only [id_map, bind_pure_comp] using h a)

/-- `prEvent_bind_le_prEvent_add_mul_prEvent_not` for an event of two sequential draws. -/
theorem prEvent_bind_bind_le_add_of_not {α β : Type} (mx : ProbComp α) (my : α → ProbComp β)
    (p : α → Prop) (q : α → β → Prop) {ε : ENNReal}
    (h : ∀ a, ¬ p a → Pr{let y ← my a}[q a y] ≤ ε) :
    Pr{let x ← mx; let y ← my x}[q x y] ≤ Pr{let a ← mx}[p a] + ε := by
  have := prEvent_bind_le_prEvent_add_mul_prEvent_not mx
    (fun a => do let y ← my a; return q a y) p id
    (fun a ha => by simpa only [id_map, bind_pure_comp] using h a ha)
  simp only [id_map, bind_pure_comp] at this
  exact this.trans (add_le_add le_rfl (mul_le_of_le_one_right' (prEvent_le_one _)))

/-- Two independent uniform draws are a counting ratio over the product, whichever samplers are
installed. This is the closed form the PMF-based statements had before ArkLib's port. -/
theorem prEvent_uniformSample_bind_eq_card {α β : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] (p : α → β → Prop) [DecidablePred fun z : α × β => p z.1 z.2] :
    Pr{let x ← $ᵗ α; let y ← $ᵗ β}[p x y] =
      (Finset.univ.filter fun z : α × β => p z.1 z.2).card /
        ((Fintype.card α * Fintype.card β : ℕ) : ENNReal) := by
  rw [← Fintype.card_prod, ← SampleableType.prEvent_uniformSample,
    SampleableType.prEvent_uniformSample_prod]

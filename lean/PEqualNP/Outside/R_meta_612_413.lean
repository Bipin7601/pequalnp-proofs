import PEqualNP.Defs

-- Vertex-elimination induction for |E| + tau - 1: a non-star C4-free graph sheds k > 0 edges
-- to a subgraph H with an edge while the circuit sheds k gates (k + 1 when the cover drops);
-- stars are the base case.
theorem PEqualNP.Outside.R_meta_612_413
    (step : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (¬ ∃ z : Fin n, ∀ u v : Fin n, G.Adj u v → u = z ∨ v = z) →
      PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      ∃ (H : SimpleGraph (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ),
        H ≤ G ∧ 0 < k ∧ (∃ u v : Fin n, H.Adj u v) ∧ H.edgeSet.ncard + k = G.edgeSet.ncard ∧
        PEqualNP.MetaComplexity.Monotone2 D ∧ (∀ x : Fin n → Bool, (D.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true)) ∧ D.size + k ≤ C.size ∧
        (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover H S → ∃ T : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T ∧ T.card ≤ S.card + 1) ∧
        ((∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover H S ∧ ∀ T : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T → S.card < T.card) →
          D.size + k + 1 ≤ C.size))
    (star : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) → (∃ z : Fin n, ∀ u v : Fin n, G.Adj u v → u = z ∨ v = z) →
      PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard ≤ C.size) :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  classical
  intro n t G C h1 h2 h3 h4 hm he
  have key : ∀ m : ℕ, ∀ (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (t : ℕ),
      G.edgeSet.ncard = m → (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) →
      (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
      PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      G.edgeSet.ncard + t ≤ C.size + 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro G C t hmG h1 h2 h3 h4 hm he
      by_cases hs : ∃ z : Fin n, ∀ u v : Fin n, G.Adj u v → u = z ∨ v = z
      · obtain ⟨z, hz⟩ := hs
        have hcov : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G {z} := by
          intro u v huv
          rcases hz u v huv with h | h
          · exact Or.inl (by simp [h])
          · exact Or.inr (by simp [h])
        have ht1 : t ≤ 1 := by simpa using h4 {z} hcov
        have hst := star n G C h1 ⟨z, hz⟩ hm he
        omega
      · obtain ⟨H, D, k, hle, hk, hHe, hcard, hDm, hDe, hsz, hcovH, hdrop⟩ := step n G C h2 hs hm he
        have hP : ∃ j : ℕ, ∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover H S ∧ S.card = j :=
          ⟨_, Finset.univ, fun u _ _ => Or.inl (Finset.mem_univ u), rfl⟩
        obtain ⟨S', hS', hcS'⟩ := Nat.find_spec hP
        have hmin' : ∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover H S → Nat.find hP ≤ S.card :=
          fun S hS => Nat.find_min' hP ⟨S, hS, rfl⟩
        have hC4H : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
            H.Adj a b → H.Adj b c → H.Adj c d → ¬ H.Adj d a :=
          fun a b c d h_ab h_ac h_ad h_bc h_bd h_cd hab hbc hcd hda =>
            h2 a b c d h_ab h_ac h_ad h_bc h_bd h_cd (hle hab) (hle hbc) (hle hcd) (hle hda)
        have hIH := ih H.edgeSet.ncard (by omega) H D (Nat.find hP) rfl hHe hC4H ⟨S', hS', hcS'⟩ hmin' hDm hDe
        obtain ⟨T, hT, hTc⟩ := hcovH S' hS'
        have htT := h4 T hT
        by_cases hlt : Nat.find hP < t
        · have hd := hdrop ⟨S', hS', fun T' hT' => by have := h4 T' hT'; omega⟩
          omega
        · omega
  exact key _ G C t rfl h1 h2 h3 h4 hm he

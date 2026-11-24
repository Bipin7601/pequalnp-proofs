import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4863

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]


def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2


theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    HasCircuitSize n F s := by
  obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, len, ?_⟩
  intro x
  have e := ev (List.ofFn x) (by simp)
  simp only [Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i

theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in

theorem bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var t) (bld_anyFinset S hSne)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

theorem deg3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin n)
    (h : (G.neighborSet w).ncard = 3) : G.degree w = 3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Set.ncard_coe_finset,
    SimpleGraph.coe_neighborFinset, h]

theorem card_inc {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    (G.edgeFinset.filter (fun e => v ∈ e)).card = G.degree v := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree, SimpleGraph.incidenceFinset_eq_filter]

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A S : Finset (Fin n))
    (v : Fin n) (hdeg : ∀ w ∉ A, (G.neighborSet w).ncard = 3)
    (hA : ∀ a b : Fin n, G.Adj a b → a ∉ A) (hSA : S ⊆ Aᶜ)
    (hcov : ∀ a b : Fin n, G.Adj a b → a ∈ S ∨ b ∈ S) (hv : v ∈ S) :
    ∃ s : ℕ, s + 5 ≤ A.card + G.edgeFinset.card + S.card ∧
      HasCircuitSize n (fun x => NestedCover.graphFun G A (Function.update x v false)) s := by
  classical
  have hvA : v ∉ A := by simpa using hSA hv
  have hdv : G.degree v = 3 := deg3 G v (hdeg v hvA)
  set E' := G.edgeFinset.filter (fun e => v ∉ e) with hE'
  have hsplit : (G.edgeFinset.filter (fun e => v ∈ e)).card + E'.card = G.edgeFinset.card :=
    Finset.card_filter_add_card_filter_not _
  have hinc : (G.edgeFinset.filter (fun e => v ∈ e)).card = 3 := by rw [card_inc, hdv]
  have hne : E'.Nonempty := by
    obtain ⟨u, hu⟩ : ∃ u, G.Adj v u := by
      have hpos : 0 < (G.neighborFinset v).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree, hdv]; norm_num
      obtain ⟨u, hu⟩ := Finset.card_pos.1 hpos
      exact ⟨u, (SimpleGraph.mem_neighborFinset _ _ _).1 hu⟩
    have hdu : G.degree u = 3 := deg3 G u (hdeg u (hA u v hu.symm))
    have hrest : ((G.neighborFinset u).erase v).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset _ _ _).2 hu.symm),
        SimpleGraph.card_neighborFinset_eq_degree, hdu]
      norm_num
    obtain ⟨w, hw⟩ := hrest
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hw
    refine ⟨s(u, w), ?_⟩
    rw [hE', Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    refine ⟨hw.2, ?_⟩
    rw [Sym2.mem_iff, not_or]
    exact ⟨fun h => G.ne_of_adj hu h, fun h => hw.1 h.symm⟩
  have hcovE : ∀ e ∈ E', ∃ t ∈ S.erase v, t ∈ e := by
    intro e he
    rw [hE', Finset.mem_filter] at he
    obtain ⟨he1, he2⟩ := he
    revert he1 he2
    refine Sym2.ind (fun a b => ?_) e
    intro he1 he2
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he1
    rw [Sym2.mem_iff, not_or] at he2
    rcases hcov a b he1 with h | h
    · exact ⟨a, Finset.mem_erase.2 ⟨fun e => he2.1 e.symm, h⟩, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, Finset.mem_erase.2 ⟨fun e => he2.2 e.symm, h⟩, Sym2.mem_mk_right _ _⟩
  have hedge := bld_edges n (S.erase v) E' hne hcovE
  have hSc : (S.erase v).card + 1 = S.card := Finset.card_erase_add_one hv
  have hE'pos := hne.card_pos
  have hfun : ∀ x : Fin n → Bool, NestedCover.graphFun G A (Function.update x v false) =
      (decide (∃ a ∈ A, x a = true) || decide (∃ e ∈ E', ∀ w ∈ e, x w = true)) := by
    intro x
    unfold NestedCover.graphFun
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_iff]
    have hupd : ∀ a ∈ A, Function.update x v false a = x a := fun a ha =>
      Function.update_of_ne (fun e => hvA (by rw [← e]; exact ha)) _ _
    apply or_congr
    · constructor
      · rintro ⟨a, ha, h⟩; exact ⟨a, ha, by rwa [hupd a ha] at h⟩
      · rintro ⟨a, ha, h⟩; exact ⟨a, ha, by rwa [hupd a ha]⟩
    · constructor
      · rintro ⟨a, b, hab, ha, hb⟩
        have hav : a ≠ v := by rintro rfl; simp at ha
        have hbv : b ≠ v := by rintro rfl; simp at hb
        rw [Function.update_of_ne hav] at ha
        rw [Function.update_of_ne hbv] at hb
        refine ⟨s(a, b), ?_, ?_⟩
        · rw [hE', Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            Sym2.mem_iff, not_or]
          exact ⟨hab, fun h => hav h.symm, fun h => hbv h.symm⟩
        · intro w hw
          rcases Sym2.mem_iff.1 hw with rfl | rfl <;> assumption
      · rintro ⟨e, he, h⟩
        rw [hE', Finset.mem_filter] at he
        obtain ⟨he1, he2⟩ := he
        revert h he1 he2
        refine Sym2.ind (fun a b => ?_) e
        intro h he1 he2
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he1
        rw [Sym2.mem_iff, not_or] at he2
        refine ⟨a, b, he1, ?_, ?_⟩
        · rw [Function.update_of_ne (fun e => he2.1 e.symm)]; exact h a (Sym2.mem_mk_left _ _)
        · rw [Function.update_of_ne (fun e => he2.2 e.symm)]; exact h b (Sym2.mem_mk_right _ _)
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · have hA0 : A.card = 0 := by simp [hAe]
    refine ⟨E'.card + (S.erase v).card - 1, by omega, ?_⟩
    apply bld_hasCircuitSize
    refine bld_congr hedge ?_
    intro x
    rw [hfun]
    simp [hAe]
  · have hApos := hAne.card_pos
    have hor := bld_or (bld_anyFinset A hAne) hedge
    refine ⟨(A.card - 1) + (E'.card + (S.erase v).card - 1) + 1, by omega, ?_⟩
    apply bld_hasCircuitSize
    refine bld_congr hor ?_
    intro x
    rw [hfun]

end PEqualNP.Outside.L_meta_4863

theorem PEqualNP.Outside.L_meta_4863 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 x5 : Finset (Fin x1)) (x6 : Fin x1), (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → x5 ⊆ x4ᶜ → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∈ x5 ∨ x11 ∈ x5) → x6 ∈ x5 → ∃ (x12 : ℕ), x12 + (5 : ℕ) ≤ x4.card + x2.edgeFinset.card + x5.card ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x13 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 (Function.update x13 x6 Bool.false)) x12 := by
  intro n G _ A S v hdeg hA hSA hcov hv
  exact PEqualNP.Outside.L_meta_4863.main n G A S v hdeg hA hSA hcov hv

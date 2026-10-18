/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.TateFree

/-!
# The dual Tate module over a field with enough points

Let `G = (G_v)` be a `p`-divisible group over a nontrivial ring `R` and `S` a field which is an
`R`-algebra such that `#G_v(S) = #G_v^∨(S) = |G_v|` for all `v` (e.g. `S = ℂ_p` for `R → O_{ℂ_p}`,
see `CartierPerfectOC.lean`). Then the levelwise Cartier pairings `G_v(S) × G_v^∨(S) → S` are
perfect (`CartierPerfect.lean`), and the inverse system `(G_v^∨(S), i_v^∨)` behaves like the
Tate module of the dual `p`-divisible group ([Hong, Prop. 3.4.6]; standard arguments, written up
here; over `ℚ_p` the dual `p`-divisible group itself is `PDivGroup.dualPDiv`):

* `dual_incl_surjective_of_card`: `i_v^∨ : G_{v+1}^∨(S) → G_v^∨(S)` is surjective (its kernel is
  the annihilator of `i_v(G_v(S))`, which embeds into the characters of `G_{v+1}(S)/i_v(G_v(S))`;
  counting);
* `DualTate.proj_surjective_of_card`: `T_p(G^∨)(S) = lim_v G_v^∨(S) → G_v^∨(S)` is surjective
  (`exists_compat_of_surjective`, for any inverse sequence of surjections);
* `dual_incl_quot_of_card`: `i_v^∨ ∘ quot_v^∨ = [p]` on `G_v^∨(S)`;
  `dual_quot_injective_of_card`: `quot_v^∨` is injective on `S`-points;
  `exists_dual_quot_eq_of_card`: a point of `G_{v+1}^∨(S)` killed by `p^v` comes from
  `G_v^∨(S)` (as `exists_dual_quot_eq_padicAlgCl`);
* **`DualTate.exists_pow_eq_of_card`**: a point `y ∈ T_p(G^∨)(S)` with `y_1 = 1` is a `p`-th
  power, `y = w^p` (i.e. `ker(T_p(G^∨) → G_1^∨) = p T_p(G^∨)`).
-/

noncomputable section

open WithConv

namespace PadicHodge

universe u

namespace InvSeq

variable {X : ℕ → Type*} (f : ∀ n, X (n + 1) → X n)

/-- The iterated transition maps `X b → X a` for `a ≤ b`. -/
def down {a b : ℕ} (h : a ≤ b) : X b → X a :=
  Nat.leRecOn (C := fun k => X k → X a) h (fun {k} g => g ∘ f k) id

theorem down_self (a : ℕ) (y : X a) : down f (le_refl a) y = y := by
  rw [down, Nat.leRecOn_self]
  rfl

theorem down_succ {a b : ℕ} (h : a ≤ b) (h' : a ≤ b + 1) (y : X (b + 1)) :
    down f h' y = down f h (f b y) := by
  rw [down, Nat.leRecOn_succ h]
  rfl

theorem down_succ_left {a b : ℕ} (h : a + 1 ≤ b) (h' : a ≤ b) (y : X b) :
    f a (down f h y) = down f h' y := by
  induction b, h using Nat.le_induction with
  | base => rw [down_self, down_succ f (le_refl a), down_self]
  | succ b hb ih => rw [down_succ f hb, down_succ f (by omega), ih]

variable (hf : ∀ n, Function.Surjective (f n))

/-- Iterated chosen lifts `X a → X b` for `a ≤ b`. -/
def up {a b : ℕ} (h : a ≤ b) (y : X a) : X b :=
  Nat.leRecOn (C := fun k => X k) h (fun {k} z => Function.surjInv (hf k) z) y

theorem up_succ {a b : ℕ} (h : a ≤ b) (h' : a ≤ b + 1) (y : X a) :
    up f hf h' y = Function.surjInv (hf b) (up f hf h y) := by
  rw [up, Nat.leRecOn_succ h]
  rfl

theorem down_up {a b : ℕ} (h : a ≤ b) (y : X a) : down f h (up f hf h y) = y := by
  induction b, h using Nat.le_induction with
  | base => rw [down_self, up, Nat.leRecOn_self]
  | succ b hb ih =>
    rw [up_succ f hf hb, down_succ f hb, Function.surjInv_eq (hf b), ih]

end InvSeq

/-- **Inverse sequences of surjections**: every element at level `v` extends to a compatible
sequence. -/
theorem exists_compat_of_surjective {X : ℕ → Type*} (f : ∀ n, X (n + 1) → X n)
    (hf : ∀ n, Function.Surjective (f n)) (v : ℕ) (y : X v) :
    ∃ z : ∀ n, X n, (∀ n, z n = f n (z (n + 1))) ∧ z v = y := by
  refine ⟨fun w => InvSeq.down f (Nat.le_add_left w v)
    (InvSeq.up f hf (Nat.le_add_right v w) y), fun w => ?_, InvSeq.down_up f hf _ y⟩
  rw [InvSeq.down_succ_left f (by omega) (by omega), InvSeq.up_succ f hf (Nat.le_add_right v w),
    InvSeq.down_succ f (Nat.le_add_left w v), Function.surjInv_eq (hf (v + w))]

namespace PDivGroup

open FFGroupScheme

variable {R : Type u} [CommRing R] [Nontrivial R] {p : ℕ} [hp : Fact p.Prime]
  (G : PDivGroup R p) (S : Type u) [Field S] [Algebra R S]

omit [Nontrivial R] hp in
/-- `T_p(G^∨)(S) → G_v^∨(S)` is surjective if the transposes `i_v^∨` are surjective on
`S`-points. -/
theorem DualTate.proj_surjective {T : Type u} [CommRing T] [Algebra R T]
    (hs : ∀ v, Function.Surjective ((G.incl v).dual.mapPoints T)) (v : ℕ)
    (y : (G.G v).dual.points T) : ∃ z : G.DualTate T, z.1 v = y := by
  obtain ⟨z, hz, hzv⟩ := exists_compat_of_surjective
    (X := fun n => (G.G n).dual.points T) (fun n => (G.incl n).dual.mapPoints T) hs v y
  exact ⟨⟨z, hz⟩, hzv⟩

variable (hc : ∀ w, Nat.card ((G.G w).points S) = (G.G w).order)
  (hc' : ∀ w, Nat.card ((G.G w).dual.points S) = (G.G w).order)

omit [Nontrivial R] hp in
theorem finite_points_field (w : ℕ) : Finite ((G.G w).points S) :=
  (G.G w).finite_points_of_free (S := S) (Module.Free.chooseBasis R _)

omit [Nontrivial R] hp in
theorem finite_dual_points_field (w : ℕ) : Finite ((G.G w).dual.points S) :=
  (G.G w).dual.finite_points_of_free (S := S) (Module.Free.chooseBasis R _)

omit [Nontrivial R] hp in
include hc in
theorem order_pos_of_card (w : ℕ) : 0 < (G.G w).order := by
  have := G.finite_points_field S w
  rw [← hc]
  exact Nat.card_pos

omit hp in
include hc hc' in
/-- **`i_v^∨ : G_{v+1}^∨(S) → G_v^∨(S)` is surjective.** -/
theorem dual_incl_surjective_of_card (v : ℕ) :
    Function.Surjective ((G.incl v).dual.mapPoints S) := by
  set f := (G.incl v).dual.mapPoints S
  set H := ((G.incl v).mapPoints S).range
  have hfin := G.finite_points_field S (v + 1)
  have hfin' := G.finite_dual_points_field S (v + 1)
  -- the kernel of `f` embeds into the characters of `G_{v+1}(S)/H`
  have hker : Nat.card f.ker ≤ H.index := by
    have hle : ∀ y : f.ker, H ≤ ((G.G (v + 1)).pairingHom (S := S) y.1).ker := by
      rintro y _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker]
      change (G.G (v + 1)).cartierPairingBase S _ _ = 1
      rw [cartierPairingBase_apply, pairing_dual]
      have hy : f y.1 = 1 := y.2
      change (G.G v).pairing S x (f y.1) = 1
      rw [hy, pairing_one_right]
    let κ : f.ker → ((G.G (v + 1)).points S ⧸ H →* S) := fun y =>
      QuotientGroup.lift H ((G.G (v + 1)).pairingHom (S := S) y.1) (hle y)
    have hκ : Function.Injective κ := by
      intro y y' h
      refine Subtype.ext ((G.G (v + 1)).pairing_injective_right (hc (v + 1)) fun φ => ?_)
      have := DFunLike.congr_fun h (φ : _ ⧸ H)
      simp only [κ, QuotientGroup.lift_mk] at this
      exact this
    have : Finite ((G.G (v + 1)).points S ⧸ H) := inferInstance
    have := finite_monoidHom ((G.G (v + 1)).points S ⧸ H) S
    calc Nat.card f.ker ≤ Nat.card ((G.G (v + 1)).points S ⧸ H →* S) :=
          Nat.card_le_card_of_injective κ hκ
      _ ≤ Nat.card ((G.G (v + 1)).points S ⧸ H) := card_monoidHom_le _ S
      _ = H.index := rfl
  have hH : Nat.card H = (G.G v).order := by
    rw [← hc v]
    exact (Nat.card_congr (Equiv.ofInjective _ (G.mapPoints_injective v S))).symm
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hc'] at h1
  have h2 := Subgroup.card_mul_index H
  rw [hc, hH] at h2
  have hrange : (G.G v).order ≤ Nat.card f.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card f.ker * Nat.card f.range < H.index * (G.G v).order :=
      Nat.mul_lt_mul_of_le_of_lt hker hlt (Nat.pos_of_ne_zero (by
        intro h0; rw [h0, mul_zero] at h2; exact (G.order_pos_of_card S hc (v + 1)).ne' h2.symm))
    rw [h1, mul_comm, h2] at this
    exact lt_irrefl _ this
  have := G.finite_dual_points_field S v
  rw [← MonoidHom.range_eq_top]
  exact Subgroup.eq_top_of_le_card _ ((hc' v).le.trans hrange)

omit hp in
include hc hc' in
/-- **`T_p(G^∨)(S) → G_v^∨(S)` is surjective.** -/
theorem DualTate.proj_surjective_of_card (v : ℕ) (y : (G.G v).dual.points S) :
    ∃ z : G.DualTate S, z.1 v = y :=
  DualTate.proj_surjective G (G.dual_incl_surjective_of_card S hc hc') v y

omit [Nontrivial R] in
include hc in
/-- The quotient maps are surjective on `S`-points. -/
theorem quot_surjective_of_card' (v : ℕ) : Function.Surjective ((G.quot v).mapPoints S) :=
  G.quot_surjective_of_card S hp.out.pos (fun w => by rw [hc, G.order_eq]) v

omit [Nontrivial R] hp in
/-- `quot_v ∘ i_v = [p]` on `G_v(T)`. -/
theorem quot_incl_points {T : Type u} [CommRing T] [Algebra R T] (v : ℕ)
    (x : (G.G v).points T) : (G.quot v).mapPoints T ((G.incl v).mapPoints T x) = x ^ p := by
  apply G.mapPoints_injective v T
  rw [G.incl_quot, map_pow]

omit hp in
include hc in
/-- **`i_v^∨ ∘ quot_v^∨ = [p]` on `G_v^∨(S)`.** -/
theorem dual_incl_quot_of_card (v : ℕ) (w : (G.G v).dual.points S) :
    (G.incl v).dual.mapPoints S ((G.quot v).dual.mapPoints S w) = w ^ p := by
  refine (G.G v).pairing_injective_right (hc v) fun x => ?_
  rw [← pairing_dual, ← pairing_dual, quot_incl_points]
  change (G.G v).cartierPairingBase S _ _ = (G.G v).cartierPairingBase S _ _
  rw [map_pow, MonoidHom.pow_apply, map_pow]

include hc in
/-- `quot_v^∨` is injective on `S`-points. -/
theorem dual_quot_injective_of_card (v : ℕ) :
    Function.Injective ((G.quot v).dual.mapPoints S) := by
  intro w w' h
  refine (G.G v).pairing_injective_right (hc v) fun x => ?_
  obtain ⟨x, rfl⟩ := G.quot_surjective_of_card' S hc v x
  rw [pairing_dual, pairing_dual, h]

include hc hc' in
/-- **A point of `G_{v+1}^∨(S)` killed by `p^v` comes from `G_v^∨(S)`.** -/
theorem exists_dual_quot_eq_of_card (v : ℕ) (y : (G.G (v + 1)).dual.points S)
    (hy : y ^ (p ^ v) = 1) : ∃ x, (G.quot v).dual.mapPoints S x = y := by
  set q := (G.quot v).mapPoints S
  set χ := (G.G (v + 1)).pairingHom y
  have hcard : ∀ w, Nat.card ((G.G w).points S) = p ^ (G.height * w) := fun w => by
    rw [hc, G.order_eq]
  have hχ : q.ker ≤ χ.ker := by
    rw [G.ker_quot, ← G.pow_range_eq_ker_pow S hp.out.pos hcard v]
    rintro _ ⟨ψ, rfl⟩
    simp only [MonoidHom.mem_ker, powMonoidHom_apply]
    change (G.G (v + 1)).cartierPairingBase _ (ψ ^ (p ^ v)) y = 1
    rw [map_pow, MonoidHom.pow_apply, ← map_pow, hy, map_one]
  let e := QuotientGroup.quotientKerEquivOfSurjective q (G.quot_surjective_of_card' S hc v)
  let χ' : (G.G v).points S →* S := (QuotientGroup.lift q.ker χ hχ).comp e.symm.toMonoidHom
  have hχ' : ∀ φ, χ' (q φ) = χ φ := by
    intro φ
    have : e.symm (q φ) = (φ : _ ⧸ q.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [χ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this]
    rfl
  obtain ⟨x, hx⟩ := ((G.G v).pairingHom_bijective (hc v) (hc' v)).2 χ'
  refine ⟨x, (G.G (v + 1)).pairing_injective_right (hc (v + 1)) fun φ => ?_⟩
  rw [← pairing_dual]
  have := DFunLike.congr_fun hx (q φ)
  rw [hχ' φ] at this
  exact this

omit [Nontrivial R] hp in
/-- `quot_v^∨ ∘ i_v^∨ = [p]`, levelwise for a point of `T_p(G^∨)`. -/
theorem DualTate.dual_quot_succ {T : Type u} [CommRing T] [Algebra R T] (y : G.DualTate T)
    (v : ℕ) : (G.quot v).dual.mapPoints T (y.1 v) = y.1 (v + 1) ^ p := by
  rw [y.2 v, G.dual_quot_incl]

omit [Nontrivial R] hp in
/-- If `y_1 = 1` then `y_{v+1}^{p^v} = 1`. -/
theorem DualTate.pow_eq_one_of_one {T : Type u} [CommRing T] [Algebra R T] (y : G.DualTate T)
    (hy : y.1 1 = 1) (v : ℕ) : y.1 (v + 1) ^ (p ^ v) = 1 := by
  induction v with
  | zero => rw [pow_zero, pow_one]; exact hy
  | succ v ih =>
    rw [pow_succ', pow_mul, ← DualTate.dual_quot_succ, ← map_pow, ih, map_one]

include hc hc' in
/-- **A point `y ∈ T_p(G^∨)(S)` with `y_1 = 1` is a `p`-th power.** -/
theorem DualTate.exists_pow_eq_of_card (y : G.DualTate S) (hy : y.1 1 = 1) :
    ∃ w : G.DualTate S, w ^ p = y := by
  choose w hw using fun v =>
    G.exists_dual_quot_eq_of_card S hc hc' v (y.1 (v + 1)) (DualTate.pow_eq_one_of_one G y hy v)
  have hwp : ∀ v, w v ^ p = y.1 v := fun v => by
    rw [← G.dual_incl_quot_of_card S hc, hw, ← y.2 v]
  refine ⟨⟨w, fun v => G.dual_quot_injective_of_card S hc v ?_⟩, ?_⟩
  · rw [G.dual_quot_incl, hw, hwp]
  · apply Subtype.ext
    funext v
    exact hwp v

end PDivGroup

end PadicHodge

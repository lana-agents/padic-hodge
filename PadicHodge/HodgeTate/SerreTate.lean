/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.Action.Basic

/-!
# The Serre–Tate lemma (abstract form)

Let a group `G` act on a field `B` by ring automorphisms, let `K → B` be a field whose image is
exactly the fixed field `B^G`, and let `ψ_q : G → K` (`q ∈ ℤ`) be a family of "characters" with
`ψ_{a+b} = ψ_a ψ_b`, `ψ_0 = 1`, such that `B` has no nonzero `ψ_q`-eigenvectors for `q ≠ 0`
(Tate's theorem, for `B = ℂ_p`, `ψ_q = χ^q`). For a `B`-module `W` with a `B`-semilinear action
of `G`, let `E_q = {w | g w = ψ_q(g) w}` (a `K`-subspace).

**Serre–Tate lemma** ([BC, Lemma 2.3.1], in the form of [BC, Remark 2.3.2]): a family of vectors
`b_i ∈ E_{q_i}` that is `K`-linearly independent within each weight is `B`-linearly independent
(`linearIndependent_of_eigen`). Hence `∑_{q ∈ S} dim_K E_q ≤ dim_B W` (`sum_finrank_le`).

The proof is the minimal-relation argument of [BC, proof of Lemma 2.3.1].
-/

noncomputable section

open Module Finset

namespace PadicHodge.SerreTate

variable {G B K W : Type*} [Group G] [Field B] [Field K] [Algebra K B] [MulSemiringAction G B]
  [AddCommGroup W] [Module B W] [Module K W] [IsScalarTower K B W]
  [DistribMulAction G W]

/-- The data of the Serre–Tate situation. -/
structure Setup (G B K : Type*) [Group G] [Field B] [Field K] [Algebra K B]
    [MulSemiringAction G B] where
  /-- the characters `ψ_q : G → K` -/
  ψ : ℤ → G → K
  ψ_add : ∀ a b g, ψ (a + b) g = ψ a g * ψ b g
  ψ_zero : ∀ g, ψ 0 g = 1
  fixed_iff : ∀ c : B, (∀ g : G, g • c = c) ↔ c ∈ Set.range (algebraMap K B)
  tate : ∀ q : ℤ, q ≠ 0 → ∀ c : B, (∀ g : G, g • c = algebraMap K B (ψ q g) * c) → c = 0

variable (T : Setup G B K) (hW : ∀ (g : G) (c : B) (w : W), g • c • w = (g • c) • (g • w))

/-- The `ψ_q`-eigenspace `E_q = {w | ∀ g, g • w = ψ_q(g) • w}`. -/
def eigen (T : Setup G B K) (W : Type*) [AddCommGroup W] [Module B W] [Module K W]
    [IsScalarTower K B W] [DistribMulAction G W]
    (hW : ∀ (g : G) (c : B) (w : W), g • c • w = (g • c) • (g • w)) (q : ℤ) :
    Submodule K W where
  carrier := {w | ∀ g : G, g • w = T.ψ q g • w}
  add_mem' := fun {w w'} hw hw' g => by
    simp only [Set.mem_setOf_eq] at *
    rw [smul_add, hw g, hw' g, smul_add]
  zero_mem' := fun g => by simp
  smul_mem' := fun k w hw g => by
    simp only [Set.mem_setOf_eq] at *
    have hk : g • algebraMap K B k = algebraMap K B k := (T.fixed_iff _).mpr ⟨k, rfl⟩ g
    conv_lhs => rw [← algebraMap_smul B k w, hW, hk, hw g]
    rw [algebraMap_smul, smul_comm]

theorem mem_eigen {q : ℤ} {w : W} : w ∈ eigen T W hW q ↔ ∀ g : G, g • w = T.ψ q g • w := Iff.rfl

theorem ψ_ne_zero (q : ℤ) (g : G) : T.ψ q g ≠ 0 := by
  intro h
  have := T.ψ_add q (-q) g
  rw [add_neg_cancel, T.ψ_zero, h, zero_mul] at this
  exact one_ne_zero this

theorem ψ_neg_mul (q : ℤ) (g : G) : T.ψ (-q) g * T.ψ q g = 1 := by
  rw [← T.ψ_add, neg_add_cancel, T.ψ_zero]

/-- **Serre–Tate lemma.** Vectors `b_i ∈ E_{q_i}` that are `K`-linearly independent within each
weight are `B`-linearly independent. -/
theorem linearIndependent_of_eigen {ι : Type*} (q : ι → ℤ) (b : ι → W)
    (hb : ∀ i, b i ∈ eigen T W hW (q i))
    (hind : ∀ q0 : ℤ, LinearIndependent K (fun i : {i // q i = q0} => b i)) :
    LinearIndependent B b := by
  classical
  rw [linearIndependent_iff']
  suffices H : ∀ n : ℕ, ∀ s : Finset ι, s.card ≤ n → ∀ c : ι → B,
      ∑ i ∈ s, c i • b i = 0 → ∀ i ∈ s, c i = 0 from
    fun s c h i hi => H s.card s le_rfl c h i hi
  intro n
  induction n with
  | zero =>
    intro s hs c _ i hi
    rw [Nat.le_zero, Finset.card_eq_zero] at hs
    simp [hs] at hi
  | succ n ih =>
    intro s hs c hrel i0 hi0
    by_contra hc0
    -- normalise
    set c' : ι → B := fun i => (c i0)⁻¹ * c i with hc'
    have hrel' : ∑ i ∈ s, c' i • b i = 0 := by
      simp only [hc', mul_smul, ← Finset.smul_sum, hrel, smul_zero]
    have hc'0 : c' i0 = 1 := inv_mul_cancel₀ hc0
    -- twisting by `g`
    have htwist : ∀ g : G, ∀ i ∈ s,
        g • c' i * algebraMap K B (T.ψ (q i) g) = algebraMap K B (T.ψ (q i0) g) * c' i := by
      intro g
      set d : ι → B := fun i =>
        g • c' i * algebraMap K B (T.ψ (q i) g) - algebraMap K B (T.ψ (q i0) g) * c' i with hd
      have hsum : ∑ i ∈ s, d i • b i = 0 := by
        have h1 : g • (∑ i ∈ s, c' i • b i) =
            ∑ i ∈ s, (g • c' i * algebraMap K B (T.ψ (q i) g)) • b i := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hW, hb i g, ← algebraMap_smul B (T.ψ (q i) g) (b i), smul_smul]
        have h2 : algebraMap K B (T.ψ (q i0) g) • (∑ i ∈ s, c' i • b i) =
            ∑ i ∈ s, (algebraMap K B (T.ψ (q i0) g) * c' i) • b i := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
        simp only [hd, sub_smul, Finset.sum_sub_distrib, ← h1, ← h2, hrel', smul_zero,
          sub_zero]
      have hdi0 : d i0 = 0 := by
        simp only [hd, hc'0, smul_one, one_mul, mul_one, sub_self]
      have hsum' : ∑ i ∈ s.erase i0, d i • b i = 0 := by
        rw [← Finset.sum_erase_add _ _ hi0, hdi0, zero_smul, add_zero] at hsum
        exact hsum
      have hcard : (s.erase i0).card ≤ n := by
        rw [Finset.card_erase_of_mem hi0]; omega
      have hzero := ih (s.erase i0) hcard d hsum'
      intro i hi
      by_cases hii : i = i0
      · subst hii; exact sub_eq_zero.mp hdi0
      · exact sub_eq_zero.mp (hzero i (Finset.mem_erase.mpr ⟨hii, hi⟩))
    -- each `c' i` is a `ψ_{q i0 - q i}`-eigenvector
    have heig : ∀ i ∈ s, ∀ g : G, g • c' i = algebraMap K B (T.ψ (q i0 - q i) g) * c' i := by
      intro i hi g
      have h := htwist g i hi
      have hu := ψ_neg_mul T (q i) g
      calc g • c' i = g • c' i * algebraMap K B (T.ψ (q i) g) * algebraMap K B (T.ψ (-q i) g) := by
            rw [mul_assoc, ← map_mul, mul_comm (T.ψ (q i) g), hu, map_one, mul_one]
        _ = _ := by
            rw [h, mul_comm _ (c' i), mul_assoc, ← map_mul, ← T.ψ_add, mul_comm,
              ← sub_eq_add_neg]
    -- hence `c' i = 0` off the weight `q i0`, and `c' i ∈ K` on it
    have hoff : ∀ i ∈ s, q i ≠ q i0 → c' i = 0 := fun i hi hne =>
      T.tate _ (sub_ne_zero.mpr (Ne.symm hne)) _ (heig i hi)
    have hon : ∀ i ∈ s, q i = q i0 → ∃ k : K, algebraMap K B k = c' i := by
      intro i hi heq
      refine (T.fixed_iff _).mp fun g => ?_
      rw [heig i hi g, heq, sub_self, T.ψ_zero, map_one, one_mul]
    choose! k hk using hon
    -- the relation restricted to the weight `q i0` is `K`-linear
    have hrelK : ∑ i ∈ s.filter (fun i => q i = q i0), k i • b i = 0 := by
      rw [← hrel', ← Finset.sum_filter_add_sum_filter_not s (fun i => q i = q i0)]
      rw [Finset.sum_eq_zero (s := s.filter (fun i => ¬ q i = q i0)) (fun i hi => by
        rw [Finset.mem_filter] at hi; rw [hoff i hi.1 hi.2, zero_smul]), add_zero]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_filter] at hi
      rw [← hk i hi.1 hi.2, algebraMap_smul]
    have hli := linearIndependent_iff'.mp (hind (q i0))
      (s.subtype (fun i => q i = q i0)) (fun i => k i)
      (by rw [Finset.sum_subtype_eq_sum_filter (f := fun i => k i • b i)]; exact hrelK)
      ⟨i0, rfl⟩ (by simp [hi0])
    have := hk i0 hi0 rfl
    rw [hli, map_zero, hc'0] at this
    exact zero_ne_one this

/-- Single-weight form (Galois descent): `K`-linearly independent vectors of `E_q` are
`B`-linearly independent. -/
theorem linearIndependent_of_eigen_single {ι : Type*} (q : ℤ) (b : ι → W)
    (hb : ∀ i, b i ∈ eigen T W hW q) (hind : LinearIndependent K b) : LinearIndependent B b := by
  refine linearIndependent_of_eigen T hW (fun _ => q) b hb fun q0 => ?_
  by_cases h : q = q0
  · subst h
    exact hind.comp _ Subtype.val_injective
  · haveI : IsEmpty {i : ι // q = q0} := ⟨fun i => h i.2⟩
    exact linearIndependent_empty_type

/-- Each eigenspace is finite-dimensional. -/
theorem finiteDimensional_eigen [FiniteDimensional B W] (q : ℤ) :
    FiniteDimensional K (eigen T W hW q) := by
  have hle : Module.rank K (eigen T W hW q) ≤ finrank B W := by
    refine rank_le fun s hs => ?_
    have h1 : LinearIndependent K (fun i : s => ((i : eigen T W hW q) : W)) :=
      hs.map' (eigen T W hW q).subtype (Submodule.ker_subtype _)
    have h2 := linearIndependent_of_eigen_single T hW q (fun i : s => ((i : eigen T W hW q) : W))
      (fun i => (i : eigen T W hW q).2) h1
    have := h2.fintype_card_le_finrank
    simpa using this
  exact Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hle Cardinal.natCast_lt_aleph0)

/-- The family of all chosen basis vectors of the eigenspaces `E_q`, `q ∈ S`, is `B`-linearly
independent. -/
theorem linearIndependent_eigenBases [FiniteDimensional B W]
    [∀ q, FiniteDimensional K (eigen T W hW q)] (S : Finset ℤ) :
    LinearIndependent B (fun x : Σ q : S, Fin (finrank K (eigen T W hW q)) =>
      ((Module.finBasis K (eigen T W hW x.1) x.2 : eigen T W hW x.1) : W)) := by
  classical
  set d : S → ℕ := fun q => finrank K (eigen T W hW q)
  set bq : (q : S) → Basis (Fin (d q)) K (eigen T W hW q) := fun q => Module.finBasis K _
  set ι := Σ q : S, Fin (d q)
  set b : ι → W := fun x => (bq x.1 x.2 : W)
  set qf : ι → ℤ := fun x => (x.1 : ℤ)
  have hb : ∀ x, b x ∈ eigen T W hW (qf x) := fun x => (bq x.1 x.2).2
  have hind : ∀ q0 : ℤ, LinearIndependent K (fun x : {x : ι // qf x = q0} => b x) := by
    intro q0
    by_cases hq0 : ∃ x : ι, qf x = q0
    · obtain ⟨⟨a0, j0⟩, ha0⟩ := hq0
      set g : Fin (d a0) → {x : ι // qf x = q0} := fun j => ⟨⟨a0, j⟩, ha0⟩
      have hg : Function.Bijective g := by
        constructor
        · intro j j' h
          have h' := congrArg Subtype.val h
          exact eq_of_heq (Sigma.mk.inj_iff.mp h').2
        · rintro ⟨⟨a, j⟩, ha⟩
          have : a = a0 := Subtype.ext (ha.trans ha0.symm)
          subst this
          exact ⟨j, rfl⟩
      rw [← linearIndependent_equiv (Equiv.ofBijective g hg)]
      have := (bq a0).linearIndependent.map' (eigen T W hW (a0 : ℤ)).subtype
        (Submodule.ker_subtype _)
      exact this
    · haveI : IsEmpty {x : ι // qf x = q0} := ⟨fun x => hq0 ⟨x.1, x.2⟩⟩
      exact linearIndependent_empty_type
  exact linearIndependent_of_eigen T hW qf b hb hind

/-- **Dimension bound** ([BC, Lemma 2.3.1]): `∑_{q ∈ S} dim_K E_q ≤ dim_B W`. -/
theorem sum_finrank_le [FiniteDimensional B W] (S : Finset ℤ) :
    ∑ q ∈ S, finrank K (eigen T W hW q) ≤ finrank B W := by
  haveI := finiteDimensional_eigen T hW
  have hcard := (linearIndependent_eigenBases T hW (W := W) S).fintype_card_le_finrank
  rw [Fintype.card_sigma] at hcard
  simp only [Fintype.card_fin] at hcard
  rwa [← Finset.sum_coe_sort S (fun q => finrank K (eigen T W hW q))]

/-- If equality holds in the dimension bound, `W` has a `B`-basis of eigenvectors with weights in
`S` ("Hodge–Tate decomposition"). -/
theorem exists_eigenbasis [FiniteDimensional B W] (S : Finset ℤ)
    (h : ∑ q ∈ S, finrank K (eigen T W hW q) = finrank B W) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Basis ι B W) (q : ι → ℤ),
      (∀ i, q i ∈ S) ∧ ∀ i, b i ∈ eigen T W hW (q i) := by
  classical
  haveI := finiteDimensional_eigen T hW
  have hli := linearIndependent_eigenBases T hW (W := W) S
  have hcard : Fintype.card (Σ q : S, Fin (finrank K (eigen T W hW q))) = finrank B W := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rwa [← Finset.sum_coe_sort S (fun q => finrank K (eigen T W hW q))] at h
  refine ⟨_, inferInstance, basisOfLinearIndependentOfCardEqFinrank' _ hli hcard,
    fun x => (x.1 : ℤ), fun x => x.1.2, fun x => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  exact (Module.finBasis K (eigen T W hW x.1) x.2).2

/-- Conversely, a `B`-basis of eigenvectors forces equality in the dimension bound. -/
theorem sum_finrank_eq_of_eigenbasis [FiniteDimensional B W] {ι : Type*} [Finite ι]
    (b : Basis ι B W) (q : ι → ℤ) (hb : ∀ i, b i ∈ eigen T W hW (q i)) (S : Finset ℤ)
    (hS : ∀ i, q i ∈ S) : ∑ q ∈ S, finrank K (eigen T W hW q) = finrank B W := by
  classical
  haveI := finiteDimensional_eigen T hW
  haveI := Fintype.ofFinite ι
  refine le_antisymm (sum_finrank_le T hW S) ?_
  rw [finrank_eq_card_basis b, ← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := q) (fun i _ => hS i)]
  refine Finset.sum_le_sum fun q0 _ => ?_
  -- the basis vectors of weight `q0` are `K`-linearly independent in `E_{q0}`
  set s := Finset.univ.filter (fun i => q i = q0)
  have hli : LinearIndependent K (fun i : s => (⟨b i, by
      have := (Finset.mem_filter.mp i.2).2; rw [← this]; exact hb i⟩ : eigen T W hW q0)) := by
    have h1 : LinearIndependent B (fun i : s => b i) :=
      b.linearIndependent.comp _ Subtype.val_injective
    have h2 : LinearIndependent K (fun i : s => b i) := h1.restrict_scalars' K
    refine LinearIndependent.of_comp (eigen T W hW q0).subtype ?_
    exact h2
  have := hli.fintype_card_le_finrank
  simpa using this

end PadicHodge.SerreTate

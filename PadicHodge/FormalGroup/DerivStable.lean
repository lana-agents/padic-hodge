/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.FrobKernel
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.FieldTheory.Perfect

/-!
# `∂`-stable ideals of `k[[X_σ]]` in characteristic `p`

Let `k` be a perfect field of characteristic `p` (e.g. `𝔽_q`) and
`A = k[[X_σ]]`, `σ` finite. An ideal `𝔟 ⊆ A` is **`∂`-stable** (`DerivStable`) if it is stable
under all partial derivatives `∂/∂X_i` (`MvPowerSeries.pderiv`).

* **Frobenius decomposition** (`frob_decomp`): `f = ∑_{m ∈ box} (γ_m)^p X^m`, where
  `box = {m | ∀ i, m_i < p}` and `γ_m = ∑_q σ⁻¹(a_{pq + m}) X^q` (`frobCoeff`, `frobInv`); this uses
  `g^p = σ(g)(X^p)` (Mathlib's `MvPowerSeries.map_frobenius_expand`).
  Also `γ ∈ (X_j^N) → γ^p ∈ (X_j^{pN})` (`pow_mem_spanXPow_mul`).
* **Extraction** (`pow_mem_of_sum_mem`): if `𝔟` is `∂`-stable and `∑_m (γ_m)^p X^m ∈ 𝔟`, then
  every `(γ_m)^p ∈ 𝔟`. Proof by induction on the total degree: `∂_i` kills `p`-th powers, so
  `∂_i (∑ c_m X^m) = ∑ m_i c_m X^{m - e_i}` with `m_i` invertible in `k` for `0 < m_i < p`; this
  gives the coefficients of the non-constant monomials, and then the constant one.
* **Main theorem** (`le_spanXPow_of_derivStable`): if `(𝔞_v)_v` are `∂`-stable ideals contained in
  `(X_i)_i`, with `h^p ∈ 𝔞_{v+1} → h ∈ 𝔞_v`, then `𝔞_v ⊆ (X_j^{p^w})_j` for `w ≤ v`; hence
  `⋂_v 𝔞_v = 0` (`iInf_eq_bot_of_derivStable`) and `𝔞_v ⊆ (X_i)^N` for `v ≥ N`
  (`le_pow_of_derivStable`).
* **Criterion** (`derivStable_ker`): if `ρ : A →ₐ[k] B` kills `(X_i)^N` and `B` carries
  `k`-derivations `D_j` with `D_j (ρ X_i) = ρ (c_{ij})`, `c` an invertible matrix over `A`, then
  `ker ρ` is `∂`-stable (chain rule `derivation_map_eq_sum`).

This is a building block for the essential surjectivity part of Serre–Tate
([Hong, Prop. 2.2.13, Thm. 2.2.16] is the statement being worked towards; the proof here is our
own, via the Frobenius decomposition, not Hong's order-counting induction).
-/

noncomputable section

open Finsupp

namespace MvPowerSeries

/-! ### `∂`-stable ideals -/

section Defs

variable {σ R : Type*} [CommRing R]

/-- An ideal of `R[[X_σ]]` is **`∂`-stable** if it is stable under all partial derivatives. -/
def DerivStable (𝔟 : Ideal (MvPowerSeries σ R)) : Prop :=
  ∀ i, ∀ f ∈ 𝔟, pderiv R i f ∈ 𝔟

/-- `∂_i X^e = e_i X^{e - e_i}`. -/
theorem pderiv_monomial_one (i : σ) (e : σ →₀ ℕ) :
    pderiv R i (monomial e (1 : R)) = monomial (e - single i 1) (e i : R) := by
  classical
  ext n
  rw [coeff_pderiv, coeff_monomial, coeff_monomial]
  by_cases h : n + single i 1 = e
  · subst h
    rw [add_tsub_cancel_right, if_pos rfl, if_pos rfl, one_mul]
    simp
  · rw [if_neg h, zero_mul]
    split_ifs with h'
    · have he : e i = 0 := by
        by_contra hne
        apply h
        rw [h', tsub_add_cancel_of_le (single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hne))]
      rw [he, Nat.cast_zero]
    · rfl

/-- In characteristic `p`, partial derivatives kill `p`-th powers. -/
theorem pderiv_pow_char (p : ℕ) [CharP R p] (i : σ) (g : MvPowerSeries σ R) :
    pderiv R i (g ^ p) = 0 := by
  rw [Derivation.leibniz_pow, nsmul_eq_mul, ← map_natCast (C (σ := σ) (R := R)),
    CharP.cast_eq_zero, map_zero, zero_mul]

theorem monomial_eq_C_mul (n : σ →₀ ℕ) (r : R) :
    monomial n r = C r * monomial n (1 : R) := by
  classical
  ext a
  rw [coeff_C_mul, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

/-- `(X_j^M)_j ⊆ (X_i)_i^M`. -/
theorem spanXPow_le_pow (M : ℕ) :
    spanXPow σ R M ≤ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ M := by
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self j)) M

end Defs

/-! ### The Frobenius decomposition -/

section Frobenius

variable {σ k : Type*} [CommRing k] (p : ℕ)

/-- `σ⁻¹`, the inverse of the Frobenius of a perfect ring `k`. -/
abbrev frobInv [CharP k p] [Fact p.Prime] [PerfectRing k p] : k →+* k :=
  ((frobeniusEquiv k p).symm : k →+* k)

/-- `(σ⁻¹ g)^p = g(X^p)` for `k` perfect of characteristic `p`, on coefficients. -/
theorem coeff_pow_char_smul [CharP k p] [hp : Fact p.Prime] [PerfectRing k p]
    (g : MvPowerSeries σ k) (q : σ →₀ ℕ) :
    coeff (p • q) (map (frobInv (k := k) p) g ^ p) = coeff q g := by
  rw [← map_frobenius_expand p hp.out.ne_zero, coeff_map, coeff_expand_smul, coeff_map]
  exact frobenius_apply_frobeniusEquiv_symm k p _

theorem coeff_pow_char_of_not_dvd [CharP k p] [hp : Fact p.Prime]
    (g : MvPowerSeries σ k) {a : σ →₀ ℕ} {i : σ} (h : ¬ p ∣ a i) : coeff a (g ^ p) = 0 := by
  rw [← map_frobenius_expand p hp.out.ne_zero, coeff_map, coeff_expand_of_not_dvd p _ _ h,
    map_zero]

/-- The `m`-th Frobenius component `γ_m = ∑_q a_{pq + m} X^q` of `f = ∑_a a_a X^a`. -/
def frobCoeff (f : MvPowerSeries σ k) (m : σ →₀ ℕ) : MvPowerSeries σ k :=
  fun q => coeff (p • q + m) f

theorem coeff_frobCoeff (f : MvPowerSeries σ k) (m q : σ →₀ ℕ) :
    coeff q (frobCoeff p f m) = coeff (p • q + m) f := rfl

/-- **Frobenius decomposition**: `f = ∑_{m_i < p} (γ_m)^p X^m` with
`γ_m = σ⁻¹(frobCoeff p f m)` (`k` perfect). -/
theorem frob_decomp [Fintype σ] [DecidableEq σ] [CharP k p] [hp : Fact p.Prime]
    [PerfectRing k p] (f : MvPowerSeries σ k) :
    f = ∑ m : σ → Fin p, map (frobInv (k := k) p) (frobCoeff p f (boxExp m)) ^ p *
      monomial (boxExp m) 1 := by
  classical
  ext n
  rw [map_sum]
  simp only [coeff_mul_monomial, mul_one]
  let m₀ : σ → Fin p := fun i => ⟨n i % p, Nat.mod_lt _ hp.out.pos⟩
  let q₀ : σ →₀ ℕ := Finsupp.mapRange (· / p) (Nat.zero_div p) n
  have hn : p • q₀ + boxExp m₀ = n := by
    ext i
    simp [q₀, m₀, Nat.div_add_mod]
  rw [Finset.sum_eq_single m₀]
  · have hle : boxExp m₀ ≤ n := hn ▸ le_add_self
    rw [if_pos hle, ← hn, add_tsub_cancel_right, coeff_pow_char_smul p, coeff_frobCoeff]
  · intro m _ hm
    split_ifs with hle
    · obtain ⟨i, hi⟩ : ∃ i, m i ≠ m₀ i := by
        by_contra! h
        exact hm (funext h)
      refine coeff_pow_char_of_not_dvd p _ (i := i) fun hdvd => hi ?_
      have hmi : (m i : ℕ) ≤ n i := by simpa using Finsupp.le_def.1 hle i
      rw [Finsupp.tsub_apply, boxExp_apply] at hdvd
      obtain ⟨c, hc⟩ := hdvd
      have hni : n i = m i + p * c := by omega
      apply Fin.ext
      change (m i : ℕ) = n i % p
      rw [hni, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (m i).isLt]
    · rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `γ ∈ (X_j^N)_j → γ^p ∈ (X_j^{pN})_j`. -/
theorem pow_mem_spanXPow_mul [CharP k p] [hp : Fact p.Prime]
    {N : ℕ} {γ : MvPowerSeries σ k} (h : γ ∈ spanXPow σ k N) :
    γ ^ p ∈ spanXPow σ k (p * N) := by
  rw [← map_frobenius_expand p hp.out.ne_zero]
  have hle : spanXPow σ k N ≤ (spanXPow σ k (p * N)).comap (expand p hp.out.ne_zero) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, map_pow, expand_X, ← pow_mul]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hle' : spanXPow σ k (p * N) ≤ (spanXPow σ k (p * N)).comap (map (frobenius k p)) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, map_pow, map_X]
    exact Ideal.subset_span ⟨j, rfl⟩
  exact hle' (hle h)

end Frobenius

/-! ### Extraction of the Frobenius components from a `∂`-stable ideal -/

section Extraction

variable {σ k : Type*} [Field k]

/-- If `𝔟` is `∂`-stable and `∑_{j ∈ T} c_j X^{e_j} ∈ 𝔟` with the `e_j` distinct, in the box
`{m_i < p}`, of total degree `≤ N`, and all `∂_i c_j = 0`, then all `c_j ∈ 𝔟`. -/
theorem mem_of_sum_mem (p : ℕ) [CharP k p] {𝔟 : Ideal (MvPowerSeries σ k)}
    (h𝔟 : DerivStable 𝔟) {ι : Type*} (N : ℕ) :
    ∀ (T : Finset ι) (e : ι → σ →₀ ℕ) (c : ι → MvPowerSeries σ k), Set.InjOn e T →
      (∀ j ∈ T, ∀ i, e j i < p) → (∀ j ∈ T, (e j).degree ≤ N) →
      (∀ j ∈ T, ∀ i, pderiv k i (c j) = 0) →
      ∑ j ∈ T, c j * monomial (e j) 1 ∈ 𝔟 → ∀ j ∈ T, c j ∈ 𝔟 := by
  classical
  have hunit : ∀ r : k, r ≠ 0 → ∀ g, C r * g ∈ 𝔟 → g ∈ 𝔟 := by
    intro r hr g hg
    have h := 𝔟.mul_mem_left (C r⁻¹) hg
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hr, map_one, one_mul] at h
  -- if the coefficients of the non-constant monomials lie in `𝔟`, so does the constant one
  have hconst : ∀ (T : Finset ι) (e : ι → σ →₀ ℕ) (c : ι → MvPowerSeries σ k),
      Set.InjOn e T → ∑ j ∈ T, c j * monomial (e j) 1 ∈ 𝔟 →
      (∀ j ∈ T, e j ≠ 0 → c j ∈ 𝔟) → ∀ j ∈ T, c j ∈ 𝔟 := by
    intro T e c he hsum hne j hj
    by_cases hj0 : e j = 0
    · have hrest : ∑ j' ∈ T.erase j, c j' * monomial (e j') 1 ∈ 𝔟 := by
        refine 𝔟.sum_mem fun j' hj' => 𝔟.mul_mem_right _ (hne j' (Finset.mem_of_mem_erase hj') ?_)
        intro h0
        exact Finset.ne_of_mem_erase hj' (he (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hj'))
          (Finset.mem_coe.mpr hj) (h0.trans hj0.symm))
      rw [← Finset.add_sum_erase T _ hj] at hsum
      have h := 𝔟.sub_mem hsum hrest
      rwa [add_sub_cancel_right, hj0, monomial_zero_one, mul_one] at h
    · exact hne j hj hj0
  induction N with
  | zero =>
    intro T e c he _ hdeg _ hsum
    exact hconst T e c he hsum fun j hj hj0 =>
      absurd ((degree_eq_zero_iff _).mp (Nat.le_zero.mp (hdeg j hj))) hj0
  | succ N ih =>
    intro T e c he hbox hdeg hc hsum
    refine hconst T e c he hsum fun j hj hj0 => ?_
    obtain ⟨i, hi⟩ : ∃ i, e j i ≠ 0 := by
      by_contra! h
      exact hj0 (Finsupp.ext h)
    have hs : ∀ j', e j' i ≠ 0 → single i 1 ≤ e j' := fun j' h =>
      single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h)
    -- differentiate in `X_i`
    have hmem : ∑ j' ∈ T.filter (fun j' => e j' i ≠ 0),
        C (e j' i : k) * c j' * monomial (e j' - single i 1) 1 ∈ 𝔟 := by
      have h1 := h𝔟 i _ hsum
      rw [map_sum] at h1
      rw [Finset.sum_filter]
      convert h1 using 1
      refine Finset.sum_congr rfl fun j' hj' => ?_
      rw [Derivation.leibniz, hc j' hj' i, smul_zero, add_zero, smul_eq_mul,
        pderiv_monomial_one]
      split_ifs with h
      · rw [monomial_eq_C_mul (e j' - single i 1) (e j' i : k)]
        ring
      · rw [not_not.mp h, Nat.cast_zero, map_zero, mul_zero]
    have hcj := ih (T.filter fun j' => e j' i ≠ 0) (fun j' => e j' - single i 1)
      (fun j' => C (e j' i : k) * c j') ?_ ?_ ?_ ?_ hmem j (Finset.mem_filter.mpr ⟨hj, hi⟩)
    · refine hunit _ ?_ _ hcj
      rw [Ne, CharP.cast_eq_zero_iff k p]
      exact fun hd => hi (Nat.eq_zero_of_dvd_of_lt hd (hbox j hj i))
    · intro a ha b hb hab
      obtain ⟨ha, hai⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
      obtain ⟨hb, hbi⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
      refine he (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) ?_
      have hab' := congrArg (· + single i 1) hab
      simp only at hab'
      rwa [tsub_add_cancel_of_le (hs a hai), tsub_add_cancel_of_le (hs b hbi)] at hab'
    · intro a ha i'
      exact lt_of_le_of_lt (by rw [Finsupp.tsub_apply]; exact tsub_le_self)
        (hbox a (Finset.mem_filter.mp ha).1 i')
    · intro a ha
      obtain ⟨ha, hai⟩ := Finset.mem_filter.mp ha
      have h1 := congrArg Finsupp.degree (tsub_add_cancel_of_le (hs a hai))
      rw [map_add, degree_single] at h1
      have := hdeg a ha
      omega
    · intro a ha i'
      rw [Derivation.leibniz, pderiv_C, hc a (Finset.mem_filter.mp ha).1 i', smul_zero,
        smul_zero, add_zero]

/-- **Extraction**: if `𝔟` is `∂`-stable and `∑_{m_i < p} (γ_m)^p X^m ∈ 𝔟`, then every
`(γ_m)^p ∈ 𝔟`. -/
theorem pow_mem_of_sum_mem [Fintype σ] [DecidableEq σ] (p : ℕ) [CharP k p]
    {𝔟 : Ideal (MvPowerSeries σ k)}
    (h𝔟 : DerivStable 𝔟) (γ : (σ → Fin p) → MvPowerSeries σ k)
    (h : ∑ m, γ m ^ p * monomial (boxExp m) 1 ∈ 𝔟) (m : σ → Fin p) : γ m ^ p ∈ 𝔟 :=
  mem_of_sum_mem p h𝔟 (Finset.univ.sup fun m => (boxExp m).degree) Finset.univ boxExp
    (fun m => γ m ^ p) boxExp_injective.injOn (fun m _ i => by rw [boxExp_apply]; exact (m i).isLt)
    (fun m _ => Finset.le_sup (f := fun m => (boxExp m).degree) (Finset.mem_univ m))
    (fun m _ i => pderiv_pow_char p i _) h m (Finset.mem_univ m)

end Extraction

/-! ### The main theorem -/

section Main

variable {σ k : Type*} [Field k] [Finite σ] (p : ℕ) [CharP k p] [Fact p.Prime] [PerfectRing k p]

/-- **Main theorem.** Let `𝔞_v` be `∂`-stable ideals of `k[[X_σ]]` contained in `(X_i)_i` such
that `h^p ∈ 𝔞_{v+1} → h ∈ 𝔞_v`. Then `𝔞_v ⊆ (X_j^{p^w})_j` for all `w ≤ v`. -/
theorem le_spanXPow_of_derivStable
    (𝔞 : ℕ → Ideal (MvPowerSeries σ k)) (hstab : ∀ v, DerivStable (𝔞 v))
    (hX : ∀ v, 𝔞 v ≤ Ideal.span (Set.range X)) (hfrob : ∀ v h, h ^ p ∈ 𝔞 (v + 1) → h ∈ 𝔞 v) :
    ∀ w v, w ≤ v → 𝔞 v ≤ spanXPow σ k (p ^ w) := by
  classical
  have := Fintype.ofFinite σ
  intro w
  induction w with
  | zero =>
    intro v _
    change 𝔞 v ≤ Ideal.span (Set.range fun j => (X j : MvPowerSeries σ k) ^ p ^ 0)
    simpa using hX v
  | succ w ih =>
    intro v hv f hf
    obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
    have hf' : ∑ m : σ → Fin p, map (frobInv (k := k) p) (frobCoeff p f (boxExp m)) ^ p *
        monomial (boxExp m) 1 ∈ 𝔞 (u + 1) := by
      rw [← frob_decomp p f]
      exact hf
    rw [frob_decomp p f]
    refine Ideal.sum_mem _ fun m _ => Ideal.mul_mem_right _ _ ?_
    rw [pow_succ']
    exact pow_mem_spanXPow_mul p (ih u (by omega) (hfrob u _
      (pow_mem_of_sum_mem p (hstab (u + 1))
        (fun m => map (frobInv (k := k) p) (frobCoeff p f (boxExp m))) hf' m)))

/-- Under the hypotheses of `le_spanXPow_of_derivStable`, `⋂_v 𝔞_v = 0`. -/
theorem iInf_eq_bot_of_derivStable
    (𝔞 : ℕ → Ideal (MvPowerSeries σ k)) (hstab : ∀ v, DerivStable (𝔞 v))
    (hX : ∀ v, 𝔞 v ≤ Ideal.span (Set.range X)) (hfrob : ∀ v h, h ^ p ∈ 𝔞 (v + 1) → h ∈ 𝔞 v) :
    ⨅ v, 𝔞 v = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot]
  ext n
  rw [map_zero]
  have hmem := le_spanXPow_of_derivStable p 𝔞 hstab hX hfrob n.degree n.degree le_rfl
    (Submodule.mem_iInf _ |>.mp hf n.degree)
  exact coeff_eq_zero_of_mem_spanXPow hmem fun j =>
    lt_of_le_of_lt (le_degree j n) (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)

/-- Under the hypotheses of `le_spanXPow_of_derivStable`, `𝔞_v ⊆ (X_i)_i^N` for `v ≥ N`. -/
theorem le_pow_of_derivStable
    (𝔞 : ℕ → Ideal (MvPowerSeries σ k)) (hstab : ∀ v, DerivStable (𝔞 v))
    (hX : ∀ v, 𝔞 v ≤ Ideal.span (Set.range X)) (hfrob : ∀ v h, h ^ p ∈ 𝔞 (v + 1) → h ∈ 𝔞 v)
    (N : ℕ) : ∀ v, N ≤ v → 𝔞 v ≤ Ideal.span (Set.range X) ^ N := by
  intro v hv
  refine (le_spanXPow_of_derivStable p 𝔞 hstab hX hfrob v v le_rfl).trans ?_
  refine (spanXPow_le_pow (p ^ v)).trans (Ideal.pow_le_pow_right ?_)
  exact hv.trans (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le

end Main

/-! ### A criterion for `∂`-stability -/

section Criterion

variable {σ k : Type*} [CommRing k] [Fintype σ]

/-- A power series all of whose monomials have total degree `> #σ · N` lies in `(X_i)_i^N`. -/
theorem mem_pow_of_coeff (N : ℕ) (g : MvPowerSeries σ k)
    (h : ∀ a, coeff a g ≠ 0 → Fintype.card σ * N < a.degree) :
    g ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ k)) ^ N := by
  letI : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  refine spanXPow_le_pow N (mem_span_X_pow N g fun a ha => ?_)
  by_contra! hlt
  have h1 := h a ha
  rw [Finsupp.degree_eq_sum] at h1
  have h2 : ∑ i, a i ≤ ∑ _i : σ, N := Finset.sum_le_sum fun i _ => (hlt i).le
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h2
  omega

/-- **Chain rule** through `ρ : k[[X]] → B` killing `(X_i)^N`: for a `k`-derivation `D` of `B`,
`D (ρ f) = ∑_i ρ (∂_i f) · D (ρ X_i)`. -/
theorem derivation_map_eq_sum {B : Type*} [CommRing B] [Algebra k B]
    (ρ : MvPowerSeries σ k →ₐ[k] B) {N : ℕ}
    (hN : Ideal.span (Set.range X) ^ N ≤ RingHom.ker ρ) (D : Derivation k B B)
    (f : MvPowerSeries σ k) : D (ρ f) = ∑ i, ρ (pderiv k i f) * D (ρ (X i)) := by
  set K := Fintype.card σ * N + 2
  set P : MvPolynomial σ k := truncTotal K f
  have hlow : ∀ a : σ →₀ ℕ, coeff a (f - (P : MvPowerSeries σ k)) ≠ 0 → K ≤ a.degree := by
    intro a ha
    by_contra! hlt
    rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hlt, sub_self] at ha
    exact ha rfl
  have hker : ∀ g ∈ Ideal.span (Set.range X) ^ N, ρ g = 0 := fun g hg =>
    RingHom.mem_ker.mp (hN hg)
  have hg : ρ (f - (P : MvPowerSeries σ k)) = 0 := hker _ (mem_pow_of_coeff N _ fun a ha => by
    have := hlow a ha
    omega)
  have hgi : ∀ i, ρ (pderiv k i (f - (P : MvPowerSeries σ k))) = 0 := fun i =>
    hker _ (mem_pow_of_coeff N _ fun a ha => by
    rw [coeff_pderiv] at ha
    have := hlow _ (left_ne_zero_of_mul ha)
    rw [map_add, degree_single] at this
    omega)
  have e : ∀ Q : MvPolynomial σ k,
      MvPolynomial.coeToMvPowerSeries.algHom k Q = (Q : MvPowerSeries σ k) := by
    intro Q
    rw [MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self,
      MvPowerSeries.map_id, RingHom.id_apply]
  have hcomp : ρ.comp (MvPolynomial.coeToMvPowerSeries.algHom k) =
      MvPolynomial.aeval fun i => ρ (X i) := MvPolynomial.algHom_ext fun i => by
    rw [AlgHom.comp_apply, e, MvPolynomial.coe_X, MvPolynomial.aeval_X]
  have hρP : ∀ Q : MvPolynomial σ k,
      ρ (Q : MvPowerSeries σ k) = MvPolynomial.aeval (fun i => ρ (X i)) Q := by
    intro Q
    rw [← e, ← AlgHom.comp_apply, hcomp]
  have h1 : ρ f = ρ (P : MvPowerSeries σ k) := by
    rw [← sub_eq_zero, ← map_sub]
    exact hg
  have h2 : ∀ i, ρ (pderiv k i f) = ρ (pderiv k i (P : MvPowerSeries σ k)) := fun i => by
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    exact hgi i
  rw [h1, hρP, MvPolynomial.derivation_aeval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, h2, pderiv_coe, hρP]

/-- **`∂`-stability criterion**: let `ρ : k[[X_σ]] →ₐ[k] B` kill `(X_i)_i^N`, and let `D_j` be
`k`-derivations of `B` with `D_j (ρ X_i) = ρ (c_{ij})` for a matrix `c` over `k[[X_σ]]` with
invertible determinant. Then `ker ρ` is `∂`-stable. -/
theorem derivStable_ker [DecidableEq σ] {B : Type*} [CommRing B] [Algebra k B]
    (ρ : MvPowerSeries σ k →ₐ[k] B) {N : ℕ}
    (hN : Ideal.span (Set.range X) ^ N ≤ RingHom.ker ρ) (D : σ → Derivation k B B)
    (c : Matrix σ σ (MvPowerSeries σ k)) (hc : IsUnit c.det)
    (hD : ∀ i j, D j (ρ (X i)) = ρ (c i j)) : DerivStable (RingHom.ker ρ) := by
  intro l f hf
  rw [RingHom.mem_ker] at hf
  have hv : ∀ j, Matrix.vecMul (fun i => pderiv k i f) c j ∈ RingHom.ker ρ := by
    intro j
    have h := derivation_map_eq_sum ρ hN (D j) f
    rw [hf, map_zero] at h
    rw [RingHom.mem_ker]
    simp only [Matrix.vecMul, dotProduct]
    rw [map_sum]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans h.symm
    rw [hD, map_mul]
  have key : pderiv k l f = Matrix.vecMul (Matrix.vecMul (fun i => pderiv k i f) c) c⁻¹ l := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hc, Matrix.vecMul_one]
  rw [key]
  simp only [Matrix.vecMul, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hv j)

end Criterion

end MvPowerSeries

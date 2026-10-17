/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.AlmostEtale.TraceOne

/-!
# `H¹(Gal(ℚ̄_p/K_∞), ℂ_p) = 0`

Let `K / ℚ_p` be finite and `H_K = Gal(ℚ̄_p/K_∞)`, `K_∞ = K(μ_{p^∞})` (realised as `HK K`, a
subgroup of `G_K = K.fixingSubgroup`). Every continuous crossed homomorphism
`c : H_K → ℂ_p`, `c(gh) = c(g) + g c(h)`, is a coboundary (`exists_coboundary`).

This is the standard consequence of Tate's almost-étaleness ([BC, Lemma 14.1.3], axiom (TS1)):

* (`exists_approx`) given `η > 0`, continuity of `c` at `1` gives a finite `E = ℚ_p(θ)` with
  `‖c‖ < η` on `H_K ∩ Gal(ℚ̄_p/E)`. Descend to a finite layer `N_m(θ) / N_m`
  (`exists_trace_one`): `α ∈ N_m(θ)` with `∑_σ σ(α) = 1`, `‖α‖ ≤ 2`, and lifts `τ_σ ∈ H_K` of the
  embeddings `σ` (`exists_extend`). Then `B = ∑_σ σ(α) c(τ_σ)` satisfies
  `‖c(g) + gB − B‖ ≤ 2η` for all `g ∈ H_K` (left multiplication by `g` permutes the `σ`, and
  `τ_{gσ}⁻¹ g τ_σ` fixes `N_m(θ) ⊇ E`), and `‖B‖ ≤ 2 sup ‖c‖`;
* (`exists_coboundary`) iterating with `η` decreasing geometrically, the `B`'s form a convergent
  series in the complete field `ℂ_p`.
-/

noncomputable section

open Polynomial IntermediateField Module Topology

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K̄" => PadicAlgCl p

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]

/-- The underlying automorphism of `ℚ̄_p` of an element of `H_K`. -/
abbrev hk (g : HK K) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p :=
  ((g : K.fixingSubgroup) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

omit [FiniteDimensional ℚ_[p] K] in
theorem hk_mem (g : HK K) : hk g ∈ (K ⊔ cycFieldInf p).fixingSubgroup := (mem_HK_iff K).mp g.2

/-- An element of `Gal(ℚ̄_p/K_∞)` as an element of `H_K`. -/
def toHK {τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hτ : τ ∈ (K ⊔ cycFieldInf p).fixingSubgroup) :
    HK K :=
  ⟨⟨τ, fixingSubgroup_antitone (le_sup_left : K ≤ K ⊔ cycFieldInf p) hτ⟩, (mem_HK_iff K).mpr hτ⟩

omit [FiniteDimensional ℚ_[p] K] in
theorem hk_toHK {τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (hτ : τ ∈ (K ⊔ cycFieldInf p).fixingSubgroup) : hk (toHK hτ) = τ := rfl

omit [FiniteDimensional ℚ_[p] K] in
/-- Continuity at `1`: a continuous function on `H_K` vanishing at `1` is small on
`H_K ∩ Gal(ℚ̄_p/E)` for some finite `E`. -/
theorem exists_small (c : HK K → ℂ_[p]) (hc : Continuous c) (hc1 : c 1 = 0) {η : ℝ}
    (hη : 0 < η) : ∃ E : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] E ∧
      ∀ g : HK K, hk g ∈ E.fixingSubgroup → ‖c g‖ < η := by
  have h1 : {g : HK K | ‖c g‖ < η} ∈ 𝓝 (1 : HK K) := by
    refine (hc.norm.isOpen_preimage _ isOpen_Iio).mem_nhds ?_
    simp [hc1, hη]
  rw [mem_nhds_subtype] at h1
  obtain ⟨u, hu, hus⟩ := h1
  rw [mem_nhds_subtype] at hu
  obtain ⟨v, hv, hvu⟩ := hu
  obtain ⟨E, hE, hEv⟩ := (krullTopology_mem_nhds_one_iff ℚ_[p] (PadicAlgCl p) v).mp hv
  refine ⟨E, hE, fun g hg => hus (hvu (hEv hg))⟩

variable (K) in
/-- The action of `H_K` on `ℂ_p`. -/
abbrev actH (g : HK K) (x : ℂ_[p]) : ℂ_[p] := autCp (hk g) x

/-- **One approximation step** ([BC, Lemma 14.1.3]). -/
theorem exists_approx (c : HK K → ℂ_[p]) (hc : Continuous c)
    (hco : ∀ g h, c (g * h) = c g + actH K g (c h)) {η : ℝ} (hη : 0 < η) :
    ∃ B : ℂ_[p], (∀ g, ‖c g + (actH K g B - B)‖ ≤ 2 * η) ∧
      ∀ r : ℝ, (∀ g, ‖c g‖ ≤ r) → ‖B‖ ≤ 2 * r := by
  classical
  have hc1 : c 1 = 0 := by
    have h := hco 1 1
    rw [mul_one] at h
    have h2 : actH K 1 (c 1) = c 1 := by
      change autCp 1 (c 1) = c 1
      rw [map_one]
      rfl
    rw [h2] at h
    linear_combination -h
  obtain ⟨E, hE, hsmall⟩ := exists_small c hc hc1 hη
  obtain ⟨θ0, hθ0⟩ := Field.exists_primitive_element ℚ_[p] E
  set θ : PadicAlgCl p := (θ0 : PadicAlgCl p)
  obtain ⟨m₀, hm₀⟩ := exists_coeff_mem_Nl K θ
  obtain ⟨m₁, hm₁⟩ := exists_trace_one K θ
  set m := max m₀ m₁
  obtain ⟨α, hα2, hαsum⟩ := hm₁ m (le_max_right _ _)
  have hcoef := hm₀ m (le_max_left _ _)
  have hEEm : E ≤ ((Nl K m)⟮θ⟯).restrictScalars ℚ_[p] := le_adjoin_of_primitive hθ0 (Nl K m)
  -- lifts of the embeddings
  choose τ hτmem hτ using fun σ : (Nl K m)⟮θ⟯ →ₐ[(Nl K m)] PadicAlgCl p => exists_extend K hcoef σ
  set T : ((Nl K m)⟮θ⟯ →ₐ[(Nl K m)] PadicAlgCl p) → HK K := fun σ => toHK (hτmem σ)
  have hT : ∀ σ (x : (Nl K m)⟮θ⟯), hk (T σ) x = σ x := fun σ x => hτ σ x
  have hnormσ : ∀ σ : (Nl K m)⟮θ⟯ →ₐ[(Nl K m)] PadicAlgCl p,
      ‖σ α‖ = ‖(α : PadicAlgCl p)‖ := fun σ => by
    rw [← hT σ α, norm_aut_apply]
  set B : ℂ_[p] := ∑ σ, ((σ α : PadicAlgCl p) : ℂ_[p]) * c (T σ)
  refine ⟨B, fun g => ?_, fun r hr => ?_⟩
  · -- left multiplication by `g` on embeddings
    set gN : PadicAlgCl p →ₐ[(Nl K m)] PadicAlgCl p :=
      { toRingHom := (hk g).toRingEquiv.toRingHom
        commutes' := fun r => (IntermediateField.mem_fixingSubgroup_iff _ _).mp (hk_mem g) r
          (Nl_le K m r.2) }
    set Φ : ((Nl K m)⟮θ⟯ →ₐ[(Nl K m)] PadicAlgCl p) →
        ((Nl K m)⟮θ⟯ →ₐ[(Nl K m)] PadicAlgCl p) := fun σ => gN.comp σ
    have hΦinj : Function.Injective Φ := by
      intro σ σ' h
      ext x
      have := congrArg (fun φ : (Nl K m)⟮θ⟯ →ₐ[(Nl K m)] PadicAlgCl p => φ x) h
      exact (hk g).injective this
    have hΦ : Function.Bijective Φ := Finite.injective_iff_bijective.mp hΦinj
    set e := Equiv.ofBijective Φ hΦ
    have hΦapp : ∀ σ x, Φ σ x = hk g (σ x) := fun σ x => rfl
    -- `h_σ = τ_{Φσ}⁻¹ g τ_σ` fixes `E`
    set hσ : ((Nl K m)⟮θ⟯ →ₐ[(Nl K m)] PadicAlgCl p) → HK K := fun σ => (T (Φ σ))⁻¹ * g * T σ
    have hfix : ∀ σ, hk (hσ σ) ∈ E.fixingSubgroup := by
      intro σ
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hxEm : x ∈ (Nl K m)⟮θ⟯ := hEEm hx
      have h1 : hk (T σ) x = σ ⟨x, hxEm⟩ := hT σ ⟨x, hxEm⟩
      have h2 : hk g (σ ⟨x, hxEm⟩) = hk (T (Φ σ)) x := by
        rw [← hΦapp]; exact (hT (Φ σ) ⟨x, hxEm⟩).symm
      simp only [hσ, hk, Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply]
      change (hk (T (Φ σ)))⁻¹ (hk g (hk (T σ) x)) = x
      rw [h1, h2]
      exact (hk (T (Φ σ))).symm_apply_apply x
    have hdecomp : ∀ σ, g * T σ = T (Φ σ) * hσ σ := fun σ => by simp only [hσ]; group
    have hgB : actH K g B = ∑ σ, ((Φ σ α : PadicAlgCl p) : ℂ_[p]) *
        (c (T (Φ σ)) + actH K (T (Φ σ)) (c (hσ σ)) - c g) := by
      simp only [B, actH, map_sum, map_mul, autCp_coe]
      refine Finset.sum_congr rfl fun σ _ => ?_
      congr 1
      have := hco g (T σ)
      rw [hdecomp, hco] at this
      change autCp (hk g) (c (T σ)) = _
      rw [actH] at this
      linear_combination -this
    have hsum1 : ∑ σ, ((Φ σ α : PadicAlgCl p) : ℂ_[p]) = 1 := by
      have h1 : ∑ σ, ((Φ σ α : PadicAlgCl p) : ℂ_[p]) = ∑ σ, ((e σ α : PadicAlgCl p) : ℂ_[p]) := rfl
      rw [h1, Equiv.sum_comp e (fun σ => ((σ α : PadicAlgCl p) : ℂ_[p]))]
      simp only [PadicComplex.coe_eq]
      rw [← map_sum, hαsum, map_one]
    have hsumB : ∑ σ, ((Φ σ α : PadicAlgCl p) : ℂ_[p]) * c (T (Φ σ)) = B :=
      Equiv.sum_comp e (fun σ => ((σ α : PadicAlgCl p) : ℂ_[p]) * c (T σ))
    have herr : c g + (actH K g B - B) = ∑ σ, ((Φ σ α : PadicAlgCl p) : ℂ_[p]) *
        actH K (T (Φ σ)) (c (hσ σ)) := by
      rw [hgB]
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsumB,
        ← Finset.sum_mul, hsum1]
      ring
    rw [herr]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun σ _ => ?_
    rw [norm_mul, PadicComplex.norm_extends, hnormσ, actH, norm_autCp]
    exact mul_le_mul hα2 (hsmall _ (hfix σ)).le (norm_nonneg _) (by norm_num)
  · have hr0 : 0 ≤ r := (norm_nonneg _).trans (hr 1)
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun σ _ => ?_
    rw [norm_mul, PadicComplex.norm_extends, hnormσ]
    exact mul_le_mul hα2 (hr _) (norm_nonneg _) (by norm_num)

/-- **`H¹(Gal(ℚ̄_p/K_∞), ℂ_p) = 0`**: every continuous crossed homomorphism `H_K → ℂ_p` is a
coboundary. -/
theorem exists_coboundary (c : HK K → ℂ_[p]) (hc : Continuous c)
    (hco : ∀ g h, c (g * h) = c g + actH K g (c h)) :
    ∃ B : ℂ_[p], ∀ g, c g = actH K g B - B := by
  classical
  have hcontd : ∀ B : ℂ_[p], Continuous fun g : HK K => actH K g B - B := fun B =>
    ((continuous_autCp_apply B).comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      continuous_const
  have hcod : ∀ (B : ℂ_[p]) (g h : HK K), actH K (g * h) B - B =
      (actH K g B - B) + actH K g (actH K h B - B) := by
    intro B g h
    simp only [actH, hk, Subgroup.coe_mul, map_mul, map_sub]
    change autCp _ (autCp _ B) - B = _
    ring
  -- the set of good data
  let S := {d : HK K → ℂ_[p] // Continuous d ∧ ∀ g h, d (g * h) = d g + actH K g (d h)}
  have step : ∀ (d : S) (η : ℝ), 0 < η → ∃ B : ℂ_[p], (∀ g, ‖d.1 g + (actH K g B - B)‖ ≤ 2 * η) ∧
      ∀ r : ℝ, (∀ g, ‖d.1 g‖ ≤ r) → ‖B‖ ≤ 2 * r := fun d η hη => exists_approx d.1 d.2.1 d.2.2 hη
  choose Bf hBf1 hBf2 using step
  have hnext : ∀ (d : S) (η : ℝ) (hη : 0 < η),
      Continuous (fun g => d.1 g + (actH K g (Bf d η hη) - Bf d η hη)) ∧
      ∀ g h, (fun g => d.1 g + (actH K g (Bf d η hη) - Bf d η hη)) (g * h) =
        (fun g => d.1 g + (actH K g (Bf d η hη) - Bf d η hη)) g +
          actH K g ((fun g => d.1 g + (actH K g (Bf d η hη) - Bf d η hη)) h) := by
    intro d η hη
    refine ⟨d.2.1.add (hcontd _), fun g h => ?_⟩
    simp only [d.2.2 g h, hcod, actH, map_add]
    ring
  set ηs : ℕ → ℝ := fun k => (1 / 4 : ℝ) ^ k with hηs
  have hηpos : ∀ k, 0 < ηs k := fun k => by positivity
  -- the sequence of cocycles `d_k` and corrections `B_k`
  let D : ℕ → S := fun k => Nat.rec ⟨c, hc, hco⟩
    (fun k dk => ⟨_, hnext dk (ηs k) (hηpos k)⟩) k
  set Bs : ℕ → ℂ_[p] := fun k => Bf (D k) (ηs k) (hηpos k) with hBs
  have hD0 : (D 0).1 = c := rfl
  have hDs : ∀ k g, (D (k + 1)).1 g = (D k).1 g + (actH K g (Bs k) - Bs k) := fun k g => rfl
  -- bounds
  have hDbound : ∀ k, ∀ g, ‖(D (k + 1)).1 g‖ ≤ 2 * ηs k := fun k g => by
    rw [hDs]; exact hBf1 _ _ _ g
  have hBbound : ∀ k, ‖Bs (k + 1)‖ ≤ 4 * ηs k := fun k => by
    have := hBf2 (D (k + 1)) (ηs (k + 1)) (hηpos _) (2 * ηs k) (hDbound k)
    linarith
  -- summability
  have hsum : Summable Bs := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_norm_bounded (g := fun k => 4 * ηs k) ?_ (fun k => hBbound k)
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4
  set Btot := ∑' k, Bs k
  -- partial sums
  have hpartial : ∀ n g, (D n).1 g = c g + (actH K g (∑ k ∈ Finset.range n, Bs k) -
      ∑ k ∈ Finset.range n, Bs k) := by
    intro n g
    induction n with
    | zero => simp [hD0, actH]
    | succ n ih =>
      rw [hDs, ih, Finset.sum_range_succ, actH, actH, actH, map_add]
      ring
  refine ⟨-Btot, fun g => ?_⟩
  have hlim : Filter.Tendsto (fun n => (D n).1 g) Filter.atTop (𝓝 0) := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num)).const_mul (8 : ℝ)
    rw [mul_zero] at ht
    refine squeeze_zero_norm' (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩) ht
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine (hDbound k g).trans (le_of_eq ?_)
    simp only [hηs]
    ring
  have hS := hsum.hasSum.tendsto_sum_nat
  have hlim2 : Filter.Tendsto (fun n => c g + (actH K g (∑ k ∈ Finset.range n, Bs k) -
      ∑ k ∈ Finset.range n, Bs k)) Filter.atTop (𝓝 (c g + (actH K g Btot - Btot))) :=
    tendsto_const_nhds.add ((((continuous_autCp (hk g)).tendsto _).comp hS).sub hS)
  have h0 : c g + (actH K g Btot - Btot) = 0 :=
    tendsto_nhds_unique (hlim2.congr fun n => (hpartial n g).symm) hlim
  rw [actH, map_neg]
  rw [actH] at h0
  linear_combination h0

end PadicHodge

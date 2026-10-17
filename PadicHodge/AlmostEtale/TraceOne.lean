/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.AlmostEtale.Tower
import PadicHodge.TateSen.H1K

/-!
# Tate's almost-étaleness theorem for `K_∞ = K(μ_{p^∞})`

For `K / ℚ_p` finite let `N_m = K(μ_{p^{m+1}})` and `K_∞ = ⋃ N_m = K ⊔ ℚ_p(μ_{p^∞})`.
For a finite extension `K_∞(θ) / K_∞` we descend to the finite layers `N_m(θ) / N_m`
([BC, Exercise 13.7.2]: for `m` large the minimal polynomial of `θ` over `K_∞` has coefficients in
`N_m`), and obtain (`exists_trace_one`, the form of [BC, Thm. 13.1.2] used in [BC, Lemma 14.1.3]):

  there is `α ∈ N_m(θ)` with `∑_σ σ(α) = Tr_{N_m(θ)/N_m}(α) = 1` and `‖α‖ ≤ 2`,

where `σ` runs over the `N_m`-embeddings `N_m(θ) → ℚ̄_p`; every such `σ` extends to an element of
`Gal(ℚ̄_p/K_∞)` (`exists_extend`). The proof combines the cyclotomic tower estimate
`exists_trace_large` (base `F_m = ℚ_p(μ_{p^{m+1}})`, layers `L_m = N_m(θ)`) with the trace bound
over the intermediate field `N_m`.
-/

noncomputable section

open Polynomial IntermediateField Module

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K̄" => PadicAlgCl p

/-- `‖Tr_{L/F}(u)‖ ≤ ‖Tr_{L/N}(u)‖` for `F ⊆ N ⊆ L`. -/
theorem norm_trace_le_norm_trace {F N L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] L] (hFN : F ≤ N) (hNL : N ≤ L) (u : PadicAlgCl p) :
    ‖(rdeg F L : PadicAlgCl p) * nt F u‖ ≤ ‖(rdeg N L : PadicAlgCl p) * nt N u‖ := by
  haveI : FiniteDimensional ℚ_[p] N := finiteDimensional_of_le' hNL
  rw [rdeg_mul hFN hNL, ← nt_nt hFN u, Nat.cast_mul, mul_assoc,
    ← nt_mul_left F (IntermediateField.natCast_mem F (rdeg N L))]
  exact norm_rdeg_mul_nt_le F hFN (mul_mem (IntermediateField.natCast_mem N _) (nt_mem N u))

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]

/-- The layers `N_m = K(μ_{p^{m+1}})`. -/
abbrev Nl (m : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) := K ⊔ cycField p (m + 1)

instance (m : ℕ) : FiniteDimensional ℚ_[p] (Nl K m) := by
  haveI := finiteDimensional_cycField (p := p) (m + 1)
  infer_instance

omit [FiniteDimensional ℚ_[p] K] in
theorem Nl_mono {m m' : ℕ} (h : m ≤ m') : Nl K m ≤ Nl K m' :=
  sup_le_sup_left (cycField_mono (by omega)) K

omit [FiniteDimensional ℚ_[p] K] in
theorem Nl_le (m : ℕ) : Nl K m ≤ K ⊔ cycFieldInf p :=
  sup_le_sup_left (le_iSup (fun k => cycField p k) (m + 1)) K

omit [FiniteDimensional ℚ_[p] K] in
theorem exists_mem_Nl {x : PadicAlgCl p} (hx : x ∈ K ⊔ cycFieldInf p) : ∃ m, x ∈ Nl K m := by
  have heq : K ⊔ cycFieldInf p = ⨆ m, Nl K m := by
    refine le_antisymm (sup_le ?_ (iSup_le fun k => ?_)) (iSup_le fun m => Nl_le K m)
    · exact (le_sup_left : K ≤ Nl K 0).trans (le_iSup (Nl K) 0)
    · exact (cycField_mono (by omega : k ≤ k + 1)).trans
        ((le_sup_right : cycField p (k + 1) ≤ Nl K k).trans (le_iSup (Nl K) k))
  rw [heq] at hx
  have hdir : Directed (· ≤ ·) (Nl K) := fun a b =>
    ⟨max a b, Nl_mono K (le_max_left a b), Nl_mono K (le_max_right a b)⟩
  rw [← SetLike.mem_coe, coe_iSup_of_directed hdir, Set.mem_iUnion] at hx
  exact hx

omit [FiniteDimensional ℚ_[p] K] in
/-- The minimal polynomial of `θ` over `K_∞` has coefficients in `N_m` for `m` large. -/
theorem exists_coeff_mem_Nl (θ : PadicAlgCl p) :
    ∃ m₀, ∀ m ≥ m₀, ∀ n, (mp (K ⊔ cycFieldInf p) θ).coeff n ∈ Nl K m := by
  classical
  have h : ∀ n, ∃ m, (mp (K ⊔ cycFieldInf p) θ).coeff n ∈ Nl K m := fun n =>
    exists_mem_Nl K (coeff_mp_mem _ θ n)
  choose f hf using h
  set D := (mp (K ⊔ cycFieldInf p) θ).natDegree
  refine ⟨(Finset.range (D + 1)).sup f, fun m hm n => ?_⟩
  by_cases hn : n ≤ D
  · exact Nl_mono K ((Finset.le_sup (Finset.mem_range.mpr (by omega))).trans hm) (hf n)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact zero_mem _

omit [FiniteDimensional ℚ_[p] K] in
/-- The trace of `N_m(θ) / N_m` as a sum over embeddings, in terms of `nt`. -/
theorem sum_embeddings_eq (m : ℕ) (θ : PadicAlgCl p) (α : (Nl K m)⟮θ⟯) :
    ∑ σ : (Nl K m)⟮θ⟯ →ₐ[Nl K m] PadicAlgCl p, σ α =
      (dg (Nl K m) θ : PadicAlgCl p) * nt (Nl K m) α := by
  rw [show ((α : PadicAlgCl p)) = algebraMap _ (PadicAlgCl p) α from rfl, ← coe_trace_adjoin]
  exact (trace_eq_sum_embeddings (E := PadicAlgCl p) (x := α)).symm

/-- **Almost étaleness of `K_∞`** in the form of [BC, Lemma 14.1.3]: for every `θ` and all large
`m` there is `α ∈ N_m(θ)` with `‖α‖ ≤ 2` and `∑_σ σ(α) = 1`. -/
theorem exists_trace_one (θ : PadicAlgCl p) : ∃ m₀, ∀ m ≥ m₀,
    ∃ α : (Nl K m)⟮θ⟯, ‖(α : PadicAlgCl p)‖ ≤ 2 ∧
      ∑ σ : (Nl K m)⟮θ⟯ →ₐ[Nl K m] PadicAlgCl p, σ α = 1 := by
  set L : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p) := fun m => Nl K m ⊔ ℚ_[p]⟮θ⟯ with hLdef
  haveI : ∀ m, FiniteDimensional ℚ_[p] (L m) := fun m => by
    haveI : FiniteDimensional ℚ_[p] ℚ_[p]⟮θ⟯ :=
      adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral θ)
    infer_instance
  have hFL : ∀ m, cycField p (m + 1) ≤ L m := fun m =>
    (le_sup_right : cycField p (m + 1) ≤ Nl K m).trans le_sup_left
  have hL : ∀ m, L (m + 1) = L m ⊔ cycField p (m + 2) := by
    intro m
    simp only [hLdef, Nl]
    refine le_antisymm (sup_le (sup_le ?_ ?_) ?_) (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_)
    · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
    · exact le_sup_right
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_left.trans le_sup_left
    · exact (cycField_mono (by omega)).trans (le_sup_right.trans le_sup_left)
    · exact le_sup_right
    · exact le_sup_right.trans le_sup_left
  obtain ⟨M, hM⟩ := exists_trace_large L hFL hL (ρ := 1 / 2) (by norm_num)
  refine ⟨M, fun m hm => ?_⟩
  obtain ⟨u, huL, hu1, hut⟩ := hM m hm
  set N := Nl K m
  have hNL : N ≤ L m := le_sup_left
  have hE : ((N)⟮θ⟯).restrictScalars ℚ_[p] = L m :=
    le_antisymm
      (restrictScalars_adjoin_le N hNL (le_sup_right (a := N) (mem_adjoin_simple_self _ _)))
      (sup_le (le_restrictScalars_adjoin N θ)
        (adjoin_simple_le_iff.mpr (mem_restrictScalars_adjoin N θ)))
  have ht := hut.trans (norm_trace_le_norm_trace (le_sup_right : cycField p (m + 1) ≤ N) hNL u)
  set t := (rdeg N (L m) : PadicAlgCl p) * nt N u with htdef
  have ht0 : t ≠ 0 := by
    intro h; rw [h, norm_zero] at ht; norm_num at ht
  have htN : t ∈ N := mul_mem (IntermediateField.natCast_mem _ _) (nt_mem N u)
  have huE : u ∈ (N)⟮θ⟯ := by rw [← hE] at huL; exact huL
  refine ⟨⟨t⁻¹ * u, mul_mem ((N⟮θ⟯).algebraMap_mem ⟨t⁻¹, inv_mem htN⟩) huE⟩, ?_, ?_⟩
  · change ‖t⁻¹ * u‖ ≤ 2
    rw [norm_mul, norm_inv]
    have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    calc ‖t‖⁻¹ * ‖u‖ ≤ ‖t‖⁻¹ * 1 := mul_le_mul_of_nonneg_left hu1 (inv_nonneg.mpr htpos.le)
      _ ≤ 2 := by
        rw [mul_one, inv_le_comm₀ htpos (by norm_num)]
        linarith
  · rw [sum_embeddings_eq]
    change (dg N θ : PadicAlgCl p) * nt N (t⁻¹ * u) = 1
    rw [nt_mul_left N (inv_mem htN), show dg N θ = rdeg N (L m) from (rdeg_adjoin hE).symm,
      mul_left_comm, ← htdef, inv_mul_cancel₀ ht0]

omit [FiniteDimensional ℚ_[p] K] in
/-- Every `N_m`-embedding of `N_m(θ)` extends to an element of `Gal(ℚ̄_p/K_∞)`, provided the
minimal polynomial of `θ` over `K_∞` has coefficients in `N_m`. -/
theorem exists_extend {m : ℕ} {θ : PadicAlgCl p}
    (hcoef : ∀ n, (mp (K ⊔ cycFieldInf p) θ).coeff n ∈ Nl K m)
    (σ : (Nl K m)⟮θ⟯ →ₐ[Nl K m] PadicAlgCl p) :
    ∃ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, τ ∈ (K ⊔ cycFieldInf p).fixingSubgroup ∧
      ∀ x : (Nl K m)⟮θ⟯, τ x = σ x := by
  have hNN : (Nl K m) ≤ (K ⊔ cycFieldInf p) := Nl_le K m
  set g := AdjoinSimple.gen (Nl K m) θ
  -- `σ θ` is a root of the minimal polynomial of `θ` over `K_∞`
  have hl : mp (K ⊔ cycFieldInf p) θ ∈ lifts (algebraMap (Nl K m) (PadicAlgCl p)) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hcoef n⟩, rfl⟩
  obtain ⟨q₀, hq₀⟩ := hl
  rw [coe_mapRingHom] at hq₀
  have hq₀θ : aeval g q₀ = 0 := by
    apply (algebraMap ((Nl K m)⟮θ⟯) (PadicAlgCl p)).injective
    rw [map_zero, ← aeval_algebraMap_apply, AdjoinSimple.algebraMap_gen, aeval_def,
      eval₂_eq_eval_map, hq₀, eval_mp]
  have hσθ : (mp (K ⊔ cycFieldInf p) θ).eval (σ g) = 0 := by
    rw [← hq₀, eval_map_algebraMap, aeval_algHom_apply, hq₀θ, map_zero]
  have hroot : aeval (σ g) (minpoly ↥(K ⊔ cycFieldInf p) θ) = 0 := by
    rwa [mp, eval_map_algebraMap] at hσθ
  obtain ⟨τ', hτ'⟩ := minpoly.exists_algEquiv_of_root (K := ↥(K ⊔ cycFieldInf p))
    (L := PadicAlgCl p)
    (Algebra.IsAlgebraic.isAlgebraic θ) hroot
  refine ⟨(τ'.symm).restrictScalars ℚ_[p], ?_, fun x => ?_⟩
  · rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact τ'.symm.commutes ⟨x, hx⟩
  · -- both sides are `(Nl K m)`-algebra maps agreeing on `θ`
    set f : (Nl K m)⟮θ⟯ →ₐ[(Nl K m)] PadicAlgCl p :=
      { toRingHom := (τ'.symm.toRingEquiv.toRingHom).comp (algebraMap ((Nl K m)⟮θ⟯) (PadicAlgCl p))
        commutes' := fun r => by
          change τ'.symm ((r : PadicAlgCl p)) = (r : PadicAlgCl p)
          exact τ'.symm.commutes ⟨r, hNN r.2⟩ }
    have hfg : f = σ := by
      refine adjoin_algHom_ext _ fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy
      change τ'.symm y = σ ⟨y, _⟩
      simp only [hy]
      change τ'.symm θ = σ g
      have h1 := τ'.symm_apply_apply (σ g)
      rw [hτ'] at h1
      exact h1
    exact congrArg (fun φ => φ x) hfg

end PadicHodge

/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.TateSen.H1GammaZero

/-!
# Coordinates on the completion of `K(μ_{p^∞})`

Let `K / ℚ_p` be finite, `F_∞ = ℚ_p(μ_{p^∞})`, `K_∞ = K F_∞` and `H = Gal(ℚ̄_p/F_∞)`. Choose a
primitive element `α` of `K` and let `d` be the degree of `α` over `F_∞`. Every element of `K_∞`
is `∑_{i<d} c_i α^i` with `c_i ∈ F_∞`. If `α_1, …, α_d` are the conjugates of `α` over `F_∞`
and `τ_k ∈ H` with `τ_k α = α_k`, then for `z = ∑ Y_i α^i` with `Y_i` fixed by `H` one has
`τ_k z = ∑ Y_i α_k^i`, so the inverse of the Vandermonde matrix `V = (α_k^i)` recovers the
coordinates: `Y = V⁻¹ (τ_k z)_k` (`coord_sum`). The coordinate maps `coord D i` are continuous
on all of `ℂ_p`, which gives:

* `exists_coords`: every `z ∈ ℂ_p` fixed by `Gal(ℚ̄_p/K_∞)` (i.e. `z ∈ \hat K_∞`, Ax–Sen–Tate)
  is `∑ Y_i α^i` with `Y_i ∈ \hat F_∞`, `Y_i = coord D i z`.

This linear disjointness device (instead of normalised traces for `K_∞`, which need Tate's
ramification estimates, [BC, Lemma 14.1.4]) reduces the analysis on `\hat K_∞` to that on
`\hat F_∞` (`Cyclotomic/Solve.lean`, `Cyclotomic/Decomp.lean`):

* `exists_twist_eq_K`: `λ γ - 1` is surjective on `\hat K_∞` for `γ ∈ G_K` a Tate generator;
* `exists_decomp_K`: `c = γ m - m + ∑ r_i α^i` with `r_i ∈ ℚ_p(μ_{p^n})`;
* `eq_zero_of_autCp_sub_eq_K`: `γ m - m = ∑ r_i α^i` with `r_i ∈ ℚ_p(μ_{p^n})` forces `r = 0`.
-/

noncomputable section

open IntermediateField Polynomial Topology

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-- Ax–Sen–Tate in the form used here: elements of `ℂ_p` fixed by `Gal(ℚ̄_p/L)` lie in the
closure of `L`. -/
theorem mem_closure_of_fixed (L : IntermediateField ℚ_[p] (PadicAlgCl p)) {x : ℂ_[p]}
    (hx : ∀ h ∈ L.fixingSubgroup, autCp h x = x) :
    x ∈ closure (cpSubmodule L : Set ℂ_[p]) := by
  refine (galCp_eq_self_iff_mem_closure x).mp fun σ => ?_
  have hσ : σ.restrictScalars ℚ_[p] ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact σ.commutes ⟨y, hy⟩
  exact hx _ hσ

theorem autCp_eq_self_of_mem_closure' (L : IntermediateField ℚ_[p] (PadicAlgCl p)) {x : ℂ_[p]}
    (hx : x ∈ closure (cpSubmodule L : Set ℂ_[p]))
    {h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hh : h ∈ L.fixingSubgroup) :
    autCp h x = x := by
  have e := galCp_eq_self_of_mem_closure hx ((fixingSubgroupEquiv L) ⟨h, hh⟩)
  have e2 : ((fixingSubgroupEquiv L) ⟨h, hh⟩).restrictScalars ℚ_[p] = h := by
    ext; rfl
  rwa [galCp_eq_autCp, e2] at e

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- Coordinate data for `K_∞ = K F_∞` over `F_∞`: a generator `α ∈ K` with
`K_∞ = ⊕_{i<d} F_∞ α^i`, the conjugates `β_k` of `α` over `F_∞` and `τ_k ∈ Gal(ℚ̄_p/F_∞)` with
`τ_k α = β_k`. -/
structure CoordData where
  d : ℕ
  α : PadicAlgCl p
  hα : α ∈ K
  spans : ∀ x ∈ K ⊔ cycFieldInf p, ∃ c : Fin d → PadicAlgCl p,
    (∀ i, c i ∈ cycFieldInf p) ∧ x = ∑ i, c i * α ^ (i : ℕ)
  β : Fin d → PadicAlgCl p
  β_inj : Function.Injective β
  τ : Fin d → (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
  τ_mem : ∀ k, τ k ∈ (cycFieldInf p).fixingSubgroup
  τ_α : ∀ k, τ k α = β k

variable {K}

theorem le_adjoin_of_primitive {α0 : K} (hα0 : ℚ_[p]⟮α0⟯ = ⊤)
    (F : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    K ≤ (F⟮(α0 : PadicAlgCl p)⟯).restrictScalars ℚ_[p] := by
  have h1 : K = ℚ_[p]⟮(α0 : PadicAlgCl p)⟯ := by
    have := adjoin_map ℚ_[p] {α0} K.val
    rw [hα0, Set.image_singleton] at this
    have h2 : (⊤ : IntermediateField ℚ_[p] K).map K.val = K := by
      rw [← AlgHom.fieldRange_eq_map, fieldRange_val]
    exact h2.symm.trans this
  have h3 : ℚ_[p]⟮(α0 : PadicAlgCl p)⟯ ≤
      (F⟮(α0 : PadicAlgCl p)⟯).restrictScalars ℚ_[p] := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]; exact mem_adjoin_simple_self F _
  exact h1.le.trans h3

theorem exists_coordData [FiniteDimensional ℚ_[p] K] : Nonempty (CoordData K) := by
  obtain ⟨α0, hα0⟩ := Field.exists_primitive_element ℚ_[p] K
  set α : PadicAlgCl p := α0.1
  set F := cycFieldInf p
  set P := minpoly F α with hP
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hPm : P.Monic := minpoly.monic hint
  have hP1 : P ≠ 1 := minpoly.ne_one F α
  -- spanning
  have hspan : ∀ x ∈ K ⊔ F, ∃ c : Fin P.natDegree → PadicAlgCl p,
      (∀ i, c i ∈ F) ∧ x = ∑ i, c i * α ^ (i : ℕ) := by
    intro x hx
    have hle : K ⊔ F ≤ (F⟮α⟯).restrictScalars ℚ_[p] := by
      refine sup_le (le_adjoin_of_primitive hα0 F) fun y hy => ?_
      exact (F⟮α⟯).algebraMap_mem ⟨y, hy⟩
    have hx' : x ∈ (F⟮α⟯).toSubalgebra := hle hx
    rw [adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hx'
    obtain ⟨g, rfl⟩ := hx'
    have e1 : aeval α g = aeval α (g %ₘ P) :=
      (aeval_modByMonic_eq_self_of_root (minpoly.aeval F α)).symm
    have hdeg : (g %ₘ P).natDegree < P.natDegree := natDegree_modByMonic_lt g hPm hP1
    refine ⟨fun i => ((g %ₘ P).coeff i : PadicAlgCl p), fun i => ((g %ₘ P).coeff i).2, ?_⟩
    change aeval α g = _
    rw [e1, aeval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def]
    rfl
  -- the conjugates
  have hsep : P.Separable := Algebra.IsSeparable.isSeparable F α
  have hsplit : Splits (P.map (algebraMap F (PadicAlgCl p))) := IsAlgClosed.splits _
  have hcard := card_rootSet_eq_natDegree hsep hsplit
  let e : Fin P.natDegree ≃ P.rootSet (PadicAlgCl p) :=
    (Fintype.equivFinOfCardEq hcard).symm
  have hroot : ∀ k, aeval ((e k : PadicAlgCl p)) P = 0 := fun k =>
    (mem_rootSet.mp (e k).2).2
  choose σ hσ using fun k => minpoly.exists_algEquiv_of_root'
    (hint.isAlgebraic) (hroot k)
  refine ⟨⟨P.natDegree, α, α0.2, hspan, fun k => (e k : PadicAlgCl p),
    fun k l h => e.injective (Subtype.ext h), fun k => (σ k).restrictScalars ℚ_[p],
    fun k => ?_, fun k => hσ k⟩⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  exact (σ k).commutes ⟨y, hy⟩

variable (D : CoordData K)

/-- The Vandermonde matrix `(β_k^i)` of the conjugates of `α`. -/
def vand : Matrix (Fin D.d) (Fin D.d) ℂ_[p] :=
  Matrix.vandermonde fun k => ((D.β k : PadicAlgCl p) : ℂ_[p])

theorem isUnit_det_vand : IsUnit (vand D).det := by
  refine isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr fun k l h => ?_)
  exact D.β_inj (UniformSpace.Completion.coe_injective _ h)

/-- The `i`-th coordinate `∑_k (V⁻¹)_{ik} τ_k(z)`. -/
def coord (i : Fin D.d) (z : ℂ_[p]) : ℂ_[p] :=
  ∑ k, (vand D)⁻¹ i k * autCp (D.τ k) z

theorem continuous_coord (i : Fin D.d) : Continuous (coord D i) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_autCp _)

theorem autCp_α_of_mem {g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hg : g ∈ K.fixingSubgroup) :
    autCp g (D.α : ℂ_[p]) = D.α := by
  rw [autCp_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _ D.hα]

theorem coord_sum (Y : Fin D.d → ℂ_[p])
    (hY : ∀ i, Y i ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p])) (i : Fin D.d) :
    coord D i (∑ j, Y j * (D.α : ℂ_[p]) ^ (j : ℕ)) = Y i := by
  have h1 : ∀ k, autCp (D.τ k) (∑ j, Y j * (D.α : ℂ_[p]) ^ (j : ℕ)) =
      (vand D).mulVec Y k := by
    intro k
    rw [map_sum, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, autCp_eq_self_of_mem_closure (hY j) (D.τ_mem k), autCp_coe, D.τ_α k,
      vand, Matrix.vandermonde_apply, mul_comm]
  unfold coord
  simp only [h1]
  have := congrFun (congrArg (fun M => M.mulVec Y) (Matrix.nonsing_inv_mul _ (isUnit_det_vand D)))
    i
  simp only [Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at this
  rw [← this, Matrix.mulVec, dotProduct]

theorem coe_sum_cp (c : Fin D.d → PadicAlgCl p) :
    ((∑ i, c i * D.α ^ (i : ℕ) : PadicAlgCl p) : ℂ_[p]) =
      ∑ i, ((c i : PadicAlgCl p) : ℂ_[p]) * (D.α : ℂ_[p]) ^ (i : ℕ) := by
  simp only [PadicComplex.coe_eq, map_sum, map_mul, map_pow]

/-- **Coordinates on `\hat K_∞`.** -/
theorem exists_coords {z : ℂ_[p]}
    (hz : ∀ h ∈ (K ⊔ cycFieldInf p).fixingSubgroup, autCp h z = z) :
    (∀ i, coord D i z ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p])) ∧
      z = ∑ i, coord D i z * (D.α : ℂ_[p]) ^ (i : ℕ) := by
  have hcl := mem_closure_of_fixed _ hz
  obtain ⟨x, hxmem, hxlim⟩ := mem_closure_iff_seq_limit.mp hcl
  have hx : ∀ n, ∃ a ∈ K ⊔ cycFieldInf p, ((a : PadicAlgCl p) : ℂ_[p]) = x n :=
    fun n => mem_cpSubmodule.mp (hxmem n)
  choose a ha hax using hx
  choose c hc hca using fun n => D.spans (a n) (ha n)
  have hcoord : ∀ n i, coord D i (x n) = ((c n i : PadicAlgCl p) : ℂ_[p]) := by
    intro n i
    rw [← hax n, hca n, coe_sum_cp]
    exact coord_sum D _ (fun j => subset_closure (coe_mem_cpSubmodule (hc n j))) i
  have hlim : ∀ i, Filter.Tendsto (fun n => ((c n i : PadicAlgCl p) : ℂ_[p])) Filter.atTop
      (𝓝 (coord D i z)) := fun i => by
    simp only [← hcoord]
    exact ((continuous_coord D i).tendsto z).comp hxlim
  refine ⟨fun i => mem_closure_of_tendsto (hlim i) (Filter.Eventually.of_forall fun n =>
    coe_mem_cpSubmodule (hc n i)), ?_⟩
  have h2 : Filter.Tendsto (fun n => ∑ i, ((c n i : PadicAlgCl p) : ℂ_[p]) *
      (D.α : ℂ_[p]) ^ (i : ℕ)) Filter.atTop
      (𝓝 (∑ i, coord D i z * (D.α : ℂ_[p]) ^ (i : ℕ))) :=
    tendsto_finsetSum _ fun i _ => (hlim i).mul_const _
  have e : ∀ n, ∑ i, ((c n i : PadicAlgCl p) : ℂ_[p]) * (D.α : ℂ_[p]) ^ (i : ℕ) = x n := by
    intro n; rw [← coe_sum_cp, ← hca n, hax n]
  simp only [e] at h2
  exact tendsto_nhds_unique hxlim h2

theorem mem_H_of_mem_HK {h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (hh : h ∈ (K ⊔ cycFieldInf p).fixingSubgroup) : h ∈ (cycFieldInf p).fixingSubgroup := by
  rw [fixingSubgroup_sup] at hh; exact hh.2

theorem mem_GK_of_mem_HK {h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (hh : h ∈ (K ⊔ cycFieldInf p).fixingSubgroup) : h ∈ K.fixingSubgroup := by
  rw [fixingSubgroup_sup] at hh; exact hh.1

/-- `∑ Y_i α^i` with `Y_i ∈ \hat F_∞` is fixed by `Gal(ℚ̄_p/K_∞)`. -/
theorem sum_fixed (Y : Fin D.d → ℂ_[p])
    (hY : ∀ i, Y i ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p]))
    {h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hh : h ∈ (K ⊔ cycFieldInf p).fixingSubgroup) :
    autCp h (∑ i, Y i * (D.α : ℂ_[p]) ^ (i : ℕ)) = ∑ i, Y i * (D.α : ℂ_[p]) ^ (i : ℕ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, autCp_eq_self_of_mem_closure (hY i) (mem_H_of_mem_HK hh),
    autCp_α_of_mem D (mem_GK_of_mem_HK hh)]

theorem autCp_mul_apply (a b : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (Y : ℂ_[p]) :
    autCp (a * b) Y = autCp a (autCp b Y) := by
  rw [map_mul]; rfl

theorem autCp_mem_closure_F (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {Y : ℂ_[p]}
    (hY : Y ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p])) :
    autCp g Y ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p]) := by
  refine mem_closure_of_H_fixed fun h hh => ?_
  have hc : g⁻¹ * h * g ∈ (cycFieldInf p).fixingSubgroup :=
    Subgroup.Normal.conj_mem' inferInstance h hh g
  have e : h * g = g * (g⁻¹ * h * g) := by group
  rw [← autCp_mul_apply, e, autCp_mul_apply, autCp_eq_self_of_mem_closure hY hc]

section Solve

variable {γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hγK : γ ∈ K.fixingSubgroup) {n : ℕ}
  (hγ : IsTateGen γ n) (hn : 1 ≤ n)
include D hγK hγ hn

omit hγ hn in
theorem autCp_sum (Y : Fin D.d → ℂ_[p]) :
    autCp γ (∑ i, Y i * (D.α : ℂ_[p]) ^ (i : ℕ)) =
      ∑ i, autCp γ (Y i) * (D.α : ℂ_[p]) ^ (i : ℕ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, autCp_α_of_mem D hγK]

/-- `λ γ - 1` is surjective on `\hat K_∞`. -/
theorem exists_twist_eq_K {lam : ℚ_[p]} (hlam1 : lam ≠ 1) (hlam : (p : ℝ) ^ 4 * ‖lam - 1‖ < 1)
    {z : ℂ_[p]} (hz : ∀ h ∈ (K ⊔ cycFieldInf p).fixingSubgroup, autCp h z = z) :
    ∃ m : ℂ_[p], (∀ h ∈ (K ⊔ cycFieldInf p).fixingSubgroup, autCp h m = m) ∧
      lam • autCp γ m - m = z := by
  obtain ⟨hY, hzY⟩ := exists_coords D hz
  choose M hM hMeq using fun i => exists_twist_eq hγ hn hlam1 hlam (hY i)
  refine ⟨∑ i, M i * (D.α : ℂ_[p]) ^ (i : ℕ), fun h hh => sum_fixed D M hM hh, ?_⟩
  rw [autCp_sum D hγK, Finset.smul_sum, ← Finset.sum_sub_distrib, hzY]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hMeq i, sub_mul, smul_mul_assoc]

/-- Decomposition on `\hat K_∞`: `c = γ m - m + ∑ r_i α^i` with `r_i ∈ ℚ_p(μ_{p^n})`. -/
theorem exists_decomp_K {c : ℂ_[p]}
    (hc : ∀ h ∈ (K ⊔ cycFieldInf p).fixingSubgroup, autCp h c = c) :
    ∃ m : ℂ_[p], (∀ h ∈ (K ⊔ cycFieldInf p).fixingSubgroup, autCp h m = m) ∧
      ∃ r : Fin D.d → PadicAlgCl p, (∀ i, r i ∈ cycField p n) ∧
        autCp γ m - m + ∑ i, ((r i : PadicAlgCl p) : ℂ_[p]) * (D.α : ℂ_[p]) ^ (i : ℕ) = c := by
  obtain ⟨hY, hcY⟩ := exists_coords D hc
  choose M hM r hr hMr using fun i => exists_decomp hγ hn (hY i)
  refine ⟨∑ i, M i * (D.α : ℂ_[p]) ^ (i : ℕ), fun h hh => sum_fixed D M hM hh, r, hr, ?_⟩
  rw [autCp_sum D hγK, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  conv_rhs => rw [hcY]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hMr i]; ring

/-- If `γ m - m = ∑ r_i α^i` with `m ∈ \hat K_∞` and `r_i ∈ ℚ_p(μ_{p^n})`, then all `r_i = 0`. -/
theorem eq_zero_of_autCp_sub_eq_K {m : ℂ_[p]}
    (hm : ∀ h ∈ (K ⊔ cycFieldInf p).fixingSubgroup, autCp h m = m)
    {r : Fin D.d → PadicAlgCl p} (hr : ∀ i, r i ∈ cycField p n)
    (h : autCp γ m - m = ∑ i, ((r i : PadicAlgCl p) : ℂ_[p]) * (D.α : ℂ_[p]) ^ (i : ℕ)) :
    ∀ i, r i = 0 := by
  obtain ⟨hY, hmY⟩ := exists_coords D hm
  set Y := fun i => coord D i m
  have e : autCp γ m - m = ∑ i, (autCp γ (Y i) - Y i) * (D.α : ℂ_[p]) ^ (i : ℕ) := by
    conv_lhs => rw [hmY]
    rw [autCp_sum D hγK, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hY' : ∀ i, autCp γ (Y i) - Y i ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p]) :=
    fun i => by
      have h1 := autCp_mem_closure_F γ (hY i)
      have h2 := hY i
      rw [← Submodule.topologicalClosure_coe, SetLike.mem_coe] at h1 h2 ⊢
      exact sub_mem h1 h2
  have hr' : ∀ i, ((r i : PadicAlgCl p) : ℂ_[p]) ∈
      closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p]) := fun i =>
    subset_closure (coe_mem_cpSubmodule (mem_cycFieldInf.mpr ⟨n, hr i⟩))
  intro i
  have h1 := coord_sum D _ hY' i
  have h2 := coord_sum D _ hr' i
  rw [← e, h] at h1
  rw [h1] at h2
  exact eq_zero_of_autCp_sub_eq hγ hn (hY i) (hr i) h2

end Solve

end PadicHodge

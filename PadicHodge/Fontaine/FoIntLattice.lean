/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Fontaine.FoIntDecomp

/-!
# (FoInt) (c): the cokernel bound (lattice lemma)

Let `M = {f ∈ Hom_{ℤ_p}(T_p F, ℂ_p) | |f(x)| ≤ 1 ∀ x} = Hom_{ℤ_p}(T_p F, O_{ℂ_p})` and let `N` be
such that `p^N ρ(ω_c)` is integral for `c ∈ O_{ℂ_p}^d` (`exists_pow_mul_rhoLin_le`). Then there
is `c` with `p^c M ⊆ p^N ρ(O_{ℂ_p}^d) + (M ∩ V₁)` (`PDivFGL.exists_lattice`,
`PDivFGL.exists_lattice'`).

Proof: project to `V₀` along `V₁`; the coordinates of `f ∈ M` in the basis `ρ(ω_l)` of `V₀` are
`ℂ_p`-linear in `f`, and `f = ∑_j f(b_j) δ_j` for a `ℤ_p`-basis `b` of `T_p F` with `|f(b_j)| ≤ 1`,
so they are bounded independently of `f`.
-/

noncomputable section

open Module

namespace PadicHodge

namespace PDivFGL

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] L] {d : ℕ} (P : PDivFGL (OL L) d p)
  {ε : ℕ → PadicAlgCl p} (hε : ∀ n, IsPrimitiveRoot (ε (n + 1)) (p ^ (n + 1)))
  (hεp : ∀ n, ε (n + 2) ^ p = ε (n + 1))

/-- The basis `ρ(ω_l)` of `V₀`. -/
def basisV0 : Basis (Fin d) ℂ_[p] (P.V0 hε hεp) := Basis.span (P.linearIndependent_rhoZp hε hεp)

theorem basisV0_apply (l : Fin d) : (P.basisV0 hε hεp l : P.WT) = P.rhoZp hε hεp l :=
  congrArg Subtype.val (Basis.span_apply _ _)

/-- The coordinates `κ_l : W → ℂ_p` of the projection to `V₀` along `V₁`. -/
def kappa (l : Fin d) : P.WT →ₗ[ℂ_[p]] ℂ_[p] :=
  (P.basisV0 hε hεp).coord l ∘ₗ (P.V0 hε hεp).projectionOnto P.V1 (P.isCompl_V0_V1 hε hεp)

theorem sub_sum_kappa_mem (f : P.WT) :
    f - ∑ l, P.kappa hε hεp l f • P.rhoZp hε hεp l ∈ P.V1 := by
  have h1 : (((P.V0 hε hεp).projectionOnto P.V1 (P.isCompl_V0_V1 hε hεp) f : P.V0 hε hεp) :
      P.WT) = ∑ l, P.kappa hε hεp l f • P.rhoZp hε hεp l := by
    conv_lhs => rw [← (P.basisV0 hε hεp).sum_repr
      ((P.V0 hε hεp).projectionOnto P.V1 (P.isCompl_V0_V1 hε hεp) f)]
    simp only [Submodule.coe_sum, Submodule.coe_smul, basisV0_apply, kappa,
      LinearMap.comp_apply, Basis.coord_apply]
  rw [← h1, Submodule.coe_projectionOnto_apply]
  exact Submodule.sub_projection_mem _ f

/-- `δ_j : x ↦ b_j^*(x)`, for the `ℤ_p`-basis `b` of `T_p F`. -/
def delta (j : Fin (finrank ℤ_[p] (Kummer.Tp (P.F.Pt p) p))) : P.WT :=
  Algebra.linearMap ℤ_[p] ℂ_[p] ∘ₗ (Module.finBasis ℤ_[p] (Kummer.Tp (P.F.Pt p) p)).coord j

theorem eq_sum_delta (f : P.WT) :
    f = ∑ j, f (Module.finBasis ℤ_[p] (Kummer.Tp (P.F.Pt p) p) j) • P.delta j := by
  refine (Module.finBasis ℤ_[p] (Kummer.Tp (P.F.Pt p) p)).ext fun i => ?_
  simp [delta, Finsupp.single_apply]

include hεp in
/-- **(FoInt)(c), the lattice lemma**: given `N` with `p^N ρ(ω_c)` integral for
`c ∈ O_{ℂ_p}^d`, there is `c` such that for every `f ∈ M = Hom_{ℤ_p}(T_p F, O_{ℂ_p})` there is
`a ∈ O_{ℂ_p}^d` with `p^c f - p^N ∑_l a_l ρ(ω_l) ∈ V₁`; this difference lies in `M`. -/
theorem exists_lattice (N : ℕ)
    (hN : ∀ c : Fin d → ℂ_[p], (∀ l, ‖c l‖ ≤ 1) → ∀ x : Kummer.Tp (P.F.Pt p) p,
      ‖(p : ℂ_[p]) ^ N * P.rhoLin (hε := hε) c x‖ ≤ 1) :
    ∃ c : ℕ, ∀ f : P.WT, (∀ x, ‖f x‖ ≤ 1) → ∃ a : Fin d → ℂ_[p], (∀ l, ‖a l‖ ≤ 1) ∧
      (p : ℂ_[p]) ^ c • f - (p : ℂ_[p]) ^ N • ∑ l, a l • P.rhoZp hε hεp l ∈ P.V1 ∧
      ∀ x, ‖((p : ℂ_[p]) ^ c • f - (p : ℂ_[p]) ^ N • ∑ l, a l • P.rhoZp hε hεp l) x‖ ≤ 1 := by
  set K : ℝ := ∑ l, ∑ j, ‖P.kappa hε hεp l (P.delta j)‖ + 1 with hKdef
  have hK : 0 < K := by positivity
  have hp1 := norm_p_cp_lt_one (p := p)
  obtain ⟨c', hc'⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hK) hp1
  refine ⟨N + c', fun f hf => ?_⟩
  set a : Fin d → ℂ_[p] := fun l => (p : ℂ_[p]) ^ c' * P.kappa hε hεp l f with hadef
  have ha : ∀ l, ‖a l‖ ≤ 1 := by
    intro l
    have hk : ‖P.kappa hε hεp l f‖ ≤ K := by
      conv_lhs => rw [P.eq_sum_delta f]
      rw [map_sum]
      calc ‖∑ j, P.kappa hε hεp l
              (f (Module.finBasis ℤ_[p] (Kummer.Tp (P.F.Pt p) p) j) • P.delta j)‖
          ≤ ∑ j, ‖P.kappa hε hεp l
              (f (Module.finBasis ℤ_[p] (Kummer.Tp (P.F.Pt p) p) j) • P.delta j)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ j, ‖P.kappa hε hεp l (P.delta j)‖ := Finset.sum_le_sum fun j _ => by
            rw [map_smul, smul_eq_mul, norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _) (hf _)
        _ ≤ ∑ l, ∑ j, ‖P.kappa hε hεp l (P.delta j)‖ :=
            Finset.single_le_sum (f := fun l => ∑ j, ‖P.kappa hε hεp l (P.delta j)‖)
              (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ l)
        _ ≤ K := by linarith
    rw [hadef, norm_mul, norm_pow]
    calc ‖(p : ℂ_[p])‖ ^ c' * ‖P.kappa hε hεp l f‖ ≤ K⁻¹ * K :=
          mul_le_mul hc'.le hk (norm_nonneg _) (inv_pos.mpr hK).le
      _ = 1 := inv_mul_cancel₀ hK.ne'
  refine ⟨a, ha, ?_, fun x => ?_⟩
  · have : (p : ℂ_[p]) ^ (N + c') • f - (p : ℂ_[p]) ^ N • ∑ l, a l • P.rhoZp hε hεp l =
        (p : ℂ_[p]) ^ (N + c') • (f - ∑ l, P.kappa hε hεp l f • P.rhoZp hε hεp l) := by
      rw [smul_sub, Finset.smul_sum, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, smul_smul, hadef, pow_add, mul_assoc]
    rw [this]
    exact Submodule.smul_mem _ _ (P.sub_sum_kappa_mem hε hεp f)
  · have h2 : (∑ l, a l • P.rhoZp hε hεp l) x = P.rhoLin (hε := hε) a x := by
      simp [rhoLin, LinearMap.sum_apply, smul_eq_mul]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
      smul_eq_mul, h2]
    have h1 : ‖(p : ℂ_[p]) ^ (N + c') * f x‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hp1.le) (norm_nonneg _) (hf x)
    have h3 := hN a ha x
    have hu : ‖(p : ℂ_[p]) ^ (N + c') * f x - (p : ℂ_[p]) ^ N * P.rhoLin (hε := hε) a x‖ ≤
        max ‖(p : ℂ_[p]) ^ (N + c') * f x‖ ‖(p : ℂ_[p]) ^ N * P.rhoLin (hε := hε) a x‖ := by
      simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max
        ((p : ℂ_[p]) ^ (N + c') * f x) (-((p : ℂ_[p]) ^ N * P.rhoLin (hε := hε) a x))
    exact hu.trans (max_le h1 h3)

include hεp in
/-- **(FoInt)(c)** with `N` from `exists_pow_mul_rhoLin_le` ([Fo, Thm 1′]). -/
theorem exists_lattice' :
    ∃ N c : ℕ, (∀ a : Fin d → ℂ_[p], (∀ l, ‖a l‖ ≤ 1) → ∀ x : Kummer.Tp (P.F.Pt p) p,
      ‖(p : ℂ_[p]) ^ N * P.rhoLin (hε := hε) a x‖ ≤ 1) ∧
      ∀ f : P.WT, (∀ x, ‖f x‖ ≤ 1) → ∃ a : Fin d → ℂ_[p], (∀ l, ‖a l‖ ≤ 1) ∧
        (p : ℂ_[p]) ^ c • f - (p : ℂ_[p]) ^ N • ∑ l, a l • P.rhoZp hε hεp l ∈ P.V1 ∧
        ∀ x, ‖((p : ℂ_[p]) ^ c • f - (p : ℂ_[p]) ^ N • ∑ l, a l • P.rhoZp hε hεp l) x‖ ≤ 1 := by
  obtain ⟨N, hN⟩ := P.exists_pow_mul_rhoLin_le (hε := hε) hεp
  obtain ⟨c, hc⟩ := P.exists_lattice hε hεp N hN
  exact ⟨N, c, hN, hc⟩

end PDivFGL

end PadicHodge

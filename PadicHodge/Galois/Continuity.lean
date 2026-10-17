/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Galois.Basic
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Continuity of the Galois action on `ℂ_p`

For each `x ∈ ℂ_[p]` the orbit map `σ ↦ σ x` on `G_L` (Krull topology) is continuous
(`continuous_galCp_apply`): it is locally constant on `ℚ̄_p` (open stabilisers), and the general
case follows by uniform approximation, since every `σ` is an isometry.
-/

noncomputable section

open Topology Pointwise

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

instance : Algebra.IsIntegral L (PadicAlgCl p) :=
  Algebra.IsIntegral.tower_top ℚ_[p]

theorem continuous_gal_apply (x : PadicAlgCl p) :
    Continuous fun σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p => σ x := by
  have hopen := stabilizer_isOpen_of_isIntegral (K := L) x
  rw [continuous_def]
  intro s _
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨σ • ((MulAction.stabilizer (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) x : Subgroup _) :
    Set (PadicAlgCl p ≃ₐ[L] PadicAlgCl p)), ?_,
    hopen.leftCoset σ, ⟨1, one_mem _, mul_one σ⟩⟩
  rintro _ ⟨τ, hτ, rfl⟩
  simp only [Set.mem_preimage, smul_eq_mul, AlgEquiv.mul_apply]
  have : τ x = x := hτ
  rw [this]
  exact hσ

theorem continuous_galCp_apply (x : ℂ_[p]) :
    Continuous fun σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p => galCp L σ x := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨y, hy⟩ : ∃ y : PadicAlgCl p, dist x y < ε :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt x hε
  refine ⟨fun σ => ((σ y : PadicAlgCl p) : ℂ_[p]),
    UniformSpace.Completion.continuous_coe _ |>.comp (continuous_gal_apply y), fun σ => ?_⟩
  apply hεu
  change dist (galCp L σ x) ((σ y : PadicAlgCl p) : ℂ_[p]) < ε
  rw [← galCp_coe, dist_eq_norm, ← map_sub, norm_galCp, ← dist_eq_norm]
  exact hy

end PadicHodge

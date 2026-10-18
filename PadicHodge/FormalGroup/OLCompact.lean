/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.OK
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# `O_L` is compact

For a finite extension `L/ℚ_p` inside `ℚ̄_p`, the unit ball `{z ∈ L | |z| ≤ 1}` of the image of `L`
in `ℂ_p` is compact (`OL.isCompact_unitBall`: `L` is a finite-dimensional, hence proper, normed
`ℚ_p`-space), so `O_L = OLSub L` with the subspace topology of `O_{ℂ_p}` is a compact space
(`OL.compactSpace_OLSub`). This is the compact companion topology of `OL L` (which itself
carries the discrete uniformity) needed for the compactness argument in the essential
surjectivity of Serre–Tate over `O_L` (the analogue of `ℤ_p^{ℕ^σ}` in
`GroupScheme/SerreTateCompact.lean`).
-/

noncomputable section

namespace PadicHodge

namespace OL

variable {p : ℕ} [hp : Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] L]

/-- **The unit ball of `L ⊆ ℂ_p` is compact.** -/
theorem isCompact_unitBall : IsCompact {z : ℂ_[p] | z ∈ cpSubmodule L ∧ ‖z‖ ≤ 1} := by
  haveI : ProperSpace (cpSubmodule L) := FiniteDimensional.proper ℚ_[p] (cpSubmodule L)
  have hc := (isCompact_closedBall (0 : cpSubmodule L) 1).image continuous_subtype_val
  convert hc using 1
  ext z
  constructor
  · rintro ⟨hz, h1⟩
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact h1
  · rintro ⟨w, hw, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    exact ⟨w.2, hw⟩

/-- **`O_L` is compact** for the subspace topology of `O_{ℂ_p} ⊆ ℂ_p`. -/
instance compactSpace_OLSub : CompactSpace (OLSub L) := by
  rw [← isCompact_univ_iff]
  have hemb : Topology.IsEmbedding (fun x : OLSub L => ((x : OC p) : ℂ_[p])) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  rw [hemb.isCompact_iff, Set.image_univ]
  convert isCompact_unitBall L using 1
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.2, norm_OC_le _⟩
  · rintro ⟨hz, h1⟩
    exact ⟨⟨⟨z, mem_OC.mpr h1⟩, hz⟩, rfl⟩

end OL

end PadicHodge

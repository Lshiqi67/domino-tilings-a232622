module

public import Domino.OddHeight.Geometry

/-! B02：所有终端都允许左右反射补全，限制与补全互逆。 -/

@[expose] public section

namespace Domino.General

variable {m : ℕ}

def unrestrictedHalfPartialEquiv (n : ℕ) : HalfPartial (m := m) false n ≃ (Σ S : State m, PartialTiling m n S) where
  toFun P := ⟨P.1.val, P.2⟩
  invFun P := ⟨⟨P.1, rfl⟩, P.2⟩
  left_inv P := by rcases P with ⟨⟨S, hS⟩, P⟩; rfl
  right_inv P := by rcases P with ⟨S, P⟩; rfl

noncomputable def reflectionFixedEquivPartial (n : ℕ) :
    {T : Tiling m (2 * n) // vertical • T = T} ≃ (Σ S : State m, PartialTiling m n S) :=
  (axialFixedEquivPartial false n).trans (unrestrictedHalfPartialEquiv n)

noncomputable def completeReflection {n : ℕ} (P : Σ S : State m, PartialTiling m n S) :=
  (reflectionFixedEquivPartial n).symm P

noncomputable def restrictReflection {n : ℕ} (T : {T : Tiling m (2 * n) // vertical • T = T}) :=
  reflectionFixedEquivPartial n T

theorem restrict_complete_reflection {n : ℕ} (P : Σ S : State m, PartialTiling m n S) :
    restrictReflection (completeReflection P) = P :=
  (reflectionFixedEquivPartial n).apply_symm_apply P

theorem complete_restrict_reflection {n : ℕ} (T : {T : Tiling m (2 * n) // vertical • T = T}) :
    completeReflection (restrictReflection T) = T :=
  (reflectionFixedEquivPartial n).symm_apply_apply T

theorem reflection_fixed_count (n : ℕ) : fixedCount m n vertical = ∑ S : State m, profileCount n S := by
  classical
  exact (Fintype.card_congr (reflectionFixedEquivPartial n)).trans Fintype.card_sigma

end Domino.General

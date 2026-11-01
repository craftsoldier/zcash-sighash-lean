import Lake
open Lake DSL

/-- Mathlib `v4.35.0`, at its commit. -/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "56a005855ea17e0b0958f73ec801ae140b0a1679"

package «zcashSighash» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target] lean_lib «ZcashSighash» {}

/-- BLAKE2b on RFC 7693's test vector. -/
@[default_target] lean_lib «Tests» where
  roots := #[`ZcashSighash.Tests.Blake2b]

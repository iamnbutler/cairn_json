import Lake
open Lake DSL

package cairn_json where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.cairn.claims.scope, "cairn_json"⟩]

require "iamnbutler" / "cairn" @ "^0.1.2"

/-- The code apps link. -/
@[default_target]
lean_lib CairnJson where
  roots := #[`CairnJson]
  defaultFacets := #[LeanLib.staticFacet]

/-- Proofs and build-time examples. Never linked. -/
@[default_target]
lean_lib CairnJsonProofs where
  roots := #[`CairnJsonProofs]

/-- The trusted fuzz check's Lean side (docs/trusted.md): reads documents, prints what
`decodeBytes` makes of them. -/
lean_exe jsonfuzz where
  root := `Fuzz.Json

import Lake
open Lake DSL

package cairn_batteries where
  leanOptions := #[⟨`weak.cairn.claims.scope, "cairn_batteries"⟩]

require "iamnbutler" / "cairn" @ "^0.1.2"

@[default_target]
lean_lib CairnBatteries where
  defaultFacets := #[LeanLib.staticFacet]

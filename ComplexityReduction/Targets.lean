-- Aggregation module for ComplexityReduction.Targets
-- Auto-generated: imports all submodules.
--
-- Trust boundary for the Schaefer bridge submodules:
--   * `Targets.SchaeferFiniteDomain` is NOT pulled in by `import ...Targets`
--     at all (nothing in the default set imports it); require it explicitly
--     with `import ComplexityReduction.Targets.SchaeferFiniteDomain`.
--   * `Targets.Schaefer` is still imported transitively by `NPCTargetCatalog`
--     (for the `ExternalBridgeKind` metadata enum only), but it carries only
--     audit-only types and no external theorems.
-- The substantive opt-in boundary is data-level: `localTargets` /
-- `initialTargets` exclude external bridge descriptors; use
-- `targetsWithExternalBridges` only with explicit opt-in.

import ComplexityReduction.Targets.CountingCSP
import ComplexityReduction.Targets.FiniteDomainCSP
import ComplexityReduction.Targets.HColoringCatalog
import ComplexityReduction.Targets.HColoringComplexityCatalog
import ComplexityReduction.Targets.Karp21Catalog
import ComplexityReduction.Targets.NPCTargetCatalog
import ComplexityReduction.Targets.NPCTransfer
import ComplexityReduction.Targets.ThreeSAT
import ComplexityReduction.Targets.ThreeSATCompleteBoundary

module

public import STC.Scoped.Context
public import STC.Scoped.Flat
public import STC.Scoped.Model
public import STC.Scoped.Resolver
public import STC.Scoped.Store

/-!
# Typed scoped coeffects, interception, and flat embedding

The ADR-10 production layer over the authoritative P5 dependent coeffect
store.  It adds the typed realm model and references, the semantic/executable
resolver split with finite override support, scoped lookup/insert/erase with
physical-distinctness frame laws, interception metadata with explicit
precedence, persistent derived contexts, and the one-way flat embedding.

This umbrella imports only the `STC.Scoped` family; the finite evidence in
`STC.Examples.Scoped` is never imported by production modules.

## Main declarations

* `STC.Scoped.RealmModel`, `STC.Scoped.RealmRef`: the typed realm boundary;
* `STC.Scoped.Resolver`, `STC.Scoped.ResolverSpec`,
  `STC.Scoped.ResolverUpdate`: the two-layer resolver and its updates;
* `STC.Scoped.RealmStoreOps`, `STC.Scoped.scopedLookup`,
  `STC.Scoped.scopedInsert`, `STC.Scoped.scopedErase`,
  `STC.Scoped.PhysicalDistinct`: the store adapter and frame boundary;
* `STC.Scoped.MetaAlgebra`, `STC.Scoped.InterceptionSpec`,
  `STC.Scoped.ScopedContext`: metadata, interception, and persistent contexts;
* `STC.Scoped.FlatEmbedding`, `STC.Scoped.FlatImage`: the one-way flat model.
-/

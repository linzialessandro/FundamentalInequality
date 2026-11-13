/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Examples.ArtinSchreierDefect.Residue

/-!
# The Artin–Schreier defect example

This is the root module for the example. The development is split as follows:

* `Examples.ArtinSchreierDefect.Basic`: Laurent base, perfect hull, and the
  quadratic Artin–Schreier extension at `p = 2`.
* `Examples.Bridge.Completeness`: rank lifting, uniqueness from
  completeness of the base, and the abstract Ostrowski-sum comparison.
* `Examples.ArtinSchreierDefect.Valuation`: spectral valuations, ramification
  index one, and uniqueness of a compatible valuative relation, using
  `ValuativeExtension.tower` for compatibility along the tower.
* `Examples.ArtinSchreierDefect.Residue`: residue degree one and the
  unconditional Ostrowski sum `Σ eᵢfᵢ = ef = 1 < 2 = [L:K]`.

The polynomial results in `Basic` hold for every prime `p`. Irreducibility
and the valued construction are currently specialised to `p = 2`.
-/

@[expose] public section

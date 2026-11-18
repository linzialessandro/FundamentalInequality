/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Examples.PadicSqrtP.Stage3

/-!
# The defectless extension `ℚ_p(√p)`

This root module exports the Stage 2 contrast example: for every prime `p`,
the extension obtained by adjoining a root of `X² - p` to `ℚ_[p]` has degree
two, ramification index two, inertia degree one, and a unique compatible
valuative relation. Hence `e f = [L : K]`.
-/

@[expose] public section

/-
  KS23 — two order-23 Kochen–Specker candidates (kscert `unresolved.json`) proved non-realizable over ℝ
  in the Lean kernel. Not a default target (the kernel checks take ~1.5 h and ~20 min):
    lake build KS23
-/
import KS23.G07c6.Main
import KS23.G266c.Main

#print axioms KS23.G07c6.not_realizable
#print axioms KS23.G266c.not_realizable

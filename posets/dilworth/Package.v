(** Dilworth's Theorem: The width of a finite poset equals its minimum chain cover number.
    
    This module provides a formalization of Dilworth's theorem and related results.
    
    Key components:
    - Definitions: Basic definitions (chains, antichains, chain covers, width)
    - CardinalArithmetic: Cardinal arithmetic utilities (removal, pigeonhole)
    - InjectionPrinciple: Cardinal injection principle (fully proven)
    - CardinalLemmas: Cardinal extensionality and helper lemmas
    - WidthLowerBound: Proof that width ≤ minimum chain cover (DilworthA)
    - WidthUpperBound: Proof that minimum chain cover ≤ width (DilworthB)
    - DilworthTheorem: Main theorem combining both directions
*)

From Dilworth Require Export CardinalArithmetic.
From Dilworth Require Export Definitions.
From Dilworth Require Export InjectionPrinciple.
From Dilworth Require Export CardinalLemmas.
From Dilworth Require Export WidthLowerBound.
From Dilworth Require Export WidthUpperBound.
From Dilworth Require Export DilworthTheorem.


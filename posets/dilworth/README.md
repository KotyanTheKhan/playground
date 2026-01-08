# Dilworth Module

A complete formalization of Dilworth's theorem: **the width of a finite poset equals its minimum chain cover number**.

This is a standalone Coq theory that depends on the Posets theory.

## Structure

```
posets/dilworth/
├── CardinalArithmetic.v     # Cardinal arithmetic (removal, pigeonhole)
├── Definitions.v            # Chains, antichains, covers, width
├── InjectionPrinciple.v     # Cardinal injection principle (fully proven)
├── CardinalLemmas.v         # Cardinal extensionality helpers
├── WidthLowerBound.v        # width ≤ min chain cover
├── WidthUpperBound.v        # min chain cover ≤ width  
├── DilworthTheorem.v        # Main theorem with corollaries
├── Examples.v               # Usage examples and documentation
├── Package.v                # Module aggregator
├── dune                     # Build configuration
└── README.md                # This file
```

## Usage

### Import everything:
```coq
From Dilworth Require Import Package.
```

### Import specific components:
```coq
From Dilworth Require Import Definitions WidthLowerBound WidthUpperBound DilworthTheorem.
```

### Example:
```coq
From Posets Require Import PosetClasses.
From Dilworth Require Import DilworthTheorem.

(* Use Dilworth's theorem here *)
```

See **Examples.v** for detailed usage examples including:
- Understanding key definitions (chains, antichains, covers)
- Applying Dilworth's main theorem
- Using corollaries and helper lemmas
- Practical workflow for proving poset width

## Components

### Core Infrastructure
- **CardinalArithmetic.v** - Cardinal arithmetic utilities
  - `cardinal_remove` - Removing an element decreases cardinality
  - `cardinal_injection_principle_poly` - Pigeonhole principle for injective functions
  - `Extensionality_Ensembles` - Set extensionality

### Dilworth Theorem
- **Definitions.v** - Chains, antichains, covers, and width
- **InjectionPrinciple.v** - Cardinal injection principle (fully proven, no axioms)
- **CardinalLemmas.v** - Cardinal extensionality helpers
- **WidthLowerBound.v** - Width ≤ minimum chain cover number
- **WidthUpperBound.v** - Minimum chain cover number ≤ width
- **DilworthTheorem.v** - Main theorem and corollaries
- **Examples.v** - Detailed usage examples and documentation
- **Package.v** - Exports all components

## Building

```bash
# Using mise
mise build

# Or with dune
dune build @all
```

## Properties

- ✅ Complete proofs - no axioms or admits
- ✅ Cardinal injection principle fully proven using Axiom of Choice
- ✅ All files compile successfully

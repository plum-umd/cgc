This is the full Agda development which accompanies
"Mechanically Verified Calculational Abstract Interpretation".

- Prelude.agda, Relations.agda, and Classes.agda set up a basic standard library
- Data/*.agda develops theorems about standard datatypes
- OSet/*.agda develops posets and monotonic types like functions and powerset
- OSet/GaloisConnection/*.agda develops classical, Kleisli and constructive Galois connections
- CDGAI/*.agda develops Cousot's calculational derivation of a generic abstract interpreter:
  - CDGAI/Syntax.agda      -- Syntax
  - CDGAI/Semantics.agda   -- Semantics
  - CDGAI/EnvHat.agda      -- Abstraction for environments
  - CDGAI/FaexpHat.agda    -- The calculated generic abstract interpreter

Typechecking CDGAI.agda will trigger typechecking the whole development, which
we provide a command for in the Makefile. To typecheck the development run:

    make

We are using the latest version of Agda: 2.4.2.3.

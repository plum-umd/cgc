This is the full Agda development which accompanies [Mechanically Verified
Calculational Abstract Interpretation](http://arxiv.org/abs/1507.03559) by
Darais and Van Horn .

- Core.agda, Relations.agda, Classes.agda and Data.agda set up a basic standard
  libarary, and are exported by Prelude.agda
- Data/*.agda develops theorems about standard datatypes
- POSet/*.agda develops posets and monotonic types like functions, product and powerset
- POSet/GaloisConnection/*.agda develops classical, Kleisli and constructive Galois connections
- CDGAI/*.agda develops Cousot's calculational derivation of a generic abstract interpreter:
  - CDGAI/Syntax.agda      -- Syntax
  - CDGAI/Semantics.agda   -- Semantics
  - CDGAI/EnvHat.agda      -- Abstraction for environments
  - CDGAI/FaexpHat.agda    -- The calculated generic abstract interpreter

Typechecking CDGAI.agda will trigger typechecking the whole development, which
we provide a command for in the Makefile. To typecheck the development run:

    make

We are using the latest version of Agda: 2.4.2.3.

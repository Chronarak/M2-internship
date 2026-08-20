This a (partial) copy of the repository I used during my M2 internship.

== Building

You will need a working version of Lean, using Elan, possibly with the vscode extension will be the easiest way to get it.

Then, launching ``lake build`` should fetch relevant dependencies and build the project.
Once that is done, you will be able to browse every file interactively.

== Content

The repository has 3 layers:
- ``Lib`` defines the Predicate Box (the underlying ressource algebra is in ``RA.lean``, the CMRA definition in ``ConstrainedPredBox.lean``)
- ``MBLogic`` instantiates it for mutable borrows
- ``Lang`` contains the full formalization of the language (``Place.lean``, ``RValue.lean`` and ``Statement.lean``),
  some definitions for abstractions ``Abstractions.lean``.
  ``BorrowLaws.lean`` contains some laws for mutable borrows along some other tests

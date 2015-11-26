Copyright (c) 2015, Lionel Rieg,
MMultisets, version 1.0

DESCRIPTION
===========

This library provides computational multisets, in the style of MSets/MMaps,
based on maps (MMap).
It was designed to have an extensive number of lemmas covering the basic
operations provided in the interface and their interactions.

The library is structured as follows:
- Preliminary.v: complement to the Coq standard library
- MMultisetInterface.v: Interface of a multiset
- MMultisetWMap.v: Implementation on a decidable non-ordered type.
- MMultisetMap.v: Implementation on a decidable ordered type.
- MMultisetFacts.v: Properties derived from the interface.
- MMultisetExtraOps.v: Additional operations (defined from the interface) with
  their properties.  It currently contains map, max_mult and max (caveat: about
  max_mult/max, only their specifications are present).

If you see any important lemma missing, feel free to contact me (with a proof
of your lemma as I will probably not have the time to do it myself) so that I
can add it.

BUILDING
========

Simply compile all the files with:
     make

To generate the documentation, type
   make html

It is known to compile with Coq v.8.5b3.

LICENCE
=======

This library is available under the CeCILL-B licence.

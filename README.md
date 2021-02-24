free-functors
=============

[![Hackage](https://img.shields.io/hackage/v/free-functors.svg)](https://hackage.haskell.org/package/free-functors)
[![Build Status](https://github.com/sjoerdvisscher/free-functors/workflows/Haskell-CI/badge.svg)]

A free functor is a left adjoint to a forgetful functor. It used to be the case
that the only category that was easy to work with in Haskell was Hask itself, so
there were no interesting forgetful functors.

But the new ConstraintKinds feature of GHC provides an easy way of creating
subcategories of Hask. That brings interesting opportunities for free (and cofree) functors.

The examples directory contains an implementation of non-empty lists as free semigroups,
and automata as free actions. The standard example of free higher order functors is free monads,
and this definition can be found in Data.Functor.HFree.
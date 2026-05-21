# Formalization of Reedy categories

As part of the workshop https://www.mittag-leffler.se/activities/formalizing-higher-categories/
the purpose of this project is to formalize the model category structure on the
category of functors from a Reedy category to a model category, following
the approach in sections C.4/C.5 of the book by Emily Riehl and
Dominic Verity *Elements of ∞-Category Theory* https://emilyriehl.github.io/files/elements.pdf

Goals:
1. very basic properties of Reedy categories ([`Reedy.Basic`](https://github.com/joelriou/reedy/blob/main/Reedy/Reedy/Basic.lean)), the example of the simplex category ([`Reedy.SimplexCategory`](https://github.com/joelriou/reedy/blob/main/Reedy/Reedy/SimplexCategory.lean))
2. the skeleton filtration on the Yoneda functor `C ⥤ Cᵒᵖ ⥤ Type u` is a relative cell complex ([`Reedy.RelativeCellComplex`](https://github.com/joelriou/reedy/blob/main/Reedy/Reedy/RelativeCellComplex.lean))
3. study of the skeleton/coskeleton filtration on functors `C ⥤ D` ([`Reedy.Skeleton`](https://github.com/joelriou/reedy/blob/main/Reedy/Reedy/Skeleton.lean))
4. a weak factorization system on `D` gives a weak factorization system on `C ⥤ D` ([`Reedy.WeakFactorizationSystem`](https://github.com/joelriou/reedy/blob/main/Reedy/Reedy/WeakFactorizationSystem.lean))
5. the model category structure ([`Reedy.ModelCategory`](https://github.com/joelriou/reedy/blob/main/Reedy/Reedy/ModelCategory.lean))

Required auxiliary API:
* API for subfunctors and subbifunctors (some API for `SSet.Subcomplex` should be generalized for `Subfunctor`, and a similar API needs to be developed for `Subfunctor₂`)
* Weighted (co)limits, which are required for 3./4./5.

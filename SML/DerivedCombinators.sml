

(* derived types *)

val Bool = Prod(Unit, Unit)

val TrueV = InlV UnitV

val FalseV = InrV UnitV

(* derived combinators *)

fun tuple_pair e1 e2 = Comp(Pairwise(e1, e2), Duplicate)

fun case_strip el er = Comp(Strip, Case(el, er))

fun predicate p = Comp(Case(Proj2, Proj2), Comp(Distribute, Comp(Pairwise(p, Identity), Duplicate)))

val swap = tuple_pair Proj2 Proj1

val distribute_right = Comp(Case(swap, swap), Comp(Distribute, swap))

fun if_expr p et ef = Comp(case_strip et ef, predicate p)


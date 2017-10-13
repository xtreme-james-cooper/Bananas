
(* derived combinators *)

fun tuple_pair e1 e2 = [Duplicate, Pairwise(e1, e2)]

fun case_strip el er = [Case(el, er), Strip]

fun predicate p = [Duplicate, Pairwise(p @ [Outj "Bool"], []), Distribute, Case([Proj2], [Proj2])]

val swap = tuple_pair [Proj2] [Proj1]

val distribute_right = swap @ [Distribute, Case(swap, swap)]

fun if_expr p et ef = predicate p @ case_strip et ef

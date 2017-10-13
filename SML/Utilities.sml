

fun those [] = []
  | those (NONE   :: _ ) = raise Option.Option
  | those (SOME b :: bs) = b :: those bs

fun option_bind x f = Option.mapPartial f x

type ('a, 'b) assoc = ('a * 'b) list

fun lookup a []             e = raise e a
  | lookup a ((b, c) :: bs) e = if a = b then c else lookup a bs e

fun zip (b :: bs) (c :: cs) = (b, c) :: zip bs cs
  | zip _         _         = []

fun mapWithIndex' _ _ []        = []
  | mapWithIndex' n f (b :: bs) = f (n, b) :: mapWithIndex' (n + 1) f bs

fun mapWithIndex f bs = mapWithIndex' 0 f bs

fun foldr1 _ [] = raise List.Empty
  | foldr1 _ [b] = b
  | foldr1 f (b :: bs) = f (b, foldr1 f bs)
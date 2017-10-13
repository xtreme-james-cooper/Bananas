

fun those [] = []
  | those (NONE :: _) = raise Option.Option
  | those (SOME b :: bs) = b :: those bs

fun option_bind x f = Option.mapPartial f x
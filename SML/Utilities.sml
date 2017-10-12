

fun those [] = SOME []
  | those (NONE :: _) = NONE  
  | those (SOME b :: bs) = case those bs of
        SOME bs' => SOME (b :: bs')
      | NONE => NONE

fun option_bind x f = Option.mapPartial f x
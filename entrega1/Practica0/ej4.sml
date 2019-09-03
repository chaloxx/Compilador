open tigerabs 


val cant = 0;


fun maxArgs (CallExp (reg,_))  = if (#func reg) = "print" then length (#args reg)
                                 else 0
    | maxArgs _ = 0
      
;


val res = let val r = maxArgs (CallExp ({func = "print", args = [StringExp ("hola",0)]},0))
          in Int.toString r
          end
;


val _ = print "hola"

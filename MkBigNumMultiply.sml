functor MkBigNumMultiply(structure BNA : BIGNUM_ADD
                         structure BNS : BIGNUM_SUBTRACT
                         sharing BNA.Util = BNS.Util) : BIGNUM_MULTIPLY =
struct
  structure Util = BNA.Util
  open Util
  open Seq
  open Primitives
  exception NotYetImplemented

  infix 6 ++ --
  infix 7 **

  fun x ++ y = BNA.add (x, y)
  fun x -- y = BNS.sub (x, y)
  
  fun add0 (len,t) =
    append(t,tabulate (fn _ => ZERO ) len)
  fun add0_ (len,t) =
    append(tabulate (fn _ => ZERO) len, t)

  fun baseMultiply (ONE,ONE)  = singleton ONE
    | baseMultiply _      = empty()

  fun getSameXY (x,y) = 
    let 
      val x_len = length x
      and y_len = length y
    in
      if x_len<y_len then (add0(y_len - x_len,x),y)
      else if x_len=y_len then (x,y)
      else (x,add0(x_len - y_len,y))
    end

  fun multiply (x,y)=
    let 
      val (x',y') = getSameXY(x,y)
      val len = length x'
    in
      if len = 0 then empty()
      else if len = 1 then baseMultiply(nth x' 0, nth y' 0)
      else 
        let
          val h = len div 2
          val (q,p) = (take(x',h),drop(x',h))
          val (s,r) = (take(y',h),drop(y',h))
          val pr = multiply(p,r)
          val qs = multiply(q,s)
          val pqrs = (multiply((p ++ q),(r ++ s)) -- pr ) -- qs
          val pr'= add0_ (2*h,pr)
          val pqrs' = add0_ (h,pqrs)
        in
          pr' ++ pqrs' ++ qs
        end
    end

  fun x ** y =
   multiply(x,y) 

  val mul = op**
end

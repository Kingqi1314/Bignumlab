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
  (*
  * 在t串后面补长度为len的零
  * @ param 
  *   len ：int ：补零的位数
  *   t   ：bignum  ：要进行补零操作的位串
  * @ return ：bignum
  *   返回补完零之后的位串
  * @ work ：O(n) (n=len)
  * @ span ：O(1)
  * *)  
  fun add0 (len,t) =
    append(t,tabulate (fn _ => ZERO ) len)
  (*
  * 在t串前面补长度为len的零
  * @ param 
  *   len ：int ：补零的位数
  *   t   ：bignum  ：要进行补零操作的位串
  * @ return ：bignum
  *   返回补完零之后的位串
  * @ work ：O(n) (n=len)
  * @ span ：O(1)
  * *)
  fun add0_ (len,t) =
    append(tabulate (fn _ => ZERO) len, t)
  (*
  * 乘操作的原子操作
  * @ param 
  *   x : bit : 进行乘法的第一个数
  *   y : bit : 进行乘法的第二个数
  * @ return : bignum
  *   返回乘法操作后的串  当x=ONE,y=ONE
  *   时，返回ONE，其他的情况返回一个空串代表ZERO
  * @ work ：O(1)
  * @ span : O(1)
  * *)
  fun baseMultiply (ONE,ONE)  = singleton ONE
    | baseMultiply _      = empty()
  (*
  * 根据x，y的长度获取两者等长的位串
  * @ param 
  *   x ：bignum ：第一个乘数
  *   y ：bignum ：第二个乘数
  * @ return ：(bignum * bignum)
  *   返回等长的串 x，y
  * @ work : O(n-m) (n=max{length x ,length y},m={length x,length y})
  * @ span : O(1)
  * *)
  fun getSameXY (x,y) = 
    let 
      val x_len = length x
      and y_len = length y
    in
      if x_len<y_len then (add0(y_len - x_len,x),y)
      else if x_len=y_len then (x,y)
      else (x,add0(x_len - y_len,y))
    end
  (*
  * 乘法操作
  * @ param  
  *   x ：bignum ：第一个乘数
  *   y ：bignum ：第二个乘数
  * @ return : bignum
  *   返回x*y的位串
  * @ work : O(n^1.585)
  * @ span : O((lgn)^2)
  * *)
  fun multiply (x,y)=
    let 
      val (x',y') = getSameXY(x,y)
      val len = length x'
    in
      (*w=O() s=O()*)
      if len = 0 then empty()
      (*w=O() s=O()*)
      else if len = 1 then baseMultiply(nth x' 0, nth y' 0)
      else 
        let
          (*w=O(1) s=O(1)*)
          val h = len div 2
          (*w=O(1) s=O(1)*)
          val (q,p) = (take(x',h),drop(x',h))
          (*w=O(1) s=O(1)*)
          val (s,r) = (take(y',h),drop(y',h))
          (*
          * w(n)=3w(n/2)+O(n) 
          * s(n)=s(n/2)+O(lg n)
          * *)
          val (pr,qs,pqrs) = par3(fn() => multiply(p,r) ,
                                  fn() => multiply(q,s) ,
                                  fn() => multiply((p ++ q ),(r ++ s)))
          (*w=O(n) s=O(lg n)*)
          val pqrs' = pqrs -- pr  -- qs
          (*w=O(n) s=O(1)*)
          val pr'= add0_ (2*h,pr)
          (*w=O(n) s=O(1)*)
          val pqrs'' = add0_ (h,pqrs')
        in
          (*w=O(n) s=O(lg n)*)
          pr' ++ pqrs'' ++ qs
        end
    end

  fun x ** y =
   multiply(x,y) 

  val mul = op**
end

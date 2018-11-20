functor MkBigNumAdd(structure U : BIGNUM_UTIL) : BIGNUM_ADD =
struct
  structure Util = U
  open Util
  open Seq

  infix 6 ++
  exception NotYetImplemented
  datatype carry = GEN | PROP | STOP

  fun sum (a,b) = 
     let 
       val a_len = length a
       and b_len = length b
       (*O(n-m)
       * n is the length of seq a
       * m is the length of seq b
       * this function aims to get the same length a and b'
       * *)
       fun getSameLenSeq (l1,l2,(t:bit seq)) =(*l1>l2*)
         append(t,tabulate (fn _ => ZERO) (l1 - l2))
       (*
       * O(1)
       * 1+1=0 generate a carry
       * 1+0=0+1=1 may propagate a carry
       * 0+0=0 stop a carry
       * *)   
       fun eleOperate (ZERO,ZERO) = STOP
         | eleOperate (ZERO,ONE ) = PROP
         | eleOperate (ONE ,ZERO) = PROP
         | eleOperate (ONE ,ONE ) = GEN

       (*
       * O(1)
       * dev and remove the PROP
       *
       * *)
       fun dev (m,n) =
         if n=PROP then m else n
        (*
        * O(1)
        * get the result accordding to the carry seq and carry_dev seq
        * *)
       fun getRes (p,q) = 
         if p=STOP orelse p=GEN then 
           if q=GEN then ONE 
           else ZERO
         else
           if q=GEN then ZERO
           else ONE
     in
       if a_len < b_len then sum(b,a)
       else 
          let 
            (*w=O(n-m) s=O(1)*)
            val b' = getSameLenSeq(a_len,b_len,b)
            (*w=O(n) s=O(lg n)*)
            val carry = map2  eleOperate a b'
            (*w=O(n) s=O(lg n)
            * scan is implemented with constraction
            * *)
            val (carry_dev,last) = scan dev STOP carry
            (*w=O(n) s=O(lg n) *) 
            val res = map2 getRes carry carry_dev
          in
            (*w=O(1) s=O(1)*)
            if last=GEN then append(res,singleton ONE)
            else res
          end
     end

  fun x ++ y =
    sum(x,y)
  val add = op++
end

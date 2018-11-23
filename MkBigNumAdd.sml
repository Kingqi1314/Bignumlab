functor MkBigNumAdd(structure U : BIGNUM_UTIL) : BIGNUM_ADD =
struct
  structure Util = U
  open Util
  open Seq

  infix 6 ++
  exception NotYetImplemented
  datatype carry = GEN | PROP | STOP
  (*
  * 求和函数
  * @ param 
  *   a：int：第一个加数
  *   b：int：第二个加数
  * @ return ：int
  *   返回a和b的和
  * @ work ：O(n)
  * @ span : O(lg n)
  * *)
  fun sum (a,b) = 
     let 
       val a_len = length a
       and b_len = length b
       (*
       * 通过补零获取到相同长度的bignum
       * @ param
       *   l1：int：目标串的长度
       *   l2：int：原始串的长度
       *   t ：bignum：原始串
       * @ return ：bignum
       *   返回与l1长度的补零t串
       * @ work ：O(n-m)（n=l1,m=l2）
       * @ span : O(1) 
       * *)
       fun getSameLenSeq (l1,l2,(t:bit seq)) =(*l1>l2*)
         append(t,tabulate (fn _ => ZERO) (l1 - l2))
       (*
       * 原子操作
       * @ param 
       *   x：bit：第一个加数
       *   y：bit：第二个加数
       * @ describe
       *   如果x=ZERO,y=ZERO ，则产生STOP ，停止进位
       *   如果x=ZERO,y=ONE  ，则产生PROP ，可能传递一个进位
       *   如果x=ONE,y=ZERO  ，则产生PROP ，可能传递一个进位
       *   如果x=ONE,y=ONE   ，则产生GEN ，产生一个进位
       * @ work ：O(1)
       * @ span : O(1)
       * *)   
       fun eleOperate (ZERO,ZERO) = STOP
         | eleOperate (ZERO,ONE ) = PROP
         | eleOperate (ONE ,ZERO) = PROP
         | eleOperate (ONE ,ONE ) = GEN

       (*
       * 将获得的carry串进行偏移，并将prop消除
       * @ param 
       *   m ：carry：前一个元素的操作结果
       *   n ：carry：将要操作的元素
       * @ return ： carry
       *   返回操作结果
       *   如果是prop则操作结果为前一个元素的操作结果，如果不是返回本元素，作为下面map的操作函数
       * @ work ：O(1)
       * @ span : O(1)
       * *)
       fun dev (m,n) =
         if n=PROP then m else n
        (*
        * 根据carry的结果计算出bit位
        * @ param
        *   p ：carry：第一个进行操作的元素，来自carry串
        *   q ：carry：第二个进行操作的元素，来自carry_dev串
        * @ return ： bit 
        *   返回p，q的匹配结果
        * @ describe 
        *   当p为STOP或者GEN，代表经过原子操作后本为剩余的数字为零
        *       q为GEN时代表有一个进位，则为ONE
        *       否则（q为STOP）没有进位，则为ZERO
        *   当p为PROP时，代表经过原子操作后本位剩余的是ONE
        *       q为GEN时表示从低一位获得一个进一位，则经过操作后表为ZERO（1+1=0）
        *       否则（q为STOP）没有进位，则为ONE
        * @ work ：O(1)
        * @ span ：O(1)
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

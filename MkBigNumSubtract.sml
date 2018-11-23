functor MkBigNumSubtract(structure BNA : BIGNUM_ADD) : BIGNUM_SUBTRACT =
struct
  structure Util = BNA.Util
  open Util
  open Seq

  exception NotYetImplemented
  infix 6 ++ --
  fun x ++ y = BNA.add (x, y)
  (*
  * 位元素相减：主函数
  * @ param 
  *   x ：bignum ：减数
  *   y ：bignum ：被减数
  * @ return ：bignum
  *   返回x-y的结果
  * @ work : O(n)
  * @ span : O(lg n)
  * *)
  fun x -- y =
    let 
      val x_len = length x
      and y_len = length y
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
      fun getSameSeq (l1,l2,t) = 
        if l2<l1 then 
           append(t,tabulate (fn _ => ZERO ) (l1-l2))
        else t
      (*
      * bit位反转ZERO和ONE
      * @ param 
      *   x ：bit ：如果是ONE就反转为ONE，如果是ZERO，就反转为ONE
      * @ return ：bit
      *   返回反转后的结果
      * @ work ：O(1)
      * @ span ：O(1)
      * *)
      fun revOZ ONE  = ZERO
        | revOZ ZERO = ONE
    in
      let
        (*w=O(n-m) s=O(1)*)
        val t = getSameSeq(x_len,y_len,y)
        (*w=O(n) s=O(lgn)*)
        val t' = map revOZ t
        (*w=O(n) s=O(lgn)*)
        val y' = t' ++ (singleton ONE)
      in
        (*w=O(1) s=O(1)*)
        take(x ++ y', x_len)
      end
    end
      
  val sub = op--
end

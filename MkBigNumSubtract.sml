functor MkBigNumSubtract(structure BNA : BIGNUM_ADD) : BIGNUM_SUBTRACT =
struct
  structure Util = BNA.Util
  open Util
  open Seq

  exception NotYetImplemented
  infix 6 ++ --
  fun x ++ y = BNA.add (x, y)
  fun x -- y =
    let 
      val x_len = length x
      and y_len = length y
      (*
      * O(n-m)
      * *)
      fun getSameSeq (l1,l2,t) = 
        if l2<l1 then 
           append(t,tabulate (fn _ => ZERO ) (l1-l2))
        else t
      (*
      * O(1)
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
        (*O(1)*)
        take(x ++ y', x_len)
      end
    end
      
  val sub = op--
end

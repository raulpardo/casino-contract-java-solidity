package blockchain.types;

import java.math.BigInteger;

/**
 * The current specification models Uint256 faithfully (with overflow). 
 * If we want to verify that a contract has no operation that will overflow we
 * can amend the contracts to detect overflows and to throw exceptions.
 * 
 * Idea: introduce static boolean ghost field like ALLOW_OVERFLOW and make precodition depend on its value.
 * 
 */
public interface Uint256 {

         // actual literal moved to utitlityFunctionsDeclarations due to KeY's JML parser problem with long literals
         // public static final ghost \bigint MAX = (\bigint)115792089237316195423570985008687907853269984665640564039457584007913129639935;

        //@ private instance accessible \inv: _value;
        //@ public instance accessible \inv: \empty;

        // one for each uint256 used in sOlidity contract
        //@ private instance invariant ZERO._value == 0;
        public static final Uint256 ZERO = new Uint256Int(0);
        //@ private instance invariant ONE._value == 1;
        public static final Uint256 ONE = new Uint256Int(1);
        //@ private instance invariant TWO._value == 2;
        public static final Uint256 TWO = new Uint256Int(2);

        //@ private instance invariant _value >= 0 && _value <= \dl_MAXUINT256();
        //@ private final instance ghost \bigint _value;        

        /*@  private normal_behavior
          @  ensures \result._value == \dl_keccak256(this._value);
          @  ensures \invariant_for(\result);
          @  accessible _value;
          @  accessible<savedHeap> \nothing;
          @  assignable<heap><savedHeap> \strictly_nothing;
          @  
          @  also
          @
          @  public normal_behavior
          @  ensures \result == keccak256();
          @  accessible \nothing;
          @  accessible<savedHeap> \nothing;
          @  assignable<heap><savedHeap> \strictly_nothing; 
          @*/
        Uint256 keccak256();
        
        /*@  private normal_behavior
          @  ensures \result._value == \dl_sha3(this._value);
          @  ensures \invariant_for(\result);
          @  accessible _value;
          @  accessible<savedHeap> \nothing;
          @  assignable<heap><savedHeap> \strictly_nothing;
          @  
          @  also
          @
          @  public normal_behavior
          @  ensures \result == sha3();
          @  accessible \nothing;
          @  accessible<savedHeap> \nothing;
          @  assignable<heap><savedHeap> \strictly_nothing; 
          @*/
        Uint256 sha3();

        /*@  private normal_behavior
          @  ensures \result == (this._value <= value._value);
          @  accessible _value, value._value;
          @  accessible<savedHeap> \nothing;
          @  assignable<heap><savedHeap> \strictly_nothing;
          @ 
          @  also
          @
          @  public normal_behavior
          @  ensures \result == leq(value);
          @  accessible \nothing;
          @  assignable \nothing;
          @  accessible<savedHeap> \nothing;
          @  assignable<savedHeap> \strictly_nothing;
          @*/
        boolean leq(Uint256 value);
        
        /*@  private normal_behavior
          @  ensures \result == (this._value >= value._value);
          @  accessible _value, value._value;
          @  accessible<savedHeap> \nothing;
          @  assignable<heap><savedHeap> \strictly_nothing;
          @
          @  also
          @
          @  public normal_behavior
          @  ensures \result == geq(value);
          @  accessible \nothing;
          @  assignable \nothing;
          @  accessible<savedHeap> \nothing;
          @  assignable<savedHeap> \strictly_nothing;          
          @*/
        boolean geq(Uint256 value);

        /*@  private normal_behavior
          @  ensures \result == (this._value > value._value);
          @  accessible _value, value._value;
          @  accessible<savedHeap> \nothing;
          @  assignable<heap><savedHeap> \strictly_nothing;
          @
          @  also
          @
          @  public normal_behavior
          @  ensures \result == gr(value);
          @  accessible \nothing;
          @  assignable \nothing;
          @  accessible<savedHeap> \nothing;
          @  assignable<savedHeap> \strictly_nothing;
          @*/
        boolean gr(Uint256 value);

        /*@  private normal_behavior
          @  ensures \result == (this._value < value._value);
          @  accessible _value, value._value;
          @  accessible<savedHeap> \nothing;
          @  assignable<heap><savedHeap> \strictly_nothing;
          @
          @  also
          @
          @  public normal_behavior
          @  ensures \result == le(value);
          @  accessible \nothing;
          @  assignable \nothing;
          @  accessible<savedHeap> \nothing;
          @  assignable<savedHeap> \strictly_nothing;
          @*/
        boolean le(Uint256 value);

        /*@  private normal_behavior
          @  ensures \result == (this._value == value._value);
          @  accessible _value, value._value;
          @  assignable<heap><savedHeap> \strictly_nothing;
          @
          @  also
          @
          @  public normal_behavior
          @  ensures \result == eq(value);
          @  accessible<heap><savedHeap> \nothing;
          @  assignable<heap><savedHeap> \strictly_nothing;
          @*/
        boolean eq(Uint256 value);

        /*@  private normal_behavior
          @  requires \invariant_for(value);
          @  requires value._value > 0;
          @  ensures \result._value == (this._value % value._value); // TODO: check if % really matches modulo in Uint256
          @  ensures \invariant_for(\result);
          @  accessible _value, value._value;
          @  accessible<savedHeap> \nothing;
          @  assignable<heap><savedHeap> \strictly_nothing;
          @
          @  also
          @ 
          @  public normal_behavior
          @  requires \invariant_for(value);
          @  ensures \result == mod(value);
          @  ensures \invariant_for(\result);
          @  accessible \nothing;
          @  assignable \nothing;
          @  accessible<savedHeap> \nothing;
          @  assignable<savedHeap> \strictly_nothing;          
          @*/
        Uint256 mod(Uint256 value) throws Exception;

        /*@  private normal_behavior
          @  requires \invariant_for(value);
          @  requires value._value > 0;
          @  ensures \result._value == (this._value / value._value); // TODO: check if / really matches div in Uint256
          @  ensures \invariant_for(\result);
          @  accessible _value, value._value;
          @  accessible<savedHeap> \nothing;
          @  assignable<heap><savedHeap> \strictly_nothing;
          @
          @  also
          @ 
          @  public normal_behavior
          @  requires \invariant_for(value);
          @  ensures \result == div(value);
          @  ensures \invariant_for(\result);
          @  accessible \nothing;
          @  assignable \nothing;
          @  accessible<savedHeap> \nothing;
          @  assignable<savedHeap> \strictly_nothing;          
          @*/
        Uint256 div(Uint256 value) throws Exception;

        /*@  private normal_behavior
          @  requires \invariant_for(value);
          @  ensures \result._value == (this._value * value._value) % (\dl_MAXUINT256() + 1);
          @  ensures \invariant_for(\result);
          @  accessible _value, value._value;
          @  accessible<savedHeap> \nothing;
          @  assignable<heap><savedHeap> \strictly_nothing;
          @
          @  also
          @ 
          @  public normal_behavior
          @  requires \invariant_for(value);
          @  ensures \result == mul(value);
          @  ensures \invariant_for(\result);
          @  accessible \nothing;
          @  assignable \nothing;
          @  accessible<savedHeap> \nothing;
          @  assignable<savedHeap> \strictly_nothing;          
          @*/
        Uint256 mul(Uint256 value) throws Exception;

        /*@  private normal_behavior
          @  requires \invariant_for(value);
          @  ensures \result._value == (this._value >= value._value ? (\bigint) 0 : \dl_MAXUINT256() + (\bigint)1) + (this._value - value._value);
          @  ensures \invariant_for(\result);
          @  accessible _value, value._value;
          @  accessible<savedHeap> \nothing;
          @  assignable<heap><savedHeap> \strictly_nothing;
          @  
          @  also
          @  
          @  public normal_behavior
          @  requires \invariant_for(value);
          @  ensures \result == sub(value);
          @  ensures value.eq(this) ==> sub(value).eq(ZERO);
          @  ensures \invariant_for(\result);
          @  accessible \nothing;
          @  assignable \nothing;
          @  accessible<savedHeap> \nothing;
          @  assignable<savedHeap> \strictly_nothing;
          @*/
        Uint256 sub(Uint256 value) throws Exception;

        /*@  private normal_behavior
          @  requires \invariant_for(value);
          @  ensures \result._value ==
          @     (this._value + value._value > \dl_MAXUINT256() ? 
          @           ((\bigint)-1)*\dl_MAXUINT256() - 1 : (\bigint) 0) + this._value + value._value; 
          @  ensures \invariant_for(\result);
          @  accessible _value, value._value;
          @  accessible<savedHeap> \nothing;
          @  assignable<heap><savedHeap> \strictly_nothing;
          @
          @  also
          @
          @  public normal_behavior
          @  requires \invariant_for(value);
          @  ensures \result == sum(value);
          @  ensures \invariant_for(\result);
          @  accessible \nothing;
          @  assignable \nothing;
          @  accessible<savedHeap> \nothing;
          @  assignable<savedHeap> \strictly_nothing;
          @*/
        Uint256 sum(Uint256 value) throws Exception;
        
        Uint256 pow(Uint256 value) throws Exception;

        Uint256 and(Uint256 value) throws Exception;

        Uint256 or(Uint256 value) throws Exception;

        /*@ private normal_behavior
          @ ensures \result == _value;
          @ accessible _value;
          @ assignable \strictly_nothing;
          @*/
        int asInt();
        
        // not specified as we do not want to specify class BigInteger
        // Our solidity contract verification should not depend on
        // classes implementing this Uint256 interface.
        BigInteger asBigInteger();

        /*@ private normal_behavior
          @ requires i >= 0;
          @ ensures \result._value == i;
          @ ensures \invariant_for(\result);
          @ assignable \nothing;
          @ 
          @ also
          @ 
          @ public exceptional_behavior
          @ requires i < 0;
          @ signals (ArithmeticException) true;
          @ assignable \nothing;
          @*/
        Uint256 valueOf(int i);

}

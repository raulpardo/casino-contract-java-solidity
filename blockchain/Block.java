package blockchain;

import blockchain.types.*;

public final class Block {
   //@ public model \locset footprint;
   //@ public represents footprint = this.*;
   //@ public accessible \inv: footprint;
   //@ public accessible footprint: footprint;
	
  /*@ public invariant \invariant_for(coinbase); @*/
  public Address coinbase;     // current block miner’s address

  /*@ public invariant \invariant_for(difficulty); @*/
  public Uint256 difficulty;   // current block difficulty
  
  /*@ public invariant \invariant_for(gaslimit); @*/
  public Uint256 gaslimit;     // current block gaslimit
  
  /*@ public invariant \invariant_for(number); @*/
  public Uint256 number;       // current block number
  
  /*@ public invariant \invariant_for(timestamp); @*/
  public Uint256 timestamp;    // current block timestamp as seconds since unix epoch


  
  public byte[] blockhash(Uint256 blockNumber) {
    // returns hash (byte array of size 32) of the given block - only works for 256 most recent blocks excluding current
    return new byte[10]; // TODO(raul): return an appropriate value
  }
}

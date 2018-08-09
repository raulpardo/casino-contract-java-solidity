package blockchain;

import blockchain.types.*;

public final class Transaction {
	//@ public model \locset footprint;
	//@ public represents footprint = \set_union(origin.footprint, \set_union(this.gasprice, this.origin));
	//@ public accessible \inv: footprint;

  //@ public invariant \invariant_for(gasprice);
  Uint256 gasprice;   // gas price of the transaction
  //@ public invariant \invariant_for(origin);
  /*@ spec_public @*/ Address origin;     // sender of the transaction (full call chain)

  public Transaction(Uint256 _gasprice, Address _origin) {
    gasprice = _gasprice;
    origin = _origin;
  }
}
